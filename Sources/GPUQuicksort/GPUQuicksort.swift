import Foundation
import Metal

/// C-01: the public entry point. Calls on one instance are serialized (D-09, E-16).
public final class GPUQuicksort: @unchecked Sendable {
    public static let version = "0.5.0"

    public let device: MTLDevice
    public let limits: DeviceLimits
    public let tuning: TunedConstants
    public let metallibSHA256: String

    let sorter: Sorter
    let lock = NSLock()
    private var _diagnostics: (@Sendable (String) -> Void)?

    /// Receives every diagnostic line of R-22 / §5.3. Getter and setter take the sort lock
    /// (F-027): a set during a running sort blocks until it returns.
    public var diagnostics: (@Sendable (String) -> Void)? {
        get { lock.withLock { _diagnostics } }
        set { lock.withLock { _diagnostics = newValue } }
    }

    public init(device: MTLDevice? = nil, tuning: TuningSource = .bundled) throws {
        guard let dev = device ?? MTLCreateSystemDefaultDevice() else { throw GPUQuicksortError.noMetalDevice }
        guard dev.supportsFamily(.apple7) else { throw GPUQuicksortError.unsupportedDevice(dev.name) }   // K-02
        self.device = dev
        let lib = try ShaderLibrary.load(device: dev)
        metallibSHA256 = lib.stamp
        self.tuning = try Self.resolveTuning(tuning, deviceName: dev.name)
        sorter = try Sorter(device: dev, library: lib)
        limits = DeviceLimits(name: dev.name,
                              maxThreadsPerThreadgroup: sorter.maxThreadsPerThreadgroup,
                              threadExecutionWidth: sorter.psoLQ.threadExecutionWidth,
                              maxThreadgroupMemoryLength: dev.maxThreadgroupMemoryLength,
                              maxBufferLength: dev.maxBufferLength,
                              maxKeys: DeviceLimits.maxKeys(maxBufferLength: dev.maxBufferLength))
    }

    /// C-10 lookup and validation for each TuningSource (E-20, E-21).
    static func resolveTuning(_ source: TuningSource, deviceName: String) throws -> TunedConstants {
        switch source {
        case .constants(let c):
            try c.validate()
            var c = c
            c.entry = "constants"
            c.exactMatch = false
            return c
        case .bundled:
            guard let url = ShaderLibrary.resourceURL("TunedParameters", "json"),
                  let data = try? Data(contentsOf: url) else {
                throw GPUQuicksortError.tunedParametersInvalid("Resources/TunedParameters.json is missing")
            }
            return try TunedTable.decode(data).lookup(deviceName: deviceName)
        case .file(let url):
            guard let data = try? Data(contentsOf: url) else {
                throw GPUQuicksortError.tunedParametersInvalid("cannot read \(url.path)")
            }
            return try TunedTable.decode(data).lookup(deviceName: deviceName)
        }
    }

    /// Resolves .automatic / partial parameters exactly as `sort` would (K-04, K-05).
    public func resolvedParameters(for n: Int, _ p: Parameters) throws -> ResolvedParameters {
        guard n >= 0, n <= limits.maxKeys else { throw GPUQuicksortError.tooManyKeys(count: n, max: limits.maxKeys) }
        return try ParameterResolver.resolve(n: n, parameters: p, tuning: tuning, limits: limits)
    }

    /// Sorts `count` keys starting at byte 0 of `buffer` (`.shared`). Synchronous; not cancellable.
    @discardableResult
    public func sort(_ buffer: MTLBuffer, count: Int, keyType: KeyType,
                     parameters: Parameters = .automatic) throws -> SortReport {
        lock.lock()
        defer { lock.unlock() }
        sorter.runner.reset()
        let handler = _diagnostics
        // Validation happens before the buffer is touched (I-006).
        guard count >= 0, count <= limits.maxKeys else {
            throw GPUQuicksortError.tooManyKeys(count: count, max: limits.maxKeys)            // E-08
        }
        let resolved = try ParameterResolver.resolve(n: count, parameters: parameters, tuning: tuning, limits: limits)
        var report = SortReport(count: count, keyType: keyType, parameters: resolved, wallTime: 0, gpuTime: 0,
                                phaseOneIterations: 0, phaseOneSequences: 0, phaseOneCapReached: false,
                                phaseTwoPartitions: 0, phaseTwoAltSorts: 0, maxStackDepth: 0,
                                auxiliaryBytes: 0, bookkeepingBytes: 0, libraryVersion: Self.version,
                                metallibSHA256: metallibSHA256, tuningEntry: tuning.entry)
        if count <= 1 {                                                                      // E-01, E-02
            Diagnostics.emit(Diagnostics.summary(report), handler)
            return report
        }
        guard buffer.storageMode == .shared else { throw GPUQuicksortError.bufferNotShared }   // E-06
        guard buffer.length >= 4 * count else {
            throw GPUQuicksortError.bufferTooSmall(required: 4 * count, actual: buffer.length) // E-07
        }
        let clock = ContinuousClock()
        let start = clock.now
        sorter.diagnosticLine = { Diagnostics.emit($0, handler) }
        defer { sorter.diagnosticLine = nil }
        let c = try sorter.run(buffer, n: count, key: keyType, p: resolved)
        report.wallTime = (clock.now - start).seconds
        report.gpuTime = sorter.runner.gpuTime
        report.phaseOneIterations = c.phaseOneIterations
        report.phaseOneSequences = c.phaseOneSequences
        report.phaseOneCapReached = c.phaseOneCapReached
        report.phaseTwoPartitions = c.phaseTwoPartitions
        report.phaseTwoAltSorts = c.phaseTwoAltSorts
        report.maxStackDepth = c.maxStackDepth
        report.auxiliaryBytes = 4 * count
        report.bookkeepingBytes = c.bookkeepingBytes
        Diagnostics.emit(Diagnostics.summary(report), handler)
        return report
    }

    /// Convenience: copies into a shared staging buffer, sorts, copies back. Copy time is
    /// included in wallTime (C-01).
    @discardableResult
    public func sort<K: GPUSortableKey>(_ keys: inout [K], parameters: Parameters = .automatic) throws -> SortReport {
        let clock = ContinuousClock()
        let start = clock.now
        let n = keys.count
        guard n <= limits.maxKeys else { throw GPUQuicksortError.tooManyKeys(count: n, max: limits.maxKeys) }
        let staging = try sorter.pool.make(4 * n)
        keys.withUnsafeBytes { if $0.count > 0 { memcpy(staging.contents(), $0.baseAddress!, $0.count) } }
        var r = try sort(staging, count: n, keyType: K.keyType, parameters: parameters)
        keys.withUnsafeMutableBytes { if $0.count > 0 { memcpy($0.baseAddress!, staging.contents(), $0.count) } }
        r.wallTime = (clock.now - start).seconds
        return r
    }

    /// GPU codec pass over a buffer (package-level; used by T-05's GPU round trip).
    package func gpuCodec(_ buffer: MTLBuffer, count: Int, key: KeyType, encode: Bool) throws {
        try lock.withLock { try sorter.codec(buffer, n: count, key: key, encode: encode) }
    }
}

extension Duration {
    var seconds: Double { Double(components.seconds) + Double(components.attoseconds) * 1e-18 }
}

#if GPUQS_TEST_HOOKS
extension GPUQuicksort {
    /// Test hook (debug builds only): report the k-th command buffer of each sort as failed (T-42).
    package func setTestFailCommandBuffer(_ k: Int?) { lock.withLock { sorter.runner.failCommandBuffer = k } }
}
#endif
