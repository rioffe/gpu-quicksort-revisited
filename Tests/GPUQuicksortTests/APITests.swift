import Foundation
import Metal
import Testing
@testable import GPUQuicksort

@Suite("API", .serialized, .requiresGPU)
struct APITests {
    static let q: GPUQuicksort? = try? GPUQuicksort()

    static func shared(_ bits: [UInt32], extra: Int = 0) -> MTLBuffer {
        let len = max(4 * bits.count + extra, 4)
        let b = TS.device!.makeBuffer(length: len, options: .storageModeShared)!
        bits.withUnsafeBytes { _ = memcpy(b.contents(), $0.baseAddress!, $0.count) }
        return b
    }
    static func contents(_ b: MTLBuffer, _ n: Int) -> [UInt32] {
        Array(UnsafeBufferPointer(start: b.contents().assumingMemoryBound(to: UInt32.self), count: n))
    }

    /// T-06 (report half; the "no command buffer" half via hook counters is in StructureTests):
    /// n = 0 and n = 1 return a report with zero counters and both byte counts 0, and leave the
    /// buffer byte-identical. Proves E-01, E-02.
    @Test func tinyInputs() throws {
        let q = try #require(Self.q)
        let buf = Self.shared([0xDEAD_BEEF, 7])
        for n in [0, 1] {
            let r = try q.sort(buf, count: n, keyType: .uint32)
            #expect(r.count == n)
            #expect(r.phaseOneIterations == 0 && r.phaseOneSequences == 0 && r.phaseTwoPartitions == 0)
            #expect(r.phaseTwoAltSorts == 0 && r.maxStackDepth == 0 && !r.phaseOneCapReached)
            #expect(r.auxiliaryBytes == 0 && r.bookkeepingBytes == 0)
            #expect(Self.contents(buf, 2) == [0xDEAD_BEEF, 7])
        }
        let empty = try #require(TS.device?.makeBuffer(length: 0 + 16, options: .storageModeShared))
        #expect(try q.sort(empty, count: 0, keyType: .float32).count == 0)
    }

    /// T-18: explicit T = 48, T = 2048, minseq = 100, minseq above the K-03 bound, maxseq = 0 and
    /// maxPhaseOneIterations = 0 each throw `invalidParameters` naming the parameter, and the
    /// buffer is byte-identical afterwards; every failure is a typed C-07 error (R-18).
    /// Proves K-04, K-03, E-05, I-006, R-18, C-07.
    @Test func invalidParameters() throws {
        let q = try #require(Self.q)
        let input = Distribution.generate(.uniform, n: 5000, seed: 1, key: .uint32)
        let buf = Self.shared(input)
        let cases: [(Parameters, String)] = [
            (Parameters(threadsPerThreadgroup: 48), "threadsPerThreadgroup"),
            (Parameters(threadsPerThreadgroup: 2048), "threadsPerThreadgroup"),
            (Parameters(minSequenceLength: 100), "minSequenceLength"),
            (Parameters(threadsPerThreadgroup: 256, minSequenceLength: 1 << 14), "minSequenceLength"),
            (Parameters(maxSequences: 0), "maxSequences"),
            (Parameters(maxPhaseOneIterations: 0), "maxPhaseOneIterations"),
        ]
        for (p, name) in cases {
            do {
                _ = try q.sort(buf, count: input.count, keyType: .uint32, parameters: p)
                Issue.record("expected invalidParameters for \(name)")
            } catch GPUQuicksortError.invalidParameters(let msg) {
                #expect(msg.hasPrefix(name), "\(msg)")
            }
            #expect(Self.contents(buf, input.count) == input)
        }
    }

    /// T-19: a `.private` buffer throws `bufferNotShared`; a buffer of 4n - 1 bytes throws
    /// `bufferTooSmall`; count = -1 and count = maxKeys + 1 throw `tooManyKeys`; buffers are
    /// untouched; each failure is the typed C-07 case named by §8 (R-18).
    /// Proves E-06, E-07, E-08, K-01, I-006, R-18, C-07.
    @Test func invalidBuffers() throws {
        let q = try #require(Self.q)
        let dev = try #require(TS.device)
        let priv = try #require(dev.makeBuffer(length: 4096, options: .storageModePrivate))
        #expect(throws: GPUQuicksortError.bufferNotShared) { try q.sort(priv, count: 1024, keyType: .uint32) }
        let input = Distribution.generate(.uniform, n: 999, seed: 2, key: .uint32)
        let small = dev.makeBuffer(length: 4 * 1000 - 1, options: .storageModeShared)!
        input.withUnsafeBytes { _ = memcpy(small.contents(), $0.baseAddress!, $0.count) }
        #expect(throws: GPUQuicksortError.bufferTooSmall(required: 4000, actual: 3999)) {
            try q.sort(small, count: 1000, keyType: .uint32)
        }
        #expect(Self.contents(small, 999) == input)
        #expect(throws: GPUQuicksortError.tooManyKeys(count: -1, max: q.limits.maxKeys)) {
            try q.sort(small, count: -1, keyType: .uint32)
        }
        #expect(throws: GPUQuicksortError.tooManyKeys(count: q.limits.maxKeys + 1, max: q.limits.maxKeys)) {
            try q.sort(small, count: q.limits.maxKeys + 1, keyType: .uint32)
        }
        #expect(q.limits.maxKeys == min(Int(Int32.max), q.limits.maxBufferLength / 4))   // K-01
        #expect(Self.contents(small, 999) == input)
    }

    /// T-20 (API half): `resolvedParameters(for:)` with `.constants(.paper8800GTX)` returns
    /// (64, 512, 256) for n = 2^20 and (256, 1024, 1024) for n = 2^24 on this device; with
    /// `.bundled` it equals optp computed from `GPUQuicksort.tuning`. The default phase-one pivot
    /// is `minMaxAverage` (R-11, D-10 revised v0.5). Proves K-05, R-16, C-10, R-11.
    @Test func resolvedParametersAPI() throws {
        let paper = try GPUQuicksort(tuning: .constants(.paper8800GTX))
        func t(_ r: ResolvedParameters) -> [Int] { [r.threadsPerThreadgroup, r.maxSequences, r.minSequenceLength] }
        #expect(t(try paper.resolvedParameters(for: 1 << 20, .automatic)) == [64, 512, 256])
        #expect(t(try paper.resolvedParameters(for: 1 << 24, .automatic)) == [256, 1024, 1024])
        let q = try #require(Self.q)
        let c = q.tuning
        let r = try q.resolvedParameters(for: 1 << 22, .automatic)
        #expect(r.threadsPerThreadgroup == min(max(ParameterResolver.optp(s: 1 << 22, k: c.threads.k, m: c.threads.m), 32), 1024))
        #expect(r.maxSequences == ParameterResolver.optp(s: 1 << 22, k: c.maxseq.k, m: c.maxseq.m))
        #expect(throws: GPUQuicksortError.self) { _ = try q.resolvedParameters(for: q.limits.maxKeys + 1, .automatic) }
        #expect(Parameters.automatic.phaseOnePivot == .minMaxAverage)                          // R-11 default
        #expect(r.phaseOnePivot == .minMaxAverage)
    }

    /// T-37 (init half): `.file` tables that are invalid make `init` throw
    /// `tunedParametersInvalid`, as does `.constants` with m = 0; a table lacking the host's name
    /// resolves to `apple-default`'s target with `exactMatch == false`; the bundled table
    /// validates. Proves C-10, E-20, E-21, C-01.
    @Test func tuningSources() throws {
        _ = try GPUQuicksort(tuning: .bundled)
        let dir = TS.tempDir()
        let badURL = dir.appendingPathComponent("bad.json")
        try Data(#"{"schema":1,"entries":{}}"#.utf8).write(to: badURL)
        #expect { _ = try GPUQuicksort(tuning: .file(badURL)) } throws: { e in
            if case GPUQuicksortError.tunedParametersInvalid = e { return true } else { return false }
        }
        var zero = TunedConstants.paper8800GTX
        zero.minseq.m = 0
        #expect { _ = try GPUQuicksort(tuning: .constants(zero)) } throws: { e in
            if case GPUQuicksortError.tunedParametersInvalid = e { return true } else { return false }
        }
        let goodURL = dir.appendingPathComponent("good.json")
        try Data(#"{"schema":1,"entries":{"Some Other GPU":{"fitted":"x","gpuqsortVersion":"x","sizes":[],"threads":{"k":0,"m":128},"maxseq":{"k":0,"m":256},"minseq":{"k":0,"m":512}},"apple-default":{"sameAs":"Some Other GPU"}}}"#.utf8).write(to: goodURL)
        let q = try GPUQuicksort(tuning: .file(goodURL))
        #expect(q.tuning.entry == "Some Other GPU" && q.tuning.exactMatch == false)
        #expect(try q.resolvedParameters(for: 1000, .automatic).threadsPerThreadgroup == 128)
    }

    /// T-21: the report for `uniform` n = 2^20 has auxiliaryBytes = 4n, bookkeepingBytes within
    /// the §7.1 bound 136 M + 2^16 for the resolved M (and for M = 1 and M = 2^16), count = n,
    /// 0 < gpuTime <= wallTime, parameters equal to resolvedParameters, and provenance fields
    /// equal to the instance's; for n = 1 both byte counts are 0. K-11: `gpuTime` is exactly the
    /// sum of gpuEndTime − gpuStartTime over the sort's command buffers (one duration per commit),
    /// and `wallTime` (seconds, ContinuousClock, measured inside `sort` after validation) lies
    /// between `gpuTime` and a ContinuousClock measurement taken around the whole call.
    /// Proves R-21, C-02, K-09, K-11.
    @Test func reportFields() throws {
        let q = try #require(Self.q)
        let n = 1 << 20
        let input = Distribution.generate(.uniform, n: n, seed: 21, key: .uint32)
        for p in [Parameters.automatic, Parameters(maxSequences: 1), Parameters(maxSequences: 1 << 16)] {
            let buf = Self.shared(input)
            let clock = ContinuousClock()
            let t0 = clock.now
            let r = try q.sort(buf, count: n, keyType: .uint32, parameters: p)
            let outer = (clock.now - t0).seconds
            let out = Self.contents(buf, n)
            let durations = q.sorter.runner.gpuDurations
            #expect(durations.count == q.sorter.runner.commits && durations.count >= 1)          // K-11
            #expect(abs(durations.reduce(0, +) - r.gpuTime) < 1e-12)                             // K-11
            #expect(r.wallTime <= outer)                                                         // K-11
            #expect(out == CPUReference.sortedReference(input, .uint32))
            let m = r.parameters.maxSequences
            #expect(r.count == n && r.auxiliaryBytes == 4 * n)
            #expect(r.bookkeepingBytes > 0 && r.bookkeepingBytes <= 136 * m + (1 << 16), "M=\(m) bytes=\(r.bookkeepingBytes)")
            #expect(r.wallTime > 0 && r.gpuTime > 0 && r.gpuTime <= r.wallTime)
            #expect(r.parameters == (try q.resolvedParameters(for: n, p)))
            #expect(r.libraryVersion == GPUQuicksort.version && r.metallibSHA256 == q.metallibSHA256)
            #expect(r.tuningEntry == q.tuning.entry && !r.metallibSHA256.isEmpty)
        }
        let r1 = try q.sort(Self.shared([5]), count: 1, keyType: .uint32)
        #expect(r1.auxiliaryBytes == 0 && r1.bookkeepingBytes == 0)
    }

    /// T-22: eight concurrent tasks sort distinct arrays on one instance; all are correct
    /// (calls are serialized, D-09). Proves E-16, C-01.
    @Test func concurrentSorts() async throws {
        let q = try #require(Self.q)
        try await withThrowingTaskGroup(of: Bool.self) { group in
            for i in 0..<8 {
                group.addTask {
                    let input = Distribution.generate(.fullrange, n: 200_000 + i * 1000, seed: UInt32(i), key: .float32)
                    var keys = input.map { Float(bitPattern: $0) }
                    try q.sort(&keys)
                    return keys.map(\.bitPattern) == CPUReference.sortedReference(input, .float32)
                }
            }
            for try await ok in group { #expect(ok) }
        }
    }

    /// T-23: `sort(&[Float])` and `sort(&[Int32])` on `fullrange` n = 10^5 give the same result as
    /// the buffer API. The generic API accepts exactly the three closed conformances, each mapped
    /// to its KeyType (E-11). Proves C-01, R-17, E-11.
    @Test func arrayAPI() throws {
        let q = try #require(Self.q)
        #expect(UInt32.keyType == .uint32 && Int32.keyType == .int32 && Float.keyType == .float32)   // E-11
        let n = 100_000
        let fbits = Distribution.generate(.fullrange, n: n, seed: 23, key: .float32)
        var floats = fbits.map { Float(bitPattern: $0) }
        let rf = try q.sort(&floats)
        #expect(floats.map(\.bitPattern) == (try gpuSort(q, fbits, .float32).0))
        #expect(rf.keyType == .float32 && rf.count == n)
        let ibits = Distribution.generate(.fullrange, n: n, seed: 24, key: .int32)
        var ints = ibits.map { Int32(bitPattern: $0) }
        try q.sort(&ints)
        #expect(ints.map { UInt32(bitPattern: $0) } == (try gpuSort(q, ibits, .int32).0))
        #expect(zip(ints, ints.dropFirst()).allSatisfy { $0 <= $1 })
        // E-11: the buffer API with a KeyType that differs from how the bytes were written sorts by
        // the declared type's order, and I-002 still holds (same multiset of bit patterns).
        let (asUInt, _) = try gpuSort(q, fbits, .uint32)
        #expect(asUInt == fbits.sorted() && asUInt != floats.map(\.bitPattern))
    }

    /// T-24: an injected allocation failure throws `allocationFailed` and leaves the buffer
    /// unchanged. Proves E-12, I-006.
    @Test func allocationFailure() throws {
        let q = try #require(Self.q)
        let input = Distribution.generate(.uniform, n: 100_000, seed: 25, key: .int32)
        let buf = Self.shared(input)
        q.sorter.pool.failAllocation = true
        #expect { _ = try q.sort(buf, count: input.count, keyType: .int32) } throws: { e in
            if case GPUQuicksortError.allocationFailed = e { return true } else { return false }
        }
        #expect(Self.contents(buf, input.count) == input)
        #expect(try gpuSort(q, input, .int32).0 == CPUReference.sortedReference(input, .int32))
    }

    /// T-29 (library half): a `diagnostics` handler receives, per sort, `phaseOneIterations`
    /// lines in the §5.3 `phase1` format with i = 1, 2, ..., then exactly one `sort` line whose
    /// fields equal the returned report; no line contains a key value. Proves R-22, C-01.
    @Test func diagnosticLines() throws {
        let q = try #require(Self.q)
        final class Box: @unchecked Sendable { var lines: [String] = []; let l = NSLock() }
        let box = Box()
        q.diagnostics = { line in box.l.withLock { box.lines.append(line) } }
        defer { q.diagnostics = nil }
        let input = Distribution.generate(.zero, n: 1 << 20, seed: 99, key: .uint32)
        let constant = String(input[0])
        for data in [Distribution.generate(.uniform, n: 1 << 21, seed: 29, key: .uint32), input] {
            box.lines = []
            let (_, r) = try gpuSort(q, data, .uint32)
            let p1 = box.lines.filter { $0.hasPrefix("phase1 ") }
            #expect(p1.count == r.phaseOneIterations)
            for (i, l) in p1.enumerated() {
                #expect(l.range(of: #"^phase1 iter=\#(i + 1) work=\d+ done=\d+ threadgroups=\d+ ms=\d+\.\d{3}$"#, options: .regularExpression) != nil, "\(l)")
            }
            let s = box.lines.filter { $0.hasPrefix("sort ") }
            #expect(s.count == 1 && box.lines.last == s.first)
            let expected = "sort n=\(r.count) key=uint32 wall_ms=\(String(format: "%.3f", r.wallTime * 1000)) gpu_ms=\(String(format: "%.3f", r.gpuTime * 1000)) phase1_iterations=\(r.phaseOneIterations) phase1_sequences=\(r.phaseOneSequences) phase2_partitions=\(r.phaseTwoPartitions) altsorts=\(r.phaseTwoAltSorts) max_stack_depth=\(r.maxStackDepth)"
            #expect(s.first == expected)
            #expect(!box.lines.contains { $0.contains(constant) })
        }
    }

    /// T-42 (library half): a hook makes the runner observe the k-th committed command buffer as
    /// completed with `.error` (with a Metal-domain error), for k in {1, 2, last}: the observed
    /// status is `.error`, `sort` throws `gpuExecutionFailed` carrying that command buffer's error
    /// description, and the next sort on the same instance succeeds. Proves E-09.
    @Test func commandBufferFailure() throws {
        let q = try #require(Self.q)
        let input = Distribution.generate(.uniform, n: 1 << 20, seed: 42, key: .float32)
        _ = try gpuSort(q, input, .float32)
        let last = q.sorter.runner.commits
        #expect(last >= 3)
        for k in [1, 2, last] {
            q.sorter.runner.failCommandBuffer = k
            var message = ""
            #expect { _ = try gpuSort(q, input, .float32) } throws: { e in
                if case GPUQuicksortError.gpuExecutionFailed(let m) = e { message = m; return true }
                return false
            }
            #expect(q.sorter.runner.commits == k && q.sorter.runner.lastStatus == .error)       // E-09
            #expect(!message.isEmpty && message == q.sorter.runner.lastErrorDescription)
            q.sorter.runner.failCommandBuffer = nil
            #expect(try gpuSort(q, input, .float32).0 == CPUReference.sortedReference(input, .float32))
        }
    }
}
