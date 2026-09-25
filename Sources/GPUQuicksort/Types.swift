import Foundation

/// C-01: the three supported key types (R-01).
public enum KeyType: String, Sendable, CaseIterable, Codable {
    case uint32, int32, float32

    /// Value passed to the codec kernels (CodecParams.keyType).
    var codecID: UInt32 { self == .int32 ? 1 : 2 }
}

/// C-01: keys the generic array API accepts. Documented as closed: only the three
/// conformances below are supported (E-11).
public protocol GPUSortableKey: BitwiseCopyable { static var keyType: KeyType { get } }
extension UInt32: GPUSortableKey { public static var keyType: KeyType { .uint32 } }
extension Int32: GPUSortableKey { public static var keyType: KeyType { .int32 } }
extension Float: GPUSortableKey { public static var keyType: KeyType { .float32 } }

/// C-03: phase-one pivot strategy (R-11, O-2).
public enum PhaseOnePivot: String, Sendable, Codable { case medianOfThree, minMaxAverage }

/// C-03: caller-supplied tuning parameters; nil fields default via optp (K-05).
public struct Parameters: Sendable, Codable, Equatable {
    public var threadsPerThreadgroup: Int?
    public var maxSequences: Int?
    public var minSequenceLength: Int?
    public var phaseOnePivot: PhaseOnePivot = .medianOfThree
    public var maxPhaseOneIterations: Int = 64          // K-07
    public static let automatic = Parameters()

    public init(threadsPerThreadgroup: Int? = nil, maxSequences: Int? = nil, minSequenceLength: Int? = nil,
                phaseOnePivot: PhaseOnePivot = .medianOfThree, maxPhaseOneIterations: Int = 64) {
        self.threadsPerThreadgroup = threadsPerThreadgroup
        self.maxSequences = maxSequences
        self.minSequenceLength = minSequenceLength
        self.phaseOnePivot = phaseOnePivot
        self.maxPhaseOneIterations = maxPhaseOneIterations
    }
}

/// C-03: parameters after defaulting and clamping (K-04, K-05).
public struct ResolvedParameters: Sendable, Codable, Equatable {
    public var threadsPerThreadgroup: Int, maxSequences: Int, minSequenceLength: Int
    public var phaseOnePivot: PhaseOnePivot, maxPhaseOneIterations: Int
}

/// C-03: device limits, queried, never assumed.
public struct DeviceLimits: Sendable, Codable, Equatable {
    public var name: String
    public var maxThreadsPerThreadgroup: Int     // min over the three sorting pipelines
    public var threadExecutionWidth: Int
    public var maxThreadgroupMemoryLength: Int
    public var maxBufferLength: Int
    public var maxKeys: Int                      // K-01

    public init(name: String, maxThreadsPerThreadgroup: Int, threadExecutionWidth: Int,
                maxThreadgroupMemoryLength: Int, maxBufferLength: Int, maxKeys: Int) {
        self.name = name
        self.maxThreadsPerThreadgroup = maxThreadsPerThreadgroup
        self.threadExecutionWidth = threadExecutionWidth
        self.maxThreadgroupMemoryLength = maxThreadgroupMemoryLength
        self.maxBufferLength = maxBufferLength
        self.maxKeys = maxKeys
    }

    /// K-01: maxKeys = min(2^31 - 1, floor(maxBufferLength / 4)).
    static func maxKeys(maxBufferLength: Int) -> Int { min(Int(Int32.max), maxBufferLength / 4) }
}

/// C-02: the report every sort returns (R-21).
public struct SortReport: Sendable, Codable, Equatable {
    public var count: Int
    public var keyType: KeyType
    public var parameters: ResolvedParameters
    public var wallTime: Double              // seconds, ContinuousClock (K-11)
    public var gpuTime: Double               // seconds, Σ (gpuEndTime − gpuStartTime)
    public var phaseOneIterations: Int
    public var phaseOneSequences: Int        // |done| handed to phase two
    public var phaseOneCapReached: Bool      // K-07: iterations == max AND the R-08 loop condition still held
    public var phaseTwoPartitions: Int
    public var phaseTwoAltSorts: Int
    public var maxStackDepth: Int            // entries after any push, initial push counts as 1 (K-08)
    public var auxiliaryBytes: Int           // K-09
    public var bookkeepingBytes: Int         // K-09, §7.1
    public var libraryVersion: String
    public var metallibSHA256: String
    public var tuningEntry: String
}
