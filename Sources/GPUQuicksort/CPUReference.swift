import CPUBaselines

/// The correctness oracle (D-12): sort the C-04 codes with Swift `Array.sort()`, then decode.
package enum CPUReference {
    package static func sortedReference(_ bits: [UInt32], _ key: KeyType) -> [UInt32] {
        var codes = bits.map { KeyCodec.encode($0, key) }
        codes.sort()
        return codes.map { KeyCodec.decode($0, key) }
    }
}

/// C-11 / R-26: the three CPU performance baselines. Each sorts the C-04 codes as UInt32; the
/// timed region (`run`) includes the CPU encode and decode for int32/float32 (D-19).
package enum CPUBaseline: String, CaseIterable, Sendable {
    case swift = "cpu-swift", qsort = "cpu-qsort", stdsort = "cpu-stdsort"

    package static func run(_ algo: CPUBaseline, _ bits: [UInt32], _ key: KeyType) -> [UInt32] {
        var codes = key == .uint32 ? bits : bits.map { KeyCodec.encode($0, key) }
        switch algo {
        case .swift: codes.sort()
        case .qsort: codes.withUnsafeMutableBufferPointer { cpub_qsort_u32($0.baseAddress, $0.count) }
        case .stdsort: codes.withUnsafeMutableBufferPointer { cpub_stdsort_u32($0.baseAddress, $0.count) }
        }
        return key == .uint32 ? codes : codes.map { KeyCodec.decode($0, key) }
    }
}
