import CPUBaselines

/// The correctness oracle (D-12): sort the C-04 codes with Swift `Array.sort()`, then decode.
package enum CPUReference {
    package static func sortedReference(_ bits: [UInt32], _ key: KeyType) -> [UInt32] {
        var codes = bits.map { KeyCodec.encode($0, key) }
        codes.sort()
        return codes.map { KeyCodec.decode($0, key) }
    }
}

/// C-11 / R-26: the four CPU performance baselines. Each sorts the C-04 codes as UInt32; the
/// timed region (`run`) includes the CPU encode and decode for int32/float32 (D-19).
package enum CPUBaseline: String, CaseIterable, Sendable {
    case swift = "cpu-swift", qsort = "cpu-qsort", stdsort = "cpu-stdsort", stdsortPar = "cpu-stdsort-par"

    package static func run(_ algo: CPUBaseline, _ bits: [UInt32], _ key: KeyType) -> [UInt32] {
        var v = bits
        runInPlace(algo, &v, key)
        return v
    }

    /// The timed region used by `bench`: encode, sort, decode in place (no copy of the input).
    package static func runInPlace(_ algo: CPUBaseline, _ v: inout [UInt32], _ key: KeyType) {
        if key != .uint32 { v.withUnsafeMutableBufferPointer { for i in $0.indices { $0[i] = KeyCodec.encode($0[i], key) } } }
        switch algo {
        case .swift: v.sort()                                              // Swift Array.sort() (D-12)
        case .qsort: v.withUnsafeMutableBufferPointer { cpub_qsort_u32($0.baseAddress, $0.count) }
        case .stdsort: v.withUnsafeMutableBufferPointer { cpub_stdsort_u32($0.baseAddress, $0.count) }
        case .stdsortPar: v.withUnsafeMutableBufferPointer { cpub_stdsort_par_u32($0.baseAddress, $0.count) }
        }
        if key != .uint32 { v.withUnsafeMutableBufferPointer { for i in $0.indices { $0[i] = KeyCodec.decode($0[i], key) } } }
    }
}
