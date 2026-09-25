import Foundation
import Metal
import Testing
@testable import GPUQuicksort

/// Sorts `bits` (key bit patterns) on the GPU through the buffer API; returns output bit patterns.
func gpuSort(_ q: GPUQuicksort, _ bits: [UInt32], _ key: KeyType, _ p: Parameters = .automatic) throws -> ([UInt32], SortReport) {
    let buf = APITests.shared(bits)
    let r = try q.sort(buf, count: bits.count, keyType: key, parameters: p)
    return (APITests.contents(buf, bits.count), r)
}

@Suite("Correctness", .serialized) struct CorrectnessTests {
    static let q: GPUQuicksort? = try? GPUQuicksort()
    static let sizes = [2, 3, 31, 32, 33, 63, 64, 65, 255, 256, 257, 1023, 1024, 1025, 4097,
                        65535, 65536, 65537, 1_000_000, (1 << 22) + 1]
    static let phaseTwoOnly = Parameters(maxSequences: 1)

    /// T-01 (phase-two-only form; W3 adds the default-parameter form): for every C-08
    /// distribution including `fullrange`, every key type and every listed n, seed 42, the output
    /// bytes equal CPUReference byte for byte. Proves R-01, R-02, R-03, R-12, I-001, I-002, I-003.
    @Test(.enabled(if: TS.hasGPU)) func matrixPhaseTwoOnly() throws {
        let q = try #require(Self.q)
        for d in Distribution.allCases {
            for key in KeyType.allCases {
                for n in Self.sizes {
                    let input = Distribution.generate(d, n: n, seed: 42, key: key)
                    let (out, _) = try gpuSort(q, input, key, Self.phaseTwoOnly)
                    #expect(out == CPUReference.sortedReference(input, key), "\(d) \(key) \(n)")
                }
            }
        }
    }

    /// T-04: the same input sorted 20 times with defaults gives identical output each time.
    /// Proves I-003.
    @Test(.enabled(if: TS.hasGPU)) func deterministicOutput() throws {
        let q = try #require(Self.q)
        let input = Distribution.generate(.uniform, n: 1 << 20, seed: 9, key: .uint32)
        let first = try gpuSort(q, input, .uint32).0
        #expect(first == CPUReference.sortedReference(input, .uint32))
        for _ in 0..<19 { #expect(try gpuSort(q, input, .uint32).0 == first) }
    }

    /// T-05 (GPU half): `key_encode` then `key_decode` on the GPU over 2^24 patterns including all
    /// special classes returns the input, and `key_encode` equals the C-04 CPU formula.
    /// Proves C-04, R-17, E-14.
    @Test(.enabled(if: TS.hasGPU)) func gpuCodecRoundTrip() throws {
        let q = try #require(Self.q)
        var patterns = [UInt32](repeating: 0, count: 1 << 24)
        for i in patterns.indices { patterns[i] = UInt32(truncatingIfNeeded: i &* 256 &+ (i & 0xFF)) }
        patterns[0...11] = [0, 1, 0x7F80_0000, 0x7F80_0001, 0x7FC0_0000, 0x7FFF_FFFF, 0x8000_0000,
                            0x8000_0001, 0xFF80_0000, 0xFF80_0001, 0xFFFF_FFFF, 0x0080_0000]
        for key in [KeyType.int32, .float32] {
            let buf = APITests.shared(patterns)
            try q.gpuCodec(buf, count: patterns.count, key: key, encode: true)
            let enc = APITests.contents(buf, patterns.count)
            for i in stride(from: 0, to: patterns.count, by: 4099) { #expect(enc[i] == KeyCodec.encode(patterns[i], key)) }
            try q.gpuCodec(buf, count: patterns.count, key: key, encode: false)
            #expect(APITests.contents(buf, patterns.count) == patterns)
        }
    }

    /// T-07: n = minseq - 1 skips phase one and is sorted by exactly one alternative sort.
    /// Proves E-03, R-15.
    @Test(.enabled(if: TS.hasGPU)) func belowMinseq() throws {
        let q = try #require(Self.q)
        for minseq in [64, 256, 1024] {
            let n = minseq - 1
            let input = Distribution.generate(.fullrange, n: n, seed: 3, key: .float32)
            let (out, r) = try gpuSort(q, input, .float32, Parameters(minSequenceLength: minseq))
            #expect(r.phaseOneIterations == 0 && r.phaseTwoAltSorts == 1 && r.phaseTwoPartitions == 0)
            #expect(out == CPUReference.sortedReference(input, .float32))
        }
    }

    /// T-09: many duplicates (keys k mod 3, and half the keys equal) sort correctly and the run
    /// terminates, in phase-two-only and default configurations. Proves E-04, I-004, I-005.
    @Test(.enabled(if: TS.hasGPU)) func duplicates() throws {
        let q = try #require(Self.q)
        let n = 1_000_000
        let mod3 = (0..<n).map { UInt32($0 % 3) }
        var half = Distribution.generate(.uniform, n: n, seed: 5, key: .uint32)
        for i in stride(from: 0, to: n, by: 2) { half[i] = 12345 }
        for input in [mod3, half] {
            for p in [Self.phaseTwoOnly, Parameters.automatic] {
                #expect(try gpuSort(q, input, .uint32, p).0 == CPUReference.sortedReference(input, .uint32))
            }
        }
    }

    /// Median-of-three killer for the R-14 pivot rule (s_b, s_mid, s_{e-1}): simulated on index
    /// positions, giving the two smallest remaining values to two of the three sample slots of
    /// the current range, then continuing on the larger side (T-40).
    static func medianOfThreeKiller(_ n: Int) -> [UInt32] {
        var v = [UInt32?](repeating: nil, count: n)
        var next: UInt32 = 0
        var lo = 0
        let hi = n
        while hi - lo >= 3 {
            for pos in [lo, (lo + hi) / 2] where v[pos] == nil { v[pos] = next; next += 1 }
            lo += 1
        }
        return v.map { x in if let x { return x }; defer { next += 1 }; return next }
    }

    /// T-40: phase-two adversarial inputs with maxseq = 1 (one lqsort threadgroup) and
    /// minseq = 64, n = 2^14: organ pipe, sawtooth (k mod 257), the median-of-3 killer for this
    /// pivot rule, and reverse-sorted input. Each output equals CPUReference and
    /// maxStackDepth <= 27. Proves E-13, K-08, R-13.
    @Test(.enabled(if: TS.hasGPU)) func phaseTwoAdversarial() throws {
        let q = try #require(Self.q)
        let n = 1 << 14
        let organ = (0..<n).map { UInt32($0 < n / 2 ? $0 : n - 1 - $0) }
        let saw = (0..<n).map { UInt32($0 % 257) }
        let reverse = (0..<n).map { UInt32(n - $0) }
        for input in [organ, saw, Self.medianOfThreeKiller(n), reverse] {
            for t in [32, 256, 1024] {
                let (out, r) = try gpuSort(q, input, .uint32,
                                           Parameters(threadsPerThreadgroup: t, maxSequences: 1, minSequenceLength: 64))
                #expect(out == CPUReference.sortedReference(input, .uint32))
                #expect(r.phaseOneIterations == 0 && r.maxStackDepth <= 27, "depth \(r.maxStackDepth)")
            }
        }
    }
}
