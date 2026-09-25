import Foundation
import Metal
import Testing
@testable import GPUQuicksort

@Suite("Correctness", .serialized, .requiresGPU)
struct CorrectnessTests {
    static let q: GPUQuicksort? = try? GPUQuicksort()
    static let sizes = [2, 3, 31, 32, 33, 63, 64, 65, 255, 256, 257, 1023, 1024, 1025, 4097,
                        65535, 65536, 65537, 1_000_000, (1 << 22) + 1]
    static let phaseTwoOnly = Parameters(maxSequences: 1)

    /// T-01: for every C-08 distribution including `fullrange`, every key type and every listed
    /// n, seed 42, the output bytes equal CPUReference byte for byte, with default parameters
    /// (both phases) and, as a supplement, with maxseq = 1 (phase two alone, R-03).
    /// R-03: with defaults and n >= minseq phase one runs (>= 1 iteration) and hands sequences to
    /// phase two, which partitions or alternative-sorts them; with maxseq = 1 phase one performs
    /// zero iterations and phase two alone sorts. Proves R-01, R-02, R-03, I-001, I-002, I-003.
    @Test func matrix() throws {
        let q = try #require(Self.q)
        for d in Distribution.allCases {
            for key in KeyType.allCases {
                for n in Self.sizes {
                    let input = Distribution.generate(d, n: n, seed: 42, key: key)
                    let ref = CPUReference.sortedReference(input, key)
                    for p in [Parameters.automatic, Self.phaseTwoOnly] {
                        let (out, r) = try gpuSort(q, input, key, p)
                        #expect(out == ref, "\(d) \(key) \(n) maxseq=\(p.maxSequences.map(String.init) ?? "auto")")
                        let minseq = r.parameters.minSequenceLength
                        if p.maxSequences == 1 {
                            #expect(r.phaseOneIterations == 0)                                   // R-03 skip
                            if n >= minseq { #expect(r.phaseOneSequences == 1 && r.phaseTwoPartitions >= 1) }
                        } else if n >= minseq {
                            #expect(r.phaseOneIterations >= 1)                                   // phase one ran
                            if d != .zero { #expect(r.phaseOneSequences >= 1 && r.phaseTwoPartitions + r.phaseTwoAltSorts >= 1) }
                        }
                    }
                }
            }
        }
    }

    /// T-02: T-01 at n = 2^24 on `uniform`, `sorted` and `zero`, uint32, default parameters. R-12:
    /// phase two is exactly one lqsort dispatch with one threadgroup per sequence in `done`, and
    /// every threadgroup finishes (the output is completely sorted). Proves R-08, R-12.
    @Test func large() throws {
        let q = try #require(Self.q)
        for d in [Distribution.uniform, .sorted, .zero] {
            let input = Distribution.generate(d, n: 1 << 24, seed: 42, key: .uint32)
            let (out, r) = try gpuSort(q, input, .uint32)
            #expect(out == CPUReference.sortedReference(input, .uint32), "\(d)")
            if d != .zero {
                #expect(r.phaseOneIterations >= 1 && r.phaseOneSequences > 1)
                let lq = q.sorter.runner.dispatchLog.filter { $0.kernel == "lqsort" }
                #expect(lq.count == 1 && lq.first?.groups == r.phaseOneSequences)                 // R-12
            }
        }
    }

    /// T-03: parameter grid — every valid T in {32..1024}, maxseq in {1, 7, 64, 1024}, minseq in
    /// {64, 256, 1024, max valid}, both pivot strategies, on `uniform` and `staggered` with
    /// n = 300,001: every output equals CPUReference. Proves R-16, O-2, I-003, K-04.
    @Test func parameterGrid() throws {
        let q = try #require(Self.q)
        let n = 300_001
        for d in [Distribution.uniform, .staggered] {
            let input = Distribution.generate(d, n: n, seed: 42, key: .uint32)
            let ref = CPUReference.sortedReference(input, .uint32)
            for t in [32, 64, 128, 256, 512, 1024] where t <= q.limits.maxThreadsPerThreadgroup {
                let maxMin = ParameterResolver.maxMinseq(t: t, q.limits)
                for m in [1, 7, 64, 1024] {
                    for ms in Set([64, 256, 1024, maxMin]).sorted() where ms <= maxMin {
                        for piv in [PhaseOnePivot.medianOfThree, .minMaxAverage] {
                            let p = Parameters(threadsPerThreadgroup: t, maxSequences: m, minSequenceLength: ms, phaseOnePivot: piv)
                            #expect(try gpuSort(q, input, .uint32, p).0 == ref, "\(d) T=\(t) M=\(m) minseq=\(ms) \(piv)")
                        }
                    }
                }
            }
        }
    }

    /// T-08: `zero` with n = 2^20 and defaults: exactly one phase-one iteration, no sequences
    /// handed to phase two, no lqsort dispatch, 0 partitions and 0 alternative sorts, correct
    /// output. Proves K-10, E-04, E-24, R-06.
    @Test func zeroIsLinear() throws {
        let q = try #require(Self.q)
        let input = Distribution.generate(.zero, n: 1 << 20, seed: 42, key: .uint32)
        let (out, r) = try gpuSort(q, input, .uint32)
        #expect(out == input)
        #expect(r.phaseOneIterations == 1 && r.phaseOneSequences == 0)
        #expect(r.phaseTwoPartitions == 0 && r.phaseTwoAltSorts == 0 && r.maxStackDepth == 0)
        #expect(q.sorter.runner.dispatches["lqsort"] == nil)
    }

    /// T-10: iteration cap — `uniform`, n = 2^20, maxseq = 1024, maxPhaseOneIterations = 1:
    /// one iteration, cap reached, phaseOneSequences = 2 minus empty children, correct output;
    /// with the default cap of 64 on the same input the cap is not reached. Proves K-07, R-08.
    @Test func iterationCap() throws {
        let q = try #require(Self.q)
        let input = Distribution.generate(.uniform, n: 1 << 20, seed: 42, key: .uint32)
        let ref = CPUReference.sortedReference(input, .uint32)
        let (out, r) = try gpuSort(q, input, .uint32, Parameters(maxSequences: 1024, maxPhaseOneIterations: 1))
        #expect(out == ref)
        #expect(r.phaseOneIterations == 1 && r.phaseOneCapReached && r.phaseOneSequences == 2)
        let (out2, r2) = try gpuSort(q, input, .uint32, Parameters(maxSequences: 1024))
        #expect(out2 == ref && !r2.phaseOneCapReached && r2.phaseOneIterations > 1)
    }

    /// T-11: for `uniform` n = 2^22 with minseq = 64, and for `sorted`, maxStackDepth (counted per
    /// C-02) <= ceil(log2(l_max / 64)) + 2, where l_max is the longest phase-two input sequence
    /// (recorded by the phase-two hook). Proves R-13, K-08.
    @Test func stackDepthBound() throws {
        let q = try #require(Self.q)
        for d in [Distribution.uniform, .sorted] {
            let input = Distribution.generate(d, n: 1 << 22, seed: 42, key: .uint32)
            var lmax = 0
            q.sorter.phaseTwoObserver = { seqs in lmax = seqs.map { Int($0.end - $0.begin) }.max() ?? 0 }
            defer { q.sorter.phaseTwoObserver = nil }
            let (out, r) = try gpuSort(q, input, .uint32, Parameters(minSequenceLength: 64))
            #expect(out == CPUReference.sortedReference(input, .uint32))
            let bound = Int(ceil(log2(Double(max(lmax, 64)) / 64))) + 2
            #expect(lmax > 0 && r.maxStackDepth <= bound, "\(d): depth \(r.maxStackDepth) bound \(bound)")
        }
    }

    /// T-41 (O-2): with minMaxAverage on `fullrange` int32 and float32 (codes above 2^31), `zero`,
    /// `sorted` and `uniform` at n = 2^20: outputs equal CPUReference; every phase-one child is
    /// strictly shorter than its parent and its pivot equals lo + (hi - lo)/2 computed on the CPU
    /// from its actual contents; `uniform` does not reach the cap. Proves O-2, I-005.
    @Test func minMaxAveragePivot() throws {
        let q = try #require(Self.q)
        let cases: [(Distribution, KeyType)] = [(.fullrange, .int32), (.fullrange, .float32), (.zero, .uint32),
                                                (.sorted, .uint32), (.uniform, .uint32)]
        for (d, key) in cases {
            let input = Distribution.generate(d, n: 1 << 20, seed: 42, key: key)
            var checked = 0
            q.sorter.phaseOneObserver = { it, dBuf, aBuf in
                for ch in it.children {
                    let parent = it.records[ch.parent]
                    #expect(ch.end - ch.begin < parent.end - parent.start)                    // I-005
                    let buf = (ch.src == 0 ? dBuf : aBuf).contents().assumingMemoryBound(to: UInt32.self)
                    var lo = UInt32.max, hi = UInt32.min
                    for i in Int(ch.begin)..<Int(ch.end) { lo = min(lo, buf[i]); hi = max(hi, buf[i]) }
                    #expect(ch.pivot == lo + (hi - lo) / 2)                                   // O-2 formula
                    checked += 1
                }
            }
            defer { q.sorter.phaseOneObserver = nil }
            let (out, r) = try gpuSort(q, input, key, Parameters(phaseOnePivot: .minMaxAverage))
            #expect(out == CPUReference.sortedReference(input, key), "\(d) \(key)")
            if d == .uniform { #expect(!r.phaseOneCapReached && checked > 0) }
        }
    }

    /// T-04: the same input sorted 20 times with defaults gives identical output each time.
    /// Proves I-003.
    @Test func deterministicOutput() throws {
        let q = try #require(Self.q)
        let input = Distribution.generate(.uniform, n: 1 << 20, seed: 9, key: .uint32)
        let first = try gpuSort(q, input, .uint32).0
        #expect(first == CPUReference.sortedReference(input, .uint32))
        for _ in 0..<19 { #expect(try gpuSort(q, input, .uint32).0 == first) }
    }

    /// T-05 (GPU half): `key_encode` then `key_decode` on the GPU over 2^24 patterns including all
    /// special classes returns the input, and `key_encode` equals the C-04 CPU formula.
    /// Proves C-04, R-17, E-14.
    @Test func gpuCodecRoundTrip() throws {
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

    /// T-07: E-03 holds exactly on 2 <= n < minseq — for n in {2, 3, minseq/2, minseq - 1} phase one
    /// is skipped and one alternative sort sorts [0, n); at the boundary n = minseq phase one runs.
    /// Proves E-03, R-15.
    @Test func belowMinseq() throws {
        let q = try #require(Self.q)
        for minseq in [64, 256, 1024] {
            for n in [2, 3, minseq / 2, minseq - 1] {
                #expect(2 <= n && n < minseq)                                               // E-03 range
                let input = Distribution.generate(.fullrange, n: n, seed: 3, key: .float32)
                let (out, r) = try gpuSort(q, input, .float32, Parameters(minSequenceLength: minseq))
                #expect(r.phaseOneIterations == 0 && r.phaseTwoAltSorts == 1 && r.phaseTwoPartitions == 0)
                #expect(out == CPUReference.sortedReference(input, .float32))
            }
            let atBoundary = Distribution.generate(.uniform, n: minseq, seed: 3, key: .uint32)
            let (out, r) = try gpuSort(q, atBoundary, .uint32, Parameters(maxSequences: 64, minSequenceLength: minseq))
            #expect(r.phaseOneIterations >= 1)                                               // not E-03
            #expect(out == CPUReference.sortedReference(atBoundary, .uint32))
        }
    }

    /// R-14: with maxseq = 1 and minseq = 64, an input of n = 127 whose sample s_0 = 0,
    /// s_63 = 63, s_126 = 126 has median-of-three pivot 63, which splits it into two parts of 63
    /// (both below minseq): exactly 1 partition and 2 alternative sorts. Any other sample
    /// (first, last, or middle-only) would produce a part of 126 and a second partition.
    /// Proves R-14, D-11.
    @Test func phaseTwoPivotRule() throws {
        let q = try #require(Self.q)
        var rest = (1...125).map(UInt32.init).filter { $0 != 63 }
        var rng = MT19937(seed: 14)
        for i in stride(from: rest.count - 1, to: 0, by: -1) { rest.swapAt(i, Int(rng.next() % UInt32(i + 1))) }
        var input = [UInt32](repeating: 0, count: 127)
        input[0] = 0; input[63] = 63; input[126] = 126
        var it = rest.makeIterator()
        for i in 1..<126 where i != 63 { input[i] = it.next()! }
        let (out, r) = try gpuSort(q, input, .uint32, Parameters(maxSequences: 1, minSequenceLength: 64))
        #expect(out == (0...126).map(UInt32.init))
        #expect(r.phaseTwoPartitions == 1 && r.phaseTwoAltSorts == 2)
    }

    /// R-11: phase-one pivots follow the configured strategy — for `medianOfThree` each child's
    /// pivot equals the median of its s_b, s_mid, s_{e-1}; for `minMaxAverage` it equals
    /// lo + (hi - lo)/2 of its contents (O-2); recomputed on the CPU from the buffers after each
    /// iteration. Proves R-11, O-2.
    @Test func phaseOnePivotStrategies() throws {
        let q = try #require(Self.q)
        let input = Distribution.generate(.gaussian, n: 1 << 19, seed: 11, key: .uint32)
        for strategy in [PhaseOnePivot.medianOfThree, .minMaxAverage] {
            var checked = 0
            q.sorter.phaseOneObserver = { it, dBuf, aBuf in
                for ch in it.children {
                    let s = (ch.src == 0 ? dBuf : aBuf).contents().assumingMemoryBound(to: UInt32.self)
                    let b = Int(ch.begin), e = Int(ch.end)
                    let expected: UInt32
                    if strategy == .medianOfThree {
                        let x = s[b], y = s[(b + e) / 2], z = s[e - 1]
                        expected = max(min(x, y), min(max(x, y), z))
                    } else {
                        var lo = UInt32.max, hi = UInt32.min
                        for i in b..<e { lo = min(lo, s[i]); hi = max(hi, s[i]) }
                        expected = lo + (hi - lo) / 2
                    }
                    #expect(ch.pivot == expected, "\(strategy)")
                    checked += 1
                }
            }
            defer { q.sorter.phaseOneObserver = nil }
            let (out, _) = try gpuSort(q, input, .uint32, Parameters(phaseOnePivot: strategy))
            #expect(out == CPUReference.sortedReference(input, .uint32) && checked > 0)
        }
    }

    /// T-09: many duplicates (keys k mod 3, and half the keys equal) sort correctly and the run
    /// terminates, in phase-two-only and default configurations. Proves E-04, I-004, I-005.
    @Test func duplicates() throws {
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
    @Test func phaseTwoAdversarial() throws {
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
