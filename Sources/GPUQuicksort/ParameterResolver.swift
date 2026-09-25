import Foundation

/// K-04 validity, K-05 defaults (optp), K-03 threadgroup-memory bounds (R-16).
package enum ParameterResolver {
    /// K-05: optp(s, k, m) = 2^floor(log2(s*k + m) + 0.5).
    package static func optp(s: Int, k: Double, m: Double) -> Int {
        let x = Double(s) * k + m
        let e = Int(floor(log2(max(x, 1)) + 0.5))
        return 1 << min(e, 40)
    }

    /// K-03 fixed words of the phase-two kernel: 3 × 32 stack entries + 8 scalars.
    static let phaseTwoFixedWords = 3 * 32 + 8

    static func phaseOneBytes(t: Int) -> Int { (4 * t + 16) * 4 }
    static func phaseTwoBytes(t: Int, minseq: Int) -> Int { (max(2 * t, minseq) + phaseTwoFixedWords) * 4 }

    static func isPow2(_ x: Int) -> Bool { x > 0 && x & (x - 1) == 0 }

    /// Largest valid T for these limits (K-04, K-03).
    static func maxT(_ l: DeviceLimits) -> Int {
        var t = 1024
        while t > 32 && (t > l.maxThreadsPerThreadgroup || phaseOneBytes(t: t) > l.maxThreadgroupMemoryLength
                         || phaseTwoBytes(t: t, minseq: 64) > l.maxThreadgroupMemoryLength) { t /= 2 }
        return t
    }

    /// Largest valid minseq for T (K-03).
    static func maxMinseq(t: Int, _ l: DeviceLimits) -> Int {
        var m = 64
        while phaseTwoBytes(t: t, minseq: m * 2) <= l.maxThreadgroupMemoryLength { m *= 2 }
        return m
    }

    /// Resolves defaults and validates explicit values. Clamping applies only to defaulted values,
    /// in the order T, maxseq, minseq (K-04); an explicit invalid value throws (E-05).
    package static func resolve(n: Int, parameters p: Parameters, tuning c: TunedConstants,
                                limits l: DeviceLimits) throws -> ResolvedParameters {
        func bad(_ s: String) -> GPUQuicksortError { .invalidParameters(s) }
        let tMax = maxT(l)
        let t: Int
        if let e = p.threadsPerThreadgroup {
            guard isPow2(e), e >= 32, e <= min(1024, l.maxThreadsPerThreadgroup),
                  phaseOneBytes(t: e) <= l.maxThreadgroupMemoryLength,
                  phaseTwoBytes(t: e, minseq: 64) <= l.maxThreadgroupMemoryLength
            else { throw bad("threadsPerThreadgroup: \(e) is not a power of two in [32, \(min(1024, l.maxThreadsPerThreadgroup))] fitting threadgroup memory (K-04, K-03)") }
            t = e
        } else {
            t = min(max(optp(s: n, k: c.threads.k, m: c.threads.m), 32), tMax)
        }
        let maxseq: Int
        if let e = p.maxSequences {
            guard e >= 1, e <= 1 << 16 else { throw bad("maxSequences: \(e) is not in [1, 65536] (K-04)") }
            maxseq = e
        } else {
            maxseq = min(max(optp(s: n, k: c.maxseq.k, m: c.maxseq.m), 1), 1 << 16)
        }
        let mMax = maxMinseq(t: t, l)
        let minseq: Int
        if let e = p.minSequenceLength {
            guard isPow2(e), e >= 64 else { throw bad("minSequenceLength: \(e) is not a power of two >= 64 (K-04)") }
            guard e <= mMax else { throw bad("minSequenceLength: \(e) exceeds the threadgroup-memory bound \(mMax) for T = \(t) (K-03)") }
            minseq = e
        } else {
            minseq = min(max(optp(s: n, k: c.minseq.k, m: c.minseq.m), 64), mMax)
        }
        guard (1...1024).contains(p.maxPhaseOneIterations) else {
            throw bad("maxPhaseOneIterations: \(p.maxPhaseOneIterations) is not in [1, 1024] (K-04)")
        }
        return ResolvedParameters(threadsPerThreadgroup: t, maxSequences: maxseq, minSequenceLength: minseq,
                                  phaseOnePivot: p.phaseOnePivot, maxPhaseOneIterations: p.maxPhaseOneIterations)
    }
}
