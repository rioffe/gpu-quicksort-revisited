import Foundation
import Metal
import Testing
@testable import GPUQuicksort

@Suite("API", .serialized) struct APITests {
    static let q: GPUQuicksort? = try? GPUQuicksort()

    static func shared(_ bits: [UInt32], extra: Int = 0) -> MTLBuffer {
        let len = max(4 * bits.count + extra, 4)
        let b = TS.device!.makeBuffer(length: len, options: .storageModeShared)!
        bits.withUnsafeBytes { memcpy(b.contents(), $0.baseAddress!, $0.count) }
        return b
    }
    static func contents(_ b: MTLBuffer, _ n: Int) -> [UInt32] {
        Array(UnsafeBufferPointer(start: b.contents().assumingMemoryBound(to: UInt32.self), count: n))
    }

    /// T-06 (report half; the "no command buffer" half via hook counters is in StructureTests):
    /// n = 0 and n = 1 return a report with zero counters and both byte counts 0, and leave the
    /// buffer byte-identical. Proves E-01, E-02.
    @Test(.enabled(if: TS.hasGPU)) func tinyInputs() throws {
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
    /// buffer is byte-identical afterwards. Proves K-04, K-03, E-05, I-006.
    @Test(.enabled(if: TS.hasGPU)) func invalidParameters() throws {
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
    /// untouched. Proves E-06, E-07, E-08, K-01, I-006.
    @Test(.enabled(if: TS.hasGPU)) func invalidBuffers() throws {
        let q = try #require(Self.q)
        let dev = try #require(TS.device)
        let priv = try #require(dev.makeBuffer(length: 4096, options: .storageModePrivate))
        #expect(throws: GPUQuicksortError.bufferNotShared) { try q.sort(priv, count: 1024, keyType: .uint32) }
        let input = Distribution.generate(.uniform, n: 999, seed: 2, key: .uint32)
        let small = dev.makeBuffer(length: 4 * 1000 - 1, options: .storageModeShared)!
        input.withUnsafeBytes { memcpy(small.contents(), $0.baseAddress!, $0.count) }
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
    /// `.bundled` it equals optp computed from `GPUQuicksort.tuning`. Proves K-05, R-16, C-10.
    @Test(.enabled(if: TS.hasGPU)) func resolvedParametersAPI() throws {
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
    }

    /// T-37 (init half): `.file` tables that are invalid make `init` throw
    /// `tunedParametersInvalid`, as does `.constants` with m = 0; a table lacking the host's name
    /// resolves to `apple-default`'s target with `exactMatch == false`; the bundled table
    /// validates. Proves C-10, E-20, E-21, C-01.
    @Test(.enabled(if: TS.hasGPU)) func tuningSources() throws {
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
}
