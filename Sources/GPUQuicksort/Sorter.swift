import CShared
import Foundation
import Metal

/// The host orchestrator (§1 "Host orchestrator"): encode (R-17), phase one (R-08), phase two
/// (R-12), decode. One Sorter per GPUQuicksort instance; calls are serialized by its lock.
final class Sorter {
    let device: MTLDevice
    let runner: CommandRunner
    let pool: BufferPool
    let psoEncode, psoDecode, psoLQ: MTLComputePipelineState

    /// K-08 stack capacity; lowered only by the T-12 test hook.
    var stackCapacity: UInt32 = 32
    /// Per-index finalization counters, bound only when test hooks are active (T-16).
    var finalizeCounters: MTLBuffer?
    private lazy var dummy: MTLBuffer = device.makeBuffer(length: 16, options: .storageModeShared)!

    struct Counters {
        var phaseOneIterations = 0, phaseOneSequences = 0, phaseOneCapReached = false
        var phaseTwoPartitions = 0, phaseTwoAltSorts = 0, maxStackDepth = 0
        var bookkeepingBytes = 0
    }

    init(device: MTLDevice, library: ShaderLibrary) throws {
        self.device = device
        guard let q = device.makeCommandQueue() else { throw GPUQuicksortError.gpuExecutionFailed("no command queue") }
        runner = CommandRunner(queue: q)
        pool = BufferPool(device: device)
        psoEncode = try library.pipeline("key_encode")
        psoDecode = try library.pipeline("key_decode")
        psoLQ = try library.pipeline("lqsort")
    }

    var maxThreadsPerThreadgroup: Int { psoLQ.maxTotalThreadsPerThreadgroup }

    // MARK: codec (R-17, C-04)

    func codec(_ buf: MTLBuffer, n: Int, key: KeyType, encode: Bool) throws {
        guard key != .uint32, n > 0 else { return }
        var prm = CodecParams(n: UInt32(n), keyType: key.codecID, _pad0: 0, _pad1: 0)
        try runner.run(encode ? "key_encode" : "key_decode") { enc in
            enc.setComputePipelineState(encode ? psoEncode : psoDecode)
            enc.setBuffer(buf, offset: 0, index: 0)
            enc.setBytes(&prm, length: MemoryLayout<CodecParams>.stride, index: 1)
            runner.dispatch(enc, encode ? "key_encode" : "key_decode", groups: min((n + 255) / 256, 4096), threads: 256)
        }
    }

    // MARK: whole sort

    /// Sorts `n >= 2` keys in `d` (already validated). Returns the counters for the report.
    func run(_ d: MTLBuffer, n: Int, key: KeyType, p: ResolvedParameters) throws -> Counters {
        runner.reset()
        let a = try pool.aux(n: n)
        let bk = try pool.bookkeeping(maxseq: p.maxSequences)
        var c = Counters()
        c.bookkeepingBytes = bk.bytes
        try codec(d, n: n, key: key, encode: true)
        let done = try phaseOne(d, a, n: n, p: p, bk: bk, counters: &c)
        c.phaseOneSequences = done.count
        if !done.isEmpty {                                   // E-24: no lqsort dispatch when empty
            try phaseTwo(d, a, done: done, p: p, bk: bk, counters: &c)
        }
        try codec(d, n: n, key: key, encode: false)
        return c
    }

    /// A sequence handed to phase two: [begin, end) in buffer `src` (0 = D, 1 = A).
    struct Seq { var begin: UInt32, end: UInt32, src: UInt32 }

    // MARK: phase one (R-08) — the E-03 and maxseq = 1 skips (R-03); the loop is W3.

    func phaseOne(_ d: MTLBuffer, _ a: MTLBuffer, n: Int, p: ResolvedParameters,
                  bk: BufferPool.Bookkeeping, counters c: inout Counters) throws -> [Seq] {
        return [Seq(begin: 0, end: UInt32(n), src: 0)]
    }

    // MARK: phase two (R-12..R-15, R-28)

    func phaseTwo(_ d: MTLBuffer, _ a: MTLBuffer, done: [Seq], p: ResolvedParameters,
                  bk: BufferPool.Bookkeeping, counters c: inout Counters) throws {
        let seqs = bk.seqs.contents().assumingMemoryBound(to: SortSequence.self)
        for (i, s) in done.enumerated() { seqs[i] = SortSequence(begin: s.begin, end: s.end, src: s.src, _pad: 0) }
        let stats = bk.stats.contents().assumingMemoryBound(to: SortStats.self)
        memset(stats, 0, MemoryLayout<SortStats>.stride * done.count)
        let t = p.threadsPerThreadgroup
        var prm = SortParams(minseq: UInt32(p.minSequenceLength), stackCap: stackCapacity,
                             hooks: finalizeCounters == nil ? 0 : 1, _pad: 0)
        try runner.run("lqsort") { enc in
            enc.setComputePipelineState(psoLQ)
            enc.setBuffer(d, offset: 0, index: 0)
            enc.setBuffer(a, offset: 0, index: 1)
            enc.setBuffer(bk.seqs, offset: 0, index: 2)
            enc.setBuffer(bk.stats, offset: 0, index: 3)
            enc.setBytes(&prm, length: MemoryLayout<SortParams>.stride, index: 4)
            #if GPUQS_TEST_HOOKS
            enc.setBuffer(finalizeCounters ?? dummy, offset: 0, index: 5)
            #endif
            enc.setThreadgroupMemoryLength(max(2 * t, p.minSequenceLength) * 4, index: 0)
            runner.dispatch(enc, "lqsort", groups: done.count, threads: t)
        }
        for i in 0..<done.count {
            let s = stats[i]
            if s.error != 0 {
                throw GPUQuicksortError.internalInvariantViolated(
                    "lqsort threadgroup \(i): stack overflow (capacity \(stackCapacity)), sequence [\(done[i].begin), \(done[i].end))")
            }
            c.phaseTwoPartitions += Int(s.partitions)
            c.phaseTwoAltSorts += Int(s.altSorts)
            c.maxStackDepth = max(c.maxStackDepth, Int(s.maxDepth))
        }
    }
}
