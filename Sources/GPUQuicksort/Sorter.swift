import CShared
import Foundation
import Metal

/// The host orchestrator (§1 "Host orchestrator"): encode (R-17), phase one (R-08), phase two
/// (R-12), decode. One Sorter per GPUQuicksort instance; calls are serialized by its lock.
final class Sorter {
    let device: MTLDevice
    let runner: CommandRunner
    let pool: BufferPool
    let psoEncode, psoDecode, psoLQ, psoPartition, psoFill: MTLComputePipelineState

    /// K-08 stack capacity; lowered only by the T-12 test hook.
    var stackCapacity: UInt32 = 32
    /// Per-index finalization counters, bound only when test hooks are active (T-16).
    var finalizeCounters: MTLBuffer?
    /// Device-atomic RMW counter for gqsort_partition, bound only when test hooks are active (T-14).
    var atomicCounter: MTLBuffer?
    /// Test hook: called after each phase-one iteration with its records and children (T-13, T-15, T-41).
    var phaseOneObserver: ((PhaseOneIteration, MTLBuffer, MTLBuffer) -> Void)?
    /// Test hook: called with the sequences handed to phase two (T-11).
    var phaseTwoObserver: (([Seq]) -> Void)?
    /// Test hook: corrupt the first SequenceRecord's cursor after this phase-one iteration (T-12).
    var corruptAfterIteration: Int?
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
        psoPartition = try library.pipeline("gqsort_partition")
        psoFill = try library.pipeline("gqsort_fill")
    }

    /// C-03: the minimum over the three sorting pipelines.
    var maxThreadsPerThreadgroup: Int {
        min(psoLQ.maxTotalThreadsPerThreadgroup, psoPartition.maxTotalThreadsPerThreadgroup,
            psoFill.maxTotalThreadsPerThreadgroup)
    }

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

    // MARK: phase one (R-08, [P Alg 1])

    /// Snapshot of one phase-one iteration for the test hooks.
    struct PhaseOneIteration {
        struct Record { var start, end, lnext, gnext, pivot, src, lmin, lmax, gmin, gmax: UInt32 }
        struct Child { var begin, end, src, pivot: UInt32; var parent: Int; var done: Bool }
        var iteration: Int, blocksize: Int, threadgroups: Int
        var records: [Record]
        var children: [Child]
    }

    /// Median of s[b], s[floor((b+e)/2)], s[e-1] of a shared buffer (R-11, R-14, D-11).
    static func medianOfThree(_ buf: MTLBuffer, _ b: UInt32, _ e: UInt32) -> UInt32 {
        let s = buf.contents().assumingMemoryBound(to: UInt32.self)
        let x = s[Int(b)], y = s[Int((UInt64(b) + UInt64(e)) / 2)], z = s[Int(e - 1)]
        return max(min(x, y), min(max(x, y), z))
    }

    /// Runs phase one and returns `done` (with `work` merged in) for phase two.
    func phaseOne(_ d: MTLBuffer, _ a: MTLBuffer, n: Int, p: ResolvedParameters,
                  bk: BufferPool.Bookkeeping, counters c: inout Counters) throws -> [Seq] {
        let root = Seq(begin: 0, end: UInt32(n), src: 0)
        if n < p.minSequenceLength { return [root] }                     // E-03
        let m = p.maxSequences, t = p.threadsPerThreadgroup
        let minlength = (n + m - 1) / m                                   // K-06
        let minMax = p.phaseOnePivot == .minMaxAverage
        var work: [(seq: Seq, pivot: UInt32)] = [(root, Self.medianOfThree(d, 0, UInt32(n)))]  // D-20
        var done: [Seq] = []
        var iteration = 0
        let recs = bk.records.contents().assumingMemoryBound(to: SequenceRecord.self)
        let blocksPtr = bk.blocks.contents().assumingMemoryBound(to: BlockDescriptor.self)

        while !work.isEmpty && work.count + done.count < m {             // R-08 loop condition
            if iteration == p.maxPhaseOneIterations { c.phaseOneCapReached = true; break }   // K-07
            iteration += 1
            let total = work.reduce(0) { $0 + Int($1.seq.end - $1.seq.begin) }
            let blocksize = max(t, (total + m - 1) / m)                   // K-06
            var nblocks = 0
            for (j, w) in work.enumerated() {
                recs[j] = SequenceRecord(start: w.seq.begin, end: w.seq.end, lnext: w.seq.begin, gnext: w.seq.end,
                                         pivot: w.pivot, src: w.seq.src,
                                         lmin: 0xFFFF_FFFF, lmax: 0, gmin: 0xFFFF_FFFF, gmax: 0)
                var b = Int(w.seq.begin)
                while b < Int(w.seq.end) {                                // last block takes the remainder
                    let e = min(b + blocksize, Int(w.seq.end))
                    blocksPtr[nblocks] = BlockDescriptor(begin: UInt32(b), end: UInt32(e), seq: UInt32(j), _pad: 0)
                    nblocks += 1
                    b = e
                }
            }
            var prm = PartitionParams(minMax: minMax ? 1 : 0, blocksize: UInt32(blocksize),
                                      hooks: (atomicCounter != nil || finalizeCounters != nil) ? 1 : 0, _pad: 0)
            let started = ContinuousClock.now
            try runner.run("phase1") { enc in
                enc.setComputePipelineState(psoPartition)
                enc.setBuffer(d, offset: 0, index: 0)
                enc.setBuffer(a, offset: 0, index: 1)
                enc.setBuffer(bk.records, offset: 0, index: 2)
                enc.setBuffer(bk.blocks, offset: 0, index: 3)
                enc.setBytes(&prm, length: MemoryLayout<PartitionParams>.stride, index: 4)
                #if GPUQS_TEST_HOOKS
                enc.setBuffer(atomicCounter ?? dummy, offset: 0, index: 5)
                enc.setBuffer(finalizeCounters ?? dummy, offset: 0, index: 6)
                #endif
                enc.setThreadgroupMemoryLength(2 * t * 4, index: 0)
                runner.dispatch(enc, "gqsort_partition", groups: nblocks, threads: t)
                // Serial encoder: the fill dispatch starts after every partition threadgroup
                // has completed (R-10, I-007).
                enc.setComputePipelineState(psoFill)
                runner.dispatch(enc, "gqsort_fill", groups: nblocks, threads: t)
            }
            #if GPUQS_TEST_HOOKS
            if let k = corruptAfterIteration, k == iteration { recs[0].lnext = recs[0].end &+ 1 }
            #endif

            // Read back (E-10), derive children in the other buffer, pick their pivots.
            var nextWork: [(seq: Seq, pivot: UInt32)] = []
            var info = PhaseOneIteration(iteration: iteration, blocksize: blocksize, threadgroups: nblocks,
                                         records: [], children: [])
            for (j, w) in work.enumerated() {
                let r = recs[j]
                guard r.start <= r.lnext, r.lnext <= r.gnext, r.gnext <= r.end else {
                    throw GPUQuicksortError.internalInvariantViolated(
                        "phase one iteration \(iteration), sequence \(j): start \(r.start) lnext \(r.lnext) gnext \(r.gnext) end \(r.end)")
                }
                info.records.append(.init(start: r.start, end: r.end, lnext: r.lnext, gnext: r.gnext, pivot: r.pivot,
                                          src: r.src, lmin: r.lmin, lmax: r.lmax, gmin: r.gmin, gmax: r.gmax))
                let childSrc: UInt32 = 1 - w.seq.src
                let kids: [(Seq, UInt32, UInt32)] = [
                    (Seq(begin: r.start, end: r.lnext, src: childSrc), r.lmin, r.lmax),
                    (Seq(begin: r.gnext, end: r.end, src: childSrc), r.gmin, r.gmax),
                ]
                for (kid, lo, hi) in kids where kid.end > kid.begin {       // E-17: empty children dropped
                    let pivot = minMax ? lo &+ (hi &- lo) / 2                // O-2, overflow-free
                                       : Self.medianOfThree(childSrc == 0 ? d : a, kid.begin, kid.end)
                    let isDone = Int(kid.end - kid.begin) < minlength
                    if isDone { done.append(kid) } else { nextWork.append((kid, pivot)) }
                    info.children.append(.init(begin: kid.begin, end: kid.end, src: kid.src, pivot: pivot,
                                               parent: j, done: isDone))
                }
            }
            work = nextWork
            phaseOneObserver?(info, d, a)
            diagnosticLine?("phase1 iter=\(iteration) work=\(work.count) done=\(done.count) threadgroups=\(nblocks) ms=\(Self.ms(ContinuousClock.now - started))")
        }
        c.phaseOneIterations = iteration
        let merged = done + work.map { $0.seq }
        phaseTwoObserver?(merged)
        return merged
    }

    /// Emits one diagnostic line (R-22); set by GPUQuicksort for the duration of a sort.
    var diagnosticLine: ((String) -> Void)?

    static func ms(_ d: Duration) -> String { String(format: "%.3f", d.seconds * 1000) }

    // MARK: phase two (R-12..R-15, R-28)

    func phaseTwo(_ d: MTLBuffer, _ a: MTLBuffer, done: [Seq], p: ResolvedParameters,
                  bk: BufferPool.Bookkeeping, counters c: inout Counters) throws {
        let seqs = bk.seqs.contents().assumingMemoryBound(to: SortSequence.self)
        for (i, s) in done.enumerated() { seqs[i] = SortSequence(begin: s.begin, end: s.end, src: s.src, _pad: 0) }
        let stats = bk.stats.contents().assumingMemoryBound(to: SortStats.self)
        memset(stats, 0, MemoryLayout<SortStats>.stride * done.count)
        let t = p.threadsPerThreadgroup
        #if GPUQS_TEST_HOOKS
        let cap = stackCapacity
        #else
        let cap: UInt32 = 32                                  // K-08
        #endif
        var prm = SortParams(minseq: UInt32(p.minSequenceLength), stackCap: cap,
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
