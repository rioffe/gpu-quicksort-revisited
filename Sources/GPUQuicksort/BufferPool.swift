import CShared
import Metal

/// Owns the auxiliary buffer A (cached, K-09) and the per-sort descriptor buffers (§7.1).
final class BufferPool {
    let device: MTLDevice
    private var cachedAux: MTLBuffer?
    /// Test hook: make the next allocation fail (T-24).
    var failAllocation = false

    init(device: MTLDevice) { self.device = device }

    func make(_ bytes: Int) throws -> MTLBuffer {
        if failAllocation { failAllocation = false; throw GPUQuicksortError.allocationFailed(bytes: bytes) }
        guard let b = device.makeBuffer(length: max(bytes, 16), options: .storageModeShared) else {
            throw GPUQuicksortError.allocationFailed(bytes: bytes)
        }
        return b
    }

    /// The auxiliary buffer for n codes; cached and grown. Reported size is always 4n (K-09).
    func aux(n: Int) throws -> MTLBuffer {
        if let a = cachedAux, a.length >= 4 * n { return a }
        cachedAux = nil
        let a = try make(4 * n)
        cachedAux = a
        return a
    }

    /// Per-sort bookkeeping buffers sized by the §7.1 terms for M = maxseq:
    /// 40 M (SequenceRecord) + 16·2M (BlockDescriptor) + 16·2M (SortSequence) + 16·2M (SortStats).
    struct Bookkeeping {
        let records: MTLBuffer, blocks: MTLBuffer, seqs: MTLBuffer, stats: MTLBuffer
        let bytes: Int
    }

    func bookkeeping(maxseq m: Int) throws -> Bookkeeping {
        let r = 40 * m, b = 16 * 2 * m, s = 16 * 2 * m, st = 16 * 2 * m
        return Bookkeeping(records: try make(r), blocks: try make(b), seqs: try make(s), stats: try make(st),
                           bytes: r + b + s + st)
    }
}
