import Metal

/// Commits one command buffer, waits for it, and maps failures to C-07 (E-09).
final class CommandRunner {
    let queue: MTLCommandQueue
    /// Σ (gpuEndTime − gpuStartTime) over completed command buffers of the current sort (K-11).
    var gpuTime: Double = 0
    /// Number of command buffers committed during the current sort.
    var commits = 0
    /// Dispatches per kernel name during the current sort.
    var dispatches: [String: Int] = [:]
    /// Test hook: report the k-th committed command buffer (1-based) of a sort as failed (T-42).
    var failCommandBuffer: Int?

    init(queue: MTLCommandQueue) { self.queue = queue }

    func reset() { gpuTime = 0; commits = 0; dispatches = [:] }

    /// Encodes with `body`, commits, waits. Throws `gpuExecutionFailed` if the buffer ends in error.
    func run(_ label: String, _ body: (MTLComputeCommandEncoder) throws -> Void) throws {
        guard let cb = queue.makeCommandBuffer(), let enc = cb.makeComputeCommandEncoder() else {
            throw GPUQuicksortError.gpuExecutionFailed("could not create a command buffer for \(label)")
        }
        cb.label = label
        try body(enc)
        enc.endEncoding()
        cb.commit()
        commits += 1
        cb.waitUntilCompleted()
        gpuTime += max(0, cb.gpuEndTime - cb.gpuStartTime)
        if let k = failCommandBuffer, k == commits {
            throw GPUQuicksortError.gpuExecutionFailed("injected failure of command buffer \(k) (\(label))")
        }
        if cb.status == .error {
            throw GPUQuicksortError.gpuExecutionFailed(cb.error?.localizedDescription ?? "\(label): unknown error")
        }
    }

    /// Records a dispatch for the test-hook counters and dispatches `groups` threadgroups of `t`.
    func dispatch(_ enc: MTLComputeCommandEncoder, _ name: String, groups: Int, threads t: Int) {
        dispatches[name, default: 0] += 1
        enc.dispatchThreadgroups(MTLSize(width: groups, height: 1, depth: 1),
                                 threadsPerThreadgroup: MTLSize(width: t, height: 1, depth: 1))
    }
}
