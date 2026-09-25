import Foundation
import Metal

/// Commits one command buffer, waits for it, and maps failures to C-07 (E-09).
final class CommandRunner {
    let queue: MTLCommandQueue
    /// Σ (gpuEndTime − gpuStartTime) over completed command buffers of the current sort (K-11).
    var gpuTime: Double = 0
    /// Number of command buffers committed during the current sort.
    var commits = 0
    /// gpuEndTime − gpuStartTime of each completed command buffer of the current sort (K-11).
    var gpuDurations: [Double] = []
    /// Dispatches per kernel name during the current sort.
    var dispatches: [String: Int] = [:]
    /// Test hook: the k-th committed command buffer (1-based) of a sort is observed as completed
    /// with `.error` (T-42, E-09). Apple GPUs gave no bounded way to force a real `.error`
    /// (purged buffers, page faults and non-terminating kernels were probed), so the hook
    /// substitutes the status and a Metal-domain error at the point real statuses are checked.
    var failCommandBuffer: Int?
    /// Test hook record: (command buffer number, kernel, threadgroups) per dispatch of the sort.
    var dispatchLog: [(commit: Int, kernel: String, groups: Int)] = []
    /// Test hook record: status and error text of the last completed command buffer.
    var lastStatus: MTLCommandBufferStatus = .notEnqueued
    var lastErrorDescription: String?

    init(queue: MTLCommandQueue) { self.queue = queue }

    func reset() { gpuTime = 0; commits = 0; gpuDurations = []; dispatches = [:]; dispatchLog = [] }

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
        let duration = max(0, cb.gpuEndTime - cb.gpuStartTime)
        gpuDurations.append(duration)
        gpuTime += duration                                                  // K-11
        var status = cb.status
        var error = cb.error
        #if GPUQS_TEST_HOOKS
        if let k = failCommandBuffer, k == commits {
            status = .error
            error = NSError(domain: MTLCommandBufferErrorDomain, code: Int(MTLCommandBufferError.internal.rawValue),
                            userInfo: [NSLocalizedDescriptionKey: "command buffer \(k) (\(label)) failed: injected by test hook"])
        }
        #endif
        lastStatus = status
        lastErrorDescription = error?.localizedDescription
        if status == .error {                                                            // E-09
            throw GPUQuicksortError.gpuExecutionFailed(error?.localizedDescription ?? "\(label): unknown error")
        }
    }

    /// Records a dispatch for the test-hook counters and dispatches `groups` threadgroups of `t`.
    func dispatch(_ enc: MTLComputeCommandEncoder, _ name: String, groups: Int, threads t: Int) {
        dispatches[name, default: 0] += 1
        dispatchLog.append((commits + 1, name, groups))
        enc.dispatchThreadgroups(MTLSize(width: groups, height: 1, depth: 1),
                                 threadsPerThreadgroup: MTLSize(width: t, height: 1, depth: 1))
    }
}
