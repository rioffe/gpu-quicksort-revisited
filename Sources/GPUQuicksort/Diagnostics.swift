import Foundation
import os

/// R-22 / §5.3: diagnostic lines go to os.Logger (subsystem GPUQuicksort, .debug) and, when
/// set, to the caller's handler, with identical text. Key values never appear in a line.
enum Diagnostics {
    static let logger = Logger(subsystem: "GPUQuicksort", category: "sort")

    static func emit(_ line: String, _ handler: (@Sendable (String) -> Void)?) {
        logger.debug("\(line, privacy: .public)")
        handler?(line)
    }

    static func ms(_ seconds: Double) -> String { String(format: "%.3f", seconds * 1000) }

    /// §5.3 summary line, one per sort.
    static func summary(_ r: SortReport) -> String {
        "sort n=\(r.count) key=\(r.keyType.rawValue) wall_ms=\(ms(r.wallTime)) gpu_ms=\(ms(r.gpuTime)) "
            + "phase1_iterations=\(r.phaseOneIterations) phase1_sequences=\(r.phaseOneSequences) "
            + "phase2_partitions=\(r.phaseTwoPartitions) altsorts=\(r.phaseTwoAltSorts) max_stack_depth=\(r.maxStackDepth)"
    }
}
