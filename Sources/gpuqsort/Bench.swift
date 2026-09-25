import ArgumentParser
import Foundation
import GPUQuicksort

/// `gpuqsort bench` (§5.2, R-23, R-26): time only the sort; discard one warm-up run per
/// configuration; verify every timed run against an oracle computed once per input.
struct Bench: ParsableCommand {
    static let configuration = CommandConfiguration(abstract: "Benchmark GPU-Quicksort and the CPU baselines.")
    @Option(help: "Distributions (comma-separated or all).") var dist: String = "all"
    @Option(help: "Sizes (K/M suffixes).") var n: String = "1M,2M,4M,8M,16M"
    @Option(help: "Key types (comma-separated or all).") var key: String = "uint32"
    @Option(help: "Timed runs per configuration.") var runs: Int = 5
    @Option(help: "MT19937 seed.") var seed: UInt32 = 42
    @Flag(help: "Also time cpu-swift, cpu-qsort and cpu-stdsort.") var cpu = false
    @Flag(help: "Allow running from a debug build.") var allowDebug = false
    @Option(help: "csv | json.") var format: String = "csv"
    @OptionGroup var tuning: TuningFlags

    static let header = ["device", "key", "distribution", "n", "run", "algorithm", "wall_ms", "gpu_ms", "threads",
                         "maxseq", "minseq", "phase1_iterations", "phase1_sequences", "max_stack_depth", "verified",
                         "gpuqsort_version", "metallib_sha256", "tuning_entry", "os_version"]

    /// One output row; nil fields are empty in CSV and null in JSON.
    struct Row {
        var fields: [String: Any?]
        func csv() -> String { Bench.header.map { CLI.csvField(Bench.text(fields[$0] ?? nil)) }.joined(separator: ",") }
    }

    static func text(_ v: Any?) -> String {
        switch v {
        case nil: return ""
        case let d as Double: return String(format: "%.3f", d)
        case let b as Bool: return b ? "true" : "false"
        case let x?: return "\(x)"
        }
    }

    func run() throws {
        try CLI.requireRelease(allowDebug, "bench")
        guard format == "csv" || format == "json" else { throw ValidationError("--format must be csv or json") }
        let dists = try CLI.distributions(dist), sizes = try CLI.sizes(n), keys = try CLI.keys(key)
        let params = try tuning.parameters()
        guard runs >= 1 else { throw ValidationError("--runs must be at least 1") }
        let q = try CLI.sorter()
        try CLI.checkSizes(sizes, max: q.limits.maxKeys)

        var jsonRows: [[String: Any]] = []
        var summaries: [String] = []
        if format == "csv" { print(Bench.header.joined(separator: ",")) }
        func emit(_ r: Row) {
            if format == "csv" { print(r.csv()); fflush(stdout) }
            else { jsonRows.append(r.fields.mapValues { $0 ?? NSNull() }) }
        }
        func flushJSON() throws {
            guard format == "json" else { return }
            let data = try JSONSerialization.data(withJSONObject: jsonRows, options: [.prettyPrinted, .sortedKeys])
            print(String(decoding: data, as: UTF8.self))
        }
        func fail(_ what: String) throws -> Never {
            try flushJSON()
            throw CLIExit(code: 1, message: "verification failed: \(what)")
        }

        for k in keys {
            for d in dists {
                for count in sizes {
                    let input = Distribution.generate(d, n: count, seed: seed, key: k)
                    let ref = CPUReference.sortedReference(input, k)          // oracle computed once (F-013)
                    let refData = CLI.bytes(ref)
                    func base(_ algo: String, _ run: Int, _ wall: Double) -> [String: Any?] {
                        ["device": q.device.name, "key": k.rawValue, "distribution": d.rawValue, "n": count, "run": run,
                         "algorithm": algo, "wall_ms": wall * 1000, "gpu_ms": nil, "threads": nil, "maxseq": nil,
                         "minseq": nil, "phase1_iterations": nil, "phase1_sequences": nil, "max_stack_depth": nil,
                         "verified": true, "gpuqsort_version": GPUQuicksort.version,
                         "metallib_sha256": q.metallibSHA256, "tuning_entry": nil, "os_version": CLI.osVersion]
                    }
                    // GPU-Quicksort.
                    guard let buf = q.device.makeBuffer(length: max(4 * count, 16), options: .storageModeShared) else {
                        throw GPUQuicksortError.allocationFailed(bytes: 4 * count)
                    }
                    var walls: [Double] = []
                    for run in 0...runs {
                        input.withUnsafeBytes { if $0.count > 0 { memcpy(buf.contents(), $0.baseAddress!, $0.count) } }
                        let r = try q.sort(buf, count: count, keyType: k, parameters: params)
                        guard Data(bytes: buf.contents(), count: 4 * count) == refData else {
                            try fail("gpu-quicksort \(d.rawValue) n=\(count) key=\(k.rawValue) run=\(run)")
                        }
                        if run == 0 { continue }                                   // warm-up discarded
                        walls.append(r.wallTime)
                        var f = base("gpu-quicksort", run, r.wallTime)
                        f["gpu_ms"] = r.gpuTime * 1000
                        f["threads"] = r.parameters.threadsPerThreadgroup
                        f["maxseq"] = r.parameters.maxSequences
                        f["minseq"] = r.parameters.minSequenceLength
                        f["phase1_iterations"] = r.phaseOneIterations
                        f["phase1_sequences"] = r.phaseOneSequences
                        f["max_stack_depth"] = r.maxStackDepth
                        f["tuning_entry"] = r.tuningEntry
                        emit(Row(fields: f))
                    }
                    summaries.append(Self.summary(d, count, "gpu-quicksort", walls))
                    // CPU baselines (R-26).
                    if cpu {
                        for algo in CPUBaseline.allCases {
                            var cw: [Double] = []
                            for run in 0...runs {
                                var v = input                                      // restore input: excluded
                                v.withUnsafeMutableBufferPointer { _ in }          // force a unique copy
                                let t0 = ContinuousClock.now
                                CPUBaseline.runInPlace(algo, &v, k)
                                let dt = ContinuousClock.now - t0
                                guard v == ref else { try fail("\(algo.rawValue) \(d.rawValue) n=\(count) run=\(run)") }
                                if run == 0 { continue }
                                let wall = Double(dt.components.seconds) + Double(dt.components.attoseconds) * 1e-18
                                cw.append(wall)
                                emit(Row(fields: base(algo.rawValue, run, wall)))
                            }
                            summaries.append(Self.summary(d, count, algo.rawValue, cw))
                        }
                    }
                }
            }
        }
        try flushJSON()
        if CLI.verbose { summaries.forEach(CLI.stderr) }
    }

    /// K-11: median and min wall_ms and throughput n / (median_ms · 10^3) Mkeys/s (0 when n or t is 0).
    static func summary(_ d: Distribution, _ n: Int, _ algo: String, _ walls: [Double]) -> String {
        let med = CLI.median(walls) * 1000, mn = (walls.min() ?? 0) * 1000
        let thr = (n == 0 || med == 0) ? 0 : Double(n) / (med * 1e3)
        return String(format: "bench %@ n=%d %@ median_ms=%.3f min_ms=%.3f mkeys_per_s=%.1f",
                      d.rawValue, n, algo, med, mn, thr)
    }
}
