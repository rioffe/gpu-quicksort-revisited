import ArgumentParser
import Foundation
import GPUQuicksort

/// `gpuqsort tune` (R-24, C-10, [P §5.3]): grid-search (T, maxseq, minseq) per size, keep the
/// fastest verified configuration, fit optp's (k, m) per parameter by least squares, and with
/// --write store the fit in the tuned-parameter table.
struct Tune: ParsableCommand {
    static let configuration = CommandConfiguration(abstract: "Fit the optp constants for this GPU.")
    @Option(help: "Sizes (K/M suffixes).") var n: String = "512K,1M,2M,4M,8M,16M"
    @Option(help: "Distribution.") var dist: String = "uniform"
    @Option(help: "Key type.") var key: String = "uint32"
    @Option(help: "Timed runs per configuration.") var runs: Int = 3
    @Option(help: "MT19937 seed.") var seed: UInt32 = 42
    @Flag(help: "Store the fit in the table (--table, default: the package resource).") var write = false
    @Flag(help: "Also point apple-default at this device's entry.") var asDefault = false
    @Flag(help: "Allow running from a debug build.") var allowDebug = false
    @Option(help: ArgumentHelp("Grid: full | small (tests).", visibility: .hidden)) var grid: String = "full"

    /// Default table path: the package resource in the source tree.
    static let defaultTable = URL(fileURLWithPath: #filePath).deletingLastPathComponent().deletingLastPathComponent()
        .appendingPathComponent("GPUQuicksort/Resources/TunedParameters.json").path

    struct Config: Hashable { var t: Int, m: Int, s: Int }

    func run() throws {
        try CLI.requireRelease(allowDebug, "tune")
        guard let d = Distribution(rawValue: dist) else { throw ValidationError("unknown distribution '\(dist)'") }
        guard let k = KeyType(rawValue: key) else { throw ValidationError("unknown key type '\(key)'") }
        guard runs >= 1 else { throw ValidationError("--runs must be at least 1") }
        let sizes = try CLI.sizes(n)
        let tablePath = CLI.table ?? Self.defaultTable

        // C-10 --write rules: validate the table before measuring anything.
        var existing: TunedTable?
        if write, FileManager.default.fileExists(atPath: tablePath) {
            guard let data = FileManager.default.contents(atPath: tablePath) else {
                throw CLIExit(code: 4, message: "cannot read \(tablePath)")
            }
            do { existing = try TunedTable.decode(data) } catch let GPUQuicksortError.tunedParametersInvalid(reason) {
                throw CLIExit(code: 4, message: "table \(tablePath) is not a valid tuned-parameter table: \(reason)")  // E-25
            }
        }

        let q = try CLI.sorter(tuning: .constants(.paper8800GTX))          // never depends on the table (R-24)
        try CLI.checkSizes(sizes, max: q.limits.maxKeys)
        let small = grid == "small"
        let ts = small ? [64, 256] : [32, 64, 128, 256, 512, 1024]
        let ms = small ? [64, 512] : [32, 64, 128, 256, 512, 1024, 2048, 4096]
        let ss = small ? [64, 256] : [64, 128, 256, 512, 1024, 2048, 4096]
        #if GPUQS_TEST_HOOKS
        let corrupt = ProcessInfo.processInfo.environment["GPUQS_TEST_CORRUPT_VERIFY"] != nil   // T-38 (e)
        #endif

        var best: [[String: Any]] = [], gridOut: [[String: Any]] = []
        var bestT: [Double] = [], bestM: [Double] = [], bestS: [Double] = []
        for count in sizes {
            let input = Distribution.generate(d, n: count, seed: seed, key: k)
            let ref = CLI.bytes(CPUReference.sortedReference(input, k))        // oracle once per size (F-013)
            if CLI.verbose { CLI.stderr("tune: oracle n=\(count)") }
            guard let buf = q.device.makeBuffer(length: max(4 * count, 16), options: .storageModeShared) else {
                throw GPUQuicksortError.allocationFailed(bytes: 4 * count)
            }
            var winner: (Config, Double)?
            for t in ts { for m in ms { for s in ss {
                let p = Parameters(threadsPerThreadgroup: t, maxSequences: m, minSequenceLength: s)
                guard (try? q.resolvedParameters(for: count, p)) != nil else { continue }   // invalid on device: skipped
                var walls: [Double] = []
                for run in 0...runs {
                    input.withUnsafeBytes { if $0.count > 0 { memcpy(buf.contents(), $0.baseAddress!, $0.count) } }
                    let r = try q.sort(buf, count: count, keyType: k, parameters: p)
                    #if GPUQS_TEST_HOOKS
                    if corrupt { buf.contents().storeBytes(of: ~buf.contents().load(as: UInt32.self), as: UInt32.self) }
                    #endif
                    guard Data(bytes: buf.contents(), count: 4 * count) == ref else {
                        throw CLIExit(code: 1, message: "verification failed: n=\(count) T=\(t) maxseq=\(m) minseq=\(s) run=\(run)")  // E-22
                    }
                    if run > 0 { walls.append(r.wallTime) }
                }
                let med = CLI.median(walls) * 1000
                gridOut.append(["n": count, "threads": t, "maxseq": m, "minseq": s, "median_ms": med])
                if CLI.verbose { CLI.stderr(String(format: "tune n=%d T=%d maxseq=%d minseq=%d median_ms=%.3f", count, t, m, s, med)) }
                let c = Config(t: t, m: m, s: s)
                if let w = winner {
                    // Lowest median; ties to smaller T, then maxseq, then minseq (loop order is ascending).
                    if med < w.1 { winner = (c, med) }
                } else { winner = (c, med) }
            } } }
            guard let (c, med) = winner else { throw CLIExit(code: 2, message: "no valid configuration for n=\(count)") }
            best.append(["n": count, "threads": c.t, "maxseq": c.m, "minseq": c.s, "wall_ms": med])
            bestT.append(Double(c.t)); bestM.append(Double(c.m)); bestS.append(Double(c.s))
        }

        let xs = sizes.map(Double.init)
        let ft = TunedTable.fitLine(sizes: xs, values: bestT)
        let fm = TunedTable.fitLine(sizes: xs, values: bestM)
        let fs = TunedTable.fitLine(sizes: xs, values: bestS)
        let out: [String: Any] = [
            "device": q.device.name, "gpuqsort_version": GPUQuicksort.version, "metallib_sha256": q.metallibSHA256,
            "os_version": CLI.osVersion, "sizes": sizes, "best": best,
            "fit": ["threads": ["k": ft.k, "m": ft.m], "maxseq": ["k": fm.k, "m": fm.m], "minseq": ["k": fs.k, "m": fs.m]],
            "grid": gridOut,
        ]
        print(String(decoding: try JSONSerialization.data(withJSONObject: out, options: [.prettyPrinted, .sortedKeys]), as: UTF8.self))

        guard write else { return }
        let entry = TunedEntry(fitted: Date().formatted(.iso8601.year().month().day()), gpuqsortVersion: GPUQuicksort.version,
                               sizes: sizes, threads: .init(k: ft.k, m: ft.m), maxseq: .init(k: fm.k, m: fm.m),
                               minseq: .init(k: fs.k, m: fs.m))
        let table = (existing ?? TunedTable()).upserting(name: q.device.name, entry: entry, asDefault: asDefault)
        try table.validate()
        do { try table.encoded().write(to: URL(fileURLWithPath: tablePath), options: .atomic) } catch {
            throw CLIExit(code: 4, message: "cannot write \(tablePath): \(error.localizedDescription)")        // E-23
        }
    }
}
