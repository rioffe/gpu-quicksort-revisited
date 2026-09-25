import Foundation
import Testing
@testable import GPUQuicksort

/// §9 recorded tests: the proof is a recorded run in SPEC_BUILD_REPORT.md; these are the
/// presence checks the §9 intro requires (a skipped one means verification pending).
@Suite("Recorded") struct RecordedTests {
    static let reportURL = TS.packageRoot.appendingPathComponent("SPEC_BUILD_REPORT.md")
    static var report: String { (try? String(contentsOf: reportURL, encoding: .utf8)) ?? "" }

    /// Text of the report section that starts with `heading` (up to the next heading of the same
    /// or higher level).
    static func section(_ heading: String) -> String? {
        let r = report
        guard let start = r.range(of: "\n" + heading + "\n") else { return nil }
        let level = heading.prefix { $0 == "#" }.count
        let rest = r[start.upperBound...]
        var end = rest.endIndex
        for line in rest.split(separator: "\n", omittingEmptySubsequences: false) {
            let hashes = line.prefix { $0 == "#" }.count
            if hashes > 0 && hashes <= level && line.dropFirst(hashes).first == " " {
                end = rest.range(of: "\n" + line + "\n")?.lowerBound ?? end
                break
            }
        }
        return String(rest[..<end])
    }

    static let shippedTable: TunedTable? = {
        guard let url = ShaderLibrary.resourceURL("TunedParameters", "json"), let d = try? Data(contentsOf: url) else { return nil }
        return try? TunedTable.decode(d)
    }()
    static var hasM5Entry: Bool { shippedTable?.entries["Apple M5 Max"]?.lineEntry != nil }

    /// T-17 (recorded): the code-inspection checklist exists in SPEC_BUILD_REPORT.md §Inspection,
    /// lists every item the T-17 row names, and records no failed item. The properties themselves
    /// are asserted by KernelSourceTests and the GPU suites.
    @Test func inspectionChecklistRecorded() throws {
        let s = try #require(Self.section("## Inspection"), "SPEC_BUILD_REPORT.md has no ## Inspection section")
        for item in ["R-05", "R-04", "I-007", "R-28(a)", "R-28(b)", "R-28(c)", "R-13", "SIMD width"] {  // speccheck:ignore
            #expect(s.contains(item), "checklist item \(item) missing")
        }
        #expect(!s.contains("| FAIL"), "an inspection item failed")
    }

    /// T-32 (recorded): the bench table analogous to [P Fig 4] (all distributions, 1M..16M,
    /// four algorithms, release build) is recorded; from the recorded rows (recorded/bench.csv)
    /// every run is verified and the K-13 ratio — median gpu-quicksort wall_ms over the fastest
    /// CPU baseline's median, `uniform` uint32 at 2^24 — is at most 0.5. Proves K-13.
    @Test func benchTableRecorded() throws {
        let csv = try String(contentsOf: TS.packageRoot.appendingPathComponent("recorded/bench.csv"), encoding: .utf8)
        let rows = csv.split(separator: "\n").dropFirst().map { BenchParse.fields(String($0)) }
        #expect(rows.count == 6 * 5 * 4 * 5 && rows.allSatisfy { $0[14] == "true" })
        func median(_ algo: String) -> Double {
            let v = rows.filter { $0[2] == "uniform" && $0[3] == "16777216" && $0[5] == algo }.map { Double($0[6])! }.sorted()
            return v.count % 2 == 1 ? v[v.count / 2] : (v[v.count / 2 - 1] + v[v.count / 2]) / 2
        }
        let gpu = median("gpu-quicksort")
        let fastestCPU = ["cpu-swift", "cpu-qsort", "cpu-stdsort"].map(median).min()!
        #expect(gpu > 0 && gpu / fastestCPU <= 0.5, "K-13 ratio \(gpu / fastestCPU)")          // K-13
        let s = try #require(Self.section("### T-32"), "SPEC_BUILD_REPORT.md §Performance lacks ### T-32")
        for algo in ["gpu-quicksort", "cpu-swift", "cpu-qsort", "cpu-stdsort"] { #expect(s.contains(algo)) }
        for d in ["uniform", "sorted", "zero", "bucket", "gaussian", "staggered"] { #expect(s.contains(d)) }
        #expect(s.contains("K-13 ratio"))
        #expect(s.contains("release"))
    }

    /// T-33 (recorded): the scaling factor from 1M to 16M `uniform` is recorded.
    @Test func scalingRecorded() throws {
        let s = try #require(Self.section("### T-33"), "SPEC_BUILD_REPORT.md §Performance lacks ### T-33")
        #expect(s.contains("scaling factor"))
    }
}

/// Skipped (verification pending, R-25) until the tuning run exists.
@Suite("RecordedTuning", .requiresTuningRecord)
struct RecordedTuningTests {
    /// T-34 (recorded): the tuning run on the reference machine is recorded, the shipped C-10 table
    /// has an `Apple M5 Max` entry whose `fitted` date appears in the record, and `apple-default`
    /// points at it. Skipped (verification pending, R-25) until the tuning run exists.
    /// Proves R-24, R-25, K-14.
    @Test func tuningRecorded() throws {
        // K-14: the recorded run (release build, default arguments) finished within 30 minutes,
        // and every grid point it measured is a configuration valid on this device (invalid ones
        // were skipped, not reported as errors).
        let status = try String(contentsOf: TS.packageRoot.appendingPathComponent("recorded/tune.status"), encoding: .utf8)
        let elapsed = Int(status.components(separatedBy: "elapsed_s=").last!.trimmingCharacters(in: .whitespacesAndNewlines))!
        #expect(status.hasPrefix("exit=0") && elapsed <= 30 * 60)                                  // K-14
        let tune = try JSONSerialization.jsonObject(with: Data(contentsOf: TS.packageRoot.appendingPathComponent("recorded/tune.json"))) as! [String: Any]
        let grid = tune["grid"] as! [[String: Any]]
        let q = try GPUQuicksort(tuning: .constants(.paper8800GTX))
        for g in grid {
            let p = Parameters(threadsPerThreadgroup: g["threads"] as? Int, maxSequences: g["maxseq"] as? Int,
                               minSequenceLength: g["minseq"] as? Int)
            #expect((try? q.resolvedParameters(for: g["n"] as! Int, p)) != nil)                      // K-14
        }
        #expect((tune["sizes"] as! [Int]).count == 6 && grid.count > 0)
        let table = try #require(RecordedTests.shippedTable)
        let entry = try #require(table.entries["Apple M5 Max"]?.lineEntry)
        #expect(table.defaultTarget == "Apple M5 Max")
        let s = try #require(RecordedTests.section("### T-34"), "SPEC_BUILD_REPORT.md §Performance lacks ### T-34")
        #expect(s.contains("fitted: \(entry.fitted)"))
        #expect(s.contains("release"))
        #expect(s.contains("elapsed"))
    }
}
