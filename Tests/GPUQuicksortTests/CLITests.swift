import Foundation
import Testing
@testable import GPUQuicksort

/// §9.4 CLI tests: run the debug `gpuqsort` binary (the test build is debug, D-21).
@Suite("CLI", .serialized, .requiresGPU)
struct CLITests {
    /// The debug `gpuqsort` built alongside this test bundle: walk up from the bundle until a
    /// directory holds an executable `gpuqsort` (layouts differ between SwiftPM build systems).
    static let exe: String = {
        var dir = Bundle.module.bundleURL
        for _ in 0..<6 {
            dir = dir.deletingLastPathComponent()
            let c = dir.appendingPathComponent("gpuqsort").path
            if FileManager.default.isExecutableFile(atPath: c) { return c }
        }
        return TS.packageRoot.appendingPathComponent(".build/debug/gpuqsort").path
    }()
    static func cli(_ args: [String], env: [String: String] = [:]) -> TS.ProcessResult { TS.run(exe, args, env: env) }
    static let q: GPUQuicksort? = try? GPUQuicksort()

    struct InfoJSON: Decodable {
        struct Default: Decodable { var n: Int; var parameters: ResolvedParameters }
        var version: String; var metallibSHA256: String; var limits: DeviceLimits; var tuning: TunedConstants
        var defaults: [Default]
    }

    /// T-27: `gen` then `sort` gives output equal to the oracle; `sort` on a 4097-byte file exits 4
    /// with the E-15 message; `--threads 48` exits 2; missing `--dist` exits 2; `gen --n` above
    /// 2^31 - 1 exits 2; `--table` pointing at an invalid table exits 3; `sort --out` into a
    /// read-only directory exits 4. Each case matches its §7.2 row. Proves R-19, K-12, E-15.
    @Test func basicCommandsAndExitCodes() throws {
        let dir = TS.tempDir()
        let inURL = dir.appendingPathComponent("in.bin"), outURL = dir.appendingPathComponent("out.bin")
        var r = Self.cli(["gen", "--dist", "staggered", "--n", "100000", "--key", "float32", "--out", inURL.path])
        #expect(r.status == 0 && r.stderr.isEmpty, "\(r.stderr)")
        r = Self.cli(["sort", "--in", inURL.path, "--out", outURL.path, "--key", "float32"])
        #expect(r.status == 0 && r.stderr.isEmpty, "\(r.stderr)")
        let input = Distribution.generate(.staggered, n: 100_000, seed: 42, key: .float32)
        let out = try Data(contentsOf: outURL)
        #expect(out == CPUReference.sortedReference(input, .float32).withUnsafeBufferPointer { Data(buffer: $0) })

        let odd = dir.appendingPathComponent("odd.bin")
        try Data(count: 4097).write(to: odd)
        r = Self.cli(["sort", "--in", odd.path, "--out", outURL.path])
        #expect(r.status == 4 && r.stderr.contains("input size 4097 is not a multiple of 4"))
        r = Self.cli(["sort", "--in", inURL.path, "--out", outURL.path, "--threads", "48"])
        #expect(r.status == 2 && r.stderr.contains("gpuqsort: error: invalidParameters"))
        r = Self.cli(["gen", "--n", "10", "--out", outURL.path])
        #expect(r.status == 2)
        r = Self.cli(["gen", "--dist", "uniform", "--n", "2147483648", "--out", outURL.path])
        #expect(r.status == 2)
        let badTable = dir.appendingPathComponent("bad.json")
        try Data("{".utf8).write(to: badTable)
        r = Self.cli(["info", "--table", badTable.path])
        #expect(r.status == 3 && r.stderr.contains("tunedParametersInvalid"))
        let ro = dir.appendingPathComponent("ro")
        try FileManager.default.createDirectory(at: ro, withIntermediateDirectories: true)
        try FileManager.default.setAttributes([.posixPermissions: 0o555], ofItemAtPath: ro.path)
        r = Self.cli(["sort", "--in", inURL.path, "--out", ro.appendingPathComponent("x.bin").path])
        #expect(r.status == 4)
        r = Self.cli(["--version"])
        #expect(r.status == 0 && r.stdout.contains(GPUQuicksort.version))
    }

    /// T-28: `bench --n 1M --runs 3 --dist uniform --cpu --allow-debug` emits the exact §5.2 header,
    /// 3 × 4 data rows (gpu-quicksort plus three cpu-* algorithms; the warm-up is not emitted),
    /// verified=true on every row, provenance columns equal to `info --json`'s version and
    /// metallibSHA256 and the tuning entry in effect, and nothing on stderr without --verbose.
    /// Proves R-23, R-22, R-26.
    @Test func benchCSV() throws {
        let info = try JSONDecoder().decode(InfoJSON.self, from: Self.cli(["info", "--json"]).stdoutData)
        let r = Self.cli(["bench", "--n", "1M", "--runs", "3", "--dist", "uniform", "--cpu", "--allow-debug"])
        #expect(r.status == 0 && r.stderr.isEmpty, "\(r.stderr)")
        let lines = r.stdout.split(separator: "\n").map(String.init)
        #expect(lines.first == "device,key,distribution,n,run,algorithm,wall_ms,gpu_ms,threads,maxseq,minseq,phase1_iterations,phase1_sequences,max_stack_depth,verified,gpuqsort_version,metallib_sha256,tuning_entry,os_version")
        let rows = lines.dropFirst().map { BenchParse.fields($0) }
        #expect(rows.count == 12)
        let algos = Dictionary(grouping: rows, by: { $0[5] })
        #expect(Set(algos.keys) == ["gpu-quicksort", "cpu-swift", "cpu-qsort", "cpu-stdsort"])
        for row in rows {
            #expect(row.count == 19 && row[14] == "true" && row[3] == "1048576")
            #expect(row[15] == info.version && row[16] == info.metallibSHA256)
            #expect(Double(row[6])! > 0)
            if row[5] == "gpu-quicksort" { #expect(row[17] == info.tuning.entry && !row[8].isEmpty) }
            else { #expect(row[7].isEmpty && row[8].isEmpty && row[17].isEmpty) }
        }
        #expect(Set(algos["gpu-quicksort"]!.map { $0[4] }) == ["1", "2", "3"])
    }

    /// T-29 (CLI half): `--verbose` writes the §5.3 phase1 lines and one sort line per sort to
    /// stderr, and no line contains a key value (the `zero` distribution's constant c).
    /// Proves R-22.
    @Test func verboseDiagnostics() throws {
        let dir = TS.tempDir()
        let inURL = dir.appendingPathComponent("z.bin")
        #expect(Self.cli(["gen", "--dist", "zero", "--n", "1048576", "--out", inURL.path]).status == 0)
        let c = String(Distribution.generate(.zero, n: 1, seed: 42, key: .uint32)[0])
        let r = Self.cli(["--verbose", "sort", "--in", inURL.path, "--out", dir.appendingPathComponent("o.bin").path])
        #expect(r.status == 0)
        let lines = r.stderr.split(separator: "\n").map(String.init)
        #expect(lines.filter { $0.hasPrefix("phase1 iter=1 ") }.count == 1)
        #expect(lines.filter { $0.hasPrefix("sort n=1048576 key=uint32 ") }.count == 1)
        #expect(!r.stderr.contains(c))
        let quiet = Self.cli(["sort", "--in", inURL.path, "--out", dir.appendingPathComponent("o2.bin").path])
        #expect(quiet.status == 0 && quiet.stderr.isEmpty)
    }

    /// T-30: `info --json` decodes as the §5.2 object — limits.maxKeys follows K-01, tuning equals
    /// GPUQuicksort.tuning, metallibSHA256 equals the stamp file, defaults equal
    /// resolvedParameters for both sizes; the human output contains the same values.
    /// The suite runs only on a device meeting K-02 (Apple7 family, checked here).
    /// Proves C-03, C-10, K-01, K-02.
    @Test func infoJSON() throws {
        let q = try #require(Self.q)
        #expect(q.device.supportsFamily(.apple7))                                  // K-02
        let r = Self.cli(["info", "--json"])
        #expect(r.status == 0)
        let info = try JSONDecoder().decode(InfoJSON.self, from: r.stdoutData)
        #expect(info.limits.maxKeys == min(Int(Int32.max), info.limits.maxBufferLength / 4))
        #expect(info.limits == q.limits && info.tuning == q.tuning && info.version == GPUQuicksort.version)
        #expect(info.metallibSHA256 == q.metallibSHA256)
        #expect(info.defaults.map(\.n) == [1 << 20, 1 << 24])
        for d in info.defaults { #expect(d.parameters == (try q.resolvedParameters(for: d.n, .automatic))) }
        let human = Self.cli(["info"]).stdout
        for v in [info.limits.name, info.metallibSHA256, info.tuning.entry, "\(info.limits.maxKeys)",
                  "threads=\(info.defaults[1].parameters.threadsPerThreadgroup)"] {
            #expect(human.contains(v), "\(v)")
        }
    }

    /// T-38: `tune --n 64K,128K --runs 1 --grid small --allow-debug`: (a) without --write, an
    /// invalid --table file is never read and the run succeeds with §5.2 JSON, computing the oracle
    /// once per size; (b) --write into a valid table changes only the host entry and validates;
    /// (c) --write into a missing file creates it with apple-default pointing at the new entry;
    /// (d) --write into an invalid file exits 4 before measuring, file byte-identical;
    /// (e) an injected verification failure exits 1 and leaves the table unchanged; (f) an
    /// unwritable path exits 4; (g) without --allow-debug it exits 2.
    /// Proves R-24, C-10, E-22, E-23, E-25.
    @Test func tune() throws {
        let q = try #require(Self.q)
        let dir = TS.tempDir()
        let base = ["tune", "--n", "64K,128K", "--runs", "1", "--grid", "small", "--allow-debug"]
        let invalid = dir.appendingPathComponent("invalid.json")
        try Data("not json".utf8).write(to: invalid)

        // (a)
        var r = Self.cli(["--verbose"] + base + ["--table", invalid.path])
        #expect(r.status == 0, "\(r.stderr)")
        let json = try #require(try JSONSerialization.jsonObject(with: r.stdoutData) as? [String: Any])
        for k in ["device", "gpuqsort_version", "metallib_sha256", "os_version", "sizes", "best", "fit", "grid"] {
            #expect(json[k] != nil, "\(k)")
        }
        #expect((json["best"] as? [[String: Any]])?.count == 2)
        #expect(r.stderr.components(separatedBy: "tune: oracle n=").count - 1 == 2)

        // (b)
        let valid = dir.appendingPathComponent("valid.json")
        try Data(#"{"schema":1,"entries":{"Other":{"fitted":"x","gpuqsortVersion":"x","sizes":[],"threads":{"k":0,"m":64},"maxseq":{"k":0,"m":64},"minseq":{"k":0,"m":64}},"apple-default":{"sameAs":"Other"}}}"#.utf8).write(to: valid)
        r = Self.cli(base + ["--write", "--table", valid.path])
        #expect(r.status == 0, "\(r.stderr)")
        let tb = try TunedTable.decode(Data(contentsOf: valid))
        #expect(tb.entries["Other"] != nil && tb.entries[q.device.name] != nil && tb.defaultTarget == "Other")

        // (c)
        let missing = dir.appendingPathComponent("new.json")
        r = Self.cli(base + ["--write", "--table", missing.path])
        #expect(r.status == 0, "\(r.stderr)")
        let tc = try TunedTable.decode(Data(contentsOf: missing))
        #expect(tc.defaultTarget == q.device.name)

        // (d)
        let before = try Data(contentsOf: invalid)
        r = Self.cli(["--verbose"] + base + ["--write", "--table", invalid.path])
        #expect(r.status == 4 && r.stderr.contains("is not a valid tuned-parameter table"))
        #expect(!r.stderr.contains("tune n="))
        #expect(try Data(contentsOf: invalid) == before)

        // (e)
        let tableBefore = try Data(contentsOf: valid)
        r = Self.cli(base + ["--write", "--table", valid.path], env: ["GPUQS_TEST_CORRUPT_VERIFY": "1"])
        #expect(r.status == 1 && r.stderr.contains("verification failed"))
        #expect(try Data(contentsOf: valid) == tableBefore)

        // (f)
        let ro = dir.appendingPathComponent("ro")
        try FileManager.default.createDirectory(at: ro, withIntermediateDirectories: true)
        try FileManager.default.setAttributes([.posixPermissions: 0o555], ofItemAtPath: ro.path)
        r = Self.cli(base + ["--write", "--table", ro.appendingPathComponent("t.json").path])
        #expect(r.status == 4)

        // (g)
        r = Self.cli(["tune", "--n", "64K", "--runs", "1", "--grid", "small"])
        #expect(r.status == 2)
    }

    /// T-39 (guard half): `bench` from a debug build exits 2 without --allow-debug. Proves C-11.
    @Test func benchDebugGuard() {
        let r = Self.cli(["bench", "--n", "1K", "--runs", "1", "--dist", "uniform"])
        #expect(r.status == 2 && r.stderr.contains("--allow-debug"), "\(r.stderr)")
    }

    /// T-42 (CLI half): with GPUQS_TEST_FAIL_CB=2 the debug CLI exits 5 with
    /// `gpuqsort: error: gpuExecutionFailed …` (§7.2 row 5). Proves K-12.
    @Test func commandBufferFailureExit() throws {
        let dir = TS.tempDir()
        let inURL = dir.appendingPathComponent("in.bin")
        #expect(Self.cli(["gen", "--dist", "uniform", "--n", "1M", "--key", "int32", "--out", inURL.path]).status == 0)
        let r = Self.cli(["sort", "--in", inURL.path, "--out", dir.appendingPathComponent("o.bin").path, "--key", "int32"],
                         env: ["GPUQS_TEST_FAIL_CB": "2"])
        #expect(r.status == 5 && r.stderr.hasPrefix("gpuqsort: error: gpuExecutionFailed"))
    }

    /// `verify --dist all` covers the six [P §5.3] distributions (fullrange is test-only, C-08): one
    /// PASS line per (dist, n, key) and exit 0 (R-19).
    @Test func verifySmall() {
        let r = Self.cli(["verify", "--dist", "all", "--n", "1K,70000", "--key", "all"])
        #expect(r.status == 0, "\(r.stderr)")
        let lines = r.stdout.split(separator: "\n")
        #expect(lines.count == 6 * 2 * 3 && lines.allSatisfy { $0.hasPrefix("PASS ") })
    }
}

/// Minimal RFC 4180 field splitter for the tests.
enum BenchParse {
    static func fields(_ line: String) -> [String] {
        var out: [String] = [], cur = "", quoted = false
        let it = Array(line)
        var i = 0
        while i < it.count {
            let ch = it[i]
            if quoted {
                if ch == "\"" { if i + 1 < it.count && it[i + 1] == "\"" { cur.append("\""); i += 1 } else { quoted = false } }
                else { cur.append(ch) }
            } else if ch == "\"" { quoted = true }
            else if ch == "," { out.append(cur); cur = "" }
            else { cur.append(ch) }
            i += 1
        }
        out.append(cur)
        return out
    }
}
