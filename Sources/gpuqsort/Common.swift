import ArgumentParser
import Foundation
import GPUQuicksort

/// A CLI failure carrying its §7.2 exit code.
struct CLIExit: Error {
    var code: Int32
    var message: String?
}

/// Process-wide CLI state and helpers (§5.2, §5.3, §7.2).
enum CLI {
    /// Global flags, extracted from anywhere on the command line by main.swift.
    nonisolated(unsafe) static var verbose = false
    nonisolated(unsafe) static var table: String?

    static var isDebugBuild: Bool {
        #if DEBUG
        return true
        #else
        return false
        #endif
    }

    static func stderr(_ s: String) { FileHandle.standardError.write(Data((s + "\n").utf8)) }

    static let osVersion = ProcessInfo.processInfo.operatingSystemVersionString

    /// A sorter using `--table` (TuningSource.file) or the bundled table; `--verbose` installs a
    /// handler that writes every diagnostic line to stderr (R-22).
    static func sorter(tuning: TuningSource? = nil) throws -> GPUQuicksort {
        let source = tuning ?? (table.map { .file(URL(fileURLWithPath: $0)) } ?? .bundled)
        let q = try GPUQuicksort(tuning: source)
        if verbose { q.diagnostics = { CLI.stderr($0) } }
        #if GPUQS_TEST_HOOKS
        if let v = ProcessInfo.processInfo.environment["GPUQS_TEST_FAIL_CB"], let k = Int(v) {
            q.setTestFailCommandBuffer(k)
        }
        #endif
        return q
    }

    /// `bench` and `tune` refuse a debug build unless --allow-debug (C-11, F-020).
    static func requireRelease(_ allowDebug: Bool, _ command: String) throws {
        if isDebugBuild && !allowDebug {
            throw CLIExit(code: 2, message: "\(command) from a debug build requires --allow-debug")
        }
    }

    /// §7.2: the exit code of every C-07 case.
    static func exitCode(for e: GPUQuicksortError) -> Int32 {
        switch e {
        case .invalidParameters: return 2
        case .noMetalDevice, .unsupportedDevice, .shaderLibraryMissing, .shaderLibraryLoadFailed, .tunedParametersInvalid:
            return 3
        case .tooManyKeys: return 4          // only reachable from an input file (sort --in)
        case .allocationFailed, .gpuExecutionFailed, .internalInvariantViolated, .bufferNotShared, .bufferTooSmall:
            return 5
        }
    }

    /// "<case>: <detail>" for `gpuqsort: error: <message>` (§5.3).
    static func describe(_ e: GPUQuicksortError) -> String {
        switch e {
        case .noMetalDevice: return "noMetalDevice"
        case .unsupportedDevice(let s): return "unsupportedDevice: \(s)"
        case .shaderLibraryMissing(let s): return "shaderLibraryMissing: shader library \(s) is missing"
        case .shaderLibraryLoadFailed(let s): return "shaderLibraryLoadFailed: shader library \(s)"
        case .tunedParametersInvalid(let s): return "tunedParametersInvalid: \(s)"
        case .invalidParameters(let s): return "invalidParameters: \(s)"
        case .bufferNotShared: return "bufferNotShared"
        case .bufferTooSmall(let r, let a): return "bufferTooSmall: required \(r) bytes, have \(a)"
        case .tooManyKeys(let c, let m): return "tooManyKeys: \(c) keys, maximum \(m)"
        case .allocationFailed(let b): return "allocationFailed: \(b) bytes"
        case .gpuExecutionFailed(let s): return "gpuExecutionFailed: \(s)"
        case .internalInvariantViolated(let s): return "internalInvariantViolated: \(s)"
        }
    }

    /// Size lists: comma-separated integers with optional K (2^10) or M (2^20) suffix.
    static func sizes(_ s: String) throws -> [Int] {
        try s.split(separator: ",").map { tok -> Int in
            var t = tok.trimmingCharacters(in: .whitespaces)
            var mult = 1
            if t.hasSuffix("K") { mult = 1 << 10; t.removeLast() } else if t.hasSuffix("M") { mult = 1 << 20; t.removeLast() }
            guard let v = Int(t), v >= 0 else { throw ValidationError("invalid size '\(tok)'") }
            let (r, o) = v.multipliedReportingOverflow(by: mult)
            guard !o else { throw ValidationError("invalid size '\(tok)'") }
            return r
        }
    }

    static func distributions(_ s: String) throws -> [Distribution] {
        if s == "all" { return Distribution.allCases.filter { $0 != .fullrange } }
        return try s.split(separator: ",").map {
            guard let d = Distribution(rawValue: String($0)) else { throw ValidationError("unknown distribution '\($0)'") }
            return d
        }
    }

    static func keys(_ s: String) throws -> [KeyType] {
        if s == "all" { return KeyType.allCases }
        return try s.split(separator: ",").map {
            guard let k = KeyType(rawValue: String($0)) else { throw ValidationError("unknown key type '\($0)'") }
            return k
        }
    }

    static func checkSizes(_ ns: [Int], max: Int) throws {
        for n in ns where n > max { throw CLIExit(code: 2, message: "--n \(n) exceeds maxKeys \(max)") }
    }

    static func ms(_ seconds: Double) -> String { String(format: "%.3f", seconds * 1000) }

    /// RFC 4180 field quoting (F-026).
    static func csvField(_ f: String) -> String {
        guard f.contains(where: { $0 == "," || $0 == "\"" || $0 == "\n" || $0 == "\r" }) else { return f }
        return "\"" + f.replacingOccurrences(of: "\"", with: "\"\"") + "\""
    }

    static func median(_ v: [Double]) -> Double {
        let s = v.sorted()
        guard !s.isEmpty else { return 0 }
        return s.count % 2 == 1 ? s[s.count / 2] : (s[s.count / 2 - 1] + s[s.count / 2]) / 2
    }

    static func write(_ data: Data, to path: String) throws {
        do { try data.write(to: URL(fileURLWithPath: path)) } catch {
            throw CLIExit(code: 4, message: "cannot write \(path): \(error.localizedDescription)")
        }
    }

    static func bytes(_ bits: [UInt32]) -> Data { bits.withUnsafeBufferPointer { Data(buffer: $0) } }
}

/// Tuning flags shared by `sort`, `verify`, `bench` (§5.2).
struct TuningFlags: ParsableArguments {
    @Option(name: .customLong("threads"), help: "Threads per threadgroup T.") var threads: Int?
    @Option(help: "Maximum phase-one sequences.") var maxseq: Int?
    @Option(help: "Minimum Quicksort sequence length.") var minseq: Int?
    @Option(help: "Phase-one pivot: minmax (default, D-10) | median.") var pivot: String = "minmax"

    func parameters() throws -> Parameters {
        let piv: PhaseOnePivot
        switch pivot {
        case "minmax": piv = .minMaxAverage
        case "median": piv = .medianOfThree
        default: throw ValidationError("--pivot must be minmax or median")
        }
        return Parameters(threadsPerThreadgroup: threads, maxSequences: maxseq, minSequenceLength: minseq, phaseOnePivot: piv)
    }
}
