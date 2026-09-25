import Foundation

/// C-01: where tuning constants come from (F-001).
public enum TuningSource: Sendable {
    case bundled                    // Resources/TunedParameters.json, lookup per C-10
    case file(URL)                  // a table with the C-10 schema, lookup per C-10
    case constants(TunedConstants)  // no table; used as given (still validated: k ≥ 0, m ≥ 1)
}

/// C-01 / C-10: the constants in effect.
public struct TunedConstants: Sendable, Codable, Equatable {
    public struct Line: Sendable, Codable, Equatable {
        public var k: Double
        public var m: Double
        public init(k: Double, m: Double) { self.k = k; self.m = m }
    }
    public var entry: String
    public var exactMatch: Bool
    public var threads: Line, maxseq: Line, minseq: Line

    public init(entry: String, exactMatch: Bool, threads: Line, maxseq: Line, minseq: Line) {
        self.entry = entry
        self.exactMatch = exactMatch
        self.threads = threads
        self.maxseq = maxseq
        self.minseq = minseq
    }

    /// [P Tab II] 8800GTX row (C-10 bootstrap entry "paper-8800gtx").
    public static let paper8800GTX = TunedConstants(
        entry: "paper-8800gtx", exactMatch: false,
        threads: Line(k: 0.00001172, m: 53), maxseq: Line(k: 0.00003748, m: 476), minseq: Line(k: 0.00004685, m: 211))

    /// C-10 validation of one set of lines: every k ≥ 0, m ≥ 1, all finite.
    func validate() throws {
        for (name, l) in [("threads", threads), ("maxseq", maxseq), ("minseq", minseq)] {
            guard l.k.isFinite, l.m.isFinite, l.k >= 0, l.m >= 1 else {
                throw GPUQuicksortError.tunedParametersInvalid("\(entry).\(name): k = \(l.k), m = \(l.m) (need k >= 0, m >= 1, finite)")
            }
        }
    }
}

/// One stored entry of the C-10 table.
package struct TunedEntry: Codable, Equatable, Sendable {
    package var fitted: String
    package var gpuqsortVersion: String
    package var sizes: [Int]
    package var threads: TunedConstants.Line
    package var maxseq: TunedConstants.Line
    package var minseq: TunedConstants.Line

    package init(fitted: String, gpuqsortVersion: String, sizes: [Int],
                 threads: TunedConstants.Line, maxseq: TunedConstants.Line, minseq: TunedConstants.Line) {
        self.fitted = fitted; self.gpuqsortVersion = gpuqsortVersion; self.sizes = sizes
        self.threads = threads; self.maxseq = maxseq; self.minseq = minseq
    }
}

/// C-10: the tuned-parameter table.
package struct TunedTable: Equatable, Sendable {
    package enum Item: Equatable, Sendable {
        case entry(TunedEntry)
        case sameAs(String)
        package var lineEntry: TunedEntry? { if case .entry(let e) = self { return e } else { return nil } }
    }
    package var schema: Int
    package var entries: [String: Item]

    package init(schema: Int = 1, entries: [String: Item] = [:]) {
        self.schema = schema
        self.entries = entries
    }

    /// The key `apple-default` points at (after its one `sameAs` hop).
    package var defaultTarget: String {
        if case .sameAs(let t)? = entries["apple-default"] { return t }
        return "apple-default"
    }

    /// Parses and validates (E-20). Every failure is `tunedParametersInvalid(<reason>)`.
    package static func decode(_ data: Data) throws -> TunedTable {
        func bad(_ s: String) -> GPUQuicksortError { .tunedParametersInvalid(s) }
        guard let root = try? JSONSerialization.jsonObject(with: data) as? [String: Any] else {
            throw bad("not a JSON object")
        }
        guard let schema = root["schema"] as? Int, schema == 1 else { throw bad("schema must be 1") }
        guard let raw = root["entries"] as? [String: Any] else { throw bad("missing entries object") }
        var entries: [String: Item] = [:]
        for (key, value) in raw {
            guard let obj = value as? [String: Any] else { throw bad("entry \(key) is not an object") }
            if let target = obj["sameAs"] as? String {
                entries[key] = .sameAs(target)
            } else {
                let sub = try JSONSerialization.data(withJSONObject: obj)
                guard let e = try? JSONDecoder().decode(TunedEntry.self, from: sub) else {
                    throw bad("entry \(key) does not have the C-10 shape")
                }
                entries[key] = .entry(e)
            }
        }
        let t = TunedTable(schema: schema, entries: entries)
        try t.validate()
        return t
    }

    package func validate() throws {
        func bad(_ s: String) -> GPUQuicksortError { .tunedParametersInvalid(s) }
        guard entries["apple-default"] != nil else { throw bad("apple-default is missing") }
        for (key, item) in entries {
            switch item {
            case .sameAs(let target):
                guard let t = entries[target] else { throw bad("\(key).sameAs \(target) does not exist") }
                guard t.lineEntry != nil else { throw bad("\(key).sameAs \(target) is itself sameAs") }
            case .entry(let e):
                try TunedConstants(entry: key, exactMatch: false, threads: e.threads, maxseq: e.maxseq, minseq: e.minseq).validate()
            }
        }
    }

    /// C-10 lookup: exact device name, else apple-default with one sameAs hop.
    package func lookup(deviceName: String) -> TunedConstants {
        let exact = entries[deviceName] != nil
        var key = exact ? deviceName : "apple-default"
        if case .sameAs(let t)? = entries[key] { key = t }
        let e = entries[key]!.lineEntry!
        return TunedConstants(entry: key, exactMatch: exact, threads: e.threads, maxseq: e.maxseq, minseq: e.minseq)
    }

    /// C-10 `--write` rule 2 (and rule 1 via an empty table).
    package func upserting(name: String, entry: TunedEntry, asDefault: Bool) -> TunedTable {
        var t = self
        t.entries[name] = .entry(entry)
        if asDefault || t.entries["apple-default"] == nil { t.entries["apple-default"] = .sameAs(name) }
        return t
    }

    /// Sorted keys, 2-space indentation.
    package func encoded() -> Data {
        var obj: [String: Any] = [:]
        for (key, item) in entries {
            switch item {
            case .sameAs(let t): obj[key] = ["sameAs": t]
            case .entry(let e):
                let d = try! JSONEncoder().encode(e)
                obj[key] = try! JSONSerialization.jsonObject(with: d)
            }
        }
        let root: [String: Any] = ["schema": schema, "entries": obj]
        var data = try! JSONSerialization.data(withJSONObject: root, options: [.prettyPrinted, .sortedKeys])
        data.append(0x0A)
        return data
    }

    /// C-10 fit: ordinary least squares of x ≈ k·s + m; k < 0 → (0, mean); m = max(m, 1);
    /// one point → (0, x1).
    package static func fitLine(sizes s: [Double], values x: [Double]) -> (k: Double, m: Double) {
        let j = Double(s.count)
        guard s.count >= 2 else { return (0, max(x.first ?? 1, 1)) }
        let sBar = s.reduce(0, +) / j, xBar = x.reduce(0, +) / j
        var sxx = 0.0, sxy = 0.0
        for i in s.indices { sxx += (s[i] - sBar) * (s[i] - sBar); sxy += (s[i] - sBar) * (x[i] - xBar) }
        var k = sxx > 0 ? sxy / sxx : 0
        var m = xBar - k * sBar
        if k < 0 { k = 0; m = xBar }
        return (k, max(m, 1))
    }
}
