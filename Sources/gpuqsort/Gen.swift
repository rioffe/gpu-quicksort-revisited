import ArgumentParser
import Foundation
import GPUQuicksort

/// `gpuqsort gen` (§5.2): write C-08 values as raw little-endian 4-byte keys. Never creates a
/// Metal device (F-028).
struct Gen: ParsableCommand {
    static let configuration = CommandConfiguration(abstract: "Generate a C-08 distribution as raw keys.")
    @Option(help: "Distribution: uniform, sorted, zero, bucket, gaussian, staggered, fullrange.") var dist: String
    @Option(help: "Number of keys (K/M suffixes allowed).") var n: String
    @Option(help: "Key type: uint32, int32, float32.") var key: String = "uint32"
    @Option(help: "MT19937 seed.") var seed: UInt32 = 42
    @Option(help: "Output file.") var out: String

    func run() throws {
        guard let d = Distribution(rawValue: dist) else { throw ValidationError("unknown distribution '\(dist)'") }
        guard let k = KeyType(rawValue: key) else { throw ValidationError("unknown key type '\(key)'") }
        let sizes = try CLI.sizes(n)
        guard sizes.count == 1, let count = sizes.first else { throw ValidationError("--n takes one size") }
        try CLI.checkSizes([count], max: Int(Int32.max))
        try CLI.write(CLI.bytes(Distribution.generate(d, n: count, seed: seed, key: k)), to: out)
    }
}
