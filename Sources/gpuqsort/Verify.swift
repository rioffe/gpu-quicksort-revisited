import ArgumentParser
import Foundation
import GPUQuicksort

/// `gpuqsort verify` (§5.2): sort each (dist, n, key) and compare bit for bit with CPUReference.
struct Verify: ParsableCommand {
    static let configuration = CommandConfiguration(abstract: "Check GPU output against the CPU reference.")
    @Option(help: "Distributions (comma-separated or all).") var dist: String = "all"
    @Option(help: "Sizes (K/M suffixes).") var n: String = "1K,1M"
    @Option(help: "Key types (comma-separated or all).") var key: String = "all"
    @Option(help: "MT19937 seed.") var seed: UInt32 = 42
    @Option(help: "Sorts per case.") var runs: Int = 1
    @OptionGroup var tuning: TuningFlags

    func run() throws {
        let dists = try CLI.distributions(dist), sizes = try CLI.sizes(n), keys = try CLI.keys(key)
        let params = try tuning.parameters()
        let q = try CLI.sorter()
        try CLI.checkSizes(sizes, max: q.limits.maxKeys)
        var failed = false
        for d in dists {
            for count in sizes {
                for k in keys {
                    let input = Distribution.generate(d, n: count, seed: seed, key: k)
                    let ref = CLI.bytes(CPUReference.sortedReference(input, k))
                    guard let buf = q.device.makeBuffer(length: max(4 * count, 16), options: .storageModeShared) else {
                        throw GPUQuicksortError.allocationFailed(bytes: 4 * count)
                    }
                    var ok = true
                    for _ in 0..<max(runs, 1) {
                        input.withUnsafeBytes { if $0.count > 0 { memcpy(buf.contents(), $0.baseAddress!, $0.count) } }
                        try q.sort(buf, count: count, keyType: k, parameters: params)
                        ok = ok && Data(bytes: buf.contents(), count: 4 * count) == ref
                    }
                    print("\(ok ? "PASS" : "FAIL") \(d.rawValue) \(count) \(k.rawValue)")
                    failed = failed || !ok
                }
            }
        }
        if failed { throw CLIExit(code: 1, message: nil) }
    }
}
