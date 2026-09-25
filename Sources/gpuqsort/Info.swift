import ArgumentParser
import Foundation
import GPUQuicksort

/// `gpuqsort info` (§5.2): library version, device limits, tuning in effect, metallib stamp,
/// resolved defaults for n = 2^20 and 2^24.
struct Info: ParsableCommand {
    static let configuration = CommandConfiguration(abstract: "Print device limits, tuning and defaults.")
    @Flag(help: "Emit one JSON object.") var json = false

    struct Default: Codable { var n: Int; var parameters: ResolvedParameters }
    struct Output: Codable {
        var version: String, metallibSHA256: String, limits: DeviceLimits, tuning: TunedConstants, defaults: [Default]
    }

    func run() throws {
        let q = try CLI.sorter()
        let defaults = try [1 << 20, 1 << 24].map { Default(n: $0, parameters: try q.resolvedParameters(for: $0, .automatic)) }
        let out = Output(version: GPUQuicksort.version, metallibSHA256: q.metallibSHA256, limits: q.limits,
                         tuning: q.tuning, defaults: defaults)
        if json {
            let enc = JSONEncoder()
            enc.outputFormatting = [.prettyPrinted, .sortedKeys]
            print(String(decoding: try enc.encode(out), as: UTF8.self))
            return
        }
        let l = q.limits, t = q.tuning
        print("gpuqsort \(GPUQuicksort.version)")
        print("device: \(l.name)")
        print("maxThreadsPerThreadgroup: \(l.maxThreadsPerThreadgroup)")
        print("threadExecutionWidth: \(l.threadExecutionWidth)")
        print("maxThreadgroupMemoryLength: \(l.maxThreadgroupMemoryLength)")
        print("maxBufferLength: \(l.maxBufferLength)")
        print("maxKeys: \(l.maxKeys)")
        if t.exactMatch {
            print("tuning: \(t.entry) (exact match)")
        } else {
            print("tuning: apple-default (no exact entry for \(l.name))")                   // E-21
            print("tuning entry: \(t.entry)")
        }
        print("tuning constants: threads k=\(t.threads.k) m=\(t.threads.m); maxseq k=\(t.maxseq.k) m=\(t.maxseq.m); minseq k=\(t.minseq.k) m=\(t.minseq.m)")
        print("metallib sha256: \(q.metallibSHA256)")
        for d in defaults {
            let p = d.parameters
            print("defaults n=\(d.n): threads=\(p.threadsPerThreadgroup) maxseq=\(p.maxSequences) minseq=\(p.minSequenceLength)")
        }
    }
}
