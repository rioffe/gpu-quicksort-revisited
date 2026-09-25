import ArgumentParser
import Foundation
import GPUQuicksort

/// `gpuqsort sort` (§5.2): read raw keys, sort them on the GPU, write raw keys.
struct SortCommand: ParsableCommand {
    static let configuration = CommandConfiguration(commandName: "sort", abstract: "Sort a raw little-endian key file.")
    @Option(name: .customLong("in"), help: "Input file.") var input: String
    @Option(name: .customLong("out"), help: "Output file.") var output: String
    @Option(help: "Key type: uint32, int32, float32.") var key: String = "uint32"
    @OptionGroup var tuning: TuningFlags

    func run() throws {
        guard let k = KeyType(rawValue: key) else { throw ValidationError("unknown key type '\(key)'") }
        let params = try tuning.parameters()
        let data: Data
        do { data = try Data(contentsOf: URL(fileURLWithPath: input)) } catch {
            throw CLIExit(code: 4, message: "cannot read \(input): \(error.localizedDescription)")
        }
        guard data.count % 4 == 0 else {
            throw CLIExit(code: 4, message: "input size \(data.count) is not a multiple of 4")   // E-15
        }
        let q = try CLI.sorter()
        let n = data.count / 4
        guard n <= q.limits.maxKeys else { throw GPUQuicksortError.tooManyKeys(count: n, max: q.limits.maxKeys) }
        guard let buf = q.device.makeBuffer(length: max(data.count, 16), options: .storageModeShared) else {
            throw GPUQuicksortError.allocationFailed(bytes: data.count)
        }
        data.withUnsafeBytes { if $0.count > 0 { memcpy(buf.contents(), $0.baseAddress!, $0.count) } }
        try q.sort(buf, count: n, keyType: k, parameters: params)
        try CLI.write(Data(bytes: buf.contents(), count: data.count), to: output)
    }
}
