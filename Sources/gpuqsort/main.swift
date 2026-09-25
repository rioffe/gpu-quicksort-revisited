import ArgumentParser
import Foundation
import GPUQuicksort

/// gpuqsort — the CLI of §5.2. Global flags --verbose and --table <path> may appear anywhere.
struct Gpuqsort: ParsableCommand {
    static let configuration = CommandConfiguration(
        commandName: "gpuqsort",
        abstract: "GPU-Quicksort (Cederman & Tsigas 2009) on Metal: sort, verify, benchmark, tune.",
        discussion: "Global flags: --verbose (diagnostics on stderr), --table <path> (tuned-parameter table).",
        version: GPUQuicksort.version,
        subcommands: [Info.self, Gen.self, SortCommand.self, Verify.self, Bench.self, Tune.self])
}

var args = Array(CommandLine.arguments.dropFirst())
var i = 0
while i < args.count {
    if args[i] == "--verbose" { CLI.verbose = true; args.remove(at: i); continue }
    if args[i] == "--table", i + 1 < args.count { CLI.table = args[i + 1]; args.removeSubrange(i...(i + 1)); continue }
    i += 1
}

do {
    var command = try Gpuqsort.parseAsRoot(args)
    try command.run()
    exit(0)
} catch let e as CLIExit {
    if let m = e.message { CLI.stderr("gpuqsort: error: \(m)") }
    exit(e.code)
} catch let e as GPUQuicksortError {
    CLI.stderr("gpuqsort: error: \(CLI.describe(e))")
    exit(CLI.exitCode(for: e))
} catch {
    if Gpuqsort.exitCode(for: error) == .success { Gpuqsort.exit(withError: error) }    // --help, --version
    CLI.stderr("gpuqsort: error: \(Gpuqsort.message(for: error))")
    exit(2)                                                                          // §7.2: usage error
}
