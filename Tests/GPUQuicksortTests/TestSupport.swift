import Foundation
import Metal
import Testing
@testable import GPUQuicksort

/// Shared helpers for the §9 suites.
enum TS {
    static let packageRoot: URL = URL(fileURLWithPath: #filePath)
        .deletingLastPathComponent().deletingLastPathComponent().deletingLastPathComponent()

    static let device: MTLDevice? = MTLCreateSystemDefaultDevice()
    static var hasGPU: Bool { device != nil }

    static let metalAvailable: Bool = {
        let r = run("/usr/bin/xcrun", ["-sdk", "macosx", "metal", "--version"])
        return r.status == 0
    }()

    struct ProcessResult { var status: Int32; var stdout: String; var stderr: String; var stdoutData: Data }

    @discardableResult
    static func run(_ exe: String, _ args: [String], env: [String: String] = [:], cwd: URL? = nil) -> ProcessResult {
        let p = Process()
        p.executableURL = URL(fileURLWithPath: exe)
        p.arguments = args
        var e = ProcessInfo.processInfo.environment
        for (k, v) in env { e[k] = v }
        p.environment = e
        if let cwd { p.currentDirectoryURL = cwd }
        let out = Pipe(), err = Pipe()
        p.standardOutput = out
        p.standardError = err
        do { try p.run() } catch { return ProcessResult(status: -1, stdout: "", stderr: "\(error)", stdoutData: Data()) }
        // Drain both pipes concurrently to avoid deadlock on large outputs.
        var outData = Data(), errData = Data()
        let g = DispatchGroup()
        g.enter(); DispatchQueue.global().async { outData = out.fileHandleForReading.readDataToEndOfFile(); g.leave() }
        g.enter(); DispatchQueue.global().async { errData = err.fileHandleForReading.readDataToEndOfFile(); g.leave() }
        p.waitUntilExit()
        g.wait()
        return ProcessResult(status: p.terminationStatus,
                             stdout: String(decoding: outData, as: UTF8.self),
                             stderr: String(decoding: errData, as: UTF8.self),
                             stdoutData: outData)
    }

    static func tempDir() -> URL {
        let u = FileManager.default.temporaryDirectory.appendingPathComponent("gpuqs-\(UUID().uuidString)")
        try! FileManager.default.createDirectory(at: u, withIntermediateDirectories: true)
        return u
    }

    static func sha256Hex(_ data: Data) -> String {
        let r = run("/usr/bin/shasum", ["-a", "256", writeTemp(data).path])
        return String(r.stdout.prefix(64))
    }

    static func writeTemp(_ data: Data) -> URL {
        let u = FileManager.default.temporaryDirectory.appendingPathComponent("gpuqs-\(UUID().uuidString).bin")
        try! data.write(to: u)
        return u
    }
}
