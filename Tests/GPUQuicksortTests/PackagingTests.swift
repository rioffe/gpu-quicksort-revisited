import CShared
import Foundation
import Metal
import Testing
@testable import GPUQuicksort

@Suite("Packaging", .requiresGPU)
struct PackagingTests {

    /// T-31: Swift mirrors of C-05/C-06 (imported from CShared) have the same size and field
    /// offsets as the MSL structs, as reported by the `layout_probe` kernel.
    @Test func layoutMatches() throws {
        let device = try #require(TS.device)
        let lib = try ShaderLibrary.load(device: device)
        let pso = try lib.pipeline("layout_probe")
        let out = try #require(device.makeBuffer(length: 64 * 4, options: .storageModeShared))
        let q = try #require(device.makeCommandQueue())
        let cb = try #require(q.makeCommandBuffer())
        let enc = try #require(cb.makeComputeCommandEncoder())
        enc.setComputePipelineState(pso)
        enc.setBuffer(out, offset: 0, index: 0)
        enc.dispatchThreadgroups(MTLSize(width: 1, height: 1, depth: 1),
                                 threadsPerThreadgroup: MTLSize(width: 1, height: 1, depth: 1))
        enc.endEncoding()
        cb.commit(); cb.waitUntilCompleted()
        let gpu = Array(UnsafeBufferPointer(start: out.contents().assumingMemoryBound(to: UInt32.self), count: 26))

        func off<T>(_ k: PartialKeyPath<T>) -> UInt32 { UInt32(MemoryLayout<T>.offset(of: k)!) }
        let cpu: [UInt32] = [
            UInt32(MemoryLayout<SequenceRecord>.size),
            off(\SequenceRecord.start), off(\SequenceRecord.end), off(\SequenceRecord.lnext),
            off(\SequenceRecord.gnext), off(\SequenceRecord.pivot), off(\SequenceRecord.src),
            off(\SequenceRecord.lmin), off(\SequenceRecord.lmax), off(\SequenceRecord.gmin),
            off(\SequenceRecord.gmax),
            UInt32(MemoryLayout<BlockDescriptor>.size),
            off(\BlockDescriptor.begin), off(\BlockDescriptor.end), off(\BlockDescriptor.seq),
            off(\BlockDescriptor._pad),
            UInt32(MemoryLayout<SortSequence>.size),
            off(\SortSequence.begin), off(\SortSequence.end), off(\SortSequence.src), off(\SortSequence._pad),
            UInt32(MemoryLayout<SortStats>.size),
            off(\SortStats.partitions), off(\SortStats.altSorts), off(\SortStats.maxDepth), off(\SortStats.error),
        ]
        #expect(gpu == cpu)
        #expect(cpu[0] == 40 && cpu[11] == 16 && cpu[16] == 16 && cpu[21] == 16)  // C-05, C-06 sizes
    }
}
extension PackagingTests {
    /// T-35 (R-27, C-09, E-19, E-18): the SHA-256 of GPUQuicksort.metal followed by SharedTypes.h equals
    /// Resources/metallib.sha256, and both shipped .metallib variants load and expose all five
    /// kernel names. E-18: a missing library throws `shaderLibraryMissing`; a corrupt library or a
    /// missing kernel throws `shaderLibraryLoadFailed`.
    @Test func stampIsCurrent() throws {
        let root = TS.packageRoot
        let src = try Data(contentsOf: root.appendingPathComponent("Sources/GPUQuicksort/Metal/GPUQuicksort.metal"))
        let hdr = try Data(contentsOf: root.appendingPathComponent("Sources/CShared/include/SharedTypes.h"))
        let stamp = try String(contentsOf: root.appendingPathComponent("Sources/GPUQuicksort/Resources/metallib.sha256"),
                               encoding: .utf8).trimmingCharacters(in: .whitespacesAndNewlines)
        #expect(TS.sha256Hex(src + hdr) == stamp, "stale .metallib: run scripts/build-metallib.sh")
        let device = try #require(TS.device)
        for v in ["GPUQuicksort", "GPUQuicksort-testhooks"] {
            let url = try #require(ShaderLibrary.resourceURL(v, "metallib"))
            let lib = try device.makeLibrary(URL: url)
            for k in ShaderLibrary.kernelNames { #expect(lib.functionNames.contains(k), "\(v): \(k)") }
        }
        // E-18
        #expect { _ = try ShaderLibrary.load(device: device, url: nil) } throws: { e in
            if case GPUQuicksortError.shaderLibraryMissing = e { return true } else { return false }
        }
        let junk = TS.writeTemp(Data("not a metallib".utf8))
        #expect { _ = try ShaderLibrary.load(device: device, url: junk) } throws: { e in
            if case GPUQuicksortError.shaderLibraryLoadFailed = e { return true } else { return false }
        }
        #expect { _ = try ShaderLibrary.load(device: device).pipeline("no_such_kernel") } throws: { e in
            if case GPUQuicksortError.shaderLibraryLoadFailed = e { return true } else { return false }
        }
    }
}

/// T-36 needs the Metal toolchain (C-09); skipped with a message when `xcrun metal` is unavailable.
@Suite("PackagingScript", .requiresMetalToolchain)
struct PackagingScriptTests {
    /// T-36 (C-09, R-27): the build script writes both variants plus the stamp into `$OUT_DIR`,
    /// its stamp equals the checked-in one, and a failing compile exits non-zero leaving the
    /// previous outputs unchanged.
    @Test func buildScript() throws {
        let out = TS.tempDir()
        let r = TS.run("/bin/bash", [TS.packageRoot.appendingPathComponent("scripts/build-metallib.sh").path],
                       env: ["OUT_DIR": out.path])
        #expect(r.status == 0, "\(r.stderr)")
        let stamp = try String(contentsOf: out.appendingPathComponent("metallib.sha256"), encoding: .utf8)
        let checkedIn = try String(contentsOf: TS.packageRoot
            .appendingPathComponent("Sources/GPUQuicksort/Resources/metallib.sha256"), encoding: .utf8)
        #expect(stamp == checkedIn)
        if let device = TS.device {
            for v in ["GPUQuicksort", "GPUQuicksort-testhooks"] {
                let lib = try device.makeLibrary(URL: out.appendingPathComponent("\(v).metallib"))
                #expect(lib.functionNames.contains("key_encode"))
            }
        }

        // Failure atomicity: a copy of the sources with a syntax error.
        let root = TS.tempDir()
        let fm = FileManager.default
        for rel in ["scripts", "Sources/GPUQuicksort/Metal", "Sources/CShared/include"] {
            try fm.createDirectory(at: root.appendingPathComponent(rel).deletingLastPathComponent(),
                                   withIntermediateDirectories: true)
            try fm.copyItem(at: TS.packageRoot.appendingPathComponent(rel), to: root.appendingPathComponent(rel))
        }
        let metal = root.appendingPathComponent("Sources/GPUQuicksort/Metal/GPUQuicksort.metal")
        try (String(contentsOf: metal, encoding: .utf8) + "\nthis is not metal;\n")
            .write(to: metal, atomically: true, encoding: .utf8)
        let before = try Data(contentsOf: out.appendingPathComponent("GPUQuicksort.metallib"))
        let bad = TS.run("/bin/bash", [root.appendingPathComponent("scripts/build-metallib.sh").path],
                         env: ["OUT_DIR": out.path])
        #expect(bad.status != 0)
        #expect(try Data(contentsOf: out.appendingPathComponent("GPUQuicksort.metallib")) == before)
        #expect(try String(contentsOf: out.appendingPathComponent("metallib.sha256"), encoding: .utf8) == stamp)
    }
}
