import Foundation
import Metal

/// Loads the precompiled kernels (R-27, C-09). MSL source is never compiled at runtime.
struct ShaderLibrary {
    /// Kernel function names pinned by C-09.
    static let kernelNames = ["key_encode", "key_decode", "gqsort_partition", "gqsort_fill", "lqsort"]

    #if GPUQS_TEST_HOOKS
    static let variant = "GPUQuicksort-testhooks"   // D-21: debug builds load the hooks variant
    #else
    static let variant = "GPUQuicksort"
    #endif

    let library: MTLLibrary
    /// Contents of Resources/metallib.sha256 (C-09, F-014 provenance).
    let stamp: String

    static func resourceURL(_ name: String, _ ext: String) -> URL? {
        Bundle.module.url(forResource: name, withExtension: ext, subdirectory: "Resources")
    }

    /// E-18: a missing resource throws `shaderLibraryMissing`; a load failure throws
    /// `shaderLibraryLoadFailed`.
    static func load(device: MTLDevice) throws -> ShaderLibrary {
        guard let url = resourceURL(variant, "metallib") else {
            throw GPUQuicksortError.shaderLibraryMissing("Resources/\(variant).metallib")
        }
        let lib: MTLLibrary
        do { lib = try device.makeLibrary(URL: url) } catch {
            throw GPUQuicksortError.shaderLibraryLoadFailed("\(url.lastPathComponent): \(error.localizedDescription)")
        }
        var stamp = ""
        if let s = resourceURL("metallib", "sha256"), let text = try? String(contentsOf: s, encoding: .utf8) {
            stamp = text.trimmingCharacters(in: .whitespacesAndNewlines)
        }
        return ShaderLibrary(library: lib, stamp: stamp)
    }

    func pipeline(_ name: String) throws -> MTLComputePipelineState {
        guard let f = library.makeFunction(name: name) else {
            throw GPUQuicksortError.shaderLibraryLoadFailed("kernel \(name) not found in \(ShaderLibrary.variant).metallib")
        }
        do { return try library.device.makeComputePipelineState(function: f) } catch {
            throw GPUQuicksortError.shaderLibraryLoadFailed("pipeline \(name): \(error.localizedDescription)")
        }
    }
}
