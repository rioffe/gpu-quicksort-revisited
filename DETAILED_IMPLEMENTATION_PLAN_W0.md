# Detailed implementation plan — W0: Packaging and the Metal pipeline

> - **Wave:** W0 of W0–W6 (`IMPLEMENTATION_PLAN.md` §4 item 1).
> - **Spec basis:** `SPEC.md` v0.4, sha256 `b05ffbd347f63bb89a07c40d9b54986f69641f2717d6a79f8f7a6936ba3563e0`. Not edited by this wave.
> - **Gate:** a package that builds, a script that produces both `.metallib` variants plus the stamp, a library that loads them, and a Swift/MSL layout check that agrees.
> - **Budget:** 120–180 production lines across 4 files, plus the build script (§5 row "Packaging").
> - **Depends on:** the Metal Toolchain being installed (plan §7). **Unlocks:** W1 (package targets), W2 (`ShaderLibrary`, the MSL file, `SharedTypes.h`).

## 1. Objective and spec obligations

| Spec id | Obligation | How W0 discharges it |
| ------- | ---------- | -------------------- |
| C-09 | package layout, script, stamp, loading from `Bundle.module` | `Package.swift`, script, `ShaderLibrary` |
| R-27 | precompiled `.metallib`, no runtime compile, stale check | script plus loader (half: T-35 needs all 5 kernels, finished in W3) |
| C-05, C-06 | one shared header, `GQS_ATOMIC_U32` | `SharedTypes.h`; T-31 |
| D-21 | hooks defined in debug | `swiftSettings` define on library and CLI |

## 2. Entry preconditions

- `xcrun -sdk macosx metal --version` exits 0.
- Network access to GitHub for `swift-argument-parser` (fetched by `swift build`).

## 3. Deliverables, file by file

- **`Package.swift`:**
  - tools 6.0; `.macOS(.v15)`;
  - targets `CShared` (C), `CPUBaselines` (C/C++, filled in W1; W0 adds only the header and an empty `.c`/`.cpp` pair), `GPUQuicksort` (`exclude: ["Metal"]`, `resources: [.copy("Resources")]`, define `GPUQS_TEST_HOOKS` when debug), `gpuqsort` (executable, ArgumentParser), `GPUQuicksortTests` (depends on all, `resources: [.copy("Fixtures")]`);
  - `cxxLanguageStandard: .cxx17`.
- **`Sources/CShared/include/SharedTypes.h`:** exactly C-05 and C-06 (`SequenceRecord` 40 B, `BlockDescriptor` 16 B, `SortSequence` 16 B, `SortStats` 16 B), plus kernel parameter structs (`PartitionParams`, `SortParams`, `CodecParams`), which are internal.
- **`Sources/CShared/CShared.c`:** an empty translation unit.
- **`Sources/GPUQuicksort/Metal/GPUQuicksort.metal`:** `key_encode`, `key_decode` (C-04), and `layout_probe` (writes `sizeof`/`offsetof` of the four structs; used by T-31). W2 and W3 append the sorting kernels.
- **`scripts/build-metallib.sh`:**
  - `OUT_DIR` (default `Sources/GPUQuicksort/Resources`);
  - two variants, built in a temp directory and moved only on success;
  - `metallib.sha256` = SHA-256 of `.metal` followed by `.h` (C-09).
- **`Sources/GPUQuicksort/ShaderLibrary.swift`:** loads the variant via `Bundle.module` and `makeLibrary(URL:)`, builds pipelines, reads the stamp. Throws `shaderLibraryMissing`/`shaderLibraryLoadFailed` (E-18). A minimal `GPUQuicksortError` enum (C-07) is introduced here.

## 4. Work items

- **W0-01:** write the tests first:
  - `PackagingTests.layoutMatches` (T-31) and `PackagingTests.buildScript` (T-36). Both fail: no package or script yet.
  - Then write the manifest, header, MSL and script. Evidence: `swift build` exits 0.
- **W0-02:** `ShaderLibrary` plus T-31 (the probe kernel's `sizeof`/`offsetof` equal `MemoryLayout`), then T-36 (script into a temp `OUT_DIR`; stamp equals the checked-in one; an injected syntax error exits non-zero with the outputs unchanged).
- **W0-03:** commit the generated `Resources/*.metallib` and the stamp.

## 5. Test plan

| File | Ids | Asserts |
| ---- | --- | ------- |
| `Tests/GPUQuicksortTests/PackagingTests.swift` | T-31, T-36 (T-35 added in W3) | layout equality; script outputs, stamp, failure atomicity |

## 6. Gate

1. `scripts/build-metallib.sh` → exit 0; `Resources/GPUQuicksort.metallib`, `GPUQuicksort-testhooks.metallib` and `metallib.sha256` exist.
2. `swift build` → exit 0, no warnings from our targets.
3. `swift test --filter PackagingTests` → exit 0; T-31 and T-36 passed.

## 7. Traceability

| Id | Realized in | Test | Status after W0 |
| -- | ----------- | ---- | --------------- |
| C-05, C-06 | `SharedTypes.h` | T-31 | passing |
| C-09, R-27 | script, `ShaderLibrary` | T-36 (T-35 in W3) | half |

## 8. Traps

- SwiftPM rejects a C target with no source file (F-029): keep `CShared.c`.
- `.metal` inside a Swift target must be excluded, or SwiftPM reports unhandled files (C-09).
- The MSL side must see `metal::atomic_uint` and Swift must see `uint32_t` through the macro, or layouts differ.

## 9. Exit and handoff

- **Frozen:** `SharedTypes.h` struct names and fields; `ShaderLibrary.load(device:) throws -> ShaderLibrary`, `pipeline(_ name: String) throws -> MTLComputePipelineState`, `stamp: String`.
- **Re-run by W1:** gate command 3.
