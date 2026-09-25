# GPU-Quicksort on Metal

A Swift + Metal implementation of **GPU-Quicksort** (Cederman and Tsigas, *GPU-Quicksort: A Practical Quicksort Algorithm for Graphics Processors*, ACM JEA 14, Art. 1.4, 2009, [doi:10.1145/1498698.1564500](https://doi.org/10.1145/1498698.1564500)) for Apple silicon GPUs. It includes a library, a CLI for benchmarking, verification and tuning, and a test suite traced to [`SPEC.md`](SPEC.md) v0.5. The suite is checked against that spec by [speccheck](https://github.com/rioffe/speccheck) — read [Introducing speccheck](https://rioffe.github.io/speccheck/introducing-speccheck.html) for the idea behind it.

**It's fast.** On an Apple M5 Max it sorts **64 million 32-bit keys in 43 ms, about 1.55 billion keys per second**. That is **9× faster than parallel `std::sort` running on all 18 CPU cores**, 24× faster than `std::sort`, and 145× faster than Swift's `Array.sort()`. 16M keys take 13 ms. It stays ahead on every random input distribution from the paper, including the adversarial `staggered` one, and all-equal input sorts at nearly 10 billion keys per second. The one case where a CPU sort keeps up is already-sorted input, where sequential `std::sort` detects the presorted runs; at 64M keys GPU-Quicksort matches it. Full numbers, methodology and next steps are in [PERFORMANCE.md](PERFORMANCE.md).

The paper itself is not included in this repository; read it at the DOI above. `SPEC.md` cites it as [P §n], [P Alg n], [P Fig n] and [P Tab n].

The algorithm runs in two phases. In phase one, several threadgroups cooperate on one sequence. Each threadgroup counts its section, runs a prefix sum, reserves output space with one atomic fetch-and-add per side, and scatters into an auxiliary buffer; the host loops until enough independent subsequences exist. In phase two, each threadgroup sorts one subsequence on its own, using an explicit stack (shorter part first) and a bitonic sort once a part fits in threadgroup memory.

## Setup

- **Required:**
  - macOS 15 or later on Apple silicon (Metal GPU family `apple7`);
  - the Swift 6 toolchain (built and tested with Swift 6.4 and Xcode 27).
- **Optional:** the Metal Toolchain, needed only to rebuild the shaders (`xcodebuild -downloadComponent MetalToolchain`). The compiled `.metallib` files are checked in, so `swift build` does not need it.
- **Dependencies:** `swift-argument-parser` (CLI only). The library has no third-party dependencies.
- **Parallel `std::sort` baseline:** the `CPUBaselines` target is built with `-fexperimental-library` to get libc++'s parallel algorithms. The SDK's `libc++experimental.a` is built for macOS 27, so the linker prints a deployment-version warning; the baseline is used only by `bench`.

```bash
swift build -c release
.build/release/gpuqsort info
```

## Quick start

```bash
# Generate 16M uniformly distributed keys, sort them on the GPU, and check the result.
.build/release/gpuqsort gen --dist uniform --n 16M --out /tmp/keys.bin
.build/release/gpuqsort sort --in /tmp/keys.bin --out /tmp/sorted.bin
.build/release/gpuqsort verify --dist all --n 1K,1M --key all

# Benchmark against four CPU sorts (Swift Array.sort, libc qsort, C++ std::sort, parallel std::sort).
.build/release/gpuqsort bench --dist uniform --n 1M,16M --runs 5 --cpu
```

## Library

```swift
import GPUQuicksort

let sorter = try GPUQuicksort()                  // default device, bundled tuning table
var keys: [Float] = ...                          // UInt32, Int32 or Float
let report = try sorter.sort(&keys)              // ascending; Float uses IEEE 754 totalOrder
print(report.wallTime, report.phaseOneIterations)

// Zero-copy on a shared MTLBuffer:
try sorter.sort(buffer, count: n, keyType: .uint32,
                parameters: Parameters(threadsPerThreadgroup: 256, maxSequences: 1024, minSequenceLength: 512))
```

| API | Notes |
| --- | --- |
| `init(device:tuning:)` | `TuningSource`: `.bundled` (default), `.file(URL)`, `.constants(TunedConstants)`. Throws `noMetalDevice`, `unsupportedDevice`, `shaderLibraryMissing`, `shaderLibraryLoadFailed`, `tunedParametersInvalid`. |
| `sort(_:count:keyType:parameters:)` | The buffer must be `.storageModeShared`. Synchronous and not cancellable. Returns a `SortReport`. |
| `sort(_ keys: inout [K])` | Copies into a staging buffer; the copy time is included in `wallTime`. |
| `resolvedParameters(for:_:)` | The parameters a sort of `n` keys would use. |
| `limits`, `tuning`, `metallibSHA256`, `version` | Device limits, tuning constants in effect, shader stamp, library version (`0.4.0`). |
| `diagnostics` | Handler for the per-iteration and summary lines (also sent to `os.Logger`, subsystem `GPUQuicksort`). |

`SortReport` fields: count, key type, resolved parameters, wall and GPU time, phase-one iterations and sequences, whether the iteration cap was reached, phase-two partitions and alternative sorts, maximum stack depth, auxiliary and bookkeeping bytes, and provenance (library version, metallib hash, tuning entry).

Errors are `GPUQuicksortError` cases (SPEC C-07). Key values are never logged.

## CLI

`gpuqsort [--verbose] [--table <path>] <subcommand>`. `--verbose` writes the diagnostic lines to stderr. `--table` uses a tuned-parameter table file instead of the bundled one.

| Subcommand | Purpose |
| ---------- | ------- |
| `info [--json]` | Device limits, tuning in effect, metallib stamp, default parameters for 1M and 16M keys |
| `gen --dist D --n N --out F [--key K] [--seed S]` | Write a [P §5.3] distribution (`uniform`, `sorted`, `zero`, `bucket`, `gaussian`, `staggered`, plus test-only `fullrange`) as raw little-endian 4-byte keys |
| `sort --in F --out F [--key K]` | Sort a raw key file on the GPU |
| `verify [--dist all] [--n 1K,1M] [--key all] [--runs R]` | Compare GPU output bit for bit against the CPU reference; prints `PASS`/`FAIL` lines |
| `bench [--dist all] [--n 1M,…,16M] [--runs 5] [--cpu] [--format csv\|json]` | Time only the sort, discard one warm-up run, verify every run. `--cpu` adds `cpu-swift`, `cpu-qsort`, `cpu-stdsort` and `cpu-stdsort-par` (parallel `std::sort`). Refuses a debug build unless `--allow-debug` is passed. |
| `tune [--n 512K,…,16M] [--runs 3] [--write] [--as-default]` | Grid-search threads/maxseq/minseq per size, fit the `optp` constants, and optionally write the table. Refuses a debug build unless `--allow-debug` is passed. |

Tuning flags for `sort`, `verify` and `bench`: `--threads T`, `--maxseq N`, `--minseq N`, `--pivot minmax|median`. The default phase-one pivot is `minmax` (the average of the sequence's minimum and maximum, as in the paper's experiments); `median` selects median-of-three. Sizes accept the suffixes `K` ($2^{10}$) and `M` ($2^{20}$).

**Exit codes** (SPEC §7.2):

| Code | Meaning |
| ---: | ------- |
| 0 | success |
| 1 | verification failed |
| 2 | usage or invalid parameters |
| 3 | Metal, shader library or tuning-table problem |
| 4 | I/O or input format |
| 5 | GPU execution failure or internal invariant violation |

**Bench CSV columns:** `device,key,distribution,n,run,algorithm,wall_ms,gpu_ms,threads,maxseq,minseq,phase1_iterations,phase1_sequences,max_stack_depth,verified,gpuqsort_version,metallib_sha256,tuning_entry,os_version`.

## Parameters and tuning

Parameters you leave unset default to the paper's formula

$$
\mathit{optp}(s, k, m) = 2^{\lfloor \log_2(s k + m) + 0.5 \rfloor}
$$

with $s$ the number of keys and $(k, m)$ per parameter taken from `Sources/GPUQuicksort/Resources/TunedParameters.json`. The table holds the paper's 8800GTX constants as `paper-8800gtx`, and the fit measured on an Apple M5 Max by `gpuqsort tune --write --as-default`. `apple-default` points at the entry used for any GPU without its own. To re-tune on another machine:

```bash
swift build -c release && .build/release/gpuqsort tune --write
```

## Artifacts

| File | Contents |
| ---- | -------- |
| `Sources/GPUQuicksort/Metal/GPUQuicksort.metal` | Kernels `key_encode`, `key_decode`, `gqsort_partition`, `gqsort_fill`, `lqsort` (plus `layout_probe` for tests) |
| `Sources/CShared/include/SharedTypes.h` | The shared host/kernel structs (`SequenceRecord` 40 B, `BlockDescriptor`, `SortSequence`, `SortStats` 16 B) |
| `Sources/GPUQuicksort/Resources/*.metallib`, `metallib.sha256` | Precompiled release and test-hook libraries, and the SHA-256 of their sources |
| `Sources/GPUQuicksort/Resources/TunedParameters.json` | The tuning table (SPEC C-10) |
| `Tests/GPUQuicksortTests/Fixtures/gen_reference.py`, `golden.json` | Independent Python generator and golden hashes for the distributions |

After editing the `.metal` file or `SharedTypes.h`, run `scripts/build-metallib.sh` and commit its outputs. The test suite fails if the stamp is stale.

## Project layout

```text
Package.swift
scripts/build-metallib.sh            MSL → .metallib (release + test hooks) and the stamp
Sources/CShared/                     SharedTypes.h (host ↔ kernel layouts)
Sources/CPUBaselines/                qsort.c, stdsort.cpp (C ABI baselines)
Sources/GPUQuicksort/
  GPUQuicksort.swift                 public API, validation, report assembly
  Sorter.swift                       host orchestration: codec, phase-one loop, phase two
  CommandRunner.swift, BufferPool.swift, ShaderLibrary.swift
  KeyCodec.swift, Distributions.swift, ParameterResolver.swift, TunedParameters.swift
  CPUReference.swift, Diagnostics.swift, Errors.swift, Types.swift
  Metal/GPUQuicksort.metal           kernels (excluded from the Swift target)
  Resources/                         metallibs, stamp, TunedParameters.json
Sources/gpuqsort/                    CLI: main, Info, Gen, SortCommand, Verify, Bench, Tuner, Common
Tests/GPUQuicksortTests/             Oracle, Packaging, Correctness, API, Structure, CLI, Recorded suites
```

## Verification

```bash
swift test --xunit-output junit.xml     # debug build: includes test hooks; ~3 minutes on an M5 Max
speccheck check --spec SPEC.md --src Sources --tests Tests \
  --results junit-swift-testing.xml --judge mock --strict --out build/speccheck
```

Every test cites the SPEC ids it proves in its doc comment. `SPEC_BUILD_REPORT.md` records the conformance evidence, the recorded benchmark and tuning runs, and the verdict.

## Scope

The full `SPEC.md` v0.4 is implemented. The spec's non-goals are:
- stable or key–value sorting;
- keys wider than 32 bits;
- a guard against Quicksort's worst case;
- non-Apple GPUs;
- the paper's competitor algorithms.

## License

Released under the [MIT License](LICENSE).
