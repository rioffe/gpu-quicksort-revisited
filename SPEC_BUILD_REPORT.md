# Spec build report — GPU-Quicksort for Metal

> - **Spec:** `SPEC.md` v0.5 (built from v0.4, then updated for D-10 revised and D-12 extended)
> - **Plan:** `IMPLEMENTATION_PLAN.md` with waves W0 to W6
> - **Reference machine:** Apple M5 Max, Version 26.6.2 (Build 25G83), Swift 6.4, Xcode 27.0, Metal toolchain 32023.921
> - **Status:** BUILT; conformance PASS WITH NOTES (see *Verdict*)

## Inspection

T-17 *(recorded)* is a code inspection of `Sources/GPUQuicksort/Metal/GPUQuicksort.metal` at the W5 commit `d57b983`, with line numbers.

| Item | Where | Result |
| ---- | ----- | ------ |
| R-05: both passes read with stride $T$ starting at $b + t$ | `lqsort` lines 200, 208; `gqsort_partition` lines 274, 290 (`for (uint i = b + tid; i < e; i += T)`) | PASS |
| R-04: pass 2 skips pivot-equal elements | lines 210–211 and 292–293 (`if (v < p) … else if (v > p) …`, no write for `v == p`) | PASS |
| I-007: no kernel reads non-atomic data written by another threadgroup of the same dispatch | `gqsort_partition` touches other threadgroups' data only through `atomic_fetch_add/sub/min/max` (lines 281–282, 306–309); `gqsort_fill` is a separate dispatch and reads the cursors with `atomic_load` (lines 336–337); `lqsort` threadgroups own disjoint sequences | PASS |
| R-28(a): the gap fill waits for every thread's pass 2 | `lqsort` line 213, a device + threadgroup barrier before the fill at line 214; `gqsort_partition` pass 2 starts only after the scan's closing barrier and the offset-broadcast barrier (line 285) | PASS |
| R-28(b): device barrier before reading other threads' device writes | `lqsort` line 182 (loop top, before every pop) and line 230 (before the alternative sorts of children written in pass 2) | PASS |
| R-28(c): the alternative-sort load completes before any write-back | `altsort` line 118 (threadgroup barrier after the load), line 133 (device barrier after the write-back) | PASS |
| R-13: longer child pushed first, pop from top | lines 219–227 (`lFirst`; the longer is pushed, then the shorter) and line 187 (`stack[--ssp]`) | PASS |
| SIMD width: no kernel assumes a SIMD width of 32 | the only SIMD use is the O-2 reduction, which uses `[[simdgroups_per_threadgroup]]` and `[[thread_index_in_simdgroup]]` (lines 262–264, 299–303); no literal 32 appears in any kernel's index arithmetic | PASS |

## Performance

All runs used the **release** build (`swift build -c release`) on the reference machine, after the tuning run (F-020). These are the v0.5 recordings: the default phase-one pivot is `minMaxAverage` (D-10 revised), and the benchmark includes the fourth CPU baseline, `cpu-stdsort-par` (D-12, D-23). The v0.4 recordings (median-of-three default, three CPU baselines) are in git history at `1f9cb52`.

### T-34

The tuning run was `.build/release/gpuqsort tune --write --as-default`, with the default sizes 512K..16M, `uniform`, `uint32`, 3 timed runs per configuration, and one warm-up discarded.

- Status: `exit=0 elapsed_s=119`, so the elapsed time is 119 s, within the K-14 limit of 30 minutes.
- Grid points measured: 2016. Every run was verified against an oracle computed once per size.
- Resulting table entry `Apple M5 Max`: fitted: 2026-09-25, `gpuqsortVersion` 0.4.0. `apple-default` is `{"sameAs": "Apple M5 Max"}`.

Best configuration per size (the Apple analogue of [P Fig 11]):

| n | threads | maxseq | minseq | median wall_ms |
| ---: | ---: | ---: | ---: | ---: |
| 524288 | 1024 | 32 | 4096 | 1.509 |
| 1048576 | 512 | 128 | 2048 | 1.855 |
| 2097152 | 512 | 64 | 4096 | 2.452 |
| 4194304 | 32 | 1024 | 128 | 3.991 |
| 8388608 | 128 | 2048 | 256 | 6.413 |
| 16777216 | 512 | 2048 | 4096 | 11.944 |

Fitted constants (the Apple analogue of [P Tab II]; OLS per C-10, then clamped to $k \geq 0$, $m \geq 1$):

| Parameter | $k$ | $m$ |
| --------- | --: | --: |
| threads per threadgroup | 0 | 453.3 |
| max sequences in phase one | 0.0001381 | 130.5 |
| min sequence length | 1.683e-05 | 2360.7 |

With these constants the defaults are threads 512, `maxseq` 256 and `minseq` 2048 at 1M keys, and threads 512, `maxseq` 2048 and `minseq` 2048 at 16M keys.

### T-32

The benchmark run was `.build/release/gpuqsort --verbose bench --dist all --n 1M,2M,4M,8M,16M --runs 5 --cpu`.

- Status: `exit=0 elapsed_s=141`.
- Rows: 750, all `verified=true`.
- Provenance: metallib `daefabcd5b9a6b33c15bbfb51561bd493900dc5a37ad5b75a09f8ca0da89ca3b`, tuning entry `Apple M5 Max`, gpuqsort 0.4.0.

The table gives the median `wall_ms` over 5 timed runs, for `uint32` keys (compare [P Fig 4]):

| Distribution | n | gpu-quicksort | cpu-swift | cpu-qsort | cpu-stdsort | cpu-stdsort-par |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| uniform | 1M | 2.120 | 74.684 | 63.744 | 14.122 | 8.270 |
| uniform | 2M | 3.118 | 158.151 | 134.398 | 29.222 | 13.281 |
| uniform | 4M | 4.730 | 331.292 | 280.964 | 60.058 | 23.720 |
| uniform | 8M | 7.300 | 691.173 | 581.318 | 122.053 | 47.748 |
| uniform | 16M | 13.003 | 1442.437 | 1222.627 | 251.053 | 95.345 |
| sorted | 1M | 2.265 | 0.705 | 2.615 | 0.693 | 3.179 |
| sorted | 2M | 3.018 | 1.441 | 5.224 | 1.374 | 5.651 |
| sorted | 4M | 4.756 | 2.823 | 10.426 | 2.739 | 9.777 |
| sorted | 8M | 7.266 | 5.664 | 20.884 | 5.468 | 15.312 |
| sorted | 16M | 12.531 | 11.383 | 42.154 | 11.067 | 29.935 |
| zero | 1M | 0.887 | 0.731 | 0.985 | 0.902 | 2.695 |
| zero | 2M | 1.038 | 1.464 | 1.916 | 1.738 | 4.701 |
| zero | 4M | 1.217 | 2.883 | 3.765 | 3.484 | 8.032 |
| zero | 8M | 1.866 | 5.686 | 7.788 | 6.983 | 13.478 |
| zero | 16M | 1.883 | 11.438 | 15.273 | 13.935 | 25.666 |
| bucket | 1M | 2.408 | 50.772 | 52.827 | 14.754 | 7.475 |
| bucket | 2M | 3.463 | 108.507 | 111.578 | 31.421 | 13.345 |
| bucket | 4M | 4.834 | 237.400 | 234.736 | 61.905 | 23.471 |
| bucket | 8M | 9.419 | 502.238 | 489.689 | 126.718 | 44.991 |
| bucket | 16M | 13.042 | 1054.787 | 1037.291 | 259.114 | 88.160 |
| gaussian | 1M | 2.677 | 74.497 | 63.877 | 14.106 | 8.204 |
| gaussian | 2M | 3.200 | 156.561 | 133.462 | 28.871 | 13.287 |
| gaussian | 4M | 5.054 | 328.587 | 280.150 | 59.166 | 24.155 |
| gaussian | 8M | 7.872 | 686.300 | 585.491 | 122.131 | 47.859 |
| gaussian | 16M | 13.569 | 1435.991 | 1215.594 | 253.034 | 94.717 |
| staggered | 1M | 2.393 | 50.253 | 50.372 | 15.777 | 6.392 |
| staggered | 2M | 3.217 | 108.068 | 107.887 | 32.321 | 10.620 |
| staggered | 4M | 4.754 | 239.789 | 223.739 | 66.593 | 17.362 |
| staggered | 8M | 7.634 | 500.892 | 472.875 | 135.080 | 32.702 |
| staggered | 16M | 13.177 | 1056.390 | 1010.806 | 274.919 | 59.148 |

**K-13 ratio** (`uniform`, 16M keys): GPU-Quicksort median 13.003 ms against the fastest CPU baseline (cpu-stdsort-par) at 95.345 ms. The ratio is $ 13.003 / 95.345 = 0.136$, which satisfies the K-13 target of $\leq 0.5$ (the GPU is 7.3× faster). Against sequential `std::sort` the GPU is 19.3× faster, and against Swift `Array.sort()` 111× faster.

Observations against [P §5.4]:
- GPU-Quicksort beats every CPU baseline, including parallel `std::sort`, on `uniform`, `bucket`, `gaussian` and `staggered` at every size, and on `zero` from 2M keys up.
- On `sorted` input, sequential `std::sort` and Swift's sort are still faster up to 32M keys, because both detect presorted runs; parallel `std::sort` does not, and the GPU beats it at every size. The paper reports the same effect for its CPU reference.
- With the `minMaxAverage` pivot, `staggered` is no longer an outlier: 12 phase-one iterations at 16M, like the other random distributions.
- The 32M and 64M results are in `recorded/bench-large.csv` and `PERFORMANCE.md`.

### T-33

The scaling factor of the median `wall_ms` from 1M to 16M `uniform` keys is **6.13**. The spec's T-33 row expects a factor in $[12, 24]$, and the measured value is below that range: at 1M keys the sort takes about 2 ms and is dominated by fixed per-iteration host round trips (one command-buffer commit and read-back per phase-one iteration), not by memory bandwidth. So the time grows sub-linearly between 1M and 16M. T-33 has no gating id. The discrepancy is recorded as spec finding **F-031** (below) rather than hidden.

## Wave ledger

| Wave | Gate run (as executed) | Result | Commit |
| ---- | ---------------------- | ------ | ------ |
| W0 Packaging, Metal pipeline | `scripts/build-metallib.sh`; `swift build`; `swift test --filter PackagingTests` | exit 0; 2 tests passed | `b8ff565` |
| W1 Pure oracles | `gen_reference.py --check`; `swift test --filter "OracleTests\|PackagingTests"` | exit 0; 8 passed | `cd111c0` |
| W2 API + phase two | `build-metallib.sh`; `swift test --filter "APITests\|CorrectnessTests"` | exit 0; 11 passed | `72c72c2` |
| W3 Phase one | `build-metallib.sh`; `swift test --filter "CorrectnessTests\|PackagingTests"`, then `"APITests\|OracleTests"` | exit 0; 15 + 11 passed | `a5ccbb0` |
| W4 Instrumentation | `swift test` | exit 0; 38 tests in 5 suites | `68a8903` |
| W5 CLI | `swift build`; `swift test` | exit 0; 46 tests in 6 suites | `d57b983` |
| W6 Prove it | release `tune`, release `bench`; `swift test --xunit-output junit.xml`; speccheck A and B | see *Conformance gate* | `7e080a8` and the final W6 commit |

## Conformance gate

This is the final run, for `SPEC.md` v0.5. `swift test --xunit-output junit.xml`: **56 tests in 10 suites passed**, 0 skipped.

Phase A (mock judge):

```text
speccheck check --spec SPEC.md --src Sources --tests Tests --results junit-swift-testing.xml --judge mock --strict --out build/speccheck
speccheck: CONFORMING - 128/128 passing (100.0%), 0 failing, 0 skipped, 0 weak, 0 unverified, 0 untested, 0 uncited; 0 dangling, 0 stale; judge=mock
```

Phase B (LLM judge `openai/gpt-6-luna-pro` via OpenRouter, `--judge-concurrency 16`):

```text
speccheck: CONFORMING - 128/128 passing (100.0%), 0 failing, 0 skipped, 0 weak, 0 unverified, 0 untested, 0 uncited; 0 dangling, 0 stale; judge=llm
```

It judged 189 edges, 4 of them unknown, so $\mathit{unknown\_rate} = 0.0212 \leq 0.2$. Elapsed time was 185 s. On v0.5 the first Phase B run found one weakly passing id, K-11: T-21 checked only that the timing fields were positive and ordered. T-21 now asserts that `gpuTime` equals the exact sum of the per-command-buffer GPU durations (one per commit), and that `wallTime` lies within a ContinuousClock measurement around the call.

The first Phase B run found **14 weakly passing ids**. Each was fixed by strengthening its test, never by weakening a citation to a real requirement:

| Id | What the judge found | Fix |
| -- | -------------------- | --- |
| R-03 | the matrix checks only the output | asserts that phase one runs with defaults, and not with `maxseq = 1` |
| R-10 | only the gap contents are checked | the dispatch log shows partition then fill in each phase-one command buffer; child pivots match the completed contents |
| R-11 | the grid never checks which strategy chose pivots | new `phaseOnePivotStrategies` recomputes every child pivot on the CPU for both strategies |
| R-12 | no phase-two dispatch check | exactly one `lqsort` dispatch, with one threadgroup per `done` sequence |
| R-14 | output-only | new `phaseTwoPivotRule`: only the median-of-three sample gives 1 partition and 2 alternative sorts |
| E-03 | only $n = \mathit{minseq} - 1$ | $n \in \{2, 3, \mathit{minseq}/2, \mathit{minseq} - 1\}$ plus the boundary $n = \mathit{minseq}$ |
| E-09 | failure injected without an `.error` status | the runner now observes `.error` with a Metal-domain error at the status check (see F-032) |
| E-11 | the mismatched-key-type buffer call was not exercised | the buffer API is called with `.uint32` on float bit patterns |
| R-04, R-05, R-28, I-007 | the T-17 presence check was cited as proof | new automated `KernelSourceTests` (stride-T loops, no pivot-equal writes, barrier placement, atomic-only cross-threadgroup access); the T-17 presence check now cites only T-17 |
| K-13 | the presence check does not check the ratio | `benchTableRecorded` computes the K-13 ratio from `recorded/bench.csv` and asserts it is at most 0.5 |
| K-14 | the presence check does not check the runtime | `tuningRecorded` asserts `recorded/tune.status` exit 0 with 247 s at most 1800 s, and that every measured grid point is a valid configuration |

## Artifact cross-check (Phase 3.2)

- **Contracts:**
  - C-01 through C-11 exist with the pinned shapes;
  - C-05/C-06 layouts are checked on both sides by T-31;
  - the C-10 bootstrap and fitted table validate (T-37, T-34);
  - C-07 has exactly the v0.4 cases (`keyTypeMismatch` removed).
- **Surfaces:** every §5.2 subcommand, flag and output format is tested by T-27..T-30, T-38, T-39 and T-42. The §7.2 exit table is implemented case by case in `CLI.exitCode(for:)`.
- **Dependencies:** swift-argument-parser (CLI only), Metal, Foundation, os, plus the in-package C/C++ baselines. Nothing else.
- **Determinism:** T-04 gives identical output across 20 runs; T-03 across the full parameter grid.
- **Formulas:**
  - `optp` (K-05) reproduces the spec's worked examples: $(64, 512, 256)$ for $2^{20}$ and $(256, 1024, 1024)$ for $2^{24}$ (T-20);
  - the §7.1 bound holds for $M \in \{1, \text{resolved}, 2^{16}\}$ (T-21);
  - the OLS fit and its degenerate cases are covered (T-37);
  - the K-11 throughput zero rule is in `Bench.summary`.
- **README:** every command in *Quick start* and *Verification* was run on the release build: `info`, `gen 16M`, `sort`, `verify` (36/36 PASS), `bench --cpu` (40 rows), `gen_reference.py --check`; all exit 0.
- **Size:** production code is 1,732 lines (cloc; Swift 1,355, MSL 281, C/C++ and headers 75, script 21) in 28 files, below the plan's 1,920–2,830 estimate with no subsystem dropped. Tests are 1,299 lines (Swift 1,215, Python 84).

## Findings and deviations

| Id | Kind | Finding | Resolution |
| -- | ---- | ------- | ---------- |
| F-031 | spec | T-33 expects the 1M→16M scaling factor in $[12, 24]$; the measured factor is 5.28, because 1M-key sorts are dominated by per-iteration host round trips on this GPU | T-33 is non-gating and records the value. Propose a spec change: either measure scaling from 4M, or drop the range |
| F-032 | environment | E-09 needs a command buffer that completes with `.error`. On the Apple M5 Max, purged buffers (shared and private), an out-of-range write, and a non-terminating kernel all failed to produce `.error` in bounded time; the non-terminating probe left an orphaned kernel on the GPU until reboot | The test hook sets the observed status to `.error` (with a Metal-domain error) at the runner's status check, so the real E-09 handling path runs. The genuine-driver-error path is not exercised |
| F-033 | tooling | speccheck 1.20's Swift adapter drops the result join for tests declared as `@Test(<trait with parentheses>) func` and for `@Suite(a, b) struct` on one line | Conditions moved to named suite traits (`.requiresGPU`, …) and `struct` onto its own line. No behavioral change |
| — | plan | Most test-hook plumbing (stack capacity, observers, counters, fault injection) landed in W2/W3, not W4; in W4 only T-29 and T-06's hook half were RED | Recorded in the W4 commit body |
| — | plan | W2 T-01 ran first as the phase-two-only form; W3 re-parameterized it to defaults and kept the $\mathit{maxseq} = 1$ run as a supplement | As planned |
| — | plan | `verify --dist all` / `bench --dist all` cover the six [P §5.3] distributions; `fullrange` is test-only (C-08) and is covered by T-01 | Test expectation corrected in W5 |

## Verdict

```text
Spec coverage: 128/128 IDs realized (0 deferred)
speccheck (mock): speccheck: CONFORMING - 128/128 passing (100.0%), 0 failing, 0 skipped, 0 weak, 0 unverified, 0 untested, 0 uncited; 0 dangling, 0 stale; judge=mock
speccheck (llm):  speccheck: CONFORMING - 128/128 passing (100.0%), 0 failing, 0 skipped, 0 weak, 0 unverified, 0 untested, 0 uncited; 0 dangling, 0 stale; judge=llm (openai/gpt-6-luna-pro via OpenRouter, unknown_rate 0.0212)
Observed: n/a — no rendered surface; the "live pass" was the release CLI on the reference machine (tune, bench, info, gen, sort, verify), all recorded above
Readiness: BUILT
Conformance: PASS WITH NOTES (F-031: T-33 range does not match the measured scaling; F-032: E-09 uses an observed-status hook, not a driver-produced error)
```
