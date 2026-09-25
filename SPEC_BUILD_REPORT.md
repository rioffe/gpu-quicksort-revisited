# Spec build report — GPU-Quicksort for Metal

> - **Spec:** `SPEC.md` v0.4 (sha256 `b05ffbd347f63bb89a07c40d9b54986f69641f2717d6a79f8f7a6936ba3563e0`)
> - **Plan:** `IMPLEMENTATION_PLAN.md` with waves W0 to W6
> - **Reference machine:** Apple M5 Max, Version 26.6.2 (Build 25G83), Swift 6.4, Xcode 27.0, Metal toolchain 32023.921
> - **Status:** see *Verdict* (filled in after the conformance gate)

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

All runs used the **release** build (`swift build -c release`) on the reference machine, after the tuning run (F-020).

### T-34

The tuning run was `.build/release/gpuqsort tune --write --as-default`, with the default sizes 512K..16M, `uniform`, `uint32`, 3 timed runs per configuration, and one warm-up discarded.

- Status: `exit=0 elapsed_s=247`, so the elapsed time is 247 s, within the K-14 limit of 30 minutes.
- Grid points measured: 2016. Every run was verified against an oracle computed once per size.
- Resulting table entry `Apple M5 Max`: fitted: 2026-09-25, `gpuqsortVersion` 0.4.0. `apple-default` is now `{"sameAs": "Apple M5 Max"}`.

Best configuration per size (the Apple analogue of [P Fig 11]):

| n | threads | maxseq | minseq | median wall_ms |
| ---: | ---: | ---: | ---: | ---: |
| 524288 | 512 | 64 | 4096 | 1.962 |
| 1048576 | 512 | 128 | 4096 | 2.471 |
| 2097152 | 1024 | 256 | 4096 | 3.561 |
| 4194304 | 512 | 512 | 4096 | 5.418 |
| 8388608 | 128 | 4096 | 512 | 8.781 |
| 16777216 | 256 | 4096 | 1024 | 14.963 |

Fitted constants (the Apple analogue of [P Tab II]; OLS per C-10, then clamped to $k \geq 0$, $m \geq 1$):

| Parameter | $k$ | $m$ | Default for 1M / 16M keys |
| --------- | --: | --: | ---------------------- |
| threads per threadgroup | 0 | 490.7 | 512 / 512 |
| max sequences in phase one | 0.0002873 | 1.0 | 256 / 4096 |
| min sequence length | 0 | 2986.7 | 4096 / 4096 |

The Apple fit differs sharply from the paper's 8800GTX constants:
- larger threadgroups (512 vs 64–256);
- a much larger alternative-sort threshold (4096 vs 256–1024), because Apple GPUs have 32 KiB of threadgroup memory and fast threadgroup barriers;
- a phase-one sequence budget growing about linearly with $n$.

### T-32

The benchmark run was `.build/release/gpuqsort --verbose bench --dist all --n 1M,2M,4M,8M,16M --runs 5 --cpu`.

- Status: `exit=0 elapsed_s=135`.
- Rows: 600, all `verified=true`.
- Provenance: metallib `daefabcd5b9a6b33c15bbfb51561bd493900dc5a37ad5b75a09f8ca0da89ca3b`, tuning entry `Apple M5 Max`, gpuqsort 0.4.0.

The table gives the median `wall_ms` over 5 timed runs, for `uint32` keys (compare [P Fig 4]):

| Distribution | n | gpu-quicksort | cpu-swift | cpu-qsort | cpu-stdsort |
| --- | ---: | ---: | ---: | ---: | ---: |
| uniform | 1M | 3.294 | 76.825 | 65.044 | 14.431 |
| uniform | 2M | 4.456 | 161.628 | 135.917 | 29.824 |
| uniform | 4M | 6.675 | 337.692 | 284.218 | 61.118 |
| uniform | 8M | 10.488 | 705.421 | 587.635 | 122.799 |
| uniform | 16M | 17.394 | 1452.308 | 1215.747 | 250.533 |
| sorted | 1M | 3.719 | 0.703 | 2.620 | 0.689 |
| sorted | 2M | 3.543 | 1.450 | 5.265 | 1.380 |
| sorted | 4M | 6.167 | 2.862 | 10.518 | 2.734 |
| sorted | 8M | 9.351 | 5.682 | 21.045 | 5.481 |
| sorted | 16M | 16.044 | 11.371 | 42.118 | 10.980 |
| zero | 1M | 0.446 | 0.702 | 0.926 | 0.880 |
| zero | 2M | 0.751 | 1.444 | 1.917 | 1.746 |
| zero | 4M | 1.473 | 2.876 | 3.747 | 3.468 |
| zero | 8M | 2.147 | 5.663 | 7.663 | 6.944 |
| zero | 16M | 2.318 | 11.333 | 15.171 | 13.971 |
| bucket | 1M | 3.730 | 50.749 | 52.288 | 14.778 |
| bucket | 2M | 4.626 | 109.277 | 109.939 | 30.252 |
| bucket | 4M | 6.271 | 232.717 | 233.820 | 61.750 |
| bucket | 8M | 10.270 | 496.511 | 495.043 | 126.714 |
| bucket | 16M | 18.328 | 1051.071 | 1024.517 | 259.986 |
| gaussian | 1M | 3.005 | 74.181 | 63.394 | 14.079 |
| gaussian | 2M | 3.703 | 158.239 | 135.102 | 28.832 |
| gaussian | 4M | 6.348 | 328.072 | 281.496 | 59.414 |
| gaussian | 8M | 10.192 | 687.324 | 587.051 | 121.822 |
| gaussian | 16M | 18.264 | 1433.397 | 1201.872 | 252.751 |
| staggered | 1M | 3.214 | 50.172 | 50.002 | 15.733 |
| staggered | 2M | 5.486 | 108.235 | 108.078 | 32.257 |
| staggered | 4M | 8.018 | 231.916 | 227.765 | 66.529 |
| staggered | 8M | 15.429 | 495.376 | 482.684 | 135.216 |
| staggered | 16M | 33.137 | 1052.305 | 1007.700 | 275.529 |

**K-13 ratio** (`uniform`, 16M keys): GPU-Quicksort median 17.394 ms against the fastest CPU baseline (cpu-stdsort) at 250.533 ms. The ratio is $ 17.394 / 250.533 = 0.069$, which satisfies the K-13 target of $\leq 0.5$ (the GPU is 14.4× faster). Against Swift `Array.sort()`, the GPU is 83× faster.

Observations against [P §5.4]:
- GPU-Quicksort beats every CPU baseline on `uniform`, `zero`, `bucket`, `gaussian` and `staggered` at every size.
- On `sorted` input, `cpu-swift` and `cpu-stdsort` are faster (0.7–11 ms), because both detect or benefit from presorted runs. The paper reports the same effect ("The CPU reference becomes faster … on the sorted distribution").
- `zero` is the fastest GPU case: one phase-one iteration and no phase two (K-10, E-24).
- `staggered` is the slowest GPU distribution at 16M keys (33 ms): its value ranges interleave, so median-of-three pivots split it less evenly.

### T-33

The scaling factor of the median `wall_ms` from 1M to 16M `uniform` keys is **5.28**. The spec's T-33 row expects a factor in $[12, 24]$, and the measured value is below that range: at 1M keys the sort takes about 3 ms and is dominated by fixed per-iteration host round trips (one command-buffer commit and read-back per phase-one iteration), not by memory bandwidth. So the time grows sub-linearly between 1M and 16M. T-33 has no gating id. The discrepancy is recorded as spec finding **F-031** (below) rather than hidden.
