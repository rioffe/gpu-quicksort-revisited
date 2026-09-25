# GPU-Quicksort on Metal: current performance and next steps

> - **Build:** `gpuqsort` 0.4.0 implementing `SPEC.md` v0.5, release configuration
> - **Machine:** Apple M5 Max (18 CPU cores), macOS 26.6.2, Metal toolchain 32023.921
> - **Source data:** `recorded/bench.csv` (1M–16M keys, 750 rows), `recorded/bench-large.csv` (32M–64M keys, 300 rows), `recorded/tune.json`, and `recorded/stdsort-par-unseq.txt`. Every GPU and CPU result was verified against the CPU reference sort.
> - **Method:** `gpuqsort bench --dist all --n 1M,2M,4M,8M,16M` (and `--n 32M,64M`) `--runs 5 --cpu`, `uint32` keys, tuned defaults from the `Apple M5 Max` entry of `TunedParameters.json`. The phase-one pivot is `minMaxAverage`, the v0.5 default. Every value is the median of 5 timed runs; one warm-up run is discarded, and copying the input is not timed.
> - **CPU baselines:** Swift `Array.sort()`, libc `qsort`, C++ `std::sort`, and parallel C++ `std::sort(std::execution::par, …)`, which is libc++'s parallel algorithms on libdispatch, enabled with `-fexperimental-library`.

## Summary

GPU-Quicksort sorts **64M 32-bit keys in 43 ms (1.55 Gkeys/s)** and 16M keys in 13 ms. On random inputs it is **9× faster than parallel `std::sort`** on all 18 CPU cores, and 24× faster than sequential `std::sort`. The only case where a CPU sort matches it is already-sorted input, where sequential `std::sort` detects the presorted runs.

## Results at 64M keys

| Input | GPU-Quicksort | GPU-only | Throughput | Phase-one iterations | vs. parallel `std::sort` | vs. `std::sort` |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| uniform | 43.2 ms | 38.7 ms | 1.55 Gkeys/s | 13 | 9.0× faster | 24.4× faster |
| gaussian | 46.0 ms | 41.2 ms | 1.46 Gkeys/s | 15 | 8.4× faster | 22.8× faster |
| bucket | 45.0 ms | 40.2 ms | 1.49 Gkeys/s | 14 | 7.9× faster | 24.0× faster |
| staggered | 45.2 ms | 40.2 ms | 1.49 Gkeys/s | 14 | 4.9× faster | 25.6× faster |
| zero | 6.8 ms | 5.7 ms | 9.94 Gkeys/s | 1 | 13.4× faster | 8.2× faster |
| sorted | 43.4 ms | 38.4 ms | 1.54 Gkeys/s | 13 | 2.5× faster | 1.0× faster |

## Results at 16M keys

| Input | GPU-Quicksort | GPU-only | Throughput | Phase-one iterations | vs. parallel `std::sort` | vs. `std::sort` |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| uniform | 13.0 ms | 9.6 ms | 1.29 Gkeys/s | 12 | 7.3× faster | 19.3× faster |
| gaussian | 13.6 ms | 9.8 ms | 1.24 Gkeys/s | 13 | 7.0× faster | 18.6× faster |
| bucket | 13.0 ms | 9.8 ms | 1.29 Gkeys/s | 12 | 6.8× faster | 19.9× faster |
| staggered | 13.2 ms | 9.7 ms | 1.27 Gkeys/s | 12 | 4.5× faster | 20.9× faster |
| zero | 1.9 ms | 1.2 ms | 8.91 Gkeys/s | 1 | 13.6× faster | 7.4× faster |
| sorted | 12.5 ms | 9.3 ms | 1.34 Gkeys/s | 11 | 2.4× faster | 1.1× slower |

*GPU-Quicksort* is the library's `wallTime`: from the `sort` call (after validation) to its return, including every host round trip. *GPU-only* is the sum of the command buffers' GPU execution time. Throughput is $n / t$ from the total time.

## Scaling (uniform)

| n | GPU-Quicksort | Throughput | GPU-only share of total | vs. parallel `std::sort` |
| ---: | ---: | ---: | ---: | ---: |
| 1M | 2.12 ms | 495 Mkeys/s | 32% | 3.9× faster |
| 2M | 3.12 ms | 673 Mkeys/s | 38% | 4.3× faster |
| 4M | 4.73 ms | 887 Mkeys/s | 45% | 5.0× faster |
| 8M | 7.30 ms | 1.15 Gkeys/s | 62% | 6.5× faster |
| 16M | 13.00 ms | 1.29 Gkeys/s | 74% | 7.3× faster |
| 32M | 23.31 ms | 1.44 Gkeys/s | 83% | 8.3× faster |
| 64M | 43.18 ms | 1.55 Gkeys/s | 90% | 9.0× faster |

## All CPU baselines at 64M keys

| Input (64M keys) | Swift `Array.sort()` | libc `qsort` | `std::sort` | parallel `std::sort` | GPU-Quicksort |
| --- | ---: | ---: | ---: | ---: | ---: |
| uniform | 6,255 ms | 5,322 ms | 1,052 ms | 388 ms | 43.2 ms |
| gaussian | 6,244 ms | 5,340 ms | 1,049 ms | 386 ms | 46.0 ms |
| bucket | 4,681 ms | 4,513 ms | 1,082 ms | 354 ms | 45.0 ms |
| staggered | 4,714 ms | 4,433 ms | 1,157 ms | 222 ms | 45.2 ms |
| zero | 45 ms | 60 ms | 56 ms | 91 ms | 6.8 ms |
| sorted | 45 ms | 164 ms | 44 ms | 109 ms | 43.4 ms |

## Parallel `std::sort`: `par` vs. `par_unseq`

`std::execution::par_unseq` was measured against `par` on the same 18 inputs (6 distributions × 16M/32M/64M, median of 5 runs). The ratio of `par` to `par_unseq` time ranged from 0.987 to 1.019 with no consistent direction, and all outputs matched. In Apple's libc++ both policies run the same parallel sort, so `par_unseq` is not a separate baseline.

| Input (64M keys) | `std::sort` | `par` | `par_unseq` |
| --- | ---: | ---: | ---: |
| uniform | 1,067 ms | 389 ms | 388 ms |
| sorted | 45 ms | 108 ms | 107 ms |
| zero | 58 ms | 93 ms | 92 ms |
| bucket | 1,119 ms | 356 ms | 356 ms |
| gaussian | 1,080 ms | 400 ms | 395 ms |
| staggered | 1,198 ms | 224 ms | 226 ms |

Parallel `std::sort` is only 2.7–5.2× faster than sequential `std::sort` on random inputs with 18 cores, and it is *slower* than sequential on sorted and all-equal input (it does not detect presorted runs).

## What changed in v0.5, and why

1. **The default phase-one pivot is now `minMaxAverage`**, the average of the sequence's minimum and maximum, which is what the paper used in its experiments [P §5.2].
   - With the previous median-of-three default, `staggered` at 64M needed about 47 phase-one iterations and took 367–593 ms, with large run-to-run swings. The median-of-three samples split its interleaved value ranges so unevenly that some very large subsequences reached phase two, where one threadgroup each must sort them.
   - With `minMaxAverage` it needs 14 iterations and takes 45 ms.
   - It was also faster on every other distribution, by 1.08–1.57×.
2. **Parallel `std::sort` is now a benchmark baseline**, `cpu-stdsort-par`. It is the fairest CPU comparison, and it is the fastest CPU baseline on every random input.
3. **Re-tuned** for the new pivot. The fit gives 512-thread threadgroups, a bitonic cut-over size of 2048 keys, and a phase-one sequence budget that grows with $n$ (`maxseq` 256 at 1M keys, 2048 at 16M).

## What the numbers say

1. **Large sorts are GPU-bound; small ones are round-trip-bound.**
   - Phase one runs one command buffer per iteration: the CPU commits it, waits, reads the cursors back, and derives the next subsequences (R-10, D-03).
   - At 64M keys, 90% of the time is GPU execution. At 1M keys only 32% is, and the rest is host round trips. This is why time grows only 6.1× from 1M to 16M keys (finding F-031).
2. **The GPU's lead grows with size.** Against parallel `std::sort` it goes from 3.9× at 1M keys to 9.0× at 64M keys (uniform).
3. **All-equal input is the best case.** One partition pass sends every key to the pivot gap, which finalizes the whole array in place; phase two never runs (K-10, E-24).
4. **Already-sorted input is the only case the CPU can match.** Sequential `std::sort` and Swift's sort run in near-linear time on presorted data. GPU-Quicksort beats them from 64M keys, and beats parallel `std::sort` at every size.

## Size limits

- **Current limit:** $2^{31} - 1$ keys, about 2.1 billion (K-01, set by 32-bit indices).
  - Keys plus the auxiliary buffer need 16 GiB at that size, well within Metal's recommended working set on this machine (115 GB).
  - Estimated time for a maximum-size sort is roughly 2–3 s.
- **With 64-bit indices** (a spec change to K-01, C-05 and C-06): about 12–14 billion keys, limited by the working set, since the key and auxiliary buffers must both fit.

## Next steps

1. **Cut the phase-one round trips.** This matters most for small and medium sizes, up to about 3× at 1M keys.
   - **Derive the children on the GPU.** Add a kernel after `gqsort_fill` that reads the final cursors, writes the next iteration's descriptors and pivots, and chains iterations with indirect dispatch, reading back only at the end of phase one.
   - **Fewer, wider iterations.** Measure whether a larger `maxseq`, or splitting each sequence into more than two parts per pass, lowers the iteration count without hurting phase-two balance.
   - Either change alters R-08/R-10 and D-03, so it goes through a spec proposal first.
2. **Detect presorted input.** A single coalesced pass that detects sorted (or reverse-sorted) input could return early, closing the last gap to sequential `std::sort`. This is a new requirement, so it needs a spec proposal.
3. **Measure effective memory bandwidth.** Divide the bytes moved per partition pass by GPU time at 64M keys, to check the paper's claim that the algorithm is bandwidth-bound [P §5.4] on this hardware.
4. **Re-tune after each change.** Run `swift build -c release && .build/release/gpuqsort tune --write --as-default` on an idle GPU and commit `TunedParameters.json`.
5. **Resolve the open findings.** F-031: measure T-33's scaling from 4M keys, or drop its range. F-032: find a bounded way to produce a real Metal command-buffer error for E-09, never with non-terminating kernels, which can leave the GPU busy until reboot.
6. **Consider 64-bit indices** if sorts beyond 2.1 billion keys are needed.
