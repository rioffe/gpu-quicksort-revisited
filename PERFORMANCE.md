# GPU-Quicksort on Metal: current performance and next steps

> - **Build:** `gpuqsort` 0.4.0 implementing `SPEC.md` v0.5, release configuration
> - **Machine:** Apple M5 Max (18 CPU cores), macOS 26.6.2, Metal toolchain 32023.921
> - **Source data:** `recorded/bench.csv` (1M–16M keys, 750 rows), `recorded/bench-large.csv` (32M–64M keys, 300 rows), `recorded/tune.json`, `recorded/stdsort-par-unseq.txt`, `recorded/bench-keys.csv` (key types), and `recorded/bench-huge.csv` with `recorded/bench-huge-cpu.csv` (128M–1G keys, `gpuqsort` 0.5.0). Every GPU and CPU result was verified against the CPU reference sort.
> - **Method:** `gpuqsort bench --dist all --n 1M,2M,4M,8M,16M` (and `--n 32M,64M`) `--runs 5 --cpu`, `uint32` keys, tuned defaults from the `Apple M5 Max` entry of `TunedParameters.json`. The phase-one pivot is `minMaxAverage`, the v0.5 default. Every value is the median of 5 timed runs; one warm-up run is discarded, and copying the input is not timed.
> - **CPU baselines:** Swift `Array.sort()`, libc `qsort`, C++ `std::sort`, and parallel C++ `std::sort(std::execution::par, …)`, which is libc++'s parallel algorithms on libdispatch, enabled with `-fexperimental-library`.

## Summary

GPU-Quicksort sorts **64M 32-bit keys in 43 ms (1.55 Gkeys/s)** and 16M keys in 13 ms. On random inputs it is **9× faster than parallel `std::sort`** on all 18 CPU cores, and 24× faster than sequential `std::sort`. The only case where a CPU sort matches it is already-sorted input, where sequential `std::sort` detects the presorted runs. At very large sizes it sorts **1G keys in 0.9 s**, 7–8× faster than parallel `std::sort` on `uniform`, `gaussian` and `bucket` input (see *Very large inputs*).

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

## Key types: `uint32`, `int32`, `float32`

`int32` and `float32` keys are converted to order-preserving `uint32` codes before the sort and converted back afterwards (C-04, R-17). The kernels only ever sort codes. Measured with `gpuqsort bench --dist uniform,gaussian,staggered --n 16M,64M --key uint32,int32,float32 --runs 5` (release build, median of 5 runs, all verified; `recorded/bench-keys.csv`):

| Input | `uint32` | `int32` | `float32` | Phase-one iterations (u / i / f) |
| --- | ---: | ---: | ---: | ---: |
| uniform 16M | 13.0 ms | 14.1 ms (+8%) | 15.4 ms (+18%) | 12 / 12 / 14 |
| uniform 64M | 43.2 ms | 45.6 ms (+6%) | 49.8 ms (+15%) | 13 / 13 / 17 |
| gaussian 16M | 13.8 ms | 14.4 ms (+5%) | 14.6 ms (+6%) | 13 / 13 / 13 |
| gaussian 64M | 46.1 ms | 48.0 ms (+4%) | 51.8 ms (+12%) | 15 / 15 / 17 |
| staggered 16M | 13.3 ms | 14.3 ms (+8%) | 14.8 ms (+11%) | 12 / 12 / 14 |
| staggered 64M | 44.9 ms | 47.4 ms (+5%) | 49.3 ms (+10%) | 14 / 14 / 16 |

- **`int32` is about 5–8% slower, all of it key conversion.** Its sort does exactly the same work as `uint32`, with the same number of iterations. The extra cost is two passes over the whole array, `key_encode` before and `key_decode` after, each with its own command buffer and CPU–GPU round trip. That is about 1 ms at 16M keys and about 2.5 ms at 64M. The cost is fixed per key and does not depend on the data.
- **`float32` is about 6–18% slower: the same conversion cost, plus up to 4 extra phase-one iterations** (none on `gaussian` 16M, which is why that case costs only 6%). The extra iterations come from the `minMaxAverage` pivot, which averages the smallest and largest **code**. A float's code is essentially its bit pattern, which grows roughly with the logarithm of the value: every exponent range (a factor of 2 in value) gets the same share of code space. So the midpoint of the codes is not the midpoint of the values. With the benchmark's inputs (values spread over $[0, 2^{31})$), most keys sit in the top few exponent ranges, and the code midpoint splits off too small a slice, so each pass makes less progress.

### Improving `float32` performance

1. **Compute the `minMaxAverage` pivot in value space for `float32`.** This is the fix for the extra iterations.
   - Decode the sequence's code minimum and maximum back to floats, $\mathit{lo}$ and $\mathit{hi}$, and take $p = \mathit{lo} + (\mathit{hi} - \mathit{lo})/2$ in floating point. Encode $p$ back to a code.
   - Use the code of $\mathit{lo}$ whenever the result is not strictly below the code of $\mathit{hi}$, which preserves O-2's guarantee that every child is strictly shorter than its parent.
   - Special values need rules: when $\mathit{lo}$ or $\mathit{hi}$ is $\pm\infty$ or NaN, or $\mathit{hi} - \mathit{lo}$ overflows, fall back to the code midpoint.
   - The change is host-side in `Sorter.phaseOne` (child pivots) plus the root pivot. The phase-one kernel is unchanged, because it already records each side's minimum and maximum code.
   - It changes O-2 and T-41, whose pivot formula is currently defined on codes, so it needs a spec change (v0.6) first.
   - Expected result: `float32` gets the same iteration counts as `uint32`, which recovers most of the 5–10% beyond the conversion cost.
2. **Fold the key conversion into the sort, to remove the fixed ≈ 5% for both `int32` and `float32`.**
   - Encode while the first phase-one pass reads the input, and decode where final values are written to $D$ (the gap fills and the phase-two alternative sort's write-back).
   - This removes two full passes over memory and two command-buffer round trips.
   - It changes R-17 (conversion as separate passes) and every kernel's write path, so it needs a spec change and a careful re-check of I-008 (each index finalized exactly once).
   - A cheaper intermediate step is to put the encode pass in the same command buffer as the first phase-one iteration, and the decode pass in the phase-two command buffer. That removes the two round trips but keeps the two memory passes.
3. **Re-check the tuning per key type.** The tuned constants were fitted on `uint32`. After the value-space pivot they should suit all three key types; confirm with `gpuqsort tune --key float32`.

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

## Very large inputs: 128M to 1G keys

Measured with `scripts/bench-large.sh` (`gpuqsort` 0.5.0, release build): `gpuqsort bench --dist all --n 128M,256M,512M,1024M --runs 5` for the GPU, and `scripts/stdsort-par-bench.cpp` for parallel `std::sort`. At these sizes the sequential CPU baselines take minutes per run, so only parallel `std::sort` is compared. The harness uses the same compiler flags as the `CPUBaselines` target, sorts the same inputs (written by `gpuqsort gen`), and follows the same timing rule: the input restore is not timed, one warm-up run is discarded, and every run is checked against a sequential `std::sort`. The two halves ran one after the other. Every value is the median of 5 runs, and every run on both sides verified.

| Input | 128M | 256M | 512M | 1G | Speed-up over parallel `std::sort` (128M → 1G) |
| --- | ---: | ---: | ---: | ---: | ---: |
| uniform | 92.8 ms | 179.5 ms | 366.6 ms | 901.8 ms | 8.6× → 8.9× → 8.9× → 7.6× |
| gaussian | 95.6 ms | 188.5 ms | 371.6 ms | 932.4 ms | 8.5× → 8.7× → 9.0× → 7.4× |
| bucket | 97.2 ms | 188.7 ms | 372.7 ms | 890.5 ms | 7.8× → 7.9× → 8.2× → 7.1× |
| staggered | 92.9 ms | 188.8 ms | 372.0 ms | 866.7 ms | 5.0× → 4.9× → 5.2× → 4.8× |
| zero | 7.5 ms | 9.6 ms | 20.1 ms | 25.2 ms | 25× → 40× → 39× → 71× |
| sorted | 91.8 ms | 178.6 ms | 357.8 ms | 815.9 ms | 2.3× → 2.5× → 2.6× → 2.4× |

Parallel `std::sort` on the same inputs:

| Input | 128M | 256M | 512M | 1G | Throughput |
| --- | ---: | ---: | ---: | ---: | ---: |
| uniform | 794 ms | 1,595 ms | 3,275 ms | 6,865 ms | 0.16–0.17 Gkeys/s |
| gaussian | 811 ms | 1,636 ms | 3,351 ms | 6,924 ms | 0.16–0.17 Gkeys/s |
| bucket | 757 ms | 1,493 ms | 3,054 ms | 6,350 ms | 0.17–0.18 Gkeys/s |
| staggered | 462 ms | 927 ms | 1,916 ms | 4,134 ms | 0.26–0.29 Gkeys/s |
| zero | 190 ms | 380 ms | 784 ms | 1,797 ms | 0.60–0.71 Gkeys/s |
| sorted | 210 ms | 444 ms | 941 ms | 1,968 ms | 0.55–0.64 Gkeys/s |

- **Up to 512M keys, GPU time is linear in $n$.** Throughput stays at 1.38–1.50 Gkeys/s on every input except `zero`, about the same as at 64M.
- **At 1G keys, GPU throughput drops by about 20%** with the default parameters, to 1.15–1.32 Gkeys/s, so the lead over parallel `std::sort` shrinks from about 9× to about 7.5×. The cause is phase one, not phase two; see *What limits throughput at 1G keys* below.
- **`staggered` is where parallel `std::sort` does best** on random inputs (0.28 Gkeys/s against 0.16 on `uniform`), so the GPU's lead there is about 5×. The GPU itself is equally fast on every random distribution.
- **All-equal input** takes one partition pass and no phase two at every size: 1G keys in 25 ms, about 43 Gkeys/s. Runs this short vary more (at 128M the median is 7.5 ms and the minimum 4.5 ms).
- **Phase one** takes 14–18 iterations at these sizes, against 13–15 at 64M.

### What limits throughput at 1G keys

Measured with `gpuqsort --verbose bench --dist uniform --runs 3` and explicit parameters (`recorded/bench-1g-params.csv`). Phase one is the sum of the per-iteration diagnostic times; the rest is phase two plus host work (there is no key conversion for `uint32`). Medians of 3 runs, all verified.

| n | T | maxseq | minseq | Keys per thread in phase one | Total | Phase one | Rest |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 512M | 512 | 65,536 (default) | 4,096 | 16 | 366 ms | 225 ms | 141 ms |
| 512M | 512 | 32,768 | 4,096 | 32 | 432 ms | 287 ms | 145 ms |
| 1G | 512 (default) | 65,536 | 4,096 | 32 | 904 ms | 611 ms | 293 ms |
| 1G | 1024 | 65,536 | 4,096 | 16 | **812 ms** | **440 ms** | 373 ms |
| 1G | 256 | 65,536 | 4,096 | 64 | 981 ms | 710 ms | 272 ms |
| 1G | 512 | 32,768 | 4,096 | 64 | 993 ms | 687 ms | 306 ms |
| 1G | 512 | 65,536 | 2,048 | 32 | 906 ms | 616 ms | 290 ms |
| 1G | 512 | 65,536 | 1,024 | 32 | 926 ms | 611 ms | 315 ms |

"Keys per thread" is the phase-one block size divided by $T$: $\max(T, \lceil n/\text{maxseq} \rceil) / T$ in the first iteration, and about the same in later ones.

- **Phase two scales linearly.** From 512M to 1G with the default parameters, the rest grows from 141 to 293 ms (2.1×). Longer phase-two sequences cost little (`maxseq` 32,768 at 512M: 141 → 145 ms), and a smaller `minseq` does not help.
- **Phase one does not.** It grows from 225 to 611 ms (2.7×) for twice the keys, with the same number of iterations.
- **Phase one's cost per key follows the keys per thread.** Because `maxseq` is capped at 65,536, the block size grows with $n$: 8,192 keys at 512M, 16,384 at 1G, so each of the $T = 512$ threads handles 32 keys instead of 16. Every configuration above fits this, measured as phase-one time per key per iteration: 16 keys per thread costs 25–26 ps, 32 costs 34–36 ps, and 64 costs 41–43 ps, at both sizes. At 1G, $T = 1024$ brings the keys per thread back to 16, and phase one back to linear (440 ms, 2.0× the 512M time). A likely reason is the scatter: each thread writes its keys to consecutive output positions, so the more keys per thread, the further apart the addresses that neighboring threads write at the same time.
- **$T = 1024$ is the fastest setting found at 1G** (812 ms, 1.32 Gkeys/s, 11% faster than the default), but it slows phase two (293 → 373 ms), because every kernel shares one $T$.
- **`minseq` cannot go above 4,096 for any $T$.** Phase two's threadgroup memory is $(\max(2T, \text{minseq}) + 104) \cdot 4$ bytes (K-03), and this GPU allows 32 KiB per threadgroup.

Two changes could keep phase one linear beyond 512M. Both change K-04 or K-06, so they need a spec proposal first:
1. **Cap the phase-one block size at a fixed number of keys per thread**, for example $16T$, and launch more blocks per sequence once `maxseq` is at its cap. This decouples the number of phase-one threadgroups from `maxseq`.
2. **Allow a separate $T$ for phase one and phase two.** With $T = 1024$ in phase one and $T = 512$ in phase two, the measurements above suggest about 440 + 293 ≈ 730 ms at 1G keys, about 1.47 Gkeys/s, matching the throughput at smaller sizes. This is an estimate, not a measurement.

## Size limits

- **Current limit:** $2^{31} - 1$ keys, about 2.1 billion (K-01, set by 32-bit indices).
  - Keys plus the auxiliary buffer need 16 GiB at that size, well within Metal's recommended working set on this machine (115 GB).
  - Measured: 1G keys ($2^{30}$) take 0.82–0.93 s (see *Very large inputs*). A maximum-size sort should take about 2 s, or more if the capped parameters keep lowering throughput.
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
6. **Keep phase one linear beyond 512M keys.** Cap the phase-one block size at a fixed number of keys per thread, or allow a separate $T$ per phase (see *What limits throughput at 1G keys*). Refit the tuning constants beyond 16M keys: at 1G, $T = 1024$ is already 11% faster than the fitted default of 512.
7. **Consider 64-bit indices** if sorts beyond 2.1 billion keys are needed.
8. **Close the `float32` gap:** compute the min/max pivot in value space for floats, and fold the key conversion into the sort (see *Improving `float32` performance*).
