import GpuQuicksortProof.GpuQuicksort.Theorems.Sorter

/-!
# GpuQuicksortProof.GpuQuicksort.Deferral
=========================================

**What this project proves** (kernel-checked, for all inputs of the transcribed code; each id is
tagged in bold on exactly one declaration in `Theorems/`):

- *Codec* (`Codec.lean`): the Swift and MSL codes are the spec's C-04 codes on all 2^32 patterns;
  the grid-stride dispatch maps the buffer pointwise; decode after encode is the identity.
- *Host decisions* (`Host.lean`): the exit map is §7.2 on every C-07 case; `resolve` returns only
  K-04/K-03-valid parameters, clamps exactly the defaults, throws on explicit invalid values; `sort`
  reaches the GPU exactly on fully valid input.
- *Kernels*: `scan2` is an exclusive prefix sum (`Scan.lean`); the threadgroup partition is the
  one-block parallel partition (`TGPartition.lean`); `altsort` is the bitonic network and sorts
  (`AltSort.lean`); `lqsort` refines the spec model's stack machine and sorts its sequence, never
  overflowing its stack (`LQSort.lean`); one `gqsort_partition` dispatch is the parallel partition
  for every atomic order, with the O-2 minima and maxima, and `gqsort_fill` writes each gap once
  (`GQSort.lean`).
- *Host orchestration* (`Sorter.lean`): the block layout; the phase-one loop keeps the spec
  model's invariant for every atomic order; phase two finalizes every sequence; `run` leaves the
  keys sorted in the C-04 order, a permutation of the input, every index finalized exactly once,
  the same result for every parameter choice and every atomic order.

**What this project does not prove**, and why:

- the Metal memory model: barriers and atomics are assumed to behave as R-28 and I-007 require
  (a barrier separates phases; atomics on one location are linearizable); `simd_min`/`simd_max`
  are assumed to reduce over the simdgroup; phase two's threadgroups are modeled one after another
  (each touches only its own sequence, which is proved per threadgroup);
- 32-bit wrap-around: the kernels' `uint` arithmetic is modeled in `Nat`; K-01 (no index
  overflow for n ≤ 2^31 − 1) is carried by its tests;
- `optp`'s Double exponent (an input to the resolver model), the report fields, diagnostics,
  timing, the API and CLI surfaces, the generators, tuning, packaging and the platform.

**Trust boundary.** Leg 1 (each model transcribes its source file) is the correspondence tables at
the top of every `Model/*.lean`, manual. Leg 2 (this project) is `lake build`, kernel-checked;
`bv_decide` additionally trusts Lean's compiled checker for the codec's 2^32-pattern checks.
Leg 3 (the binaries on a real GPU) is the §9 suite (56 tests) and the speccheck gate.

## Deferral table — spec ids carried by the §9 tests

"(process side)" marks an id whose code model is proven above but whose runtime half is not.

| Spec id | Content | Carried by |
| ------- | ------- | ---------- |
| R-09 (process side) | the atomics are linearizable relaxed RMWs on the GPU | T-14 |
| R-12 (process side) | one `lqsort` threadgroup dispatched per sequence, running independently | T-02, T-07 |
| O-2 (process side) | `simd_min`/`simd_max` reduce over the simdgroup | T-14, T-41 |
| R-18 | the public API and its error cases | T-18, T-19, T-24 |
| R-19 | the CLI subcommands | T-27, T-28 |
| R-20 | the generators' exact bytes (MT19937) | T-25, T-26 |
| R-21 | `SortReport` assembly | T-21 |
| R-22 | diagnostics lines and verbosity | T-28, T-29 |
| R-23 | `bench` times only the sort | T-28 |
| R-24 | `tune` | T-34, T-38 |
| R-25 | the shipped tuning table | T-34, T-37 |
| R-26 | CPU baselines | T-28, T-39 |
| R-27 | precompiled `.metallib` | T-35, T-36 |
| R-28 | barrier placement (memory ordering) | T-17, T-01 |
| I-005 | disjointness and progress of live sequences | T-09, T-13, T-41 |
| I-007 | ordering only through atomics, barriers, dispatch boundaries | T-17, T-01 |
| K-01 | 32-bit index arithmetic, maxKeys | T-19, T-30 |
| K-02 | platform (macOS 15, Apple7) | T-30 |
| K-05 | `optp`'s concrete defaults (Double arithmetic) | T-20 |
| K-09 | auxiliary and bookkeeping bytes | T-21 |
| K-10 | complexity on all-equal input | T-08 |
| K-11 | timing | T-21, T-28 |
| K-13 | recorded performance | T-32 |
| K-14 | `tune` duration | T-34 |
| E-04 | duplicates terminate | T-08, T-09 |
| E-09 | command buffer error | T-42 |
| E-12 | allocation failure | T-24 |
| E-15 | CLI input size errors | T-27 |
| E-16 | concurrent calls serialized | T-22 |
| E-18 | missing or broken metallib | T-35 |
| E-19 | stale metallib | T-35 |
| E-20 | invalid tuning table | T-37 |
| E-21 | unknown device | T-37 |
| E-22 | tune verification failure | T-38 |
| E-23 | tune table write failure | T-38 |
| E-25 | invalid table under `tune --write` | T-38 |
| C-01 | `GPUQuicksort`, `TuningSource` | T-20, T-22, T-23, T-29, T-37 |
| C-02 | `SortReport` | T-21 |
| C-03 | `Parameters`, `DeviceLimits` | T-20, T-30 |
| C-05 | `SequenceRecord`, `BlockDescriptor` layouts | T-13, T-31 |
| C-06 | `SortSequence`, `SortStats` layouts | T-11, T-31 |
| C-08 | generator formulas and bytes | T-25, T-26 |
| C-09 | packaging, shader library | T-35, T-36 |
| C-10 | tuning table format | T-20, T-37, T-38 |
| C-11 | `CPUBaselines` target | T-39 |

## Excluded by the spec

| Spec id | Reason |
| ------- | ------ |
| O-1 | retired in v0.2 (`tune` became R-24) |
-/
