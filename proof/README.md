# GPU-Quicksort for Metal — implementation proof

A Lean 4 transcription of the Swift + Metal implementation in [`../Sources`](../Sources), proved against [`SPEC.md`](../SPEC.md) v0.5. Each theorem states that a transcribed source file **equals or refines** an element of the spec's own model in [`../proof_from_spec`](../proof_from_spec), so the spec model's theorems carry over to the code.

> **Lean proves the transcription, not the file.** Lean cannot read Swift or MSL. The correspondence tables at the top of each `Model/*.lean` map every source line to its model element, or say why it is not modeled; that is the manual trust boundary. The real binaries on a real GPU are verified by the §9 test suite (56 tests) and the speccheck gate.

## The headline result

`Theorems/Sorter.lean`, `sortRunSpec`, is `Sorter.run` as the code runs it: encode, the phase-one host loop over the `gqsort_partition` and `gqsort_fill` dispatches, phase two's `lqsort` threadgroups, decode. It holds for:
- 2 ≤ n ≤ 2^31 − 1 keys of any key type;
- T = 2^k threads, minseq ≥ 64, any maxseq, any iteration cap and either pivot strategy;
- **every** order in which the GPU's atomics take effect, in every iteration.

Under those conditions:
- `run` never reports an internal invariant violation;
- key i ends as the i-th smallest C-04 code, decoded. That is the keys sorted in C-04 order (IEEE `totalOrder` for floats) and a permutation of the input;
- nothing past the n keys changes;
- every index is finalized exactly once;
- the result is the same for every parameter choice and every atomic order.

## Layout

- `Spec.lean` imports the spec model (a path dependency on `../proof_from_spec`).
- `Model/` holds the transcriptions:
  - `Codec` (`KeyCodec.swift`, `key_encode`/`key_decode`, `Sorter.codec`);
  - `Host` (the exit map, `ParameterResolver`, the guards of `sort`);
  - `Scan` (`scan2`);
  - `LQSort` (`lqsort`, `altsort`, the threadgroup partition);
  - `GQSort` (`gqsort_partition`, `gqsort_fill`, one dispatch);
  - `Sorter` (`run`, `phaseOne`, `phaseTwo`).
- `Theorems/` holds the proofs, one file per model, plus `TGPartition` and `AltSort`.
- `Deferral.lean` lists what is proven, what is not, the trust boundary, and the table of spec ids carried by tests.

**Coverage:** 45 of the spec's 88 ids are proven against the code, each tagged in bold on exactly one theorem. 42 are carried by named §9 tests (listed in `Deferral.lean`). 1 is excluded (O-1, retired).

## What is proven

- **Codec:**
  - the Swift and MSL codes equal C-04 on all 2^32 patterns;
  - the grid-stride dispatch maps the buffer pointwise;
  - decode after encode is the identity (C-04, E-14, E-11).
- **Host decisions:**
  - the CLI exit map is §7.2 on every C-07 case (C-07, K-12);
  - `resolve` returns only K-04/K-03-valid parameters (K-04, K-03), clamps defaults as the spec model's `clampPow2` (R-16), and never clamps an explicit value, throwing on an invalid one (E-05);
  - `sort` reaches the GPU exactly on fully valid input (I-006, E-06..E-08), and returns early for n ≤ 1 (E-01, E-02).
- **Kernels:**
  - `scan2` is an exclusive prefix sum, race-free per level;
  - the threadgroup partition is the spec model's one-block parallel partition;
  - `altsort` is the bitonic network and sorts (R-15);
  - `lqsort` refines the spec model's stack machine: it sorts its sequence, finalizes every index once, and never overflows its 32-entry stack (R-13, R-14, K-08, E-10);
  - one `gqsort_partition` dispatch is the parallel partition for every atomic order (R-04, R-05, R-07, R-09), and its atomic min/max reductions are right (O-2);
  - `gqsort_fill` writes each gap exactly once (R-06, R-10, I-004).
- **Host loop:**
  - the block layout (K-06) and pivots (R-11);
  - the iteration cap (K-07);
  - the loop invariant, including that empty children are dropped (R-08, E-17);
  - the whole sort (R-01, R-02, R-03, R-12, R-17, I-001, I-002, I-003, I-008, E-03, E-13, E-24).

## What is assumed

- **The Metal memory model** (R-28, I-007):
  - a barrier separates phases;
  - atomics on one location are linearizable, and the theorems quantify over every modification order;
  - `simd_min`/`simd_max` reduce over the simdgroup;
  - phase two's threadgroups each touch only their own sequence (proved per threadgroup) and are modeled one after another.
- **32-bit wrap-around:** the kernels' `uint` arithmetic is modeled in `Nat`. K-01 (no overflow for n ≤ 2^31 − 1) is carried by its tests.
- **`optp`:** its exponent `Int(floor(log2(max(x, 1)) + 0.5))` is computed in Doubles. The model takes it as an input, and every resolver theorem holds for any value; T-20 checks the concrete defaults.
- **`bv_decide`:** the codec's 2^32-pattern checks additionally trust Lean's compiled `bv_decide` checker.

## Commands

    lake build            # Lean v4.34.1; builds ../proof_from_spec too; ~100 s from scratch; 0 warnings
