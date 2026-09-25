# GPU-Quicksort for Metal — implementation proof

A Lean 4 transcription of the Swift + Metal implementation in [`../Sources`](../Sources), proved against [`SPEC.md`](../SPEC.md) v0.5. Each theorem states that a transcribed source file **equals or refines** an element of the spec's own model in [`../proof_from_spec`](../proof_from_spec), so the spec model's theorems carry over to the code.

> **Lean proves the transcription, not the file.** Lean cannot read Swift or MSL. The correspondence tables at the top of each `Model/*.lean` file map every source line to its model element (or say why it is not modeled). That table is the manual trust boundary. The real binaries on a real GPU are verified by the §9 test suite (56 tests) and the speccheck gate.

## Status

Built in four steps; this README tracks what exists.

| Step | Source | Status |
| ---- | ------ | ------ |
| 1 | codec (`KeyCodec.swift`, `key_encode`/`key_decode`, `Sorter.codec`), exit map, `ParameterResolver`, validation in `sort` | **proven** |
| 2 | `scan2`, the threadgroup partition, `altsort`, `lqsort` | **proven** |
| 3 | `gqsort_partition`, `scan2`, `gqsort_fill` | planned |
| 4 | the phase-one host loop and the whole-sort composition | planned |

## Layout

- `GpuQuicksortProof/GpuQuicksort/Spec.lean` — the normative side: the spec model, imported.
- `GpuQuicksortProof/GpuQuicksort/Model/Codec.lean`, `Theorems/Codec.lean` — the codec. The Swift and MSL codes equal the spec's C-04 codes on all 2^32 patterns. The host dispatch's grid-stride loop visits every index below n exactly once, so the pass maps the buffer pointwise (C-04), and decode after encode restores it bit for bit (E-14, E-11).
- `GpuQuicksortProof/GpuQuicksort/Model/Host.lean`, `Theorems/Host.lean` — the host decisions:
  - the CLI exit map is §7.2 on every C-07 case (C-07, K-12);
  - `resolve` returns only K-04-valid parameters within the K-03 budget, on any device that admits T = 32 (K-04, K-03);
  - defaults are the `optp` values clamped exactly as the spec model's `clampPow2` (R-16);
  - explicit values are never clamped, and an explicit invalid value throws (E-05);
  - `sort` reaches the GPU exactly when every check passes (I-006, E-06..E-08), and returns early for n ≤ 1 whatever the buffer (E-01, E-02).

- `Model/Scan.lean`, `Theorems/Scan.lean` — `scan2` is an exclusive prefix sum for every T = 2^m, and no thread of a level reads or writes a slot another thread writes (R-28(a) for the scan).
- `Model/LQSort.lean` — the transcription of `lqsort`, `altsort` and the partition they share.
- `Theorems/TGPartition.lean` — the threadgroup partition (pass 1, `scan2`, pass 2, gap fill) is the spec model's one-block parallel partition.
- `Theorems/AltSort.lean` — each kernel round of `altsort` is the spec model's comparator round, so `altsort` writes its sequence sorted, each index once (R-15).
- `Theorems/LQSort.lean` — each `lqsort` iteration is the spec model's `PhaseTwo.step2` on the popped segment in thread-major order, with the kernel's median-of-three pivot. So `lqsort` sorts its sequence into D, finalizes every index exactly once, changes nothing outside it, and never overflows its stack (R-13, R-14, K-08, E-10).

## What is assumed

- `optp`'s exponent `Int(floor(log2(max(x, 1)) + 0.5))` is computed in Doubles; the model takes it as an input, and every theorem holds for any value of it. The concrete defaults are checked by T-20.
- A kernel dispatch is modeled as its threads run one after another. For `key_encode` this is exact, because the threads touch disjoint indices (proven). For the sorting kernels (steps 2–4), it relies on the barriers and atomics behaving as R-28 and I-007 require.

## Commands

    lake build            # Lean v4.34.1; depends only on ../proof_from_spec (a path dependency)
