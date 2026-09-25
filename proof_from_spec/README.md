# GPU-Quicksort for Metal — spec model

A Lean 4 formalization of what [`SPEC.md`](../SPEC.md) v0.5 *says*: its normative tables as pure, total functions, with the spec's own claims about itself kernel-checked for all inputs.

> **This certifies the spec, not the implementation.** An implementation exists in `../Sources`, and its evidence is the §9 test suite (56 tests, green) and the speccheck gate. Neither is linked into this Lean project. Linking the implementation to this model would be a separate `spec-proof` project that refines this one.

## Layout

- `GpuQuicksortSpec/GpuQuicksort/Spec.lean` — the **spec side**: the pinned constants (the sign mask of the key codes, the 2^31 − 1 key cap, the 32-entry stack, the K-03/K-04 bounds, the §7.1 byte terms, the C-08 p and w, the six §7.2 exit codes), plus five facts about how the separately pinned values relate.
- `GpuQuicksortSpec/GpuQuicksort/Model.lean` — the **model**. It contains:
  - the C-04 codes on `BitVec 32`, and IEEE 754 `totalOrder` defined independently;
  - the partition and the sort as list functions, with the pivot rule as a parameter;
  - the phase-one host loop over sequence lengths;
  - the §7.2 exit map;
  - the §3.1 transition table (one row per table line, guards as written);
  - the C-08 formulas, `optp` and clamping.

  The correspondence table at the top of the file (spec anchor → model element) is the manual trust boundary.
- `GpuQuicksortSpec/GpuQuicksort/Theorems.lean` — **the proof**. It contains:
  - 50 theorems in five sections (codes, sort model, phase one, tables, rows), plus the finding witness;
  - the deferral table mapping every id out of Lean's reach to the §9 tests that carry it;
  - the excluded table.

## Commands

    lake build            # checks every proof (Lean v4.34.1, pinned in lean-toolchain; no external packages)

## What "proven" means here

Lean proves the **model**. It cannot read a document, and it does not read the implementation either. The bridge has three legs, and this project builds only the middle one:

| Leg | Claim | Evidence |
| --- | ----- | -------- |
| A. Transcription | the model faithfully transcribes the spec's tables | **manual**: the correspondence table in `Model.lean` |
| B. Lean (this project) | the model satisfies the claims the spec makes about itself, for all inputs | `lake build`, kernel-checked; `bv_decide` and `native_decide` also trust Lean's compiled evaluator for the codec and `optp` checks |
| C. The system | the implementation behaves as specified | **not established here**: the §9 suite and speccheck carry it, outside Lean |

**What is proven** (46 of the spec's 88 ids, each tagged in bold on exactly one declaration):
- **The key codes (C-04):** they are bijections for every key type. Unsigned order of codes equals signed `int32` order and IEEE `totalOrder` for every pair of 32-bit patterns.
- **The sort model:**
  - the partition is a permutation, and the gap holds exactly the pivot-equal elements;
  - the sort returns a sorted permutation for every pivot rule, and its output is the same for every parameter choice;
  - the alternative sort's padding trick is correct;
  - both pivot rules make progress, and the min/max pivot halves the code range at every level.
- **Phase one:**
  - the loop never holds 2M or more sequences, and each iteration dispatches fewer than 2M threadgroups, so the §7.1 buffers cannot overflow;
  - the iteration cap works as K-07 states;
  - all-equal input takes exactly one iteration and hands nothing to phase two;
  - empty children are never kept.
- **The tables:**
  - the exit map is closed over {0..5}, every code is reached, and only success maps to 0;
  - the lifecycle table has no silent case, and invalid inputs never reach GPU work.
- **The numbers:**
  - the generator formulas stay in [0, 2^31);
  - `optp` reproduces the spec's worked examples;
  - clamping keeps defaults valid, and the K-03 memory budget holds;
  - 32-bit index arithmetic cannot overflow, and the stack depth stays at most 27 of 32 entries.

**What is not proven here:** GPU memory ordering (R-28, I-007), index-level placement (I-008), threads, dispatches, timing, the API, the CLI surfaces and the packaging. These 41 ids, plus the "process side" of the proven ones, are listed in the deferral table in `Theorems.lean`, each with the §9 tests that carry it.

## Findings

One spec-precision gap, with a kernel-checked witness; see [`../docs/reviews/SPEC_MODEL_FINDINGS.md`](../docs/reviews/SPEC_MODEL_FINDINGS.md).

- **F-034 (G-2, P2):** the §3.1 transition table's rows overlap and no precedence is stated. For example, n = 0 with invalid inputs matches both "invalid → Failed" and "n ≤ 1 → Done" (`Theorems.overlap`).

There is no silent case (the lifecycle table covers every non-terminal state: `noSilence`), and no requirement that lacks both a proof and a test.
