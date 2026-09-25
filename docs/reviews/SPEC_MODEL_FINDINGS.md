# Spec model findings — `SPEC.md` v0.5

> - **Source:** `proof_from_spec/` (Lean 4.34.1), the spec's own formal model (spec-model).
> - **Scope:** 88 spec ids: 50 proven (kernel-checked), 37 deferred to named §9 tests, 1 excluded (O-1, retired).
> - **Numbering:** continues the project's review sequence. F-001..F-030 are in `SPEC_REVIEW_REPORT.md` (rounds 1 and 2); F-031..F-033 are in `SPEC_BUILD_REPORT.md`.
> - **Rule:** findings are reported, not fixed. `SPEC.md` was not edited to make any proof close.

## Summary

| Class | Count | Ids |
| ----- | ----: | --- |
| G-1 · silent case | 0 | — |
| G-2 · over-strong or under-stated pin | 1 | F-034 |
| G-3a · requirement with neither proof nor test | 0 | — |

- **No silent case.** The §3.1 lifecycle table has at least one applicable row for every non-terminal state under every combination of facts (`noSilence`). The other transcribed tables (the §7.2 exit map, the C-04 codes, the C-08 formulas) are total functions over their whole input space.
- **No unwitnessed requirement.** Every one of the 37 deferred ids, and every "process side" half of a proven id, names the §9 tests that carry it.

## F-034 — the §3.1 transition table's rows overlap, and no precedence is stated

- **Class:** G-2 (the table admits two outcomes for the same input).
- **Severity:** P2. The implementation follows the natural reading (failures first, then the size checks), so no behavior is wrong today. But the spec does not pin that reading, and a second implementation could legitimately choose the other.
- **Spec anchor:** §3.1 transition table; E-01, E-02, E-09, E-12 (which read those rows).
- **Witness:** `Theorems.overlap` (kernel-checked, `decide`).

**Argument.** `Model.rows` transcribes each line of the §3.1 table with its guard exactly as written. For these three concrete inputs, two rows apply at once and lead to different states:

| Input | Rows that apply | Resulting states |
| ----- | --------------- | ---------------- |
| n = 0, inputs invalid | "parameters or buffer invalid → Failed" and "n ≤ 1 → Done" | `failed`, `done` |
| n = 4096, inputs valid, allocation fails | "valid, n ≥ 2 → Encoding" and "allocation of A or a descriptor buffer fails → Failed" | `encoding`, `failed` |
| encoding, n ≥ minseq, a GPU error | "otherwise → PhaseOne" and "any GPU state, command buffer .error → Failed" | `phaseOne`, `failed` |

The first case is the observable one. E-01 says $n = 0$ "returns immediately … The buffer MAY be any length", while the validation row says invalid parameters or buffers fail. The spec does not say which applies to `sort(privateBuffer, count: 0, …)` or to $n = 0$ with an explicit invalid parameter. The implementation resolves parameters first (so invalid parameters throw even for $n = 0$), then returns early for $n \leq 1$ before checking the buffer (so a private buffer with $n = 0$ succeeds). That mixed order is a reasonable choice, but it is not written anywhere.

**Proposed resolution** (for `spec-proposal` / `spec-writing` to decide; not applied):
- give the §3.1 table an explicit precedence, e.g. "rows are tried top to bottom; the first whose guard holds applies", and order the rows as the implementation behaves;
- or make the guards mutually exclusive: row 2 becomes "inputs valid and n ≤ 1", row 3 "inputs valid, n ≥ 2 and allocation succeeded", and the GPU-state rows add "and no command-buffer error";
- and state in E-01/E-02 which validation, if any, happens for $n \leq 1$ (parameters: yes; buffer mode and length: no), with a T-row that pins it.

## Observations (not findings)

- **K-08, checked at the spec's strength.** A first draft proved the stack-depth arithmetic only to 28. The statement audit caught the gap, and the model now proves the spec's own bound: $\lceil \log_2(\ell / \mathit{minseq}) \rceil + 2 \leq 27$ for $\ell \leq 2^{31} - 1$ and $\mathit{minseq} \geq 64$ (`stackArithmetic`). The spec was right; only the proof was weak.
- **D-07 is confirmed.** With the paper's condition $i \leq \lfloor p/2 \rfloor$, block 64 of the staggered distribution yields values of $2^{31}$ or more (`paperStaggeredOverflows`). The spec's 0-based $i < p/2$ reading keeps every value in $[0, 2^{31})$ (`distRange`).
- **The Appendix A.7 bound holds.** Under the min/max pivot, each child spans at most half the parent's code range (`minMaxHalvesRange`), and a range below $2^{32}$ that halves at every level is 0 after 32 levels (`halvingChain`).
- **K-08 holds for the stack machine itself, not only as arithmetic.** The shorter-first rule keeps the phase-two stack at ⌊log₂(ℓ/S)⌋ + 1 entries or fewer in every reachable state, for every pivot sequence (`PhaseTwo.phaseTwoDepth`). That is one entry tighter than the spec's ⌈log₂(ℓ/S)⌉ + 2, which counts depth with the initial push as 1 (C-02); the spec's bound is safe.
- **R-05 is a performance requirement only.** The parallel partition is correct for every assignment of elements to threads and threadgroups and for every order of the atomics (`ParallelPartition.parallelPartition`). The stride-T pattern R-05 pins affects coalescing, not the result.
- **Correctness never depends on pivot quality.** The list model of the sort is proved sorted and a permutation for *every* pivot rule and threshold (`qsortCorrect`), and its output is the same for all of them (`qsortDeterministic`). Pivot quality affects only running time, as E-13 says.
