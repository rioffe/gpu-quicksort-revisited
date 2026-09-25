# Detailed implementation plan — W3: Phase one

> - **Wave:** W3 of W0–W6 (`IMPLEMENTATION_PLAN.md` §4 item 4).
> - **Spec basis:** `SPEC.md` v0.4 (sha256 `b05ffbd3…63e0`).
> - **Gate:** with default parameters, the full §9.1 suite is green; O-2 is correct and makes progress.
> - **Budget:** 250–400 production lines (edits to `Sorter.swift` and `GPUQuicksort.metal`).
> - **Depends on:** W2 (`Sorter`, `CommandRunner`, `BufferPool`). **Unlocks:** W4, W5.

## 1. Objective and spec obligations

R-03, R-04..R-11, K-06, K-07, K-10, E-04, E-10 (read-back), E-17, E-24, O-2, I-005 and I-007, and T-35 in full (all 5 kernels present).

## 2. Entry preconditions

The W2 gate is green.

## 3. Deliverables

- **MSL `gqsort_partition`** (one threadgroup per `BlockDescriptor`):
  - pass 1 counts, then an in-place scan;
  - thread 0: `lbeg = atomic_fetch_add(lnext, L)` and `gbeg = atomic_fetch_sub(gnext, G) - G`, shared through threadgroup memory and a barrier (R-09);
  - pass 2 scatters from `src` into `1 - src`;
  - O-2 only: per-thread min/max of each side, a SIMD reduction then a threadgroup reduction, then one `atomic_fetch_min`/`atomic_fetch_max` per field.
- **MSL `gqsort_fill`:** one threadgroup per `BlockDescriptor`. Block $j = (\mathit{begin} - \mathit{start}) / \mathit{blocksize}$ of a sequence fills its proportional slice of the gap $[\mathit{lnext}, \mathit{gnext})$ in $D$, read with `atomic_load` (R-06, R-10).
- **`Sorter.phaseOne`:**
  - encode, then compute the root pivot on the CPU (median of three over $D$);
  - the loop per R-08, where $\mathit{minlength} = \lceil n / M \rceil$ and $\mathit{blocksize} = \max(T, \lceil \sum \ell / M \rceil)$ (K-06);
  - partition and fill in one command buffer, then wait;
  - read-back checks: $\mathit{start} \leq \mathit{lnext} \leq \mathit{gnext} \leq \mathit{end}$ (E-10);
  - children in `1 - src`: empty ones dropped (E-17), pivots per strategy (O-2: the root uses median-of-three, D-20);
  - classify each child as `done` if it is shorter than $\mathit{minlength}$, otherwise `work`;
  - the cap per K-07 and F-024: after the iteration, if `iters == max` and the condition still holds, set `capReached`;
  - merge; if `done` is empty, skip phase two (E-24).

## 4. Work items

- **W3-01:** T-08 (`zero`: 1 iteration, no `lqsort` dispatch; the counter hook stub lands in W4, so W3 asserts the report fields), then the loop plus `gqsort_fill`.
- **W3-02:** T-01 and T-02 with defaults, T-03 (the grid including $\mathit{maxseq} \in \{1, 7, 64, 1024\}$ and both pivots), T-10 (cap), T-11 (depth), then `gqsort_partition`.
- **W3-03:** T-41 (O-2: correctness plus a CPU recomputation of each child's pivot through a host-side iteration callback), then the min/max path.
- **W3-04:** T-35 (all 5 kernel names plus the stamp).

## 5. Test plan

| File | Ids |
| ---- | --- |
| `CorrectnessTests.swift` | T-01, T-02, T-03, T-08, T-10, T-11, T-41 |
| `PackagingTests.swift` | T-35 |

## 6. Gate

1. `scripts/build-metallib.sh` → exit 0.
2. `swift test --filter "CorrectnessTests|APITests|OracleTests|PackagingTests"` → exit 0.

## 7. Traceability

R-03..R-11, K-06, K-07, K-10, E-04, E-17, E-24, O-2, I-001..I-005 and T-35 become passing. E-10's fault injection lands in W4.

## 8. Traps

- Reading a child's median-of-three is valid only after `waitUntilCompleted` (shared buffers are CPU-coherent after completion).
- O-2 empty sides still issue their atomics with identity values (T-14 expects exactly 6 atomics).
- $\mathit{blocksize} \geq T$ keeps every block non-empty.

## 9. Exit and handoff

- **Frozen:** `Sorter.phaseOneObserver` (a package-level closure called after each iteration with records and buffers), which W4's hooks and T-13/T-15/T-41 use.
- **Re-run by W4:** gate 2.
