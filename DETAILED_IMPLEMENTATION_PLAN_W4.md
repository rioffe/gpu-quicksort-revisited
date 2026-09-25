# Detailed implementation plan — W4: Instrumentation, reports, diagnostics

> - **Wave:** W4 of W0–W6 (`IMPLEMENTATION_PLAN.md` §4 item 5).
> - **Spec basis:** `SPEC.md` v0.4 (sha256 `b05ffbd3…63e0`).
> - **Gate:** the structural claims (atomics, finalization, dispatches, stack) are checked by counters, the fault paths are exercised, and the reports and diagnostics are exact.
> - **Budget:** 150–250 production lines, 2 files, plus `#ifdef GPUQS_TEST_HOOKS` blocks in MSL.
> - **Depends on:** W3. **Unlocks:** W5.

## 1. Objective and spec obligations

R-21, R-22, C-02 (all fields), K-09 (§7.1), K-11, E-09, E-10, E-12, E-16, I-008, D-21, and T-12..T-16, T-21..T-24, T-29 (library), T-42 (library).

## 2. Entry preconditions

The W3 gate is green.

## 3. Deliverables

- **`TestHooks.swift`** (compiled only with `GPUQS_TEST_HOOKS`): a per-instance `package var testHooks` holding:
  - `commandBufferCommits`, `dispatches[kernel]`;
  - `failCommandBuffer: Int?` (E-09 injection);
  - `stackCapacityOverride: UInt32?`;
  - `failAllocation: Bool`;
  - `corruptSequenceRecordAfterIteration: Int?`;
  - `atomicCounter` and `finalizeCounter` device buffers (bound by the testhooks metallib; kernels increment them under `#ifdef`);
  - `phaseOneObserver`.
- **`Diagnostics.swift`:** formats the §5.3 lines exactly and sends each to `os.Logger` (subsystem `GPUQuicksort`, `.debug`) and to the handler.
- **Report fields:** `bookkeepingBytes` (hook buffers excluded), `libraryVersion`, `metallibSHA256`, `tuningEntry`.

## 4. Work items

- **W4-01:** T-06 counter half, T-08 dispatch half, T-12, T-42 (library), T-24, then `TestHooks` and the injection points.
- **W4-02:** T-13, T-14, T-15, T-16, then the MSL counters and the observer data.
- **W4-03:** T-21 (the §7.1 bound for the resolved $M$, $M = 1$ and $M = 2^{16}$; zeros when $n \leq 1$), T-22 (8 concurrent tasks), T-23, then the report fields and `inout` API polish.
- **W4-04:** T-29 (library): the handler receives `phase1` lines $i = 1..$ and one `sort` line equal to the report, with no key value. Then `Diagnostics`.

## 5. Test plan

| File | Ids |
| ---- | --- |
| `StructureTests.swift` | T-12..T-16 |
| `APITests.swift` | T-21..T-24, T-29 (library), T-42 (library) |

## 6. Gate

1. `scripts/build-metallib.sh` → exit 0.
2. `swift test` (the whole suite so far) → exit 0.

## 7. Traceability

E-09, E-10, E-12, E-16, I-008, R-21, R-22 (library), K-09 and K-11 become passing.

## 8. Traps

- Hook buffers must never be bound or allocated in release builds (§10).
- The `diagnostics` setter blocks during a sort (F-027); tests must set it before sorting.

## 9. Exit and handoff

- **Frozen:** the `testHooks` API used by W5's CLI (`GPUQS_TEST_FAIL_CB` maps to `failCommandBuffer`).
- **Re-run by W5:** gate 2.
