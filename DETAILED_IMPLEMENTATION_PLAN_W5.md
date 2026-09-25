# Detailed implementation plan — W5: CLI

> - **Wave:** W5 of W0–W6 (`IMPLEMENTATION_PLAN.md` §4 item 6).
> - **Spec basis:** `SPEC.md` v0.4 (sha256 `b05ffbd3…63e0`).
> - **Gate:** all six subcommands match §5.2, the §7.2 exit table is total, and the CLI tests pass against the debug binary.
> - **Budget:** 400–550 production lines, 7 files.
> - **Depends on:** W1 (generators, baselines, table), W4 (hooks, diagnostics). **Unlocks:** W6.

## 1. Objective and spec obligations

R-19, R-22 (CLI), R-23, R-24, R-26, K-12 (§7.2), K-14, E-15, E-22, E-23, E-25, §5.2, §5.3, and T-27..T-30, T-38, T-39 (the guard), T-42 (CLI).

## 2. Entry preconditions

The W4 gate is green.

## 3. Deliverables

- **`Sources/gpuqsort/`:**
  - `main.swift` (a custom `main`: parse errors go to stderr and exit 2; any error maps through `ExitCode.from(_:)` per §7.2);
  - `Info.swift`, `Gen.swift`, `SortCommand.swift`, `Verify.swift`, `Bench.swift` (RFC 4180 CSV, JSON, provenance columns, oracle computed once, warm-up discarded, CPU baselines, debug guard);
  - `Tuner.swift` (validates `--table` before measuring when `--write` is given; grid; oracle computed once per size; fit; atomic write; `.constants(.paper8800GTX)` sorter; debug guard; `--grid small` test flag);
  - `Common.swift` (size parsing with K/M suffixes, error printing, `GPUQS_TEST_FAIL_CB`).

## 4. Work items

- **W5-01:** T-27 and T-30, then `Info`, `Gen`, `SortCommand`, and the exit mapping.
- **W5-02:** T-28, T-29 (CLI), T-39 (guard), then `Verify` and `Bench`.
- **W5-03:** T-38 (a)–(g), then `Tuner`.
- **W5-04:** T-42 (CLI), exit 5 under `GPUQS_TEST_FAIL_CB`.

## 5. Test plan

| File | Ids |
| ---- | --- |
| `CLITests.swift` | T-27..T-30, T-38, T-39 (guard), T-42 (CLI); runs `.build/debug/gpuqsort` through `Process` |

## 6. Gate

1. `swift build` → exit 0.
2. `swift test` → exit 0.

## 7. Traceability

R-19, R-23, R-24, R-26, K-12, K-14 (the design; the measurement is in W6), E-15, E-22, E-23, E-25 and T-27..T-30, T-38 become passing.

## 8. Traps

- ArgumentParser exits 64 on usage errors by default; §7.2 requires 2.
- `gen` must not create a Metal device (F-028).
- CSV quoting (F-026).

## 9. Exit and handoff

- **Frozen:** the CLI surface of §5.2.
- **Re-run by W6:** gate 2.
