# Detailed implementation plan — W6: Prove it

> - **Wave:** W6 of W0–W6 (`IMPLEMENTATION_PLAN.md` §4 item 7).
> - **Spec basis:** `SPEC.md` v0.4 (sha256 `b05ffbd3…63e0`).
> - **Gate:** the recorded runs exist, T-34 is no longer skipped, speccheck Phase A and Phase B are strict-clean, and `SPEC_BUILD_REPORT.md` is written.
> - **Budget:** no production code except fixes found by the audit.
> - **Depends on:** W5.

## 1. Objective and spec obligations

R-25, K-13, K-14 (measured), T-17, T-32, T-33, T-34, the README, and conformance.

## 2. Entry preconditions

The W5 gate is green. The reference machine (Apple M5 Max) is available. Ollama is serving `qwen3:8b`.

## 3. Deliverables

- `TunedParameters.json` with the `Apple M5 Max` entry and `apple-default` pointing at it.
- `SPEC_BUILD_REPORT.md` §Performance (T-32, T-33, T-34), §Inspection (T-17), the per-id evidence, and the verdict.
- `README.md`.
- Tests `RecordedTests.swift` (T-17, T-32, T-33, T-34 presence checks).

## 4. Work items

- **W6-01:** `swift build -c release`, then `.build/release/gpuqsort tune --write --as-default`, and record the JSON and elapsed time (K-14).
- **W6-02:** `.build/release/gpuqsort bench --dist all --n 1M,2M,4M,8M,16M --runs 5 --cpu`, and record the table and the K-13 ratio (T-32) and the scaling factor (T-33).
- **W6-03:** the T-17 inspection checklist, with file:line for each barrier and access pattern.
- **W6-04:** the README from the built surface.
- **W6-05:** speccheck Phase A, then Phase B; fix any finding; write the report.

## 6. Gate

1. `swift test --xunit-output junit.xml` → exit 0.
2. `speccheck check --spec SPEC.md --src Sources --tests Tests --results junit-swift-testing.xml --judge mock --strict --out build/speccheck` → exit 0, `CONFORMING`.
3. The same with `--judge llm` (qwen3:8b) and `--out build/speccheck-llm` → exit 0.

## 8. Traps

- The recorded runs must use the release build (F-020).
- Re-run `swift test` after `tune` rewrites the table, because the defaults change.

## 9. Exit

The verdict block in `SPEC_BUILD_REPORT.md`.
