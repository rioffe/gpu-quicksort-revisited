# Specification Review Report

> - **Subject:** `SPEC.md` v0.3 — GPU-Quicksort for Metal (Swift library + CLI)
> - **Round:** 2. The round-1 report (on v0.2, findings F-001..F-019) is in git history at commit `a1720d1`. This round's new findings start at **F-020** so their ids never collide with the round-1 ids that the v0.3 revision history cites.
> - **Reviewer:** spec-review skill, four passes (comprehension, local precision, cross-consistency, implementation simulation)
> - **Date:** 2026-09-25
> - **Source of intent checked against:** `gpu-quicksort.md` (Cederman and Tsigas 2009), cited as [P …]

## 1. Executive Summary

v0.3 resolves all 19 round-1 findings (§3.1 below). Most fixes are complete, not partial:
- the tuning bootstrap now works end to end (`TuningSource`, the `paper-8800gtx` entry, and `tune` using constants);
- R-28 makes intra-threadgroup ordering normative;
- O-2 is fully defined, with a progress argument;
- the §7.1 bound follows from the contract sizes;
- the §7.2 exit-code table is total.

A script check confirms that every cited id is declared, and that every R, C, I, K, E and O id has a §11 row with a declared test.

This round found **no CRITICAL or HIGH issues**. Three MEDIUM issues remain, all introduced or exposed by the v0.3 changes:
- T-28 runs `bench` in the debug test build, which `bench` refuses (F-020);
- `tune --write` has no rule for a missing or invalid table file, and T-38 contradicts itself on this (F-021);
- T-34's "pending" outcome has no defined meaning in swift-testing (F-022).

Eight LOW editorial items round out the list.

**Maturity: Level 3 (implementation-grade).** **Readiness: READY WITH MINOR FIXES.** There are no blocking questions. The three MEDIUM items are local edits to test and CLI rows.

| Severity | Count |
| -------- | ----: |
| CRITICAL | 0 |
| HIGH | 0 |
| MEDIUM | 3 |
| LOW | 8 |

## 2. Overall Maturity

**Level 3 — Implementation-grade.** A coding agent can implement every component without semantic guesses, and every requirement has an objective pass condition.

It is not Level 4. That would need mechanically checkable semantics, for example a formal model of the partition and stack invariants, and there is none. §11's traceability is complete but maintained by hand.

## 3. Findings Summary

### 3.1 Round-1 findings: disposition in v0.3

| Round-1 id | Resolution in v0.3 | Status |
| ---------- | ------------------ | ------ |
| F-001 | `TuningSource` in C-01; bootstrap `paper-8800gtx`; R-24 uses `.constants`; T-20/T-34/T-37/T-38 updated | Resolved (T-38 wording: F-021) |
| F-002 | R-28 (a)–(c); I-007 extended; T-17 checklist item | Resolved |
| F-003 | §2.5 O-2 row; T-14 counts; T-41; D-20 | Resolved |
| F-004 | §7.1 display bound; `bookkeepingBytes`; T-21 | Resolved (test-hook allocations: F-025) |
| F-005 | R-03 allows $\mathit{maxseq} = 1$; K-10 needs $\mathit{maxseq} \geq 2$; D-22 | Resolved |
| F-006 | E-24; §3.1 diagram and table; T-08 dispatch counter | Resolved |
| F-007 | C-01 `diagnostics`; §5.3 formats; R-22; T-29 | Resolved (setter locking: F-027) |
| F-008 | `CShared/include/SharedTypes.h`; `GQS_ATOMIC_U32`; `exclude: ["Metal"]`; script paths | Resolved (empty C target: F-029) |
| F-009 | `gaussian` pinned to $u_i$, 64-bit sum, draw order; `bucket` cleaned | Resolved |
| F-010 | T-10 deterministic cap test; T-40 phase-two inputs | Resolved (T-40 reference: F-030) |
| F-011 | T-42; T-12 narrowed; §11 fixed | Resolved |
| F-012 | §7.2 table; K-12 points to it; T-27 cases | Resolved (`gen` bound: F-028) |
| F-013 | Oracle computed once in `bench` and `tune`; T-38 hook counter | Resolved |
| F-014 | Provenance in `SortReport`, CSV, tune JSON, `info --json` | Resolved (CSV quoting: F-026) |
| F-015 | `keyTypeMismatch` removed | Resolved |
| F-016 | R-23, K-03, K-04 order, T-17 marker, `OUT_DIR`, `info --json` | Resolved (report section name: F-030) |
| F-017 | E-10 and E-12 transitions added | Resolved |
| F-018 | C-02 depth convention; K-08 and T-11 cite it | Resolved |
| F-019 | K-02 rationale dropped; K-09 scoped; `sort` synchronous | Resolved |

### 3.2 New findings

| ID | Severity | Location | Title | Plan |
| -- | -------- | -------- | ----- | ---- |
| F-020 | MEDIUM | T-28, C-11, D-21 | T-28 runs `bench` in the debug test build, which `bench` refuses | P1 |
| F-021 | MEDIUM | C-10 `--write`, T-38, E-23 | `tune --write` behaviour for a missing or invalid table file is undefined; T-38 is self-contradictory | P1 |
| F-022 | MEDIUM | T-34, §9 | "Pending" is not a defined test outcome | P1 |
| F-023 | LOW | R-28 | Requirement titled "inside one `lqsort` threadgroup" also constrains `gqsort_partition` | P2 |
| F-024 | LOW | K-07, C-02 | `phaseOneCapReached` undefined when the loop would have ended exactly at the cap | P2 |
| F-025 | LOW | §7.1, T-16 | Test-hook buffers are not excluded from `bookkeepingBytes` | P2 |
| F-026 | LOW | §5.2 CSV | No quoting rule for CSV fields | P2 |
| F-027 | LOW | C-01 `diagnostics` | Only reads are said to take the lock | P2 |
| F-028 | LOW | §7.2, `gen` | `gen` needs a Metal device to learn `maxKeys` | P2 |
| F-029 | LOW | C-09 | A header-only `CShared` C target needs a source file for SwiftPM | P2 |
| F-030 | LOW | T-40, §9 | Musser's killer sequence is cited but not constructed; the spec names two build-report sections for recorded results | P2 |

## 4. Detailed Findings

### F-020 — T-28 runs `bench` in the debug test build, which `bench` refuses

**Severity:** MEDIUM  **Location:** T-28, C-11, §7.2 row 2, D-21, §9 intro

**Observation.** §9 says tests run with `swift test` in the debug configuration (so the D-21 hooks are present). C-11 and §7.2 say `bench` exits 2 from a debug build unless `--allow-debug` is passed. T-28 invokes `bench --n 1M --runs 3 --dist uniform --cpu` with no `--allow-debug`, so as written it must exit 2 and cannot see 12 rows. `tune` has no debug guard at all, although it produces the timings stored in C-10.

**Why it matters.** A conforming implementation fails T-28. Or an implementer "fixes" the guard and weakens C-11.

**Recommended resolution.**
- Add `--allow-debug` to T-28's command line.
- Give `tune` the same guard as `bench`: it exits 2 from a debug build unless `--allow-debug` is passed. Add that to the §7.2 row and to T-38's command line.
- State in T-34 and T-32 that the recorded runs use a release build.

### F-021 — `tune --write` behaviour for a missing or invalid table file is undefined

**Severity:** MEDIUM  **Location:** C-10 (`--write`), T-38, E-23, §7.2

**Observation.** C-10 says `--write` "replace[s] or insert[s] the entry … keep[s] the other entries". It says nothing about a file that does not exist or is not a valid table. T-38 requires both that `tune … --table <tmp>` "succeeds even when `<tmp>` initially holds an invalid table" and that "`--write` updates only the host device's entry". The two cannot both hold for an invalid file. A newly created table written without `--as-default` would also lack `apple-default`, so the table `tune` produces would fail C-10 validation.

**Why it matters.** Two implementations will differ: one overwrites an invalid table, one refuses, and one writes a table its own loader rejects.

**Recommended resolution.** Add these rules to C-10 `--write`:
- If the file does not exist, create a table containing the new entry, with `apple-default` pointing at it whether or not `--as-default` is given.
- If the file exists but is not a valid C-10 table, exit 4 with `table <path> is not a valid tuned-parameter table: <reason>` and leave it unchanged. Validation happens before the grid search starts, so no time is wasted.
- The written table MUST pass C-10 validation.

Then split T-38: without `--write`, an invalid `<tmp>` is ignored and the run succeeds. With `--write`, an invalid `<tmp>` exits 4 with no change, and a missing `<tmp>` is created and passes validation. Add these cases to E-23 or a new E row.

### F-022 — "Pending" is not a defined test outcome

**Severity:** MEDIUM  **Location:** T-34, §9 intro

**Observation.** T-34 says that before the first tuning run, its presence check "reports *pending* rather than failing". swift-testing has pass, fail, skipped (`.disabled`), and known issue; it has no "pending". The spec also does not say how a pending T-34 affects a conformance claim.

**Recommended resolution.**
- T-34's suite check is declared with `.disabled(if: <no Apple M5 Max entry>, "tuning not yet recorded (R-25)")`. A skipped T-34 means R-25 is *verification pending*, and a build report MUST NOT claim conformance while it is skipped.
- Add that rule to the §9 intro for all *(recorded)* tests.

### F-023 — R-28's title is narrower than its content

**Severity:** LOW  **Location:** R-28

**Observation.** R-28 opens with "Ordering inside one `lqsort` threadgroup", but its last sentence constrains `gqsort_partition`.

**Recommended resolution.** Retitle it "Ordering inside one threadgroup (`lqsort`, and rule (a) for `gqsort_partition`)", or split the last sentence into its own row.

### F-024 — `phaseOneCapReached` boundary

**Severity:** LOW  **Location:** K-07, C-02

**Observation.** If the R-08 loop condition becomes false exactly after the capped iteration, it is unclear whether the cap was "reached".

**Recommended resolution.** `phaseOneCapReached` is `true` iff $\mathit{phaseOneIterations} = \mathit{maxPhaseOneIterations}$ and the R-08 loop condition still holds after that iteration.

### F-025 — Test-hook buffers and the §7.1 bound

**Severity:** LOW  **Location:** §7.1, T-16, T-14

**Observation.** The T-16 hook allocates one counter per index ($4n$ bytes), and T-14 allocates atomic counters. Both exceed the $136M + 2^{16}$ bound if they are counted.

**Recommended resolution.** State that buffers allocated only under `GPUQS_TEST_HOOKS` are excluded from `bookkeepingBytes`.

### F-026 — CSV quoting

**Severity:** LOW  **Location:** §5.2 CSV

**Observation.** `device` and `os_version` are free text (for example, `Version 26.6.2 (Build …)`) and could contain commas or quotes.

**Recommended resolution.** The CSV follows RFC 4180: fields containing a comma, a double quote or a newline are enclosed in double quotes, with inner quotes doubled.

### F-027 — `diagnostics` setter locking

**Severity:** LOW  **Location:** C-01

**Observation.** The spec says the handler "is read under the same lock". A setter that does not take the lock is a data race under Swift 6 strict concurrency (the class is `@unchecked Sendable`).

**Recommended resolution.** Both getter and setter acquire the lock, and a set during a running sort takes effect for the next sort.

### F-028 — `gen` and `maxKeys`

**Severity:** LOW  **Location:** §7.2 row 2, §5.2 `gen`

**Observation.** `maxKeys` depends on `maxBufferLength`, but `gen` is otherwise GPU-free.

**Recommended resolution.** For `gen`, the bound is $2^{31} - 1$ (K-01's device-independent term), so `gen` does not create a Metal device.

### F-029 — Header-only C target

**Severity:** LOW  **Location:** C-09

**Observation.** SwiftPM does not accept a C-family target without at least one source file. `Sources/CShared/` as listed contains only `include/SharedTypes.h`.

**Recommended resolution.** Add `Sources/CShared/CShared.c` (empty translation unit) to the C-09 layout.

### F-030 — Two loose references in tests (batched)

**Severity:** LOW  **Location:** T-40, §9 intro, T-17

- **T-40** names "Musser's median-of-3 killer sequence [Musser 1997]" without giving its construction for this pivot rule ($s_b$, $s_{\lfloor (b+e)/2 \rfloor}$, $s_{e-1}$). Either give the generator in the row or cite the construction precisely. The test's pass condition (correctness plus depth) holds regardless, so this is editorial.
- **Build-report sections:** the §9 intro puts every recorded result in `SPEC_BUILD_REPORT.md` §Performance, while T-17 records into §Inspection. Name both sections in the intro.

## 5. Requirements Review

Requirements R-01 … R-28 and O-2 are observable, normative and sourced. The round-1 conflicts (R-03 against `maxseq = 1`, and R-22's missing hook) are gone. R-28 now carries the memory-model obligations the stated principle requires; its scope wording is F-023. No missing requirements were found.

## 6. Interface and Data-Contract Review

- **C-01:** complete, now including tuning injection, diagnostics, provenance and blocking semantics. Remaining gap: setter locking (F-027).
- **C-05/C-06:** compilable on both sides through `GQS_ATOMIC_U32`, with host access restricted to times when no GPU work is in flight.
- **C-08:** fully determined; T-25's Python reference can match it byte for byte.
- **C-10:** complete for reading; the write path has the gaps in F-021.
- **CLI outputs:** exact, except for CSV quoting (F-026).
- **Visual-surface completeness:** n/a.

## 7. State and Failure Review

The §3.1 diagram and table now agree, including E-10 in phase one, E-12, and E-24. Every C-07 case has an edge case, a transition and an exit code. The tune file-write failures are incomplete (F-021). Cancellation is explicitly excluded (C-01: synchronous, not cancellable).

## 8. Determinism and Algorithm Review

Output determinism rests on I-001 + I-002. O-2's pivot arithmetic is overflow-free, and its progress argument is correct:
- if $\mathit{lo} < \mathit{hi}$, then $\mathit{lo} \leq p < \mathit{hi}$, so the element $\mathit{hi}$ leaves the $<$ side and the element $\mathit{lo}$ leaves the $>$ side;
- if $\mathit{lo} = \mathit{hi}$, the whole sequence becomes a gap.

The §7.1 bound is sound. At the start of an iteration $|\mathit{work}| < M$, and the number of blocks is at most $\sum \lceil \ell / \mathit{blocksize} \rceil \leq M + |\mathit{work}| < 2M$, because $\mathit{blocksize} \geq \lceil \sum \ell / M \rceil$. The final $|\mathit{done}|$ is below $2M$. The cap boundary is F-024.

## 9. Edge-Case Review

Covered: empty, singleton, below-threshold, all-equal (now with E-24), duplicates, float specials, adversarial inputs for phase two (T-40), and every buffer, parameter, allocation, GPU, table and file failure. Remaining: `tune --write` on a missing or invalid table (F-021).

## 10. Non-Functional Requirement Review

- **K-09:** now measurable (`bookkeepingBytes`) and tested, subject to F-025.
- **K-13:** unchanged and sound.
- **K-14:** made achievable by the compute-the-oracle-once rule.
- **Recorded runs:** they should state a release build (F-020).

## 11. Security and Trust-Boundary Review

No change and no findings. Key values are never logged, input sizes are validated, and table writes are atomic.

## 12. Observability and Provenance Review

This is resolved. `SortReport`, the bench CSV, the tune JSON and `info --json` all carry the library version, metallib hash and tuning entry, and the CLI outputs add the OS version. The diagnostics lines have exact formats and a test (T-29) tying them to the report.

## 13. Testing and Verification Review

T-01 … T-42 give each I, K and E id at least one test with an unambiguous pass condition. The exceptions are T-28 (fails as written, F-020), T-38 (contradictory, F-021) and T-34 (undefined outcome, F-022).

Oracles remain independent of the implementation: a CPU sort, a Python generator, hand-computed fits, and CPU recomputation of O-2 pivots. Fault injection now covers E-09, E-10, E-12, the table-validation failures, and a verification failure during `tune`.

## 14. Metrics and Evaluation Review

No change from round 1. Every metric is defined with units and a degenerate-case rule, including the new `bookkeepingBytes` formula (both fields are 0 for $n \leq 1$). No findings.

## 15. Traceability Review

A mechanical check found:
- 0 cited-but-undeclared ids;
- 0 R/C/I/K/E/O ids missing from §11;
- 0 §11 test references that are undeclared.

T-33 is intentionally untraced (it records without passing or failing, and says so). The §12 *Affects* cells name only declared ids. D-21 should add T-28 once F-020 is resolved.

## 16. Internal-Consistency Review

Contradictions found:
- T-28 against C-11 and D-21 (F-020);
- T-38's two clauses (F-021);
- two names for build-report sections (F-030).

The round-1 contradictions are all gone.

## 17. Architecture Review

The components are sound, and the host–kernel, library–CLI and build–runtime boundaries are explicit. The one packaging gap is F-029.

## 18. Implementation-Agent Readiness

**YES — WITH MINOR CLARIFICATIONS.** An agent can build everything as specified. The clarifications are:
- add `--allow-debug` to T-28, and a debug guard for `tune` (F-020);
- the `--write` rules for missing and invalid tables (F-021);
- how a skipped T-34 is reported (F-022).

None changes runtime behaviour of the sorter itself.

## 19. Quality Scorecard

| Dimension | Round 1 (v0.2) | Round 2 (v0.3) |
| --------- | -----: | -----: |
| Scope clarity | 5 | 5 |
| Terminology | 4 | 4 |
| Requirement precision | 4 | 5 |
| Interface completeness | 4 | 4 |
| Visual-surface completeness | n/a | n/a |
| Data-contract completeness | 4 | 5 |
| State/lifecycle definition | 4 | 5 |
| Algorithm precision | 4 | 5 |
| Failure semantics | 4 | 4 |
| Edge-case coverage | 4 | 5 |
| Non-functional requirements | 4 | 4 |
| Security specification | 4 | 4 |
| Observability/provenance | 3 | 5 |
| Testability | 4 | 4 |
| Evaluation/metrics | 4 | 5 |
| Traceability | 4 | 5 |
| Internal consistency | 3 | 4 |
| Architecture consistency | 4 | 4 |
| Implementation readiness | 3 | 4 |

## 20. Remediation Plan

### P0 — Blocking

None.

### P1 — Important

- **F-020:** add `--allow-debug` to T-28; add a debug guard to `tune`; state that recorded runs use release builds.
- **F-021:** define `--write` for missing and invalid tables; guarantee a valid output; split T-38.
- **F-022:** define a skipped T-34 as *verification pending* and forbid a conformance claim while it is skipped.

### P2 — Improvement

F-023 (R-28 title), F-024 (cap flag), F-025 (hooks excluded from the bound), F-026 (RFC 4180), F-027 (setter lock), F-028 (`gen` bound), F-029 (`CShared.c`), F-030 (T-40 construction; report sections).

## 21. Final Verdict

```text
Specification maturity:
Level 3

Implementation readiness:
READY WITH MINOR FIXES

Primary blocker:
NONE

Most important improvement:
Define tune --write for missing or invalid table files and split T-38 accordingly (F-021), and make T-28 runnable in the debug test build (F-020).
```
