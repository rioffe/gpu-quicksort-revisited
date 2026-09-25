# Specification Review Report

> - **Subject:** `SPEC.md` v0.2 — GPU-Quicksort for Metal (Swift library + CLI)
> - **Reviewer:** spec-review skill, four passes (comprehension, local precision, cross-consistency, implementation simulation)
> - **Date:** 2026-09-25
> - **Source of intent checked against:** `gpu-quicksort.md` (Cederman and Tsigas 2009), cited as [P …]

## 1. Executive Summary

`SPEC.md` v0.2 is a strong, well-traced specification. It pins the algorithm's observable structure: the two-pass partition, one atomic per side per threadgroup, the pivot gap, the buffer ping-pong, and the smaller-first stack. It also turns every place where the paper's pseudocode is wrong or unsafe under Metal (the last-finisher step, pivots read one past the end, the staggered overflow) into an explicit decision the requester has ratified. The output of a sort is fully determined, so there is a single oracle, and the tests use it consistently.

**Maturity: Level 2, close to Level 3.** **Readiness: READY WITH MINOR FIXES**, provided the two P0 findings are folded in first. Both are local edits of a few rows each.

| Severity | Count |
| -------- | ----: |
| CRITICAL | 0 |
| HIGH | 2 |
| MEDIUM | 12 |
| LOW | 5 |

**Strengths.**
- Every requirement cites the paper.
- The memory-model argument that motivates D-03 is explicit.
- The C-04 key encoding makes I-002 and I-004 hold bit for bit.
- The traceability matrix is complete for R, C, I, K and E ids.
- §12 records every departure from the paper.

**Most important weaknesses.**
- The tuned-parameter table cannot be bootstrapped. `init` rejects the shipped placeholder table, and `tune` needs `init` to run (F-001).
- The spec pins ordering *across* threadgroups (I-007) but not the device-memory ordering *within* one `lqsort` threadgroup. That is where a Metal implementation is most likely to race (F-002).

## 2. Overall Maturity

**Level 2 — Implementable, bordering on Level 3.**

A competent agent could build a correct sorter from this spec today. What keeps it from Level 3:
- One workflow cannot run as written: tuning (F-001).
- One correctness rule is left for the implementer to discover: intra-threadgroup ordering (F-002).
- The optional `minMaxAverage` path is underspecified (F-003).
- A few tests cannot be built as written, or prove the wrong id (F-010, F-011).

Once these are resolved, the spec meets Level 3.

## 3. Findings Summary

| ID | Severity | Location | Title | Plan |
| -- | -------- | -------- | ----- | ---- |
| F-001 | HIGH | C-01, C-10, R-24/R-25, T-20/T-37/T-38 | Tuned-parameter table cannot be bootstrapped or injected | P0 |
| F-002 | HIGH | R-06, R-13, R-15, I-007 | Device-memory ordering inside an `lqsort` threadgroup unspecified | P0 |
| F-003 | MEDIUM | R-11, O-2, C-05 | `minMaxAverage` (O-2) has no defining row; root pivot, overflow, child pivots undefined | P1 |
| F-004 | MEDIUM | K-09 | Auxiliary-allocation bound contradicts C-05/C-06 sizes and is untested | P1 |
| F-005 | MEDIUM | R-03, R-08, K-10, T-03 | `maxseq = 1` runs zero phase-one iterations, contradicting K-10 and R-03 | P1 |
| F-006 | MEDIUM | R-12, §3.1 | Empty `done` set (e.g. `zero`) has no defined phase-two behaviour | P1 |
| F-007 | MEDIUM | R-22, §5.3, C-01 | CLI must mirror library diagnostics, but the library exposes no hook | P1 |
| F-008 | MEDIUM | C-05, C-09 | Package layout and shared header are not buildable as written | P1 |
| F-009 | MEDIUM | C-08 | `gaussian` formula reuses the symbol $r$ and does not pin arithmetic width | P1 |
| F-010 | MEDIUM | T-10 | Adversarial test cannot be constructed; it is the only test of K-07/E-13 | P1 |
| F-011 | MEDIUM | E-09, T-12, §11 | Command-buffer failure path is untested; §11 maps it to a test of E-10 | P1 |
| F-012 | MEDIUM | K-12, C-07 | Error-to-exit-code mapping is incomplete | P1 |
| F-013 | MEDIUM | §5.2 `tune`, K-14 | Per-run verification cost can exceed the K-14 budget | P2 |
| F-014 | MEDIUM | C-02, §5.2 | Recorded results lack provenance (metallib stamp, tuning entry, version) | P2 |
| F-015 | LOW | C-07, E-11 | `keyTypeMismatch` is never thrown | P2 |
| F-016 | LOW | R-23, K-03, K-04, T-17, T-36, C-08, §5.2 | Stale or loose wording (batched) | P2 |
| F-017 | LOW | §3.1 | Lifecycle diagram and table omit two failure transitions | P2 |
| F-018 | LOW | C-02, K-08, T-11 | "Stack depth" counting convention undefined | P2 |
| F-019 | LOW | K-02, K-09, C-01 | Unverified rationale, array-API space, blocking semantics (batched) | P2 |

## 4. Detailed Findings

### F-001 — Tuned-parameter table cannot be bootstrapped or injected

**Severity:** HIGH  **Location:** C-01, C-10, R-24, R-25, T-20, T-37, T-38, E-20

**Observation.** C-10's shipped example has $k = m = 0$ as placeholders, but C-10 validation requires $m \geq 1$, so `init` throws `tunedParametersInvalid` (E-20). `gpuqsort tune` must sort in order to measure, which needs a `GPUQuicksort` instance. So before the first tune, `tune` exits 3 and can never produce the entry R-25 requires. Separately, C-01's `init(device:)` has no way to supply a different table. Yet T-20 ("a test C-10 table holding the paper's constants"), T-37 (invalid tables make `init` throw) and T-38 (`--table <tmp>`) all need to inject one.

**Why it matters.** The required tuning workflow (D-06) deadlocks on a fresh checkout, and three tests cannot be written against the public API.

**Potential consequence.** Implementers will each invent their own escape hatch: an environment variable, a hidden initializer, or a relaxed validation. These are incompatible, and the fix may silently mask E-20.

**Recommended resolution.**
1. Add a tuning source to C-01: `init(device: MTLDevice? = nil, tuning: TuningSource = .bundled)`, with `enum TuningSource { case bundled, file(URL), constants(TunedConstants) }`.
2. Ship a valid bootstrap table: an entry `"paper-8800gtx"` holding the [P Tab II] 8800GTX constants, and `"apple-default": {"sameAs": "paper-8800gtx"}`.
3. Have `tune` construct its sorter with `.constants(paper-8800gtx)` and explicit parameters, so it never depends on the table it is writing.
4. Change T-34 to check that after `tune --write --as-default`, `apple-default` points at `Apple M5 Max`, which then satisfies R-25.
5. Make T-20 and T-37 use `.constants` and `.file`.

### F-002 — Device-memory ordering inside an `lqsort` threadgroup unspecified

**Severity:** HIGH  **Location:** R-06, R-13, R-15, I-007, §3.3

**Observation.** I-007 constrains only reads *across* threadgroups. Inside one `lqsort` threadgroup, three device-memory hazards are left unspecified:
- **(a)** When a sequence lives in $D$ (`src = 0`), its gap $[b+L, e-G)$ in $D$ is filled while other threads may still be reading $D[b..e)$ in pass 2.
- **(b)** The next popped child was written to device memory by *other* threads of the same threadgroup in the previous pass 2. Metal makes those writes visible only after `threadgroup_barrier(mem_flags::mem_device)`, not after a threadgroup-memory barrier alone.
- **(c)** The alternative-sort load has the same visibility need as (b), and so does its write-back into $D$ when the sequence already lives in $D$.

**Why it matters.** The spec's stated principle is "correct under Metal's memory model". These are the ordering rules that principle needs, and they are nowhere normative.

**Potential consequence.** An implementation that is correct on one GPU or at one threadgroup size corrupts data intermittently on another. T-01 may pass by luck.

**Recommended resolution.** Add a requirement, cited by T-17's inspection checklist and by I-007:

> **R-28.** Within an `lqsort` threadgroup: (a) the gap fill of a partition MUST NOT begin until every thread has finished pass 2 of that partition; (b) before any thread reads elements that other threads of the same threadgroup wrote to device memory (the next popped sequence, or an alternative-sort load), the threadgroup MUST execute `threadgroup_barrier(mem_flags::mem_device | mem_flags::mem_threadgroup)`; (c) the alternative sort MUST finish loading into threadgroup memory before any write-back to $D$.

Extend I-007 to say that ordering *within* a threadgroup is established only by barriers.

### F-003 — `minMaxAverage` (O-2) has no defining row

**Severity:** MEDIUM  **Location:** R-11, C-03, C-05 (`lmin` … `gmax`), K-02, T-03, §11

**Observation.** O-2 is cited in six places but defined nowhere. There is no O-n table, and O-1's retirement left none. The following are unspecified:
- how the *root* sequence's min and max are obtained, since no partition has happened yet;
- the pivot formula. $\lfloor(\min+\max)/2\rfloor$ overflows 32 bits for codes above $2^{31}$, which covers all negative `Int32` and positive `Float` codes;
- how `lmin`/`lmax`/`gmin`/`gmax` map to the children's pivots;
- what `SequenceRecord` holds for these fields under `medianOfThree`.

**Why it matters.** "Optional ≠ unspecified." T-03 requires this path to be correct, and an overflowed pivot below $\min$ sends every element to the $>$ side. The child is then as long as its parent, which violates I-005's progress clause (only the K-07 cap stops it).

**Recommended resolution.** Add an **O-2** row:
- The root min and max come from one reduction dispatch (or from the first iteration using `medianOfThree`; pick one).
- The pivot is $p = \min + \lfloor (\max - \min)/2 \rfloor$ in unsigned 32-bit arithmetic.
- The children of sequence $j$ take pivots from $(\mathit{lmin}_j, \mathit{lmax}_j)$ and $(\mathit{gmin}_j, \mathit{gmax}_j)$.
- The fields are ignored under `medianOfThree`.

Add a T-row showing that O-2 keeps I-005 on `fullrange` `int32`.

### F-004 — K-09 allocation bound contradicts the contract sizes

**Severity:** MEDIUM  **Location:** K-09, C-05, C-06, T-21

**Observation.** K-09 bounds all non-auxiliary allocations by $64(\mathit{maxseq} + 1) + 2^{16}$ bytes. But per iteration:
- `SequenceRecord` takes 40 bytes $\times\ |\mathit{work}| < \mathit{maxseq}$;
- `BlockDescriptor` takes 16 bytes $\times$ up to $\mathit{maxseq} + |\mathit{work}|$ threadgroups.

Phase one alone therefore reaches about $72\,\mathit{maxseq}$. Phase two adds `SortSequence` and `SortStats` at 32 bytes $\times\ |\mathit{done}| \leq 2\,\mathit{maxseq}$. No test checks the bound.

**Recommended resolution.** Restate the bound from the contracts and verify it through `SortReport`:

$$
\mathit{bookkeepingBytes} \leq 40\,\mathit{maxseq} + 16\,(2\,\mathit{maxseq}) + 32\,(2\,\mathit{maxseq}) + 2^{16}
$$

Here the three terms count `SequenceRecord`, `BlockDescriptor`, and `SortSequence` + `SortStats`. Add `bookkeepingBytes` to C-02 and an assertion to T-21.

### F-005 — `maxseq = 1` contradicts K-10 and R-03

**Severity:** MEDIUM  **Location:** R-03, R-08, K-10, T-03, T-08

**Observation.** R-08's loop condition $|\mathit{work}| + |\mathit{done}| < \mathit{maxseq}$ is false before the first iteration when $\mathit{maxseq} = 1$, so phase one runs zero times. K-04 allows this value and T-03 uses it. That conflicts with:
- R-03, which says phase one may be skipped *only* under E-03;
- K-10, which says `zero` input gives exactly one phase-one iteration, with no condition on $\mathit{maxseq}$.

**Recommended resolution.** Restrict K-10 to $\mathit{maxseq} \geq 2$, and add "$\mathit{maxseq} = 1$" as a second permitted skip in R-03. Alternatively, raise K-04's lower bound to 2 and change T-03's grid.

### F-006 — Empty `done` set has no defined phase-two behaviour

**Severity:** MEDIUM  **Location:** R-12, §3.1, K-10

**Observation.** With `zero` input (and any input where phase one finalizes everything), `done` $= \emptyset$. R-12 would then dispatch zero threadgroups. A zero-sized dispatch is a Metal validation error on some configurations, and the state table has no transition for it.

**Recommended resolution.** Add E-24: "`done` is empty after phase one: no `lqsort` dispatch; PhaseTwo → Decoding directly; `phaseOneSequences = 0`." Add a table row, and make T-08 check that no phase-two command buffer is committed.

### F-007 — CLI must mirror library diagnostics, but the library exposes no hook

**Severity:** MEDIUM  **Location:** R-22, §5.3, C-01

**Observation.** R-22 says the CLI mirrors the library's per-iteration lines to stderr, and §5.3 pins their format, including `ms=<t>`. But the library emits them only through `os.Logger`, which a process cannot read back, and C-01 has no callback.

**Recommended resolution.** Add `public var diagnostics: (@Sendable (String) -> Void)?` to C-01, or a `package`-level equivalent. Pin that the library calls it with exactly the §5.3 line formats, and that the `os.Logger` output is identical.

### F-008 — Package layout and shared header are not buildable as written

**Severity:** MEDIUM  **Location:** C-05, C-09

**Observation.**
- **(a)** `SharedTypes.h` sits inside the Swift target's directory but must be the public header of a separate `CShared` target. SwiftPM requires a target's `publicHeadersPath` to be inside that target.
- **(b)** The `.metal` and `.h` files under `Sources/GPUQuicksort/Metal/` are "unhandled files" for a Swift target unless they are excluded.
- **(c)** C-05 declares `atomic_uint` fields. In MSL that is a Metal type, and in C it is `_Atomic unsigned`. Swift does not import C11 `_Atomic` struct fields, so a single header cannot serve both sides without a `__METAL_VERSION__` guard.

**Recommended resolution.**
- Move the header to `Sources/CShared/include/SharedTypes.h`.
- Point the build script's `-I` at that directory.
- Add `exclude: ["Metal"]` to the library target.
- Pin in C-05 that the header declares the atomic fields as `atomic_uint` under `#ifdef __METAL_VERSION__` and as `uint32_t` otherwise.
- Update the stamp inputs (C-09, T-35) to the new path.

### F-009 — `gaussian` formula is ambiguous

**Severity:** MEDIUM  **Location:** C-08, T-25

**Observation.** C-08 defines $r$ as the next *raw* 32-bit draw. The `gaussian` row then writes $\lfloor(r_1+r_2+r_3+r_4)/4\rfloor$ "of four consecutive `uniform` values". That could mean raw draws or $\mathrm{U}(0, 2^{31})$ values. The sum also needs 34 bits, and no arithmetic width is pinned. Because T-25 hashes exact bytes, two readings give different goldens, and the Python reference and the Swift generator could disagree. (Minor: the `bucket` row computes a block $B$ that it never uses.)

**Recommended resolution.** Write the row as $v_k = \lfloor (u_1 + u_2 + u_3 + u_4)/4 \rfloor$, where $u_i = \mathrm{U}(0, 2^{31})$ are four consecutive draws summed in 64-bit arithmetic. Drop $B$ from `bucket` or state that it is informational.

### F-010 — T-10 cannot be constructed

**Severity:** MEDIUM  **Location:** T-10, K-07, E-13

**Observation.** T-10 asks for input where "every median-of-three pivot is the second-smallest element". After the first phase-one iteration, though, a child's element order depends on the order in which threadgroups perform their fetch-and-adds. That order is nondeterministic by design (I-003). So no fixed input can control later phase-one pivots, and `phaseOneCapReached == true` is not reliably reached. T-10 is the only test of K-07 and E-13.

**Recommended resolution.** Split T-10 into two tests:
- **K-07:** `uniform` with $n = 2^{20}$, $\mathit{maxseq} = 1024$ and `maxPhaseOneIterations = 1`. This deterministically reaches the cap, and the test checks the flag and correctness.
- **E-13:** use `lqsort` alone with a phase-two killer sequence of length $\leq 2^{14}$, whose order *is* deterministic within a single threadgroup. Assert correctness and `maxStackDepth` $\leq$ K-08.

### F-011 — Command-buffer failure path is untested

**Severity:** MEDIUM  **Location:** E-09, T-12, §11

**Observation.** §11 maps E-09 (a command buffer completes with `.error`) to T-12. T-12 injects a stack overflow, which is E-10. Nothing exercises E-09's promises: the thrown `gpuExecutionFailed` and the instance staying usable.

**Recommended resolution.** Add a test hook in the command runner that reports a completed buffer as failed with a synthetic `NSError`. The new T-row asserts `gpuExecutionFailed(description)`, CLI exit 5, and a successful next sort. Update §11.

### F-012 — Error-to-exit-code mapping is incomplete

**Severity:** MEDIUM  **Location:** K-12, C-07, §5.3

**Observation.** K-12 maps error *categories* to exit codes, but several C-07 cases fit none of them or more than one: `tooManyKeys` (an oversized `sort --in` file: usage 2 or format 4?), `allocationFailed`, `bufferTooSmall`, and `keyTypeMismatch`.

**Recommended resolution.** Replace the prose with a table giving each C-07 case and CLI condition its exit code. Suggested:

| Condition | Exit |
| --------- | ---: |
| `invalidParameters` | 2 |
| `noMetalDevice`, `unsupportedDevice`, `shaderLibraryMissing`, `shaderLibraryLoadFailed`, `tunedParametersInvalid` | 3 |
| I/O errors, bad input size, `tooManyKeys` from a file | 4 |
| `allocationFailed`, `gpuExecutionFailed`, `internalInvariantViolated` | 5 |

### F-013 — `tune` verification can blow the K-14 budget

**Severity:** MEDIUM  **Location:** §5.2 `tune`, K-14

**Observation.** Every timed run is "verified". If each verification re-sorts on the CPU, the 16M size alone costs about $336 \times 4 \times 1\,\mathrm{s}$, around 22 minutes, before any GPU time. That is close to the 30-minute K-14 limit.

**Recommended resolution.** Pin that the oracle output is computed once per (distribution, $n$, seed) and that each run is verified by a byte comparison against it. Apply the same rule to `bench`.

### F-014 — Recorded results lack provenance

**Severity:** MEDIUM  **Location:** C-02, §5.2 (bench CSV, tune JSON), T-32, T-34

**Observation.** The project's purpose is to revisit the paper's claims with recorded results. Yet bench rows and tune output carry only `device`. They do not record the `metallib.sha256` stamp, the C-10 entry used, the `gpuqsort` version, or the OS version. A recorded table therefore cannot be tied to the code that produced it.

**Recommended resolution.** Add `gpuqsort_version`, `metallib_sha256`, `tuning_entry` and `os_version` to the bench CSV/JSON, the tune JSON, and `SortReport`. T-28 already pins the exact header, so update it too.

### F-015 — `keyTypeMismatch` is never thrown

**Severity:** LOW  **Location:** C-07, E-11

**Observation.** E-11 says a mismatched `KeyType` is undetectable, but C-07 still declares `case keyTypeMismatch // E-11`.

**Recommended resolution.** Remove the case, or state that it is reserved.

### F-016 — Stale or loose wording (batched)

**Severity:** LOW

- **R-23** still excludes "compiling shaders", which no longer happens after D-05.
- **K-03:** $\mathit{minseq}^{\uparrow}$ equals $\mathit{minseq}$ because $\mathit{minseq}$ is already a power of two. Drop the notation.
- **K-04:** state the clamp order (clamp $T$ first, then $\mathit{minseq}$ against K-03, which depends on $T$).
- **T-17** is a recorded inspection but lacks the `*(recorded)*` marker.
- **T-36** relies on an `OUT_DIR` override that C-09 never defines.
- **C-08:** `bucket` computes a block $B$ it never uses (see F-009).
- **§5.2 `info`:** the human output lists the tuning entry and stamp, while `--json` is only `DeviceLimits` (T-30). Make them match.

### F-017 — Lifecycle diagram and table omit two failure transitions

**Severity:** LOW  **Location:** §3.1

**Observation.**
- E-10 read-back violations happen in PhaseOne, but only PhaseTwo → Failed is labelled with E-10.
- Allocating $A$ (E-12) happens in Validating → Encoding, with no failure edge.

**Recommended resolution.** Add `PhaseOne --> Failed : read-back check (E-10)` and `Validating --> Failed : allocation (E-12)` to the diagram and the table.

### F-018 — "Stack depth" counting convention undefined

**Severity:** LOW  **Location:** C-02 `maxStackDepth`, K-08, T-11

**Observation.** The spec doesn't say whether depth counts entries after a push, before a pop, or including the initial sequence. The T-11 bound $\lceil \log_2(\ell/64) \rceil + 2$ is off by one under some readings.

**Recommended resolution.** Define it as "the maximum number of entries on the stack immediately after any push, where the initial push counts as 1".

### F-019 — Minor rationale and semantic gaps (batched)

**Severity:** LOW

- **K-02** says `apple7` is "required for device-memory atomic min/max". Check that against Apple's Metal Feature Set Tables, or drop the rationale; D-01 stands either way.
- **K-09 / [P Thm 2]:** the `inout [K]` API adds a second $4n$ staging buffer, so its space is $3n + c$. State that K-09 applies to the buffer API.
- **C-01:** state that `sort` is synchronous, blocks the calling thread until the GPU finishes, and is not cancellable.

## 5. Requirements Review

The requirements are observable and use normative language throughout. The algorithmic requirements (R-04 … R-15) pin exactly what the paper's algorithm is: count/scan/scatter, one atomic per side, gap fill, buffer alternation, smaller-first stack, alternative sort. Each cites [P].

**Missing:** the intra-threadgroup ordering rule (F-002) and an O-2 definition (F-003).

**Conflicts:** R-03 against the `maxseq = 1` behaviour of R-08 (F-005).

R-22's CLI mirroring depends on an interface that does not exist (F-007).

## 6. Interface and Data-Contract Review

- C-01 through C-11 each pin a shape in a code block.
- C-04 is exact and invertible.
- C-05 and C-06 layouts are explicit, but not compilable as one header for both Swift and MSL (F-008).
- C-08 is precise except for `gaussian` (F-009).
- C-10's schema, lookup, validation and fit are well specified, but its API surface is missing (F-001).
- Serialization of the CLI outputs is pinned: exact CSV header, raw little-endian files.
- **Visual-surface completeness:** n/a. There is no rendered surface. The CLI's machine-readable outputs are pinned, and its human text is free.

## 7. State and Failure Review

The §3.1 lifecycle is complete for success paths and is backed by a normative transitions table. Gaps:
- the empty `done` path (F-006);
- two missing failure edges (F-017).

Failure semantics are defined for every C-07 case. Retry is correctly absent: a sort is not retried, and E-09 keeps the instance usable. Partial completion is explicitly "contents unspecified" after a GPU failure and "untouched" before one (I-006). Cancellation is not addressed (F-019).

## 8. Determinism and Algorithm Review

Output determinism follows from I-001 + I-002, so a single oracle suffices (I-003), and intermediate nondeterminism is explicitly allowed. The following are all pinned: tie handling (equal keys go to the gap), pivot indices (D-11), padding (`0xFFFFFFFF`), splitting (K-06), and `optp` rounding.

Open items:
- the O-2 arithmetic (F-003);
- one test that assumes deterministic intermediate order (F-010).

I checked the numeric claims:
- the `optp` examples (for $n = 2^{20}$: $(64, 512, 256)$; for $n = 2^{24}$: $(256, 1024, 1024)$);
- the MT19937 first output for seed 5489 (3499211612);
- the throughput unit conversion ($n / (t_{\mathrm{ms}} \cdot 10^3)$ Mkeys/s);
- the K-08 depth bound under K-01/K-04 ($\leq 27$).

All are correct.

## 9. Edge-Case Review

The spec covers:
- $n \in \{0, 1\}$ and $n < \mathit{minseq}$;
- all-equal keys and heavy duplication;
- float specials;
- bad buffers and parameters;
- allocation failure, GPU failure, stack overflow;
- concurrency;
- empty children;
- the build and tuning artifacts.

Missing:
- empty `done` (F-006);
- the O-2 overflow (F-003);
- an oversized input file in the CLI (F-012).

## 10. Non-Functional Requirement Review

The performance targets are measurable and honestly scoped:
- K-13 is a SHOULD that is only recorded, with the baseline named;
- K-11 defines the clocks, units and the zero-denominator rule;
- K-14 bounds tuning time.

Space (K-09) is stated but internally inconsistent (F-004). Platform constraints (K-01 … K-04) are precise and queried at runtime rather than assumed.

## 11. Security and Trust-Boundary Review

The scope is appropriate. This is a local library and CLI with no network or secrets. The relevant rules are present: key values never logged (R-22, T-29), input-file size validated (E-15), atomic table writes (E-23). No findings.

## 12. Observability and Provenance Review

`SortReport` gives good per-sort introspection: phase counters, stack depth, times. `--verbose` gives per-iteration traces.

Two gaps:
- recorded benchmark and tuning results are not attributable to a code, metallib or tuning version (F-014);
- the CLI trace depends on a missing hook (F-007).

## 13. Testing and Verification Review

Every I, K and E id has a test.

- **Oracles:** they are independent. The CPU sort is the correctness oracle, the golden hashes come from an independent Python generator, and the fit is checked with hand-computed points. None are self-generated goldens.
- **Instrumentation:** hooks make structural claims (R-09, I-008, K-06) directly checkable, which is well above typical.
- **Defects:**
  - T-10 cannot be built as written (F-010);
  - E-09 is untested (F-011);
  - T-20/T-37/T-38 depend on a missing injection API (F-001);
  - T-11 depends on an undefined counting convention (F-018).
- **Recorded tests** (T-32/T-33/T-34) carry the marker and a presence check.
- **T-33:** its $[12, 24]$ range has no gating id. That is acceptable, but the row should say it reports rather than passes or fails.

## 14. Metrics and Evaluation Review

- Throughput, median and min `wall_ms`, and the K-13 ratio are all defined, with units and a zero rule.
- The `optp` fit is a stated OLS problem with its degenerate cases ($J = 1$, $k < 0$).
- The metrics are measured by the harness, not self-reported by the kernel. The exception is `SortStats`, whose values are cross-checked by instrumented tests.

No findings beyond F-014.

## 15. Traceability Review

§11 has a row for every R, C, I, K and E id and a test for each.

**Defects:**
- E-09 is mapped to the wrong test (F-011).
- O-2 appears in §11 and in D-10's *Affects* cell but is never declared (F-003). The `speccheck` impact walk would treat it as an undeclared id.

§12 *Affects* cells otherwise name only declared ids and are complete against each decision's prose. D-18 could add T-36.

## 16. Internal-Consistency Review

Contradictions found:
- R-03 and K-10 against `maxseq = 1` (F-005);
- K-09 against C-05/C-06 (F-004);
- C-07 `keyTypeMismatch` against E-11 (F-015);
- R-23's shader compilation against D-05 (F-016);
- C-10's placeholder against its own validation (F-001).

Diagrams match their tables except for the two missing failure edges (F-017). The formulas agree with their worked examples.

## 17. Architecture Review

The host/kernel split supports the requirements:
- the host orchestrates phase one and reads back through a dispatch boundary (D-03);
- phase two is GPU-resident;
- the codec, generators, tuner and baselines are separate components.

Two architecture gaps:
- the diagnostics path from library to CLI (F-007);
- the target and header layout needed for SwiftPM plus Metal (F-008).

Neither requires redesign.

## 18. Implementation-Agent Readiness

**NO — MATERIAL QUESTIONS REMAIN.** There are only four questions, and each is answerable with a row or two:

1. How does `tune` (and the test suite) obtain a sorter before a valid tuned table exists, and how is a table injected? (F-001)
2. Which barriers order device-memory accesses within an `lqsort` threadgroup? (F-002)
3. How is the root pivot computed under `minMaxAverage`, and with what overflow-safe formula? (F-003)
4. What happens when `done` is empty? (F-006)

Everything else can be decided safely by the implementer or is a documentation fix.

## 19. Quality Scorecard

| Dimension | Score |
| --------- | ----: |
| Scope clarity | 5 |
| Terminology | 4 |
| Requirement precision | 4 |
| Interface completeness | 4 |
| Visual-surface completeness | n/a |
| Data-contract completeness | 4 |
| State/lifecycle definition | 4 |
| Algorithm precision | 4 |
| Failure semantics | 4 |
| Edge-case coverage | 4 |
| Non-functional requirements | 4 |
| Security specification | 4 |
| Observability/provenance | 3 |
| Testability | 4 |
| Evaluation/metrics | 4 |
| Traceability | 4 |
| Internal consistency | 3 |
| Architecture consistency | 4 |
| Implementation readiness | 3 |

## 20. Remediation Plan

### P0 — Blocking

- **F-001:** add `TuningSource` to C-01; ship a valid bootstrap table (the paper's constants) as `apple-default`; make `tune` independent of the table it writes; update T-20, T-34, T-37 and T-38.
- **F-002:** add R-28 for intra-threadgroup device-memory ordering; extend I-007; add it to T-17's checklist.

### P1 — Important

- **F-003:** define O-2 (root min/max, overflow-safe pivot, child pivots) and add a test.
- **F-004:** restate the K-09 bound from the contract sizes; add `bookkeepingBytes` and assert it.
- **F-005:** reconcile `maxseq = 1` with R-03 and K-10.
- **F-006:** add E-24 for an empty `done`, with a transition row.
- **F-007:** add a diagnostics hook to C-01.
- **F-008:** fix the target layout, add `exclude`, and add the `__METAL_VERSION__`-guarded header.
- **F-009:** pin the `gaussian` operands and their 64-bit sum.
- **F-010:** split T-10 into a deterministic cap test and a phase-two killer test.
- **F-011:** add an E-09 fault-injection test and fix §11.
- **F-012:** replace the exit-code prose with a full mapping table.

### P2 — Improvement

F-013 (oracle computed once), F-014 (provenance fields), F-015, F-016, F-017, F-018, F-019.

## 21. Final Verdict

```text
Specification maturity:
Level 2

Implementation readiness:
READY WITH MINOR FIXES

Primary blocker:
The tuned-parameter table cannot be bootstrapped or injected (F-001), so the required tune workflow and three tests cannot run as specified.

Most important improvement:
Make the Metal memory-ordering rules normative inside a phase-two threadgroup (F-002), not only across threadgroups.
```
