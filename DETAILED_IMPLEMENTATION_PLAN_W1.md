# Detailed implementation plan — W1: Pure oracles

> - **Wave:** W1 of W0–W6 (`IMPLEMENTATION_PLAN.md` §4 item 2).
> - **Spec basis:** `SPEC.md` v0.4 (sha256 `b05ffbd3…63e0`).
> - **Gate:** every oracle the GPU waves compare against exists, and is tested against independent references (Python, hand arithmetic).
> - **Budget:** 450–650 production lines, 7 files.
> - **Depends on:** W0 targets. **Unlocks:** W2/W3 (oracles), W5 (generators, baselines, table).

## 1. Objective and spec obligations

| Id | Obligation | Discharge |
| -- | ---------- | --------- |
| C-04 | order-preserving codec | `KeyCodec` (CPU); the GPU half is in W2 |
| C-08, R-20 | MT19937 plus 7 distributions | `Distributions.swift` |
| K-04, K-05, R-16 | `optp`, clamps and their order | `ParameterResolver` |
| C-10, E-20, E-21 | table parse, validation, lookup, fit, `TuningSource` | `TunedParameters.swift`, bootstrap JSON |
| C-11, R-26 | `qsort`, `std::sort` shims | `CPUBaselines` |
| I-003 oracle | CPUReference = sort codes, then decode | `CPUReference.swift` |

## 2. Entry preconditions

The W0 gate is green.

## 3. Deliverables

- **`KeyCodec.swift`:** `encode(_ bits: UInt32, _ t: KeyType) -> UInt32`, `decode`; the C-04 formulas verbatim.
- **`Distributions.swift`:**
  - `struct MT19937` (`init(seed:)`, `next() -> UInt32`);
  - `enum Distribution: String, CaseIterable { uniform, sorted, zero, bucket, gaussian, staggered, fullrange }`;
  - `generate(_:n:seed:key:) -> [UInt32]` (bit patterns);
  - $\mathrm{U}(a, \mathit{len})$, 64-bit products, gaussian draws $4k..4k+3$.
- **`ParameterResolver.swift`:** `optp(s:k:m:)`; `resolve(n:parameters:tuning:limits:) throws -> ResolvedParameters`; K-03 memory formula; the clamp order $T$, then maxseq, then minseq.
- **`TunedParameters.swift`:** `TuningSource`, `TunedConstants` (with `.paper8800GTX`); `TunedTable` (decode, validate, lookup with one `sameAs` hop, `upserting(entry:asDefault:)`, encode with sorted keys); `fitLine(sizes:values:) -> (k, m)` (OLS, then $k \geq 0$ fallback, $m \geq 1$, the $J = 1$ rule).
- **`Resources/TunedParameters.json`:** the bootstrap table (C-10).
- **`CPUReference.swift`:** `sortedReference(_ bits: [UInt32], _ key: KeyType) -> [UInt32]`.
- **`CPUBaselines/{qsort.c, stdsort.cpp, include/CPUBaselines.h}`:** C-11.
- **`Tests/Fixtures/gen_reference.py`** and **`golden.json`:** an independent MT19937 and C-08 implementation, with SHA-256 per distribution for $n = 1024$, seed 42 (`uint32`).

## 4. Work items

- **W1-01:** T-05 CPU half (round trip on 16 M sampled patterns plus 64 hand-picked floats; monotone under `totalOrder`), then `KeyCodec`.
- **W1-02:** T-25 (the Python-produced goldens plus MT19937(5489) giving 3499211612 first) and T-26 (properties), then `Distributions`. The goldens are produced by running the Python script *before* the Swift generator exists.
- **W1-03:** T-20 (the paper-constants cases $(64, 512, 256)$ and $(256, 1024, 1024)$; clamp order), then `ParameterResolver`.
- **W1-04:** T-37 (loader negatives; fit points $(1,3), (2,5), (3,7)$ give $(2, 1)$; decreasing data; $J = 1$), then `TunedParameters` and the bootstrap JSON. The `init`-level half of T-37 lands in W2.
- **W1-05:** T-39 (the three baselines equal CPUReference over all distributions and keys, $n \in \{0, 1, 2, 1000, 10^6\}$), then `CPUBaselines` and `CPUReference`. The bench-guard half of T-39 lands in W5.

## 5. Test plan

| File | Ids |
| ---- | --- |
| `OracleTests.swift` | T-05 (CPU), T-20, T-25, T-26, T-37 (table), T-39 (baselines) |

## 6. Gate

1. `python3 Tests/Fixtures/gen_reference.py --check` → exit 0 (the fixture reproduces).
2. `swift test --filter "OracleTests|PackagingTests"` → exit 0.

## 7. Traceability

C-04 and C-08 become passing at CPU level; K-04, K-05, C-10 (read and fit), C-11 and R-26 become half (the CLI parts are in W5).

## 8. Traps

- Python's `random` seeds MT19937 with `init_by_array`, not `init_genrand`. Implement `init_genrand` explicitly in the script.
- `gaussian` must use 64-bit sums (F-009).
- `optp` must use `floor(log2(x) + 0.5)` in `Double`; watch exact powers of two.

## 9. Exit and handoff

- **Frozen:** `KeyCodec`, `Distribution.generate`, `ParameterResolver.resolve`, `TunedTable`, `TunedConstants`, `TuningSource`, `CPUReference.sortedReference`, `cpub_*`.
- **Re-run by W2:** gate 2.
