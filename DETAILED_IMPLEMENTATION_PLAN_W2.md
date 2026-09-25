# Detailed implementation plan — W2: API plus phase two (the first end-to-end sorter)

> - **Wave:** W2 of W0–W6 (`IMPLEMENTATION_PLAN.md` §4 item 3).
> - **Spec basis:** `SPEC.md` v0.4 (sha256 `b05ffbd3…63e0`).
> - **Gate:** with $\mathit{maxseq} = 1$ (D-22), `GPUQuicksort.sort` sorts every C-08 distribution of every key type correctly using `lqsort` alone.
> - **Budget:** 550–800 production lines, 6 files.
> - **Depends on:** W0 (`ShaderLibrary`, header), W1 (oracles, resolver, table). **Unlocks:** W3 (the `Sorter` phase-one slot), W4.

## 1. Objective and spec obligations

| Ids | Discharge |
| --- | --------- |
| C-01, C-02, C-03, C-07, R-18, R-21, D-09 | the public API, the report, the lock, errors |
| R-03 (half), R-12..R-15, R-28, K-08, E-13 | `lqsort` kernel plus `Sorter.phaseTwo` |
| R-06, R-07, I-004, I-008 (phase two) | gap fill in $D$, buffer alternation |
| R-17, C-04 (GPU) | `key_encode`/`key_decode` dispatch |
| E-01..E-03, E-05..E-08, E-12, I-006, K-01, K-03, K-09 (aux) | validation and allocation |
| C-10 `init` half, E-20 | `init(device:tuning:)` |

## 2. Entry preconditions

The W1 gate is green.

## 3. Deliverables

- **`GPUQuicksort.swift`** (public, C-01):
  - `init`, `limits`, `tuning`, `metallibSHA256`, `diagnostics` (lock-guarded), and both `sort` overloads;
  - `resolvedParameters`, `version = "0.4.0"`;
  - validation order: count range, buffer mode, buffer length, parameters (I-006).
- **`Sorter.swift`:** per call, encode, then phase one (W3 fills this in; W2 runs only the E-03 and $\mathit{maxseq} = 1$ paths, which are the complete R-03 skip cases), then phase two, then decode. Builds `SortReport`.
- **`BufferPool.swift`:** a cached aux buffer $A$ (grows; reports $4n$); per-sort descriptor buffers sized to the §7.1 terms ($40M$, $32M$, $32M$, $32M$ bytes, plus parameters); `bookkeepingBytes`.
- **`CommandRunner.swift`:** commit, wait, map `.error` to `gpuExecutionFailed` (E-09), accumulate `gpuTime`.
- **MSL `lqsort`** (one threadgroup per `SortSequence`):
  - **Threadgroup scalars:** exactly 8 (`b`, `e`, `src`, `pivot`, `L`, `G`, `sp`, `err`); the stack is `StackEntry[32]` (K-03: $\max(2T, \mathit{minseq}) + 104$ words).
  - **Loop:** pop (thread 0), then a barrier; pivot = median of $s_b$, $s_{\lfloor (b+e)/2 \rfloor}$, $s_{e-1}$ (R-14).
  - **Pass 1:** per-thread `lt`/`gt` counts into `scratch[0..T)` and `scratch[T..2T)`; an in-place exclusive Blelloch scan of both, keeping the totals.
  - **Pass 2:** scatter `<` elements to `dst[b + Lex + j]` and `>` elements to `dst[e - Gtot + Gex + j]`.
  - **Then** `threadgroup_barrier(mem_device|mem_threadgroup)` (R-28a); fill the gap $[b+L, e-G)$ of $D$; barrier.
  - **Children** in `1 - src`: the longer then the shorter pushed if $\geq \mathit{minseq}$ (R-13); each non-empty child below $\mathit{minseq}$ is alternative-sorted cooperatively (load, pad with `0xFFFFFFFF` to a power of two, barrier, bitonic network, barrier, write the first $\ell$ to $D$: R-15, R-28c); a device barrier before the next pop (R-28b).
  - **Overflow:** set `err = 1` and exit (E-10).
  - **Stats:** thread 0 writes `SortStats` (partitions, altSorts, maxDepth per the C-02 convention).
- **MSL `key_encode`/`key_decode`:** grid-stride over $n$.

## 4. Work items

- **W2-01:** API tests (T-06, T-18, T-19, T-37 `init` cases), then `GPUQuicksort` validation and init.
- **W2-02:** T-07 ($n = \mathit{minseq} - 1$), then `lqsort` alternative-sort path, `Sorter.phaseTwo`, codec dispatch.
- **W2-03:** T-01 run with `Parameters(maxSequences: 1)` over the full distribution/key/size matrix, T-04, T-40 ($\mathit{maxseq} = 1$ adversarial inputs, depth $\leq 27$), T-05 (GPU round trip), then the partition path of `lqsort`. T-01 with *default* parameters becomes meaningful in W3.
- **W2-04:** T-09 (duplicates) with $\mathit{maxseq} = 1$.

## 5. Test plan

| File | Ids |
| ---- | --- |
| `APITests.swift` | T-06, T-18, T-19, T-37 (init) |
| `CorrectnessTests.swift` | T-01, T-04, T-05, T-07, T-09, T-40 (with $\mathit{maxseq} = 1$ in W2; T-01 re-parameterized to defaults in W3) |

## 6. Gate

1. `scripts/build-metallib.sh` → exit 0 (the stamp changes; commit it).
2. `swift test --filter "APITests|CorrectnessTests|OracleTests|PackagingTests"` → exit 0.

## 7. Traceability

R-12..R-15, R-28, K-08, E-01..E-03, E-05..E-08, E-12 and E-13 become passing. R-03 and R-17 are half until W3 adds phase one.

## 8. Traps

- Threadgroup memory: the static scalars plus the stack must stay within the K-03 constant of 104 words; the scan runs in place in the dynamic region.
- A device-memory barrier is needed between pass 2 and the gap fill, and before the next pop (R-28). Test at $T = 32$ and $T = 1024$.
- NSLock is not re-entrant: `sort` must read the stored `diagnostics` value directly while holding the lock.

## 9. Exit and handoff

- **Frozen:** `Sorter.run(buffer:count:key:resolved:) throws -> SortReport`, `CommandRunner.run(_ encode: (MTLCommandBuffer) -> Void) throws`, `BufferPool.aux(n:)`.
- **Re-run by W3:** gate 2.
