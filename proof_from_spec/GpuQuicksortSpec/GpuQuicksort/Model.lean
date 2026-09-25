import GpuQuicksortSpec.GpuQuicksort.Spec

/-!
# GpuQuicksortSpec.GpuQuicksort.Model
======================================

The **transcription**: `SPEC.md` v0.5's normative tables as pure, total Lean functions. This file
is leg A of the trust boundary — a manual, anchor-by-anchor transcription. The row theorems in
`Theorems.lean` make it *checkable*; nothing makes it *proven*.

## Correspondence table (spec anchor → model element)

| Spec anchor | Model element | Notes |
| ----------- | ------------- | ----- |
| C-04 (int32, float32 codes) | `encI`, `decI`, `encF`, `decF` on `BitVec 32` | exact formulas |
| R-01, C-04 (IEEE 754 `totalOrder`) | `totalLE` | defined independently of the codes, from sign bit and magnitude |
| R-04, R-06 (two-pass partition, gap) | `lowerPart`, `gapPart`, `upperPart`, `partition3` | list-level semantics; the GPU's index arithmetic is not modeled |
| R-14 (median of three) | `med3`, `medianOfThree` | sample indices b, ⌊(b+e)/2⌋, e − 1 (D-11) |
| O-2 (min/max average) | `minMaxPivot` | p = lo + ⌊(hi − lo)/2⌋ |
| R-15 (alternative sort) | `altSort` | pad with 0xFFFFFFFF to a length, sort, take the first ℓ |
| R-03, R-12, R-13 (the sort) | `qsort` | recursive list model; the pivot rule is a parameter |
| R-08, K-06, K-07 (phase-one loop) | `P1`, `p1Step`, `p1Loop` | sequences abstracted to their lengths; children function is a parameter |
| K-06 (splitting) | `blocksFor` | ⌈ℓ / blocksize⌉ threadgroups per sequence |
| §7.2, K-12, C-07 (exit codes) | `Failure`, `exitCode` | one constructor per §7.2 condition |
| §3.1 (lifecycle table) | `St`, `Facts`, `rows`, `applicable` | one row per transition-table line, guards as written |
| C-08 (distributions) | `uniformV`, `bucketV`, `staggeredV`, `paperStaggeredV`, `gaussianV` | value formulas; MT19937 itself is not modeled (T-25 carries it) |
| K-05 (optp) | `optp` | IEEE doubles; checked with `native_decide` |
| K-04 (clamping) | `clampPow2`, `isPow2` | defaulted values only |
| K-01 (index arithmetic) | stated directly in `Theorems.lean` | no model element needed |
| §4 C-01..C-03, C-05, C-06, C-09..C-11 | not modeled | API, layouts and packaging: no finite behavior table; §9 tests carry them |
| §5 CLI surfaces, R-18..R-27 | not modeled beyond the exit map | process-level; §9 tests carry them |
| R-04, R-09 (threads, prefix sums, atomic reservations) | `ParallelPartition.lean` | per-thread counts, exclusive scan, one fetch-and-add per side per block, in any atomic order |
| R-13, I-008 (explicit stack, exactly-once finalization) | `PhaseTwo.lean` | stack machine over (start, contents) segments; finalized (position, value) writes |
| R-15 (bitonic network) | `Bitonic.lean` | the kernel's `k`/`j` loops with its own `i ^ j` and `i & k` |
| R-05, R-07, R-10, R-28, I-007 | not modeled | memory-access pattern, buffer ping-pong and GPU memory ordering; T-13..T-17 carry them |
| K-02, K-11, K-13, K-14 | not modeled | platform, timing and performance |
-/

namespace GpuQuicksortSpec.GpuQuicksort.Model

open GpuQuicksortSpec.GpuQuicksort.Spec

/-! ## C-04 key codes -/

/-- C-04 — `int32` encode: u = b XOR 0x8000_0000. -/
@[grind unfold] def encI (b : BitVec 32) : BitVec 32 := b ^^^ signMask
/-- C-04 — `int32` decode: b = u XOR 0x8000_0000. -/
@[grind unfold] def decI (u : BitVec 32) : BitVec 32 := u ^^^ signMask
/-- C-04 — `float32` encode: u = (b & 0x8000_0000) ? ~b : b XOR 0x8000_0000. -/
@[grind unfold] def encF (b : BitVec 32) : BitVec 32 := if b.msb then ~~~b else b ^^^ signMask
/-- C-04 — `float32` decode: b = (u & 0x8000_0000) ? u XOR 0x8000_0000 : ~u. -/
@[grind unfold] def decF (u : BitVec 32) : BitVec 32 := if u.msb then u ^^^ signMask else ~~~u

/-- R-01, C-04 — IEEE 754-2008 `totalOrder` on binary32 bit patterns, defined without the
codes: negative (sign bit set) before positive; two non-negatives in unsigned order of their bits;
two negatives in *reverse* unsigned order (a larger magnitude, or a larger NaN payload, is more
negative). -/
@[grind unfold] def totalLE (a b : BitVec 32) : Bool :=
  match a.msb, b.msb with
  | true, false => true
  | false, true => false
  | false, false => a.ule b
  | true, true => b.ule a

/-! ## R-04, R-06: one partition step (list semantics) -/

/-- R-04 — the elements a partition sends below the pivot. -/
@[grind unfold] def lowerPart (p : Nat) (xs : List Nat) : List Nat := xs.filter (fun x => decide (x < p))
/-- R-04 — the elements a partition sends above the pivot. -/
@[grind unfold] def upperPart (p : Nat) (xs : List Nat) : List Nat := xs.filter (fun x => decide (p < x))
/-- R-06 — the gap: "the gap [s + L, e − G) MUST be filled with p" — one copy of p for
every pivot-equal element, which pass 2 does not write (R-04). -/
@[grind unfold] def gapPart (p : Nat) (xs : List Nat) : List Nat := List.replicate (xs.count p) p
/-- R-04, R-06 — the partition's result in index order: lower part, gap, upper part. -/
@[grind unfold] def partition3 (p : Nat) (xs : List Nat) : List Nat :=
  lowerPart p xs ++ gapPart p xs ++ upperPart p xs

/-! ## Pivot rules -/

/-- R-14 — the median of three values. -/
@[grind unfold] def med3 (a b c : Nat) : Nat := max (min a b) (min (max a b) c)

/-- R-14, D-11 — median of s_b, s_⌊(b+e)/2⌋ and s_(e−1), for the list holding [b, e)
(so b = 0, e = length). An empty list has no pivot; 0 is returned and never used. -/
@[grind unfold] def medianOfThree (xs : List Nat) : Nat :=
  match xs with
  | [] => 0
  | _ :: _ => med3 (xs.getD 0 0) (xs.getD (xs.length / 2) 0) (xs.getD (xs.length - 1) 0)

/-- O-2 — "p = lo + ⌊(hi − lo)/2⌋", computed without overflow. -/
@[grind unfold] def minMaxPivot (lo hi : Nat) : Nat := lo + (hi - lo) / 2

/-! ## R-15: the alternative sort -/

/-- The sort order on codes used by the reference sort. -/
@[grind unfold] def leB (a b : Nat) : Bool := decide (a ≤ b)

/-- R-15 — the alternative sort: pad the ℓ elements with `0xFFFFFFFF` to `padTo`, sort the
padded array, and write back the first ℓ elements. -/
@[grind unfold] def altSort (padTo : Nat) (xs : List Nat) : List Nat :=
  ((xs ++ List.replicate (padTo - xs.length) 0xFFFFFFFF).mergeSort leB).take xs.length

/-! ## R-03, R-12, R-13: the sort as a recursive list function -/

set_option linter.unusedVariables false in
/-- R-03, R-13, R-15 — the sort: sequences shorter than `S` go to the alternative sort (as
a plain sort); longer ones are partitioned around `piv xs` and both parts recurse. If a pivot
rule ever failed to shrink both parts (which I-005 excludes for the spec's two rules), the model
falls back to the plain sort, so the function is total for *any* pivot rule (E-13).
(The unused-variable lint cannot see that `h` is used by `decreasing_by`, hence the option above.) -/
def qsort (piv : List Nat → Nat) (S : Nat) (xs : List Nat) : List Nat :=
  if xs.length < S then xs.mergeSort leB
  else
    let p := piv xs
    if h : (lowerPart p xs).length < xs.length ∧ (upperPart p xs).length < xs.length then
      qsort piv S (lowerPart p xs) ++ gapPart p xs ++ qsort piv S (upperPart p xs)
    else xs.mergeSort leB
termination_by xs.length
decreasing_by
  · exact h.1
  · exact h.2

/-! ## R-08, K-06, K-07: the phase-one host loop over sequence lengths -/

/-- R-08 — the host loop's state: live sequences (`work`), finished ones (`done`), the
iteration counter and the cap flag (K-07). Sequences are represented by their lengths. -/
structure P1 where
  work : List Nat
  done : List Nat
  iterations : Nat
  capReached : Bool
deriving DecidableEq, Repr

/-- R-08, E-17 — one iteration: every work sequence is replaced by its non-empty children
(`children`), and each child goes to `done` if shorter than `minlength`, else to `work`. -/
def p1Step (children : Nat → List Nat) (minlength : Nat) (st : P1) : P1 :=
  let kids := (st.work.flatMap children).filter (fun c => decide (0 < c))
  { work := kids.filter (fun c => decide (minlength ≤ c)),
    done := st.done ++ kids.filter (fun c => decide (c < minlength)),
    iterations := st.iterations + 1, capReached := st.capReached }

/-- R-08, K-07 — the loop: while `work` is non-empty and |work| + |done| < M, stop with the
cap flag if `maxIter` iterations have run, else take a step. `fuel` bounds the recursion; the
loop condition is re-checked at every step. -/
def p1Loop (children : Nat → List Nat) (minlength M maxIter : Nat) : Nat → P1 → P1
  | 0, st => st
  | fuel + 1, st =>
    if st.work ≠ [] ∧ st.work.length + st.done.length < M then
      if st.iterations = maxIter then { st with capReached := true }
      else p1Loop children minlength M maxIter fuel (p1Step children minlength st)
    else st

/-- K-06 — threadgroups for one sequence of length ℓ: ⌈ℓ / blocksize⌉. -/
@[grind unfold] def blocksFor (blocksize l : Nat) : Nat := (l + blocksize - 1) / blocksize

/-! ## §7.2, K-12, C-07: exit codes -/

/-- §7.2 — every condition the exit-code table names, one constructor per condition. The
first eleven are the C-07 error cases as they reach the CLI; the rest are CLI conditions. -/
inductive Failure
  | success
  | verificationFailed
  | argumentParsing
  | invalidParameters
  | sizeAboveMaxKeys
  | debugBuildWithoutAllowDebug
  | noMetalDevice
  | unsupportedDevice
  | shaderLibraryMissing
  | shaderLibraryLoadFailed
  | tunedParametersInvalid
  | fileIO
  | inputSizeNotMultipleOf4
  | inputFileTooManyKeys
  | tableWriteFailure
  | invalidTableOnWrite
  | allocationFailed
  | gpuExecutionFailed
  | internalInvariantViolated
  | bufferNotShared
  | bufferTooSmall
deriving DecidableEq, Repr

/-- §7.2 — the exit-code table, row by row. -/
@[grind unfold] def exitCode : Failure → Nat
  | .success => exitSuccess
  | .verificationFailed => exitVerify
  | .argumentParsing | .invalidParameters | .sizeAboveMaxKeys | .debugBuildWithoutAllowDebug => exitUsage
  | .noMetalDevice | .unsupportedDevice | .shaderLibraryMissing | .shaderLibraryLoadFailed
  | .tunedParametersInvalid => exitEnvironment
  | .fileIO | .inputSizeNotMultipleOf4 | .inputFileTooManyKeys | .tableWriteFailure
  | .invalidTableOnWrite => exitIO
  | .allocationFailed | .gpuExecutionFailed | .internalInvariantViolated | .bufferNotShared
  | .bufferTooSmall => exitGPU

/-- C-07 — the library's error cases, as the CLI can observe them. -/
@[grind unfold] def c07Cases : List Failure :=
  [.noMetalDevice, .unsupportedDevice, .shaderLibraryMissing, .shaderLibraryLoadFailed,
   .tunedParametersInvalid, .invalidParameters, .bufferNotShared, .bufferTooSmall,
   .inputFileTooManyKeys, .allocationFailed, .gpuExecutionFailed, .internalInvariantViolated]

/-- Every constructor of `Failure`, for the exhaustiveness theorems. -/
@[grind unfold] def allFailures : List Failure :=
  [.success, .verificationFailed, .argumentParsing, .invalidParameters, .sizeAboveMaxKeys,
   .debugBuildWithoutAllowDebug, .noMetalDevice, .unsupportedDevice, .shaderLibraryMissing,
   .shaderLibraryLoadFailed, .tunedParametersInvalid, .fileIO, .inputSizeNotMultipleOf4,
   .inputFileTooManyKeys, .tableWriteFailure, .invalidTableOnWrite, .allocationFailed,
   .gpuExecutionFailed, .internalInvariantViolated, .bufferNotShared, .bufferTooSmall]

/-! ## §3.1: the sort-call lifecycle -/

/-- §3.1 — the lifecycle states. -/
inductive St
  | validating | encoding | phaseOne | phaseTwo | decoding | done | failed
deriving DecidableEq, Repr

/-- §3.1 — the facts the transition table's guards read. -/
structure Facts where
  n : Nat
  minseq : Nat
  inputsValid : Bool      -- parameters and buffer pass validation
  allocationOk : Bool     -- A and the descriptor buffers were obtained
  loopContinues : Bool    -- the R-08 loop condition holds and iterations < K-07
  doneEmpty : Bool        -- `done` is empty after merging (E-24)
  gpuError : Bool         -- a command buffer ended in `.error`, or a kernel error flag (E-09, E-10)
  readBackOk : Bool       -- the phase-one read-back checks pass (E-10)
deriving DecidableEq, Repr

/-- §3.1 — one row of the transition table: from-state, guard, to-state. The guards are
transcribed as written; the table states no precedence between rows. -/
structure Row where
  src : St
  guard : Facts → Bool
  dst : St

/-- §3.1 — the transition table, one element per table line (plus the "any GPU state" line
expanded to the four GPU states). -/
def rows : List Row :=
  [ ⟨.validating, fun f => !f.inputsValid, .failed⟩,
    ⟨.validating, fun f => decide (f.n ≤ 1), .done⟩,
    ⟨.validating, fun f => f.inputsValid && decide (2 ≤ f.n), .encoding⟩,
    ⟨.validating, fun f => !f.allocationOk, .failed⟩,
    ⟨.encoding, fun f => decide (f.n < f.minseq), .phaseTwo⟩,
    ⟨.encoding, fun f => decide (f.minseq ≤ f.n), .phaseOne⟩,
    ⟨.phaseOne, fun f => f.loopContinues, .phaseOne⟩,
    ⟨.phaseOne, fun f => !f.loopContinues && !f.doneEmpty, .phaseTwo⟩,
    ⟨.phaseOne, fun f => !f.loopContinues && f.doneEmpty, .decoding⟩,
    ⟨.phaseOne, fun f => !f.readBackOk, .failed⟩,
    ⟨.phaseTwo, fun f => !f.gpuError, .decoding⟩,
    ⟨.encoding, fun f => f.gpuError, .failed⟩,
    ⟨.phaseOne, fun f => f.gpuError, .failed⟩,
    ⟨.phaseTwo, fun f => f.gpuError, .failed⟩,
    ⟨.decoding, fun f => f.gpuError, .failed⟩,
    ⟨.decoding, fun _ => true, .done⟩ ]

/-- §3.1 — the states a state may move to under the given facts (every applicable row). -/
def applicable (s : St) (f : Facts) : List St :=
  (rows.filter (fun r => decide (r.src = s) && r.guard f)).map (·.dst)

/-! ## C-08: the distribution value formulas (MT19937 draws abstracted to `r`) -/

/-- C-08 — `uniform`: U(0, 2^31) = r mod 2^31. -/
@[grind unfold] def uniformV (r : Nat) : Nat := r % 2 ^ 31
/-- C-08 — `bucket`: section S = ⌊k p² / n⌋ mod p; v = S w + (r mod w). -/
@[grind unfold] def bucketV (k n r : Nat) : Nat := (k * distP * distP / n % distP) * distW + r % distW
/-- C-08, D-07 — `staggered` as the spec defines it: block i = ⌊k p / n⌋, 0-based;
i < p/2 → (2i + 1) w + (r mod w), else (2i − p) w + (r mod w). -/
@[grind unfold] def staggeredV (k n r : Nat) : Nat :=
  let i := k * distP / n
  if i < distP / 2 then (2 * i + 1) * distW + r % distW else (2 * i - distP) * distW + r % distW
/-- D-07 — the staggered formula with the paper's condition i ≤ ⌊p/2⌋ (the reading D-07
rejected), for the witness that it leaves [0, 2^31). -/
@[grind unfold] def paperStaggeredV (i r : Nat) : Nat :=
  if i ≤ distP / 2 then (2 * i + 1) * distW + r % distW else (2 * i - distP) * distW + r % distW
/-- C-08 — `gaussian`: ⌊(u₁ + u₂ + u₃ + u₄) / 4⌋ of four `uniform` values. -/
@[grind unfold] def gaussianV (r1 r2 r3 r4 : Nat) : Nat :=
  (uniformV r1 + uniformV r2 + uniformV r3 + uniformV r4) / 4

/-! ## K-04, K-05: parameters -/

/-- K-05 — optp(s, k, m) = 2^⌊log₂(s k + m) + 0.5⌋, in IEEE doubles as the implementation
computes it. -/
def optp (s : Nat) (k m : Float) : Nat :=
  2 ^ (Float.floor (Float.log2 (s.toFloat * k + m) + 0.5)).toUInt64.toNat

/-- K-04 — x is a power of two. -/
def isPow2 (x : Nat) : Prop := ∃ e, x = 2 ^ e

/-- K-04 — clamp a defaulted power of two into [lo, hi]. -/
@[grind unfold] def clampPow2 (lo hi x : Nat) : Nat := if x < lo then lo else if hi < x then hi else x

end GpuQuicksortSpec.GpuQuicksort.Model
