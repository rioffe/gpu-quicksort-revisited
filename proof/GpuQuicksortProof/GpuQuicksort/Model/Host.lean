import GpuQuicksortProof.GpuQuicksort.Spec

/-!
# GpuQuicksortProof.GpuQuicksort.Model.Host
===========================================

Transcription of the host-side decision code: the C-07 error enum and the CLI's exit map
(`Sources/GPUQuicksort/Errors.swift`, `Sources/gpuqsort/Common.swift:50-59`), the parameter
resolver (`Sources/GPUQuicksort/ParameterResolver.swift`), and the validation sequence of
`GPUQuicksort.sort(_:count:keyType:parameters:)` (`Sources/GPUQuicksort/GPUQuicksort.swift:95-122`).
Swift `Int` values here are small (at most 2^40, see `optp`) and are modeled as `Int`/`Nat`
without overflow.

## Correspondence

| Source | Model |
| ------ | ----- |
| `Errors.swift:2-15` `GPUQuicksortError` (12 cases; payloads dropped) | `LibError` |
| `Common.swift:50-59` `CLI.exitCode(for:)` | `cliExitCode` |
| `ParameterResolver.swift:5-9` `optp` | `optpOf`: `1 << min(e, 40)` with the exponent `e = Int(floor(log2(max(x,1)) + 0.5))` an input (**not modeled**: Double `log2`/`floor`; T-20 carries the values) |
| `ParameterResolver.swift:12-17` byte formulas | the spec model's `phaseOneBytes`, `phaseTwoBytes` (identical text) |
| `ParameterResolver.swift:19` `isPow2` | `isPow2S` |
| `ParameterResolver.swift:22-27` `maxT` | `maxTFrom` (the `while` loop from 1024) |
| `ParameterResolver.swift:30-34` `maxMinseq` | `maxMinseqFrom` (the `while` loop from 64) |
| `ParameterResolver.swift:38-72` `resolve` | `resolveT`, `resolveMaxseq`, `resolveMinseq`, `resolveIters`, `resolve` (same checks, same order; the error carries the parameter's name) |
| `GPUQuicksort.swift:98-122` guards of `sort` | `sortEntry` |
| `GPUQuicksort.swift:95-97` lock, `runner.reset`, handler; `110-111`, `113-116` report | not modeled: bookkeeping with no decision (T-06, T-21) |
| `Common.swift:1-49, 60-152`, `main.swift` | not modeled: CLI surfaces (T-27, T-42) |
-/

namespace GpuQuicksort.Model

open GpuQuicksortSpec.GpuQuicksort.Spec (phaseOneBytes phaseTwoBytes)

/-- `Errors.swift:2-15` — the C-07 cases (their String/Int payloads do not affect the exit map). -/
inductive LibError
  | noMetalDevice | unsupportedDevice | shaderLibraryMissing | shaderLibraryLoadFailed
  | tunedParametersInvalid | invalidParameters (param : String) | bufferNotShared | bufferTooSmall
  | tooManyKeys | allocationFailed | gpuExecutionFailed | internalInvariantViolated
deriving DecidableEq, Repr

/-- `Common.swift:51-59` — `CLI.exitCode(for:)`. -/
def cliExitCode : LibError → Nat
  | .invalidParameters _ => 2
  | .noMetalDevice | .unsupportedDevice | .shaderLibraryMissing | .shaderLibraryLoadFailed
  | .tunedParametersInvalid => 3
  | .tooManyKeys => 4
  | .allocationFailed | .gpuExecutionFailed | .internalInvariantViolated | .bufferNotShared
  | .bufferTooSmall => 5

/-! ## The resolver -/

/-- `DeviceLimits` fields the resolver reads. -/
structure Limits where
  maxThreads : Nat
  maxTGMem : Nat

/-- `Parameters` (`Types.swift:22-37`): explicit values or `nil`; `maxPhaseOneIterations` always set. -/
structure Params where
  threads : Option Int
  maxseq : Option Int
  minseq : Option Int
  iterations : Int

/-- `ResolvedParameters`. -/
structure Resolved where
  threads : Nat
  maxseq : Nat
  minseq : Nat
  iterations : Nat
deriving DecidableEq, Repr

/-- `ParameterResolver.swift:8` — `1 << min(e, 40)`, for the exponent e the Double code computes. -/
def optpOf (e : Nat) : Nat := 2 ^ min e 40

/-- `ParameterResolver.swift:19` — `x > 0 && x & (x - 1) == 0`. -/
def isPow2S (x : Int) : Bool := decide (0 < x) && (x.toNat &&& (x.toNat - 1)) == 0

/-- `ParameterResolver.swift:22-27` — the loop condition of `maxT`. -/
def maxTShrinks (l : Limits) (t : Nat) : Bool :=
  decide (32 < t) && (decide (l.maxThreads < t) || decide (l.maxTGMem < phaseOneBytes t) ||
    decide (l.maxTGMem < phaseTwoBytes t 64))

/-- `ParameterResolver.swift:22-27` — `while cond { t /= 2 }`, from t. -/
def maxTFrom (l : Limits) (t : Nat) : Nat :=
  if maxTShrinks l t then maxTFrom l (t / 2) else t
termination_by t
decreasing_by simp [maxTShrinks] at *; omega

/-- `maxT(l)`: the loop from 1024. -/
def maxT (l : Limits) : Nat := maxTFrom l 1024

/-- `ParameterResolver.swift:30-34` — `while phaseTwoBytes(t, m * 2) <= mem { m *= 2 }`, from m. -/
def maxMinseqFrom (t : Nat) (l : Limits) (m : Nat) (hm : 0 < m) : Nat :=
  if h : phaseTwoBytes t (m * 2) ≤ l.maxTGMem then maxMinseqFrom t l (m * 2) (by omega) else m
termination_by l.maxTGMem - m
decreasing_by
  simp only [phaseTwoBytes, GpuQuicksortSpec.GpuQuicksort.Spec.phaseTwoFixedWords] at h
  have : m * 2 ≤ max (2 * t) (m * 2) := Nat.le_max_right _ _
  omega

/-- `maxMinseq(t, l)`: the loop from 64. -/
def maxMinseq (t : Nat) (l : Limits) : Nat := maxMinseqFrom t l 64 (by decide)

/-- `ParameterResolver.swift:40-49` — T: an explicit value is checked (K-04, K-03), a defaulted one
is `optp` clamped into [32, maxT]. -/
def resolveT (p : Params) (eT : Nat) (l : Limits) : Except String Nat :=
  match p.threads with
  | some e =>
    if isPow2S e ∧ 32 ≤ e ∧ e ≤ min 1024 (l.maxThreads : Int) ∧
        phaseOneBytes e.toNat ≤ l.maxTGMem ∧ phaseTwoBytes e.toNat 64 ≤ l.maxTGMem
    then pure e.toNat else throw "threadsPerThreadgroup"
  | none => pure (min (max (optpOf eT) 32) (maxT l))

/-- `ParameterResolver.swift:50-56` — maxseq: explicit in [1, 2^16], or `optp` clamped. -/
def resolveMaxseq (p : Params) (eM : Nat) : Except String Nat :=
  match p.maxseq with
  | some e => if 1 ≤ e ∧ e ≤ 2 ^ 16 then pure e.toNat else throw "maxSequences"
  | none => pure (min (max (optpOf eM) 1) (2 ^ 16))

/-- `ParameterResolver.swift:57-65` — minseq: explicit power of two ≥ 64 within the K-03 bound for
the resolved T, or `optp` clamped into [64, maxMinseq(T)]. -/
def resolveMinseq (p : Params) (eS t : Nat) (l : Limits) : Except String Nat :=
  match p.minseq with
  | some e =>
    if isPow2S e ∧ 64 ≤ e then
      if e ≤ (maxMinseq t l : Int) then pure e.toNat else throw "minSequenceLength"
    else throw "minSequenceLength"
  | none => pure (min (max (optpOf eS) 64) (maxMinseq t l))

/-- `ParameterResolver.swift:66-68` — maxPhaseOneIterations in [1, 1024]. -/
def resolveIters (p : Params) : Except String Nat :=
  if 1 ≤ p.iterations ∧ p.iterations ≤ 1024 then pure p.iterations.toNat else throw "maxPhaseOneIterations"

/-- `ParameterResolver.swift:38-72` — `resolve(n:parameters:tuning:limits:)`: T, then maxseq, then
minseq (bounded by T), then the iteration cap; the first failure throws. `eT`, `eM`, `eS` are the
exponents the Double `optp` computes from n and the C-10 constants. -/
def resolve (p : Params) (eT eM eS : Nat) (l : Limits) : Except String Resolved := do
  let t ← resolveT p eT l
  let maxseq ← resolveMaxseq p eM
  let minseq ← resolveMinseq p eS t l
  let it ← resolveIters p
  pure ⟨t, maxseq, minseq, it⟩

/-! ## Validation in `sort` -/

/-- What `sort` does with its inputs: throw, return early, or run the GPU sort. -/
inductive Entry
  | throws (e : LibError)
  | earlyReturn
  | runs (r : Resolved)
deriving DecidableEq, Repr

/-- `GPUQuicksort.swift:98-122` — the guards of `sort`, in source order: count range (E-08),
parameter resolution (E-05), n ≤ 1 (E-01/E-02), storage mode (E-06), buffer length (E-07), then
`sorter.run`. -/
def sortEntry (count : Int) (maxKeys : Nat) (res : Except String Resolved) (shared : Bool)
    (length : Nat) : Entry :=
  if count < 0 ∨ count > maxKeys then .throws .tooManyKeys
  else match res with
    | .error s => .throws (.invalidParameters s)
    | .ok r =>
      if count ≤ 1 then .earlyReturn
      else if !shared then .throws .bufferNotShared
      else if (length : Int) < 4 * count then .throws .bufferTooSmall
      else .runs r

end GpuQuicksort.Model
