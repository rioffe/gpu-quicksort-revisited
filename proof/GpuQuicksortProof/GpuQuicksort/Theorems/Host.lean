import GpuQuicksortProof.GpuQuicksort.Spec
import GpuQuicksortProof.GpuQuicksort.Model.Host

/-!
# GpuQuicksortProof.GpuQuicksort.Theorems.Host
==============================================

The host's decision code against the spec: the CLI exit map equals §7.2 on every C-07 case;
`resolve` only ever returns K-04-valid parameters that fit K-03, clamps exactly the defaulted
values (to the spec model's `clampPow2`), never clamps an explicit value, and throws on an
explicit invalid one; and `sort` reaches the GPU only with fully valid inputs.
-/

namespace GpuQuicksort.Theorems

open GpuQuicksort.Model
open GpuQuicksortSpec.GpuQuicksort.Spec (phaseOneBytes phaseTwoBytes phaseTwoFixedWords)

/-! ## Exit codes -/

/-- The §7.2 condition each C-07 case is, as the spec model names it. -/
def toFailure : LibError → GpuQuicksortSpec.GpuQuicksort.Model.Failure
  | .noMetalDevice => .noMetalDevice
  | .unsupportedDevice => .unsupportedDevice
  | .shaderLibraryMissing => .shaderLibraryMissing
  | .shaderLibraryLoadFailed => .shaderLibraryLoadFailed
  | .tunedParametersInvalid => .tunedParametersInvalid
  | .invalidParameters _ => .invalidParameters
  | .bufferNotShared => .bufferNotShared
  | .bufferTooSmall => .bufferTooSmall
  | .tooManyKeys => .inputFileTooManyKeys
  | .allocationFailed => .allocationFailed
  | .gpuExecutionFailed => .gpuExecutionFailed
  | .internalInvariantViolated => .internalInvariantViolated

/-- **C-07, K-12** (T-18, T-19, T-27): the CLI's exit map is the §7.2 table on every C-07 case
(any payload), and the enum's twelve cases are exactly the spec's C-07 list. The CLI's own
failure conditions (`CLIExit` sites, argument parsing) are K-12's process side. -/
theorem exitMapIsSpec :
    (∀ e : LibError, cliExitCode e = GpuQuicksortSpec.GpuQuicksort.Model.exitCode (toFailure e)) ∧
    [LibError.noMetalDevice, .unsupportedDevice, .shaderLibraryMissing, .shaderLibraryLoadFailed,
      .tunedParametersInvalid, .invalidParameters "", .bufferNotShared, .bufferTooSmall, .tooManyKeys,
      .allocationFailed, .gpuExecutionFailed, .internalInvariantViolated].map toFailure =
      GpuQuicksortSpec.GpuQuicksort.Model.c07Cases := by
  refine ⟨fun e => ?_, by decide⟩
  cases e <;> rfl

/-! ## Powers of two -/

/-- **(lemma)**: the resolver's bit test `x > 0 && x & (x − 1) == 0` holds exactly for powers of two. -/
theorem isPow2S_iff (x : Int) : isPow2S x = true ↔ 0 < x ∧ ∃ k, x.toNat = 2 ^ k := by
  unfold isPow2S
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
  constructor
  · rintro ⟨hx, hand⟩
    refine ⟨hx, x.toNat.log2, ?_⟩
    have hn : x.toNat ≠ 0 := by omega
    have h1 := Nat.log2_self_le hn
    have h2 := @Nat.lt_log2_self x.toNat
    rcases Nat.lt_or_ge (2 ^ x.toNat.log2) x.toNat with h | h
    · exfalso
      have t1 := Nat.testBit_log2 hn
      have h2' : x.toNat < 2 * 2 ^ x.toNat.log2 := by rw [Nat.pow_succ] at h2; omega
      have t2 := Nat.testBit_of_two_pow_le_and_two_pow_add_one_gt (n := x.toNat - 1)
        (i := x.toNat.log2) (by omega) (by rw [Nat.pow_succ]; omega)
      have := congrArg (fun m => Nat.testBit m x.toNat.log2) hand
      simp only [Nat.testBit_and, t1, t2, Nat.zero_testBit] at this
      exact absurd this (by decide)
    · omega
  · rintro ⟨hx, k, hk⟩
    refine ⟨hx, ?_⟩
    rw [hk, Nat.and_two_pow_sub_one_eq_mod, Nat.mod_self]

/-- A device limit set's fit for T (K-03, K-04's upper bound): the three checks of `maxT`. -/
def fitsT (l : Limits) (t : Nat) : Prop :=
  t ≤ l.maxThreads ∧ phaseOneBytes t ≤ l.maxTGMem ∧ phaseTwoBytes t 64 ≤ l.maxTGMem

theorem p1Mono {a b : Nat} (h : a ≤ b) : phaseOneBytes a ≤ phaseOneBytes b := by
  simp only [phaseOneBytes]; omega

theorem p2Mono {t t' s s' : Nat} (h1 : t ≤ t') (h2 : s ≤ s') : phaseTwoBytes t s ≤ phaseTwoBytes t' s' := by
  simp only [phaseTwoBytes]
  have : max (2 * t) s ≤ max (2 * t') s' := by
    rcases Nat.le_total (2 * t) s with h | h
    · rw [Nat.max_eq_right h]; exact Nat.le_trans h2 (Nat.le_max_right _ _)
    · rw [Nat.max_eq_left h]; exact Nat.le_trans (by omega) (Nat.le_max_left _ _)
  omega

/-- **(lemma)**: `maxT`'s loop, started at 2^k with k ≥ 5, stops at a power of two 2^j with
5 ≤ j ≤ k, which fits the device unless it is the floor 32. -/
theorem maxTFrom_spec (l : Limits) : ∀ k, 5 ≤ k →
    ∃ j, maxTFrom l (2 ^ k) = 2 ^ j ∧ 5 ≤ j ∧ j ≤ k ∧ (2 ^ j = 32 ∨ fitsT l (2 ^ j))
  | k, hk => by
    rw [maxTFrom]
    split
    · next h =>
      simp only [maxTShrinks, Bool.and_eq_true, decide_eq_true_eq] at h
      have hk5 : 5 < k := by
        rcases Nat.lt_or_ge 5 k with h' | h'
        · exact h'
        · have : k = 5 := by omega
          subst this; exact absurd h.1 (by decide)
      obtain ⟨j, e, h1, h2, h3⟩ := maxTFrom_spec l (k - 1) (by omega)
      refine ⟨j, ?_, h1, by omega, h3⟩
      rw [show 2 ^ k / 2 = 2 ^ (k - 1) by
        rw [show k = (k - 1) + 1 by omega, Nat.pow_succ, Nat.mul_div_cancel _ (by decide)]; simp]
      exact e
    · next h =>
      refine ⟨k, rfl, hk, Nat.le_refl _, ?_⟩
      simp only [maxTShrinks, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, not_and,
        not_or, Nat.not_lt] at h
      rcases Nat.lt_or_ge 32 (2 ^ k) with h' | h'
      · have := h h'; exact Or.inr (by simp only [fitsT]; omega)
      · left; have : 2 ^ 5 ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) hk
        simp at this; omega
termination_by k => k

/-- **(lemma)**: `maxT` is a power of two in [32, 1024] that fits every device admitting T = 32. -/
theorem maxT_spec (l : Limits) (hl : fitsT l 32) :
    ∃ j, maxT l = 2 ^ j ∧ 32 ≤ maxT l ∧ maxT l ≤ 1024 ∧ fitsT l (maxT l) := by
  obtain ⟨j, e, h1, h2, h3⟩ := maxTFrom_spec l 10 (by decide)
  have e' : maxT l = 2 ^ j := e
  have lo : 32 ≤ 2 ^ j := by
    have := Nat.pow_le_pow_right (show 0 < 2 by decide) h1; simpa using this
  have hi : 2 ^ j ≤ 1024 := by
    have := Nat.pow_le_pow_right (show 0 < 2 by decide) h2; simpa using this
  refine ⟨j, e', by omega, by omega, ?_⟩
  rw [e']
  rcases h3 with h | h
  · rw [h]; exact hl
  · exact h

/-- **(lemma)**: `maxMinseq`'s loop keeps a power of two ≥ 64 whose K-03 phase-two budget fits. -/
theorem maxMinseqFrom_spec (t : Nat) (l : Limits) :
    ∀ m (hm : 0 < m), (∃ k, m = 2 ^ k) → 64 ≤ m → phaseTwoBytes t m ≤ l.maxTGMem →
      (∃ k, maxMinseqFrom t l m hm = 2 ^ k) ∧ 64 ≤ maxMinseqFrom t l m hm ∧
        phaseTwoBytes t (maxMinseqFrom t l m hm) ≤ l.maxTGMem := by
  intro m hm
  induction m, hm using maxMinseqFrom.induct t l with
  | case1 m hm h ih =>
    intro ⟨k, hk⟩ h64 _
    rw [maxMinseqFrom]; simp only [h, ↓reduceDIte]
    exact ih ⟨k + 1, by rw [hk, Nat.pow_succ]⟩ (by omega) h
  | case2 m hm h =>
    intro hp h64 hb
    rw [maxMinseqFrom]; simp only [h, ↓reduceDIte]
    exact ⟨hp, h64, hb⟩

/-! ## The resolver -/

/-- K-04 and K-03 for resolved parameters on a device. -/
def validFor (l : Limits) (r : Resolved) : Prop :=
  (∃ k, r.threads = 2 ^ k) ∧ 32 ≤ r.threads ∧ r.threads ≤ min 1024 l.maxThreads ∧
  phaseOneBytes r.threads ≤ l.maxTGMem ∧
  1 ≤ r.maxseq ∧ r.maxseq ≤ 2 ^ 16 ∧
  (∃ k, r.minseq = 2 ^ k) ∧ 64 ≤ r.minseq ∧ phaseTwoBytes r.threads r.minseq ≤ l.maxTGMem ∧
  1 ≤ r.iterations ∧ r.iterations ≤ 1024

/-- **(lemma)**: `resolve` succeeds exactly when its four steps do, and returns their values. -/
theorem resolve_ok (p : Params) (eT eM eS : Nat) (l : Limits) (r : Resolved) :
    resolve p eT eM eS l = .ok r ↔
      resolveT p eT l = .ok r.threads ∧ resolveMaxseq p eM = .ok r.maxseq ∧
      resolveMinseq p eS r.threads l = .ok r.minseq ∧ resolveIters p = .ok r.iterations := by
  unfold resolve
  cases h1 : resolveT p eT l <;> cases h2 : resolveMaxseq p eM <;>
    simp only [bind, Except.bind, pure, Except.pure, reduceCtorEq, false_iff, not_and, false_and,
      Except.ok.injEq] <;> try (intro h; cases h)
  all_goals first
    | (intro h; exact absurd h (by simp))
    | skip
  all_goals (rename_i t m; cases h3 : resolveMinseq p eS t l <;> cases h4 : resolveIters p <;>
    simp only [reduceCtorEq, Except.ok.injEq, false_iff, not_and] <;>
    first
      | (constructor
         · rintro rfl; exact ⟨rfl, rfl, h3, rfl⟩
         · rintro ⟨e1, e2, e3, e4⟩; cases r; simp_all)
      | (intro e1 e2 e3; subst e1; subst e2; simp_all)
      | (intro e1 e2; subst e1; subst e2; simp_all)
      | skip)

theorem powMinMax (x lo hi : Nat) (hx : ∃ k, x = 2 ^ k) (hlo : ∃ k, lo = 2 ^ k) (hhi : ∃ k, hi = 2 ^ k) :
    ∃ k, min (max x lo) hi = 2 ^ k := by
  rcases Nat.le_total x lo with h | h
  · rw [Nat.max_eq_right h]; rcases Nat.le_total lo hi with h' | h'
    · rw [Nat.min_eq_left h']; exact hlo
    · rw [Nat.min_eq_right h']; exact hhi
  · rw [Nat.max_eq_left h]; rcases Nat.le_total x hi with h' | h'
    · rw [Nat.min_eq_left h']; exact hx
    · rw [Nat.min_eq_right h']; exact hhi

theorem resolveT_spec (p : Params) (eT : Nat) (l : Limits) (hl : fitsT l 32) (t : Nat)
    (h : resolveT p eT l = .ok t) :
    (∃ k, t = 2 ^ k) ∧ 32 ≤ t ∧ t ≤ min 1024 l.maxThreads ∧ fitsT l t := by
  unfold resolveT at h
  split at h
  · next e _ =>
    split at h
    · next hc =>
      simp only [pure, Except.pure, Except.ok.injEq] at h; subst h
      obtain ⟨hp, h1, h2, h3, h4⟩ := hc
      obtain ⟨_, k, hk⟩ := (isPow2S_iff e).1 hp
      refine ⟨⟨k, hk⟩, by omega, ?_, ?_, h3, h4⟩
      · have : e ≤ (1024 : Int) ∧ e ≤ (l.maxThreads : Int) := by
          constructor <;> omega
        omega
      · omega
    · simp [throw, throwThe, MonadExceptOf.throw] at h
  · simp only [pure, Except.pure, Except.ok.injEq] at h; subst h
    obtain ⟨j, ej, lo, hi, fit⟩ := maxT_spec l hl
    refine ⟨powMinMax _ _ _ ⟨_, rfl⟩ ⟨5, rfl⟩ ⟨j, ej⟩, ?_, ?_, ?_⟩
    · have := Nat.le_max_right (optpOf eT) 32; omega
    · have := Nat.min_le_right (max (optpOf eT) 32) (maxT l)
      have := fit.1; omega
    · have hle := Nat.min_le_right (max (optpOf eT) 32) (maxT l)
      exact ⟨Nat.le_trans hle fit.1, Nat.le_trans (p1Mono hle) fit.2.1,
        Nat.le_trans (p2Mono hle (Nat.le_refl _)) fit.2.2⟩

theorem resolveMinseq_spec (p : Params) (eS t : Nat) (l : Limits) (ht : fitsT l t) (s : Nat)
    (h : resolveMinseq p eS t l = .ok s) :
    (∃ k, s = 2 ^ k) ∧ 64 ≤ s ∧ phaseTwoBytes t s ≤ l.maxTGMem := by
  obtain ⟨hk, h64, hb⟩ := maxMinseqFrom_spec t l 64 (by decide) ⟨6, rfl⟩ (Nat.le_refl _) ht.2.2
  have hM : maxMinseq t l = maxMinseqFrom t l 64 (by decide) := rfl
  unfold resolveMinseq at h
  split at h
  · next e _ =>
    split at h
    · next hc =>
      split at h
      · next hle =>
        simp only [pure, Except.pure, Except.ok.injEq] at h; subst h
        obtain ⟨_, k, hk'⟩ := (isPow2S_iff e).1 hc.1
        refine ⟨⟨k, hk'⟩, by omega, Nat.le_trans (p2Mono (Nat.le_refl _) (by omega)) (hM ▸ hb)⟩
      · simp [throw, throwThe, MonadExceptOf.throw] at h
    · simp [throw, throwThe, MonadExceptOf.throw] at h
  · simp only [pure, Except.pure, Except.ok.injEq] at h; subst h
    rw [← hM] at hk h64 hb
    refine ⟨powMinMax _ _ _ ⟨_, rfl⟩ ⟨6, rfl⟩ hk, ?_, ?_⟩
    · have := Nat.le_max_right (optpOf eS) 64
      have := Nat.le_min.2 ⟨this, h64⟩
      exact Nat.le_trans (Nat.le_min.2 ⟨Nat.le_max_right _ _, h64⟩) (Nat.le_refl _)
    · exact Nat.le_trans (p2Mono (Nat.le_refl _) (Nat.min_le_right _ _)) hb

/-- **K-04, K-03** (T-03, T-18, T-20): on any device that admits T = 32, every set of parameters
`resolve` returns is valid: T a power of two in [32, min(1024, maxThreadsPerThreadgroup)] within
the phase-one memory budget, maxseq ∈ [1, 2^16], minseq a power of two ≥ 64 within the phase-two
budget for that T, and the iteration cap in [1, 1024] — whatever the explicit values, the tuning
constants and the (opaque) `optp` exponents. -/
theorem resolveValid (p : Params) (eT eM eS : Nat) (l : Limits) (hl : fitsT l 32) (r : Resolved)
    (h : resolve p eT eM eS l = .ok r) : validFor l r := by
  obtain ⟨h1, h2, h3, h4⟩ := (resolve_ok p eT eM eS l r).1 h
  obtain ⟨tp, t32, tle, tfit⟩ := resolveT_spec p eT l hl _ h1
  obtain ⟨sp, s64, sfit⟩ := resolveMinseq_spec p eS _ l tfit _ h3
  have hm : 1 ≤ r.maxseq ∧ r.maxseq ≤ 2 ^ 16 := by
    unfold resolveMaxseq at h2
    split at h2
    · split at h2
      · simp only [pure, Except.pure, Except.ok.injEq] at h2; rw [← h2]; omega
      · simp [throw, throwThe, MonadExceptOf.throw] at h2
    · simp only [pure, Except.pure, Except.ok.injEq] at h2; rw [← h2]
      have := Nat.le_max_right (optpOf eM) 1
      exact ⟨Nat.le_min.2 ⟨this, by decide⟩, Nat.min_le_right _ _⟩
  have hi : 1 ≤ r.iterations ∧ r.iterations ≤ 1024 := by
    unfold resolveIters at h4
    split at h4
    · simp only [pure, Except.pure, Except.ok.injEq] at h4; rw [← h4]; omega
    · simp [throw, throwThe, MonadExceptOf.throw] at h4
  exact ⟨tp, t32, tle, tfit.2.1, hm.1, hm.2, sp, s64, sfit, hi.1, hi.2⟩

/-- **R-16** (T-03, T-20): with no explicit values and a valid iteration cap, `resolve` never
throws, and each default is its `optp` value clamped (the spec model's `clampPow2`): T into
[32, maxT], then maxseq into [1, 2^16], then minseq into [64, maxMinseq(T)] — the K-04 order,
with minseq's bound taken from the T just resolved. -/
theorem resolveDefaults (p : Params) (eT eM eS : Nat) (l : Limits) (hl : fitsT l 32)
    (ht : p.threads = none) (hm : p.maxseq = none) (hs : p.minseq = none)
    (hi : 1 ≤ p.iterations ∧ p.iterations ≤ 1024) :
    ∃ r, resolve p eT eM eS l = .ok r ∧
      r.threads = GpuQuicksortSpec.GpuQuicksort.Model.clampPow2 32 (maxT l) (optpOf eT) ∧
      r.maxseq = GpuQuicksortSpec.GpuQuicksort.Model.clampPow2 1 (2 ^ 16) (optpOf eM) ∧
      r.minseq = GpuQuicksortSpec.GpuQuicksort.Model.clampPow2 64 (maxMinseq r.threads l) (optpOf eS) := by
  obtain ⟨_, _, lo, _, _⟩ := maxT_spec l hl
  have clamp : ∀ lo hi x : Nat, lo ≤ hi →
      min (max x lo) hi = GpuQuicksortSpec.GpuQuicksort.Model.clampPow2 lo hi x := by
    intro lo hi x h; simp only [GpuQuicksortSpec.GpuQuicksort.Model.clampPow2]
    (repeat' split) <;> omega
  let t := min (max (optpOf eT) 32) (maxT l)
  have tfit := (resolveT_spec p eT l hl t (by simp [resolveT, ht, pure, Except.pure, t])).2.2.2
  obtain ⟨_, m64, _⟩ := maxMinseqFrom_spec t l 64 (by decide) ⟨6, rfl⟩ (Nat.le_refl _) tfit.2.2
  refine ⟨⟨t, min (max (optpOf eM) 1) (2 ^ 16), min (max (optpOf eS) 64) (maxMinseq t l),
    p.iterations.toNat⟩, ?_, clamp _ _ _ lo, clamp _ _ _ (by decide), clamp _ _ _ m64⟩
  simp [resolve, resolveT, resolveMaxseq, resolveMinseq, resolveIters, ht, hm, hs, hi, bind,
    Except.bind, pure, Except.pure, t]

/-- **E-05** (T-18): an explicit value is never clamped — if `resolve` succeeds, every explicit
T, maxseq and minseq comes back exactly as given — and an explicit T or maxseq outside its K-04
range, an explicit minseq that is not a power of two ≥ 64 or exceeds its K-03 bound, or an
iteration cap outside [1, 1024], makes `resolve` throw `invalidParameters`. -/
theorem resolveExplicit (p : Params) (eT eM eS : Nat) (l : Limits) :
    (∀ r, resolve p eT eM eS l = .ok r →
      (∀ e, p.threads = some e → (r.threads : Int) = e) ∧
      (∀ e, p.maxseq = some e → (r.maxseq : Int) = e) ∧
      (∀ e, p.minseq = some e → (r.minseq : Int) = e)) ∧
    (∀ e, p.threads = some e → ¬ (isPow2S e ∧ 32 ≤ e ∧ e ≤ min 1024 (l.maxThreads : Int) ∧
        phaseOneBytes e.toNat ≤ l.maxTGMem ∧ phaseTwoBytes e.toNat 64 ≤ l.maxTGMem) →
      ∃ s, resolve p eT eM eS l = .error s) ∧
    (∀ e, p.maxseq = some e → ¬ (1 ≤ e ∧ e ≤ 2 ^ 16) → ∃ s, resolve p eT eM eS l = .error s) ∧
    (∀ e, p.minseq = some e → ¬ (isPow2S e ∧ 64 ≤ e) → ∃ s, resolve p eT eM eS l = .error s) ∧
    (¬ (1 ≤ p.iterations ∧ p.iterations ≤ 1024) → ∃ s, resolve p eT eM eS l = .error s) := by
  -- a step that cannot succeed makes `resolve` throw
  have fails : (∀ r : Resolved, ¬ (resolveT p eT l = .ok r.threads ∧ resolveMaxseq p eM = .ok r.maxseq ∧
      resolveMinseq p eS r.threads l = .ok r.minseq ∧ resolveIters p = .ok r.iterations)) →
      ∃ s, resolve p eT eM eS l = .error s := by
    intro h
    cases hr : resolve p eT eM eS l with
    | error s => exact ⟨s, rfl⟩
    | ok r => exact absurd ((resolve_ok p eT eM eS l r).1 hr) (h r)
  have noOk : ∀ {x : Except String Nat} {v : Nat}, (∃ s, x = .error s) → x ≠ .ok v := by
    rintro x v ⟨s, rfl⟩ h; cases h
  refine ⟨fun r h => ?_,
    fun e he hbad => fails fun r ⟨h1, _⟩ => noOk ⟨"threadsPerThreadgroup", by
      simp only [resolveT, he, hbad, ↓reduceIte]; rfl⟩ h1,
    fun e he hbad => fails fun r ⟨_, h2, _⟩ => noOk ⟨"maxSequences", by
      simp only [resolveMaxseq, he, hbad, ↓reduceIte]; rfl⟩ h2,
    fun e he hbad => fails fun r ⟨_, _, h3, _⟩ => noOk ⟨"minSequenceLength", by
      simp only [resolveMinseq, he, hbad, ↓reduceIte]; rfl⟩ h3,
    fun hbad => fails fun r ⟨_, _, _, h4⟩ => noOk ⟨"maxPhaseOneIterations", by
      simp only [resolveIters, hbad, ↓reduceIte]; rfl⟩ h4⟩
  · obtain ⟨h1, h2, h3, _⟩ := (resolve_ok p eT eM eS l r).1 h
    refine ⟨fun e he => ?_, fun e he => ?_, fun e he => ?_⟩
    · simp only [resolveT, he] at h1
      split at h1
      · simp only [pure, Except.pure, Except.ok.injEq] at h1; rw [← h1]; omega
      · simp [throw, throwThe, MonadExceptOf.throw] at h1
    · simp only [resolveMaxseq, he] at h2
      split at h2
      · simp only [pure, Except.pure, Except.ok.injEq] at h2; rw [← h2]; omega
      · simp [throw, throwThe, MonadExceptOf.throw] at h2
    · simp only [resolveMinseq, he] at h3
      split at h3
      · split at h3
        · simp only [pure, Except.pure, Except.ok.injEq] at h3; rw [← h3]; omega
        · simp [throw, throwThe, MonadExceptOf.throw] at h3
      · simp [throw, throwThe, MonadExceptOf.throw] at h3

/-! ## Validation in `sort` -/

/-- **I-006, E-06, E-07, E-08** (T-18, T-19, T-24): `sort` reaches the GPU (`sorter.run`) exactly
when 0 ≤ count ≤ maxKeys, the parameters resolve, count ≥ 2, the buffer is shared and holds
4·count bytes; every thrown error is thrown before any GPU work, so a failed validation leaves the
buffer untouched. The first failing check decides the error: `tooManyKeys` for a count out of
range (negative included), `invalidParameters` for unresolvable parameters, then `bufferNotShared`,
then `bufferTooSmall`. -/
theorem sortEntrySpec (count : Int) (maxKeys : Nat) (res : Except String Resolved) (shared : Bool)
    (length : Nat) :
    (∀ r, sortEntry count maxKeys res shared length = .runs r ↔
      (0 ≤ count ∧ count ≤ maxKeys ∧ res = .ok r ∧ 2 ≤ count ∧ shared = true ∧ 4 * count ≤ length)) ∧
    ((count < 0 ∨ count > maxKeys) → sortEntry count maxKeys res shared length = .throws .tooManyKeys) ∧
    (∀ s, 0 ≤ count → count ≤ maxKeys → res = .error s →
      sortEntry count maxKeys res shared length = .throws (.invalidParameters s)) ∧
    (∀ r, 2 ≤ count → count ≤ maxKeys → res = .ok r → shared = false →
      sortEntry count maxKeys res shared length = .throws .bufferNotShared) ∧
    (∀ r, 2 ≤ count → count ≤ maxKeys → res = .ok r → shared = true → (length : Int) < 4 * count →
      sortEntry count maxKeys res shared length = .throws .bufferTooSmall) := by
  refine ⟨fun r => ?_, fun h => ?_, fun s h0 h1 h2 => ?_, fun r h0 h1 h2 h3 => ?_,
    fun r h0 h1 h2 h3 h4 => ?_⟩
  · unfold sortEntry
    by_cases hc : count < 0 ∨ count > maxKeys
    · simp only [hc, ↓reduceIte, reduceCtorEq, false_iff]; omega
    · simp only [hc, ↓reduceIte]
      cases res with
      | error s => simp
      | ok r' =>
        simp only
        by_cases h1 : count ≤ 1
        · simp only [h1, ↓reduceIte, reduceCtorEq, false_iff]; omega
        · simp only [h1, ↓reduceIte]
          cases shared
          · simp
          · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
            by_cases h2 : (length : Int) < 4 * count
            · simp only [h2, ↓reduceIte, reduceCtorEq, false_iff]; omega
            · simp only [h2, ↓reduceIte, Entry.runs.injEq, Except.ok.injEq]
              constructor
              · rintro rfl; exact ⟨by omega, by omega, rfl, by omega, trivial, by omega⟩
              · rintro ⟨_, _, h, _⟩; cases h; rfl
  · simp [sortEntry, h]
  · subst h2; simp [sortEntry, show ¬ (count < 0 ∨ count > maxKeys) by omega]
  · subst h2; subst h3
    simp [sortEntry, show ¬ (count < 0 ∨ count > maxKeys) by omega, show ¬ count ≤ 1 by omega]
  · subst h2; subst h3
    simp [sortEntry, show ¬ (count < 0 ∨ count > maxKeys) by omega, show ¬ count ≤ 1 by omega, h4]

/-- **E-01, E-02** (T-06): for n = 0 or 1 with parameters that resolve, `sort` returns early —
no GPU work, no allocation — whatever the buffer's storage mode and length (a zero-length or
private buffer included). With parameters that do not resolve it throws `invalidParameters` even
for n ≤ 1: the order the code fixes for the overlap F-034 reports in the spec's §3.1 table. -/
theorem smallCountEntry (count : Int) (maxKeys : Nat) (shared : Bool) (length : Nat)
    (h0 : 0 ≤ count) (h1 : count ≤ 1) (hk : count ≤ maxKeys) :
    (∀ r, sortEntry count maxKeys (.ok r) shared length = .earlyReturn) ∧
    (∀ s, sortEntry count maxKeys (.error s) shared length = .throws (.invalidParameters s)) := by
  constructor <;> intro _ <;>
    simp [sortEntry, show ¬ (count < 0 ∨ count > maxKeys) by omega, h1]

/-! ## optp -/

/-- **K-05** (T-20): the code's `optp` — `1 << min(Int(floor(log2(max(s·k + m, 1)) + 0.5)), 40)` in
IEEE doubles — reproduces the spec's worked examples for the paper's 8800GTX constants at 1M and 16M
keys, and agrees there with the spec model's formula. These are the values `resolve` clamps
(`resolveDefaults`). Checked by evaluation: `native_decide` trusts Lean's compiled `Float`, which
calls the platform's `log2`, as the Swift code does. -/
theorem optpCodeExamples :
    optpOf (optpExp (2 ^ 20) 0.00001172 53) = 64 ∧ optpOf (optpExp (2 ^ 20) 0.00003748 476) = 512 ∧
    optpOf (optpExp (2 ^ 20) 0.00004685 211) = 256 ∧ optpOf (optpExp (2 ^ 24) 0.00001172 53) = 256 ∧
    optpOf (optpExp (2 ^ 24) 0.00003748 476) = 1024 ∧ optpOf (optpExp (2 ^ 24) 0.00004685 211) = 1024 ∧
    optpOf (optpExp (2 ^ 20) 0.00001172 53) = GpuQuicksortSpec.GpuQuicksort.Model.optp (2 ^ 20) 0.00001172 53 ∧
    optpOf (optpExp (2 ^ 24) 0.00004685 211) = GpuQuicksortSpec.GpuQuicksort.Model.optp (2 ^ 24) 0.00004685 211 := by
  native_decide

end GpuQuicksort.Theorems
