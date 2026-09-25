import GpuQuicksortProof.GpuQuicksort.Spec
import GpuQuicksortProof.GpuQuicksort.Model.LQSort
import GpuQuicksortProof.GpuQuicksort.Theorems.Codec
import GpuQuicksortProof.GpuQuicksort.Theorems.TGPartition

/-!
# GpuQuicksortProof.GpuQuicksort.Theorems.AltSort
=================================================

The kernel's `altsort` sorts: its threads' "swap unless ordered" rounds are the spec model's
bitonic network (`Bitonic.rnd`, `merge`, `net`) on [0, P), so the write-back puts the sorted
sequence at [b, b + ℓ), each index written once.
-/

namespace GpuQuicksort.Theorems

open GpuQuicksort.Model
open GpuQuicksortSpec.GpuQuicksort.Model (leB)
open GpuQuicksortSpec.GpuQuicksort.Bitonic (rnd merge net padF bitonicAltSort bitonicSorts)

/-- f and g agree on [0, P). -/
def agree (P : Nat) (f g : Nat → Nat) : Prop := ∀ x < P, f x = g x

/-- **(lemma)**: `P = 1; while (P < len) P <<= 1` stops at a power of two ≥ len. -/
theorem padLoopPow (len : Nat) :
    ∀ P (hP : 0 < P), (∃ j, P = 2 ^ j) → ∃ m, padLoop len P hP = 2 ^ m ∧ len ≤ 2 ^ m := by
  intro P hP
  induction P, hP using padLoop.induct len with
  | case1 P hP hlt ih =>
    intro ⟨j, hj⟩
    rw [padLoop]; simp only [hlt, ↓reduceIte]
    exact ih ⟨j + 1, by rw [hj, pow_succ2]⟩
  | case2 P hP hlt =>
    intro ⟨j, hj⟩
    rw [padLoop]; simp only [hlt, ↓reduceIte]
    exact ⟨j, hj, by omega⟩

/-- Membership in one round's writes: the lower index i of a pair below P, when the pair is out of
order for its direction, writes s[ixj] at i and s[i] at ixj. -/
theorem roundMem (T : Nat) (hT : 0 < T) (P k j : Nat) (s : Nat → Nat) (w : Nat × Nat) :
    w ∈ roundWrites T hT P k j s ↔ ∃ i < P, i < i ^^^ j ∧ decide (s i > s (i ^^^ j)) = decide (i &&& k = 0) ∧
      (w = (i, s (i ^^^ j)) ∨ w = (i ^^^ j, s i)) := by
  simp only [roundWrites, List.mem_flatMap, List.mem_range]
  constructor
  · rintro ⟨t, ht, i, hi, hw⟩
    have hiP := (strideMem T P hT i t).1 hi
    split at hw
    · next hlt =>
      split at hw
      · next hc =>
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hw
        exact ⟨i, hiP.2.1, hlt, hc, hw⟩
      · simp at hw
    · simp at hw
  · rintro ⟨i, hi, hlt, hc, hw⟩
    refine ⟨i % T, Nat.mod_lt _ hT, i, ?_, ?_⟩
    · exact (gridMem T P hT i).2 hi |> fun h => by
        rw [strideMem]; refine ⟨Nat.mod_le _ _, hi, ?_⟩
        rw [show i - i % T = T * (i / T) by have := Nat.div_add_mod i T; omega]; exact Nat.mul_mod_right _ _
    · simp only [hlt, ↓reduceIte, hc, List.mem_cons, List.mem_nil_iff, or_false]; exact hw

theorem xorInvol (i j : Nat) : (i ^^^ j) ^^^ j = i := by
  rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]

/-- **(lemma)** (R-15, R-28 for the network): one round of the kernel — each thread, for each
lower index i of its pairs, swaps s[i] and s[i ^ j] unless ordered — leaves at every x < P
exactly what the spec model's comparator round `rnd k j` computes. -/
theorem roundIsRnd (T : Nat) (hT : 0 < T) (m k j : Nat) (hj : j < 2 ^ m) (s : Nat → Nat) (x : Nat)
    (hx : x < 2 ^ m) : applyW (roundWrites T hT (2 ^ m) k j s) s x = rnd k j s x := by
  have hxj : x ^^^ j < 2 ^ m := Nat.xor_lt_two_pow hx hj
  rcases Nat.lt_trichotomy x (x ^^^ j) with hlt | heq | hgt
  · -- x is the lower index of its pair
    simp only [rnd, hlt, ↓reduceIte]
    by_cases hc : decide (s x > s (x ^^^ j)) = decide (x &&& k = 0)
    · rw [applyW_uniq _ x (s (x ^^^ j)) (fun w hw he => ?_) s ⟨(x, s (x ^^^ j)),
        (roundMem T hT _ k j s _).2 ⟨x, hx, hlt, hc, Or.inl rfl⟩, rfl⟩]
      · by_cases hup : x &&& k = 0
        · simp only [hup, decide_true, decide_eq_true_eq] at hc; simp [hup]; omega
        · simp only [hup, decide_false, decide_eq_false_iff_not, Nat.not_lt] at hc; simp [hup]; omega
      · obtain ⟨i, _, hi2, _, hw'⟩ := (roundMem T hT _ k j s w).1 hw
        rcases hw' with rfl | rfl
        · simp only at he; subst he; rfl
        · simp only at he; subst he; rw [xorInvol] at hlt; omega
    · rw [applyW_not _ _ _ (by
        simp only [List.mem_map, not_exists, not_and]
        intro w hw he
        obtain ⟨i, _, hi2, hci, hw'⟩ := (roundMem T hT _ k j s w).1 hw
        rcases hw' with rfl | rfl
        · simp only at he; subst he; exact hc hci
        · simp only at he; subst he; rw [xorInvol] at hlt; omega)]
      by_cases hup : x &&& k = 0
      · simp only [hup, decide_true, decide_eq_true_eq, Nat.not_lt] at hc; simp [hup]; omega
      · simp only [hup, decide_false, decide_eq_false_iff_not, Decidable.not_not] at hc; simp [hup]; omega
  · -- j = 0: nothing is written and rnd keeps the value
    have hnw : x ∉ (roundWrites T hT (2 ^ m) k j s).map Prod.fst := by
      simp only [List.mem_map, not_exists, not_and]
      intro w hw he
      obtain ⟨i, _, hi2, _, hw'⟩ := (roundMem T hT _ k j s w).1 hw
      have hj0 : j = 0 := by
        have := congrArg (· ^^^ x) heq; simp only [Nat.xor_self] at this
        rw [Nat.xor_comm, ← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor] at this; omega
      subst hj0; simp at hi2
    rw [applyW_not _ _ _ hnw]
    simp only [rnd, ← heq]
    split <;> simp
  · -- x is the upper index; its partner l = x ^ j is the lower one
    have hl : (x ^^^ j) ^^^ j = x := xorInvol x j
    simp only [rnd, show ¬ x < x ^^^ j by omega, ↓reduceIte]
    by_cases hc : decide (s (x ^^^ j) > s x) = decide ((x ^^^ j) &&& k = 0)
    · rw [applyW_uniq _ x (s (x ^^^ j)) (fun w hw he => ?_) s ⟨(x, s (x ^^^ j)),
        (roundMem T hT _ k j s _).2 ⟨x ^^^ j, hxj, by rw [hl]; omega, by rw [hl]; exact hc,
          Or.inr (by rw [hl])⟩, rfl⟩]
      · by_cases hup : (x ^^^ j) &&& k = 0
        · simp only [hup, decide_true, decide_eq_true_eq] at hc; simp [hup]; omega
        · simp only [hup, decide_false, decide_eq_false_iff_not, Nat.not_lt] at hc; simp [hup]; omega
      · obtain ⟨i, _, hi2, _, hw'⟩ := (roundMem T hT _ k j s w).1 hw
        rcases hw' with rfl | rfl
        · simp only at he; subst he; omega
        · simp only at he; subst he; rw [xorInvol]
    · rw [applyW_not _ _ _ (by
        simp only [List.mem_map, not_exists, not_and]
        intro w hw he
        obtain ⟨i, _, hi2, hci, hw'⟩ := (roundMem T hT _ k j s w).1 hw
        rcases hw' with rfl | rfl
        · simp only at he; subst he; omega
        · simp only at he
          have : i = x ^^^ j := by rw [← he, xorInvol]
          subst this; rw [hl] at hci; exact hc hci)]
      by_cases hup : (x ^^^ j) &&& k = 0
      · simp only [hup, decide_true, decide_eq_true_eq, Nat.not_lt] at hc; simp [hup]; omega
      · simp only [hup, decide_false, decide_eq_false_iff_not, Decidable.not_not] at hc; simp [hup]; omega

theorem rndAgree (m k j : Nat) (hj : j < 2 ^ m) (f g : Nat → Nat) (h : agree (2 ^ m) f g) :
    agree (2 ^ m) (rnd k j f) (rnd k j g) := by
  intro x hx
  have hxj : x ^^^ j < 2 ^ m := Nat.xor_lt_two_pow hx hj
  simp only [rnd, h x hx, h _ hxj]

theorem jLoopIsMerge (T : Nat) (hT : 0 < T) (m s' : Nat) (hs : s' ≤ m) :
    ∀ t (f g : Nat → Nat), t < s' → agree (2 ^ m) f g →
      agree (2 ^ m) (jLoop T hT (2 ^ m) (2 ^ s') (2 ^ t) f) (merge s' (t + 1) g) := by
  intro t
  induction t with
  | zero =>
    intro f g _ h x hx
    rw [show (2 : Nat) ^ 0 = 0 + 1 from rfl, jLoop, show (0 + 1) / 2 = 0 from rfl, jLoop]
    simp only [merge]
    rw [roundIsRnd T hT m _ _ (by have := Nat.one_lt_two_pow_iff.2 (show m ≠ 0 by omega); simpa using this) f x hx]
    exact rndAgree m _ _ (Nat.one_lt_two_pow (by omega)) f g h x hx
  | succ t ih =>
    intro f g ht h
    have hjm : 2 ^ (t + 1) < 2 ^ m := Nat.pow_lt_pow_right (by decide) (by omega)
    rw [show 2 ^ (t + 1) = (2 ^ (t + 1) - 1) + 1 by have := Nat.two_pow_pos (t + 1); omega, jLoop,
      show (2 ^ (t + 1) - 1 + 1) / 2 = 2 ^ t by rw [pow_succ2]; have := Nat.two_pow_pos t; omega,
      show 2 ^ (t + 1) - 1 + 1 = 2 ^ (t + 1) by have := Nat.two_pow_pos (t + 1); omega]
    simp only [merge]
    refine ih _ _ (by omega) (fun x hx => ?_)
    rw [roundIsRnd T hT m _ _ hjm f x hx]
    exact rndAgree m _ _ hjm f g h x hx

theorem kLoopIsNet (T : Nat) (hT : 0 < T) (m : Nat) (g : Nat → Nat) :
    ∀ n s' k (hk : 0 < k) (f : Nat → Nat), k = 2 ^ s' → s' + n = m + 1 → 1 ≤ s' →
      agree (2 ^ m) f (net (s' - 1) g) → agree (2 ^ m) (kLoop T hT (2 ^ m) k hk f) (net m g)
  | 0, s', k, hk, f, hks, hn, _, h => by
    rw [kLoop]
    have : ¬ k ≤ 2 ^ m := by
      rw [Nat.not_le, hks]; exact Nat.pow_lt_pow_right (by decide) (by omega)
    simp only [this, ↓reduceIte]
    have e : net m g = net (s' - 1) g := by rw [show m = s' - 1 by omega]
    intro x hx; rw [e]; exact h x hx
  | n + 1, s', k, hk, f, hks, hn, h1, h => by
    rw [kLoop]
    have hle : k ≤ 2 ^ m := by rw [hks]; exact Nat.pow_le_pow_right (by decide) (by omega)
    simp only [hle, ↓reduceIte]
    refine kLoopIsNet T hT m g n (s' + 1) (2 * k) _ _ (by rw [hks, pow_succ2]) (by omega) (by omega) ?_
    have hk2 : k / 2 = 2 ^ (s' - 1) := by
      rw [hks, show s' = (s' - 1) + 1 by omega, pow_succ2]; simp
    rw [hk2, hks]
    have := jLoopIsMerge T hT m s' (by omega) (s' - 1) f (net (s' - 1) g) (by omega) h
    rw [show s' - 1 + 1 = s' by omega] at this
    rw [show s' + 1 - 1 = s' by omega]
    obtain ⟨s'', rfl⟩ : ∃ s'', s' = s'' + 1 := ⟨s' - 1, by omega⟩
    simpa [net] using this

/-- **R-15** (T-07, T-16): the kernel's `altsort` of [b, b + ℓ) — `P` doubled from 1 until P ≥ ℓ,
the padded load, the k/j rounds of per-thread compare-and-swap, the write-back — writes the ℓ
elements sorted into D at [b, b + ℓ), each index exactly once, and nothing else, for every thread
count T and every ℓ-element sequence of 32-bit codes. -/
theorem altsortSpec (T : Nat) (hT : 0 < T) (S : Nat → Nat) (b len : Nat)
    (hx : ∀ i < len, S (b + i) ≤ 0xFFFFFFFF) :
    (∀ D x, applyW (altsortK T hT S b len) D x =
      if b ≤ x ∧ x < b + len then (((List.range len).map fun i => S (b + i)).mergeSort leB).getD (x - b) 0
      else D x) ∧
    ((altsortK T hT S b len).map Prod.fst).Perm (List.range' b len) := by
  let xs := (List.range len).map fun i => S (b + i)
  obtain ⟨m, hPm, hlen⟩ := padLoopPow len 1 (by decide) ⟨0, rfl⟩
  have hload : agree (2 ^ m) (altLoad S b len) (net 0 (padF xs)) := by
    intro i _
    simp only [altLoad, net, padF, xs, List.getD_eq_getElem?_getD, List.getElem?_map]
    split <;> simp [*]
  have hk := kLoopIsNet T hT m (padF xs) m 1 2 (by decide) _ rfl (by omega) (Nat.le_refl _) hload
  have hsorted := bitonicSorts m xs (by simp [xs]; exact hlen) (by
    intro v hv; simp only [xs, List.mem_map, List.mem_range] at hv; obtain ⟨i, hi, rfl⟩ := hv; exact hx i hi)
  have hval : ∀ i < len, (xs.mergeSort leB).getD i 0 = kLoop T hT (2 ^ m) 2 (by decide) (altLoad S b len) i := by
    intro i hi
    rw [hk i (by omega), ← hsorted, bitonicAltSort]
    simp [List.getD_eq_getElem?_getD, hi, show i < 2 ^ m by omega, xs]
  have hws : altsortK T hT S b len =
      (gridVisits T len hT).map fun i => (b + i, kLoop T hT (2 ^ m) 2 (by decide) (altLoad S b len) i) := by
    simp only [altsortK, gridVisits, List.map_flatMap, hPm]
  refine ⟨fun D x => ?_, ?_⟩
  · rw [hws]
    by_cases h : b ≤ x ∧ x < b + len
    · simp only [h, and_self, ↓reduceIte]
      rw [hval (x - b) (by omega)]
      refine applyW_uniq _ x _ (fun w hw he => ?_) D ⟨(x, kLoop T hT (2 ^ m) 2 (by decide) (altLoad S b len) (x - b)),
        List.mem_map.2 ⟨x - b, (gridMem T len hT _).2 (by omega), by rw [show b + (x - b) = x by omega]⟩, rfl⟩
      obtain ⟨i, _, rfl⟩ := List.mem_map.1 hw
      simp only at he ⊢; rw [show x - b = i by omega]
    · simp only [h, ↓reduceIte]
      apply applyW_not
      simp only [List.map_map, List.mem_map, Function.comp, not_exists, not_and]
      intro i hi he
      have := (gridMem T len hT i).1 hi; omega
  · rw [hws, List.map_map, List.range'_eq_map_range]
    exact (gridPerm T len hT).map _

end GpuQuicksort.Theorems
