import GpuQuicksortSpec.GpuQuicksort.Spec
import GpuQuicksortSpec.GpuQuicksort.Model
import Std.Tactic.BVDecide

/-!
# GpuQuicksortSpec.GpuQuicksort.Theorems
=========================================

**What this proves** (kernel-checked, for all inputs of the model):

- *Key codes (C-04):* the `int32` and `float32` codes are bijections on all 2^32 bit patterns, and
  unsigned order of codes equals signed `int32` order and IEEE 754 `totalOrder` (defined from sign
  and magnitude, not from the codes), for all 2^32 × 2^32 pairs (`bv_decide`).
- *The sort (list model):* the three-way partition is a permutation; the gap is exactly the
  pivot-equal elements; the recursive sort returns a sorted permutation for **every** pivot rule and
  threshold; sorted permutations are unique, so the output is deterministic across parameters; the
  alternative sort's padding trick is correct; both pivot rules make progress; the min/max pivot
  halves the code range (the Appendix A.7 bound).
- *Phase one:* the host loop never holds 2M or more sequences and dispatches fewer than 2M
  threadgroups per iteration (so the §7.1 buffers cannot overflow); the iteration cap and its flag;
  all-equal input needs exactly one iteration and hands nothing to phase two; empty children are
  never kept.
- *Tables:* the §7.2 exit map is closed over {0..5}, every code is reachable, only success is 0, and
  every C-07 case maps to 2..5; the §3.1 transition table covers every non-terminal state (no silent
  case), its terminals absorb, and invalid inputs never reach GPU work.
- *Numbers:* the distribution formulas stay in [0, 2^31); `optp` reproduces the spec's worked
  examples; clamping keeps defaults valid; the K-03 memory budget; 32-bit index arithmetic cannot
  overflow; the stack-depth arithmetic of K-08.
- *The paper's algorithms* (in sibling modules): the parallel partition with per-thread prefix
  sums and one fetch-and-add per side per threadgroup is the partition, for every thread split and
  every order of the atomics (`ParallelPartition.lean`: R-04, R-09); the phase-two explicit stack
  machine sorts, finalizes every position exactly once, and never holds more than
  log₂(ℓ/S) + 1 entries (`PhaseTwo.lean`: R-13, I-008, K-08); the kernel's bitonic network sorts
  every power-of-two length (`Bitonic.lean`: R-15).

**What this does not prove:** anything about the implementation (`Sources/`). This project
certifies the *spec*. The implementation's evidence is the §9 suite (56 tests, green) and the
speccheck gate, which are not linked into Lean; a later `spec-proof` would link them. Nor does it
model the GPU: memory ordering (R-28, I-007), threadgroup scheduling and timing are out of Lean's
reach (the algorithm modules assume that barriers and atomics behave as R-28 and R-09 say) and carried by the tests named in the deferral table below.

**Trust boundary.** Leg A (the model transcribes the spec) is the correspondence table in
`Model.lean`, manual. Leg B (the model satisfies the spec's claims) is this file, kernel-checked;
`bv_decide` and `native_decide` additionally trust Lean's compiled evaluator for the codec and `optp`
checks. Leg C (a system behaves as specified) is not established here.

**Tautology rule.** `section Rows` holds transcription: one theorem per lifecycle row the E-cases
name, so every id has a declaration to join; they re-read `rows`, and say so. Every theorem outside
`section Rows` discharges a spec sentence that is not the definition it is about: a claim quantified
over all inputs, a relation between separately pinned values, a coverage or reachability claim, or
a worked example the spec states separately from its formula.
-/

namespace GpuQuicksortSpec.GpuQuicksort.Theorems

open GpuQuicksortSpec.GpuQuicksort.Spec
open GpuQuicksortSpec.GpuQuicksort.Model

section Codec

/-- **R-17** (T-05): the `int32` code is invertible — decode ∘ encode is the identity on every bit
pattern, and encode ∘ decode on every code — so converting before the sort and back after it loses
nothing. -/
theorem int32CodeRoundTrip (b u : BitVec 32) : decI (encI b) = b ∧ encI (decI u) = u := by
  simp only [decI, encI, signMask]; constructor <;> bv_decide

/-- **E-14, E-11** (T-05, T-23): the `float32` code is invertible on every bit pattern — NaNs with
any payload, ±0, ±∞ and subnormals — so every bit pattern is preserved; and since each key type's
code is a bijection, sorting under a mismatched declared type still permutes the input (E-11). -/
theorem float32CodeRoundTrip (b u : BitVec 32) : decF (encF b) = b ∧ encF (decF u) = u := by
  simp only [decF, encF, signMask]; constructor <;> bv_decide

/-- **C-04** (T-05): for every pair of `int32` keys, signed order equals unsigned order of their
codes. -/
theorem int32CodeOrder (a b : BitVec 32) : (encI a).ule (encI b) = a.sle b := by
  simp only [encI, signMask]; bv_decide

/-- **R-01** (T-05): for every pair of `float32` bit patterns, IEEE 754 `totalOrder` (`totalLE`,
defined from sign and magnitude, not from the codes) equals unsigned order of their codes, so
sorting codes sorts floats in `totalOrder`. -/
theorem float32CodeOrder (a b : BitVec 32) : (encF a).ule (encF b) = totalLE a b := by
  simp only [encF, totalLE, signMask]
  cases ha : a.msb <;> cases hb : b.msb <;> simp <;> bv_decide

/-- **(special values)** (T-05): anchors for the order above — −0.0 sorts strictly before +0.0,
−∞ before the most negative finite float, and +∞ before a positive NaN (R-02, E-14 in prose). -/
theorem float32CodeSpecialCases :
    (encF 0x80000000#32).ult (encF 0x00000000#32) = true ∧
    (encF 0xFF800000#32).ult (encF 0xFF7FFFFF#32) = true ∧
    (encF 0x7F800000#32).ult (encF 0x7FC00000#32) = true := by
  simp only [encF, signMask]; decide

end Codec

section SortModel

/-- **(lemma)**: two sorted permutations of the same multiset are equal. -/
theorem sortedPermUnique : ∀ (l₁ l₂ : List Nat), l₁.Pairwise (· ≤ ·) → l₂.Pairwise (· ≤ ·) → l₁.Perm l₂ → l₁ = l₂
  | [], l₂, _, _, hp => List.Perm.nil_eq hp
  | a :: t, [], _, _, hp => absurd hp.length_eq (by simp)
  | a :: t, b :: u, h₁, h₂, hp => by
    have hb : b ∈ a :: t := hp.symm.subset (List.mem_cons_self)
    have ha : a ∈ b :: u := hp.subset (List.mem_cons_self)
    have hab : a ≤ b := by
      rcases List.mem_cons.1 hb with h | h
      · omega
      · exact (List.pairwise_cons.1 h₁).1 b h
    have hba : b ≤ a := by
      rcases List.mem_cons.1 ha with h | h
      · omega
      · exact (List.pairwise_cons.1 h₂).1 a h
    have e : a = b := by omega
    subst e
    have := sortedPermUnique t u (List.pairwise_cons.1 h₁).2 (List.pairwise_cons.1 h₂).2 (List.Perm.cons_inv hp)
    rw [this]

/-- **(lemma)**: the reference sort's output is sorted. -/
theorem mergeSortSorted (l : List Nat) : (l.mergeSort leB).Pairwise (· ≤ ·) := by
  have h := List.pairwise_mergeSort (le := leB)
    (by intro a b c h1 h2; simp [leB] at *; omega) (by intro a b; simp [leB]; omega) l
  exact h.imp (by intro a b hab; simpa [leB] using hab)

/-- **(lemma)** (R-04, T-15): the two-pass scheme's result — lower part, gap, upper part — is a permutation of the sequence. -/
theorem partitionPerm (p : Nat) (xs : List Nat) : (partition3 p xs).Perm xs := by
  have h1 := List.filter_append_perm (fun x => decide (x < p)) xs
  have h2 := List.filter_append_perm (fun x => decide (x = p)) (xs.filter (fun x => !decide (x < p)))
  rw [List.filter_filter, List.filter_filter] at h2
  have e1 : xs.filter (fun a => decide (a = p) && !decide (a < p)) = xs.filter (fun a => decide (a = p)) := by
    apply List.filter_congr; intro x _; by_cases hx : x = p <;> simp [hx]
  have e2 : xs.filter (fun a => !decide (a = p) && !decide (a < p)) = xs.filter (fun a => decide (p < a)) := by
    apply List.filter_congr; intro x _
    by_cases h1 : x < p <;> by_cases h2 : x = p <;> by_cases h3 : p < x <;> simp_all <;> omega
  rw [e1, e2, List.filter_eq] at h2
  simp only [partition3, lowerPart, gapPart, upperPart]
  rw [List.append_assoc]
  exact (List.Perm.append_left _ h2).trans h1

/-- **R-06, I-004** (T-15): the gap filled with p holds exactly the pivot-equal elements: one copy of p for each element whose code equals p. -/
theorem gapIsPivotEqual (p : Nat) (xs : List Nat) : gapPart p xs = xs.filter (fun x => decide (x = p)) := by
  simp only [gapPart]; rw [List.filter_eq]

/-- **I-001, I-002, R-02, E-13** (T-01, T-40): for every pivot rule and threshold, the sort returns a sorted permutation of its input — correctness never depends on pivot quality. -/
theorem qsortCorrect (piv : List Nat → Nat) (S : Nat) (xs : List Nat) :
    (qsort piv S xs).Pairwise (· ≤ ·) ∧ (qsort piv S xs).Perm xs := by
  fun_induction qsort piv S xs with
  | case1 xs hS => exact ⟨mergeSortSorted xs, List.mergeSort_perm xs leB⟩
  | case2 xs hS p h ih₁ ih₂ =>
    have hl : ∀ x ∈ qsort piv S (lowerPart p xs), x < p := by
      intro x hx
      have := (ih₁.2.subset hx)
      simp only [lowerPart, List.mem_filter, decide_eq_true_eq] at this
      exact this.2
    have hu : ∀ x ∈ qsort piv S (upperPart p xs), p < x := by
      intro x hx
      have := (ih₂.2.subset hx)
      simp only [upperPart, List.mem_filter, decide_eq_true_eq] at this
      exact this.2
    have hg : ∀ x ∈ gapPart p xs, x = p := by
      intro x hx; simp only [gapPart, List.mem_replicate] at hx; exact hx.2
    have hgs : (gapPart p xs).Pairwise (· ≤ ·) := by
      simp only [gapPart]; exact List.pairwise_replicate.2 (Or.inr (Nat.le_refl p))
    refine ⟨?_, ?_⟩
    · rw [List.pairwise_append, List.pairwise_append]
      refine ⟨⟨ih₁.1, hgs, ?_⟩, ih₂.1, ?_⟩
      · intro a ha b hb; have := hl a ha; have := hg b hb; omega
      · intro a ha b hb
        have hb' := hu b hb
        rcases List.mem_append.1 ha with ha | ha
        · have := hl a ha; omega
        · have := hg a ha; omega
    · exact ((List.Perm.append (List.Perm.append ih₁.2 (List.Perm.refl _)) ih₂.2)).trans (partitionPerm p xs)
  | case3 xs hS p h => exact ⟨mergeSortSorted xs, List.mergeSort_perm xs leB⟩

/-- **I-003** (T-03, T-04): the output does not depend on the pivot rule or the threshold: all parameter choices give the same bytes. -/
theorem qsortDeterministic (piv₁ piv₂ : List Nat → Nat) (S₁ S₂ : Nat) (xs : List Nat) :
    qsort piv₁ S₁ xs = qsort piv₂ S₂ xs := by
  have h₁ := qsortCorrect piv₁ S₁ xs
  have h₂ := qsortCorrect piv₂ S₂ xs
  exact sortedPermUnique _ _ h₁.1 h₂.1 (h₁.2.trans h₂.2.symm)

/-- **(lemma)** (R-15, T-07): padding with 0xFFFFFFFF, sorting, and keeping the first ℓ elements equals sorting the ℓ elements. The network that does the sorting is proved in `Bitonic.bitonicSorts`. -/
theorem altSortCorrect (padTo : Nat) (xs : List Nat) (hx : ∀ x ∈ xs, x ≤ 0xFFFFFFFF) :
    altSort padTo xs = xs.mergeSort leB := by
  let pad := List.replicate (padTo - xs.length) 0xFFFFFFFF
  have hsorted : (xs.mergeSort leB ++ pad).Pairwise (· ≤ ·) := by
    rw [List.pairwise_append]
    refine ⟨mergeSortSorted xs, ?_, ?_⟩
    · exact List.pairwise_replicate.2 (Or.inr (Nat.le_refl _))
    · intro a ha b hb
      have ha' := hx a ((List.mergeSort_perm xs leB).subset ha)
      simp only [pad, List.mem_replicate] at hb
      omega
  have hperm : (xs.mergeSort leB ++ pad).Perm (xs ++ pad) :=
    List.Perm.append_right _ (List.mergeSort_perm xs leB)
  have heq : (xs ++ pad).mergeSort leB = xs.mergeSort leB ++ pad :=
    sortedPermUnique _ _ (mergeSortSorted _) hsorted ((List.mergeSort_perm _ leB).trans hperm.symm)
  simp only [altSort]
  change ((xs ++ pad).mergeSort leB).take xs.length = _
  rw [heq, List.take_left' (List.length_mergeSort xs)]

/-- **I-005** (T-09): any pivot that is an element of the sequence shrinks both parts strictly — the progress half of I-005. -/
theorem memPartShrinks (p : Nat) (xs : List Nat) (hp : p ∈ xs) :
    (lowerPart p xs).length < xs.length ∧ (upperPart p xs).length < xs.length := by
  constructor
  · exact List.length_filter_lt_length_iff_exists.2 ⟨p, hp, by simp⟩
  · exact List.length_filter_lt_length_iff_exists.2 ⟨p, hp, by simp⟩

/-- **(lemma)**: an in-range sample is an element of the list. -/
theorem getDMem (xs : List Nat) (i : Nat) (h : i < xs.length) : xs.getD i 0 ∈ xs := by
  rw [List.getD, List.getElem?_eq_getElem h]; exact List.getElem_mem h

/-- **R-14** (T-01): the median of s_b, s_⌊(b+e)/2⌋ and s_(e−1) is an element of the sequence, so median-of-three always makes progress. -/
theorem medianOfThreeMem (xs : List Nat) (hne : xs ≠ []) : medianOfThree xs ∈ xs := by
  match xs, hne with
  | a :: t, _ =>
    have hl : 0 < (a :: t).length := by simp
    have h0 := getDMem (a :: t) 0 hl
    have h1 := getDMem (a :: t) ((a :: t).length / 2) (by omega)
    have h2 := getDMem (a :: t) ((a :: t).length - 1) (by omega)
    simp only [medianOfThree, med3]
    generalize (a :: t).getD 0 0 = x at h0
    generalize (a :: t).getD ((a :: t).length / 2) 0 = y at h1
    generalize (a :: t).getD ((a :: t).length - 1) 0 = z at h2
    rcases Nat.le_total x y with hxy | hxy <;> rcases Nat.le_total y z with hyz | hyz <;>
      rcases Nat.le_total x z with hxz | hxz <;>
      simp_all <;> split <;> simp_all <;> split <;> simp_all

/-- **(lemma)**: lo ≤ p < hi when lo < hi. -/
theorem minMaxPivotBounds (lo hi : Nat) (h : lo < hi) : lo ≤ minMaxPivot lo hi ∧ minMaxPivot lo hi < hi := by
  simp only [minMaxPivot]; omega

/-- **O-2** (T-41): with lo < hi the min/max pivot shrinks both parts strictly (the element hi leaves the lower part, lo the upper part). -/
theorem minMaxShrinks (xs : List Nat) (lo hi : Nat) (hlo : lo ∈ xs) (hhi : hi ∈ xs) (h : lo < hi) :
    (lowerPart (minMaxPivot lo hi) xs).length < xs.length ∧ (upperPart (minMaxPivot lo hi) xs).length < xs.length := by
  have hb := minMaxPivotBounds lo hi h
  constructor
  · exact List.length_filter_lt_length_iff_exists.2 ⟨hi, hhi, by simp; omega⟩
  · exact List.length_filter_lt_length_iff_exists.2 ⟨lo, hlo, by simp; omega⟩

/-- **(Appendix A.7)**: each child of a min/max partition spans at most half the parent's code range. -/
theorem minMaxHalvesRange (xs : List Nat) (lo hi : Nat) (hr : ∀ x ∈ xs, lo ≤ x ∧ x ≤ hi) :
    (∀ x ∈ lowerPart (minMaxPivot lo hi) xs, ∀ y ∈ lowerPart (minMaxPivot lo hi) xs, x - y ≤ (hi - lo) / 2) ∧
    (∀ x ∈ upperPart (minMaxPivot lo hi) xs, ∀ y ∈ upperPart (minMaxPivot lo hi) xs, x - y ≤ (hi - lo) / 2) := by
  constructor
  · intro x hx y hy
    simp only [lowerPart, List.mem_filter, minMaxPivot] at hx hy
    obtain ⟨hx1, hx2⟩ := hx; obtain ⟨hy1, hy2⟩ := hy
    obtain ⟨_, _⟩ := hr x hx1; obtain ⟨_, _⟩ := hr y hy1
    have := of_decide_eq_true hx2; have := of_decide_eq_true hy2
    omega
  · intro x hx y hy
    simp only [upperPart, List.mem_filter, minMaxPivot] at hx hy
    obtain ⟨hx1, hx2⟩ := hx; obtain ⟨hy1, hy2⟩ := hy
    obtain ⟨_, _⟩ := hr x hx1; obtain ⟨_, _⟩ := hr y hy1
    have := of_decide_eq_true hx2; have := of_decide_eq_true hy2
    omega

/-- **(Appendix A.7)**: a range that halves at every level and starts below 2^32 is 0 after 32 levels, so phase one partitions any sequence at most 32 times after the root. -/
theorem halvingChain (w : Nat → Nat) (h : ∀ k, w (k + 1) ≤ w k / 2) (h0 : w 0 < 2 ^ 32) : w 32 = 0 := by
  have key : ∀ k, w k ≤ w 0 / 2 ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      calc w (k + 1) ≤ w k / 2 := h k
        _ ≤ (w 0 / 2 ^ k) / 2 := Nat.div_le_div_right ih
        _ = w 0 / 2 ^ (k + 1) := by rw [Nat.div_div_eq_div_mul, Nat.pow_succ]
  have := key 32
  have : w 0 / 2 ^ 32 = 0 := Nat.div_eq_of_lt h0
  omega

end SortModel

section PhaseOne

/-- **(lemma)**: counting sequences across one step. -/
theorem flatMapLength (children : Nat → List Nat) (hc : ∀ c, (children c).length ≤ 2) :
    ∀ (w : List Nat), (w.flatMap children).length ≤ 2 * w.length
  | [] => by simp
  | a :: t => by
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    have := flatMapLength children hc t; have := hc a; omega

/-- **(lemma)**: counting sequences across one step. -/
theorem splitLength (m : Nat) (k : List Nat) :
    (k.filter (fun c => decide (m ≤ c))).length + (k.filter (fun c => decide (c < m))).length = k.length := by
  have h := (List.filter_append_perm (fun c => decide (m ≤ c)) k).length_eq
  rw [List.length_append] at h
  have e : k.filter (fun c => !decide (m ≤ c)) = k.filter (fun c => decide (c < m)) := by
    apply List.filter_congr; intro x _; by_cases hx : m ≤ x <;> simp [hx] <;> omega
  rw [e] at h; exact h

/-- **(lemma)**: counting sequences across one step. -/
theorem stepCount (children : Nat → List Nat) (hc : ∀ c, (children c).length ≤ 2) (m : Nat) (st : P1) :
    (p1Step children m st).work.length + (p1Step children m st).done.length ≤ 2 * st.work.length + st.done.length := by
  simp only [p1Step, List.length_append]
  have h1 := splitLength m ((st.work.flatMap children).filter (fun c => decide (0 < c)))
  have h2 := List.length_filter_le (fun c => decide (0 < c)) (st.work.flatMap children)
  have h3 := flatMapLength children hc st.work
  omega

/-- **R-08, K-09** (T-13, T-21): starting from one sequence, the phase-one loop never holds 2M or more sequences, so `done` handed to phase two fits the §7.1 buffers. -/
theorem loopBound (children : Nat → List Nat) (hc : ∀ c, (children c).length ≤ 2) (m M maxIter : Nat) :
    ∀ (fuel : Nat) (st : P1), st.work.length + st.done.length < 2 * M →
      (p1Loop children m M maxIter fuel st).work.length + (p1Loop children m M maxIter fuel st).done.length < 2 * M
  | 0, st, h => by simpa [p1Loop] using h
  | fuel + 1, st, h => by
    simp only [p1Loop]
    split
    · rename_i hcond
      split
      · simpa using h
      · apply loopBound children hc m M maxIter fuel
        have := stepCount children hc m st; omega
    · exact h

/-- **(lemma)**: the loop never runs more than `maxIter` iterations. -/
theorem loopIterations (children : Nat → List Nat) (m M maxIter : Nat) :
    ∀ (fuel : Nat) (st : P1), st.iterations ≤ maxIter →
      (p1Loop children m M maxIter fuel st).iterations ≤ maxIter
  | 0, st, h => by simpa [p1Loop] using h
  | fuel + 1, st, h => by
    simp only [p1Loop]
    split
    · split
      · simpa using h
      · rename_i hne
        apply loopIterations children m M maxIter fuel
        simp only [p1Step]; omega
    · exact h

/-- **K-07** (T-10): the cap flag is set only when iterations = maxIter and the R-08 loop condition still holds. -/
theorem loopCap (children : Nat → List Nat) (m M maxIter : Nat) :
    ∀ (fuel : Nat) (st : P1), st.capReached = false →
      (p1Loop children m M maxIter fuel st).capReached = true →
      (p1Loop children m M maxIter fuel st).iterations = maxIter ∧
      (p1Loop children m M maxIter fuel st).work ≠ [] ∧
      (p1Loop children m M maxIter fuel st).work.length + (p1Loop children m M maxIter fuel st).done.length < M
  | 0, st, h0, h => by simp [p1Loop] at h; simp [h0] at h
  | fuel + 1, st, h0, h => by
    simp only [p1Loop] at h ⊢
    split at h
    · rename_i hcond
      split at h
      · rename_i hit; simp only [hcond, hit, ne_eq, not_false_eq_true, and_self, ↓reduceIte]
      · rename_i hit; simp only [hcond, hit, ne_eq, not_false_eq_true, and_self, ↓reduceIte]
        exact loopCap children m M maxIter fuel _ (by simp [p1Step, h0]) h
    · simp [h0] at h

/-- **(lemma)**: ceiling and floor sums. -/
theorem ceilMul (a m : Nat) (hm : 0 < m) : a ≤ (a + m - 1) / m * m := by
  have h1 := Nat.div_add_mod (a + m - 1) m
  have h2 := Nat.mod_lt (a + m - 1) hm
  rw [Nat.mul_comm] at h1; omega

/-- **(lemma)**: ceiling and floor sums. -/
theorem divSum (b : Nat) (hb : 0 < b) : ∀ (ls : List Nat), (ls.map (· / b)).sum ≤ ls.sum / b
  | [] => by simp
  | a :: t => by
    simp only [List.map_cons, List.sum_cons]
    have ih := divSum b hb t
    apply (Nat.le_div_iff_mul_le hb).2
    have e1 := Nat.div_mul_le_self a b
    have e2 : (t.map (· / b)).sum * b ≤ t.sum := by
      calc (t.map (· / b)).sum * b ≤ t.sum / b * b := Nat.mul_le_mul_right b ih
        _ ≤ t.sum := Nat.div_mul_le_self _ _
    rw [Nat.add_mul]; omega

/-- **(lemma)**: ceiling and floor sums. -/
theorem blocksSum (b : Nat) (hb : 0 < b) : ∀ (ls : List Nat), (ls.map (blocksFor b)).sum ≤ (ls.map (· / b)).sum + ls.length
  | [] => by simp
  | a :: t => by
    simp only [List.map_cons, List.sum_cons, List.length_cons, blocksFor]
    have ih := blocksSum b hb t
    have : (a + b - 1) / b ≤ a / b + 1 := by
      have h1 := Nat.div_add_mod (a + b - 1) b; have h2 := Nat.mod_lt (a + b - 1) hb
      have h3 := Nat.div_add_mod a b; have h4 := Nat.mod_lt a hb
      apply (Nat.div_le_iff_le_mul_add_pred hb).2
      rw [Nat.mul_add, Nat.mul_one]; omega
    omega

/-- **K-06** (T-13): with blocksize = max(T, ⌈Σℓ / M⌉) and fewer than M sequences, an iteration
dispatches fewer than 2M threadgroups — the §7.1 `BlockDescriptor` term. -/
theorem blocksBound (ls : List Nat) (M T : Nat) (hM : 0 < M) (hT : 0 < T) (hl : ls.length < M) :
    (ls.map (blocksFor (max T ((ls.sum + M - 1) / M)))).sum < 2 * M := by
  have hb : 0 < max T ((ls.sum + M - 1) / M) := Nat.lt_of_lt_of_le hT (Nat.le_max_left _ _)
  have h1 := blocksSum _ hb ls
  have h2 := divSum _ hb ls
  have h3 : ls.sum / max T ((ls.sum + M - 1) / M) ≤ M := by
    apply Nat.div_le_of_le_mul
    calc ls.sum ≤ (ls.sum + M - 1) / M * M := ceilMul ls.sum M hM
      _ ≤ max T ((ls.sum + M - 1) / M) * M := Nat.mul_le_mul_right M (Nat.le_max_right _ _)
  omega

/-- **E-17** (T-13): a phase-one step never keeps a child of length 0 in `work` or `done`. -/
theorem noEmptyChildren (children : Nat → List Nat) (m : Nat) (st : P1) (hd : ∀ c ∈ st.done, 0 < c) :
    (∀ c ∈ (p1Step children m st).work, 0 < c) ∧ (∀ c ∈ (p1Step children m st).done, 0 < c) := by
  constructor
  · intro c hc; simp only [p1Step, List.mem_filter, decide_eq_true_eq] at hc; exact hc.1.2
  · intro c hc
    simp only [p1Step, List.mem_append, List.mem_filter, decide_eq_true_eq] at hc
    rcases hc with h | h
    · exact hd c h
    · exact h.1.2

/-- **(lemma)**: an all-equal sequence has no lower or upper part under its median-of-three
pivot; the whole sequence is the gap. -/
theorem allEqualNoChildren (n c : Nat) (hn : 0 < n) :
    medianOfThree (List.replicate n c) = c ∧ lowerPart c (List.replicate n c) = [] ∧
    upperPart c (List.replicate n c) = [] ∧ gapPart c (List.replicate n c) = List.replicate n c := by
  have hne : List.replicate n c ≠ [] := by simp; omega
  have hm := medianOfThreeMem _ hne
  refine ⟨(List.eq_of_mem_replicate hm), ?_, ?_, ?_⟩
  · simp [lowerPart]
  · simp [upperPart]
  · simp [gapPart]

/-- **K-10, E-04** (T-08): with no children (all-equal input, above), n ≥ minseq, M ≥ 2 and a cap of
at least 1, phase one performs exactly one iteration and hands nothing to phase two. -/
theorem allEqualOneIteration (n m M maxIter fuel : Nat) (_hn : 0 < n) (hM : 2 ≤ M) (hI : 1 ≤ maxIter) :
    p1Loop (fun _ => []) m M maxIter (fuel + 2) ⟨[n], [], 0, false⟩ = ⟨[], [], 1, false⟩ := by
  have h1 : ([n] : List Nat) ≠ [] ∧ [n].length + ([] : List Nat).length < M := by simp; omega
  have h2 : (0 : Nat) ≠ maxIter := by omega
  simp only [p1Loop, p1Step]
  simp [h1, h2]
  omega

end PhaseOne

section Tables

/-- **K-12** (T-27): the §7.2 map is closed over {0..5}, every code is reached, and 0 means
success and nothing else. -/
theorem exitMap :
    (∀ f : Failure, exitCode f ≤ 5) ∧ (∀ k, k ≤ 5 → ∃ f, exitCode f = k) ∧
    (∀ f : Failure, exitCode f = 0 ↔ f = .success) := by
  refine ⟨?_, ?_, ?_⟩
  · intro f; cases f <;> decide
  · intro k hk
    match k, hk with
    | 0, _ => exact ⟨.success, rfl⟩
    | 1, _ => exact ⟨.verificationFailed, rfl⟩
    | 2, _ => exact ⟨.invalidParameters, rfl⟩
    | 3, _ => exact ⟨.noMetalDevice, rfl⟩
    | 4, _ => exact ⟨.fileIO, rfl⟩
    | 5, _ => exact ⟨.gpuExecutionFailed, rfl⟩
  · intro f; cases f <;> decide

/-- **C-07** (T-18, T-19, T-24): every C-07 case the CLI can observe maps to a failure code in 2..5 — never success, never a verification failure. -/
theorem c07Codes : ∀ f ∈ c07Cases, 2 ≤ exitCode f ∧ exitCode f ≤ 5 := by decide

/-- **(§3.1 coverage)** (T-06..T-08): every non-terminal lifecycle state has at least one applicable row for every combination of facts — the table has no silent case. -/
theorem noSilence : ∀ (s : St) (f : Facts), s ≠ .done → s ≠ .failed → applicable s f ≠ [] := by
  intro s f h1 h2
  cases s <;> simp_all [applicable, rows] <;>
    cases f.inputsValid <;> cases f.loopContinues <;> cases f.doneEmpty <;> cases f.gpuError <;> simp <;> omega

/-- **(§3.1 terminals)**: `done` and `failed` have no outgoing rows. -/
theorem terminal : ∀ f : Facts, applicable .done f = [] ∧ applicable .failed f = [] := by
  intro f; simp [applicable, rows]

/-- **I-006** (T-18, T-19): with invalid inputs no row leads from validation to GPU work, so the caller's buffer cannot be touched before the failure. -/
theorem invalidNeverEncodes (f : Facts) (h : f.inputsValid = false) : .encoding ∉ applicable .validating f := by
  simp only [applicable, rows, List.filter_cons, List.filter_nil]
  by_cases hn : f.n ≤ 1 <;> simp [h, hn]

/-- **C-08, R-20** (T-26): every generator formula — uniform, bucket, staggered (0-based, D-07) and gaussian — yields values in [0, 2^31) for every draw. -/
theorem distRange (k n r1 r2 r3 r4 : Nat) (hk : k < n) :
    uniformV r1 < 2 ^ 31 ∧ bucketV k n r1 < 2 ^ 31 ∧ staggeredV k n r1 < 2 ^ 31 ∧ gaussianV r1 r2 r3 r4 < 2 ^ 31 := by
  have hn : 0 < n := by omega
  have hi : k * distP / n < distP := by
    apply (Nat.div_lt_iff_lt_mul hn).2; simp [distP]; omega
  simp only [uniformV, bucketV, staggeredV, gaussianV, distP, distW] at *
  have m1 := Nat.mod_lt r1 (show 0 < 2 ^ 31 by decide)
  have m2 := Nat.mod_lt r2 (show 0 < 2 ^ 31 by decide)
  have m3 := Nat.mod_lt r3 (show 0 < 2 ^ 31 by decide)
  have m4 := Nat.mod_lt r4 (show 0 < 2 ^ 31 by decide)
  have mw := Nat.mod_lt r1 (show 0 < 2 ^ 24 by decide)
  have ms := Nat.mod_lt (k * 128 * 128 / n) (show 0 < 128 by decide)
  refine ⟨m1, by omega, ?_, by omega⟩
  by_cases hc : k * 128 / n < 128 / 2 <;> simp only [hc, ↓reduceIte] <;> omega

/-- **(D-07 witness)**: with the paper's condition i ≤ ⌊p/2⌋, block 64 already yields values ≥ 2^31 — the reason D-07 exists. -/
theorem paperStaggeredOverflows : 2 ^ 31 ≤ paperStaggeredV 64 0 := by decide

/-- **K-05, R-16** (T-20): the spec's worked examples — (64, 512, 256) at 2^20 keys and (256, 1024, 1024) at 2^24 keys with the paper's constants — follow from its optp formula (checked with `native_decide`, i.e. with compiled IEEE doubles). -/
theorem optpExamples :
    optp (2 ^ 20) 0.00001172 53 = 64 ∧ optp (2 ^ 20) 0.00003748 476 = 512 ∧ optp (2 ^ 20) 0.00004685 211 = 256 ∧
    optp (2 ^ 24) 0.00001172 53 = 256 ∧ optp (2 ^ 24) 0.00003748 476 = 1024 ∧ optp (2 ^ 24) 0.00004685 211 = 1024 := by
  native_decide

/-- **K-04** (T-20): clamping a defaulted power of two into [lo, hi] yields a power of two in [lo, hi]. -/
theorem clampValid (lo hi x : Nat) (h : lo ≤ hi) (hlo : isPow2 lo) (hhi : isPow2 hi) (hx : isPow2 x) :
    lo ≤ clampPow2 lo hi x ∧ clampPow2 lo hi x ≤ hi ∧ isPow2 (clampPow2 lo hi x) := by
  simp only [clampPow2]
  split
  · exact ⟨Nat.le_refl _, h, hlo⟩
  · split
    · exact ⟨h, Nat.le_refl _, hhi⟩
    · refine ⟨by omega, by omega, hx⟩

/-- **K-03** (T-18): every valid T from 32 to 1024 fits 32 KiB with minseq = 64 in both kernels, and at T = 1024 the largest valid minseq is 4096 (8192 overflows). -/
theorem threadgroupBudget :
    (∀ e, e ≤ 5 → phaseOneBytes (32 * 2 ^ e) ≤ refThreadgroupMemory ∧ phaseTwoBytes (32 * 2 ^ e) minseqFloor ≤ refThreadgroupMemory) ∧
    phaseTwoBytes tCeil 4096 ≤ refThreadgroupMemory ∧ refThreadgroupMemory < phaseTwoBytes tCeil 8192 := by
  refine ⟨?_, by decide, by decide⟩
  intro e he
  match e, he with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ => decide

/-- **K-01** (T-19): with n ≤ 2^31 − 1, the index sums the kernels compute fit 32 bits, and the median index lies in [b, e). -/
theorem indexArithmetic (b e : Nat) (hbe : b ≤ e) (he : e ≤ keyCap) :
    b + e < 2 ^ 32 ∧ (b < e → b ≤ (b + e) / 2 ∧ (b + e) / 2 < e) := by
  simp only [keyCap] at he; omega

/-- **(lemma)** (K-08, T-11): for ℓ ≤ 2^31 − 1 and minseq ≥ 64, ⌊log₂(ℓ/minseq)⌋ + 3 ≤ 27. Since ⌈log₂ x⌉ ≤ ⌊log₂ x⌋ + 1, the spec's depth bound ⌈log₂(ℓ/minseq)⌉ + 2 is at most 27, as K-08 states, below the 32-entry stack. -/
theorem stackArithmetic (l S : Nat) (hl : l ≤ keyCap) (hS : minseqFloor ≤ S) :
    Nat.log2 (l / S) + 3 ≤ 27 := by
  simp only [keyCap, minseqFloor] at *
  have hq : l / S < 2 ^ 25 := by
    have : l / S ≤ l / 64 := Nat.div_le_div_left hS (by decide)
    have : l / 64 < 2 ^ 25 := by omega
    omega
  by_cases h0 : l / S = 0
  · rw [h0]; decide
  · have := (Nat.log2_lt h0).2 hq; omega

end Tables

section Rows

/-! Transcription: each theorem below re-reads a line of `rows` so the E-ids have a declaration to join. They prove nothing beyond `Model.lean`. -/

/-- **(lemma)**: row i of the table applies when it starts at s and its guard holds. -/
theorem rowApplies (i : Nat) (hi : i < rows.length) (s : St) (f : Facts)
    (hs : rows[i].src = s) (hg : rows[i].guard f = true) : rows[i].dst ∈ applicable s f := by
  unfold applicable
  exact List.mem_map.2 ⟨rows[i], List.mem_filter.2 ⟨List.getElem_mem hi, by simp [hs, hg]⟩, rfl⟩

/-- **E-01, E-02** (transcription; T-06): n ≤ 1 leads from validation to `done`. -/
theorem smallInputDone (f : Facts) (h : f.n ≤ 1) : .done ∈ applicable .validating f :=
  rowApplies 1 (by decide) .validating f rfl (by simp [rows, h])

/-- **E-03** (transcription; T-07): n < minseq leads from encoding straight to phase two. -/
theorem belowMinseqSkipsPhaseOne (f : Facts) (h : f.n < f.minseq) : .phaseTwo ∈ applicable .encoding f :=
  rowApplies 4 (by decide) .encoding f rfl (by simp [rows, h])

/-- **E-24** (transcription; T-08): an empty `done` leads from phase one straight to decoding. -/
theorem emptyDoneSkipsPhaseTwo (f : Facts) (h1 : f.loopContinues = false) (h2 : f.doneEmpty = true) :
    .decoding ∈ applicable .phaseOne f :=
  rowApplies 8 (by decide) .phaseOne f rfl (by simp [rows, h1, h2])

/-- **E-05, E-06, E-07, E-08, E-09, E-10, E-12** (transcription; T-12, T-18, T-19, T-24, T-42):
invalid inputs, allocation failure, a failed read-back, and a GPU error each lead to `failed`. -/
theorem failuresReachFailed (f : Facts) :
    (f.inputsValid = false → .failed ∈ applicable .validating f) ∧
    (f.allocationOk = false → .failed ∈ applicable .validating f) ∧
    (f.readBackOk = false → .failed ∈ applicable .phaseOne f) ∧
    (f.gpuError = true → ∀ s ∈ [St.encoding, .phaseOne, .phaseTwo, .decoding], .failed ∈ applicable s f) := by
  refine ⟨fun h => rowApplies 0 (by decide) _ f rfl (by simp [rows, h]),
          fun h => rowApplies 3 (by decide) _ f rfl (by simp [rows, h]),
          fun h => rowApplies 9 (by decide) _ f rfl (by simp [rows, h]), ?_⟩
  intro h s hs
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl
  · exact rowApplies 11 (by decide) _ f rfl (by simp [rows, h])
  · exact rowApplies 12 (by decide) _ f rfl (by simp [rows, h])
  · exact rowApplies 13 (by decide) _ f rfl (by simp [rows, h])
  · exact rowApplies 14 (by decide) _ f rfl (by simp [rows, h])

end Rows

section Findings

/-- **(F-034, G-2)**: the §3.1 table's rows are not mutually exclusive and it states no precedence: (1) n = 0 with invalid inputs matches both "invalid → failed" and "n ≤ 1 → done"; (2) valid inputs, n ≥ 2 and a failed allocation match both "→ encoding" and "allocation fails → failed"; (3) a GPU error during encoding matches both the n-vs-minseq rows and "any GPU state → failed". -/
theorem overlap :
    applicable .validating ⟨0, 64, false, true, false, false, false, true⟩ = [.failed, .done] ∧
    applicable .validating ⟨4096, 64, true, false, false, false, false, true⟩ = [.encoding, .failed] ∧
    applicable .encoding ⟨4096, 64, true, true, false, false, true, true⟩ = [.phaseOne, .failed] := by
  decide

end Findings

/-!
## Deferral table — spec ids out of Lean's reach, and the §9 tests that carry them

Every §9 test named here exists in `Tests/GPUQuicksortTests` and passes (56 tests); this model does
not link to them. "(process side)" marks an id whose model half is tagged in this library.

| Spec id | Content | Carried by |
| ------- | ------- | ---------- |
| R-01 (process side) | the library sorts in the caller's storage | T-01, T-23 |
| R-02 (process side) | the output bytes are sorted and a permutation | T-01, T-05 |
| R-03 | the two phases as GPU dispatches | T-01, T-07 |
| R-04 (process side) | counting, scanning and scattering by threads | T-15, T-17 |
| R-05 | stride-T coalesced reads | T-17 |
| R-06 (process side) | the gap is written in D at [s + L, e − G) | T-08, T-15 |
| R-07 | reading one buffer and writing the other | T-13 |
| R-08 (process side) | the host loop's dispatches | T-02, T-13 |
| R-09 (process side) | the kernel issues the two atomics from one thread and shares them through threadgroup memory | T-14 |
| R-10 | fill and child derivation after the dispatch completes | T-15 |
| R-11 | pivots follow the configured strategy | T-03 |
| R-12 | one phase-two threadgroup per sequence | T-02, T-07 |
| R-13 (process side) | the kernel's stack in threadgroup memory and its push order | T-11, T-17 |
| R-14 (process side) | the kernel samples s_b, s_mid, s_(e−1) | T-01, T-17 |
| R-15 (process side) | the bitonic network in threadgroup memory | T-07, T-16 |
| R-16 (process side) | defaults come from the C-10 table | T-03, T-20 |
| R-17 (process side) | the codec runs on the GPU in place | T-05, T-23 |
| R-18 | typed errors, no crashes | T-18, T-19, T-24 |
| R-19 | the six CLI subcommands | T-27, T-28 |
| R-20 (process side) | exact generator bytes (MT19937) | T-25, T-26 |
| R-21 | the SortReport fields | T-21 |
| R-22 | diagnostics lines and stderr policy | T-28, T-29 |
| R-23 | bench times only the sort | T-28 |
| R-24 | the tune procedure | T-34, T-38 |
| R-25 | the shipped table | T-34, T-37 |
| R-26 | the four CPU baselines | T-28, T-39 |
| R-27 | precompiled metallib and stale check | T-35, T-36 |
| R-28 | intra-threadgroup barriers | T-17, T-01 |
| C-01 | the public API | T-22, T-23 |
| C-02 | SortReport | T-21 |
| C-03 | Parameters and device limits | T-20, T-30 |
| C-04 (process side) | the GPU codec kernels | T-05 |
| C-05 | phase-one struct layouts | T-13, T-31 |
| C-06 | phase-two struct layouts | T-11, T-31 |
| C-07 (process side) | the error enum | T-18, T-19, T-24 |
| C-08 (process side) | the generators' exact bytes | T-25, T-26 |
| C-09 | package layout and shader delivery | T-35, T-36 |
| C-10 | the tuned-parameter table | T-20, T-37, T-38 |
| C-11 | the CPU baseline shim | T-39 |
| I-001, I-002 (process side) | sortedness and permutation of the bytes | T-01 |
| I-003 (process side) | identical bytes across runs and parameters | T-03, T-04 |
| I-004 (process side) | gap fills in D | T-09, T-15 |
| I-005 (process side) | disjoint live ranges | T-09, T-13, T-41 |
| I-006 (process side) | buffer untouched on validation failure | T-18, T-19, T-24 |
| I-007 | ordering only through atomics, barriers, dispatches | T-17, T-01 |
| I-008 (process side) | the kernel's finalizing writes in D, counted | T-16 |
| K-01 (process side) | maxKeys from maxBufferLength | T-19, T-30 |
| K-02 | platform | T-30 |
| K-03 (process side) | pipeline memory on the device | T-18 |
| K-04 (process side) | validation of explicit values | T-03, T-18, T-20 |
| K-05 (process side) | defaults from the table | T-20 |
| K-06 (process side) | dispatch sizes | T-13 |
| K-07 (process side) | the cap in the host loop | T-10 |
| K-08 (process side) | the kernel's stack | T-11, T-40 |
| K-09 (process side) | auxiliaryBytes and bookkeepingBytes | T-21 |
| K-10 (process side) | zero input dispatches no lqsort | T-08 |
| K-11 | timing definitions | T-21, T-28 |
| K-12 (process side) | CLI exit codes observed | T-27, T-42 |
| K-13 | performance target (recorded) | T-32 |
| K-14 | tune within 30 minutes (recorded) | T-34 |
| E-01, E-02 (process side) | no command buffer for n ≤ 1 | T-06 |
| E-03 (process side) | one alternative sort below minseq | T-07 |
| E-04 (process side) | duplicates terminate | T-08, T-09 |
| E-05 (process side) | invalidParameters before GPU work | T-18 |
| E-06, E-07, E-08 (process side) | buffer and count errors | T-19 |
| E-09 (process side) | command-buffer error handling | T-42 |
| E-10 (process side) | stack overflow flag, read-back checks | T-12 |
| E-11 (process side) | mismatched key type | T-23 |
| E-12 (process side) | allocation failure | T-24 |
| E-13 (process side) | adversarial phase-two inputs | T-40 |
| E-14 (process side) | float specials on the GPU | T-05, T-01 |
| E-15 | CLI input size errors | T-27 |
| E-16 | concurrent calls serialized | T-22 |
| E-17 (process side) | empty children in the host loop | T-13 |
| E-18 | missing or broken metallib | T-35 |
| E-19 | stale metallib | T-35 |
| E-20 | invalid tuning table | T-37 |
| E-21 | unknown device name | T-37 |
| E-22 | tune verification failure | T-38 |
| E-23 | tune table write failure | T-38 |
| E-24 (process side) | no lqsort dispatch when done is empty | T-08 |
| E-25 | invalid table under tune --write | T-38 |
| O-2 (process side) | min/max reduction and atomics in the kernel | T-14, T-41 |

## Excluded by the spec

| Spec id | Reason |
| ------- | ------ |
| O-1 | retired in v0.2 (`tune` became R-24) |
-/

end GpuQuicksortSpec.GpuQuicksort.Theorems
