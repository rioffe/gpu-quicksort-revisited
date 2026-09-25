import GpuQuicksortSpec.GpuQuicksort.Spec
import GpuQuicksortSpec.GpuQuicksort.Model
import GpuQuicksortSpec.GpuQuicksort.Theorems

/-!
# GpuQuicksortSpec.GpuQuicksort.PhaseTwo
=========================================

Phase two as the **explicit stack machine** R-13 describes (the kernel `lqsort`), proved to sort,
to finalize every position exactly once (I-008), and to keep its stack within the depth bound K-08
derives from the shorter-first rule.

## The model

- A pending segment is its start position `b` and its current contents `xs`; it covers
  [b, b + |xs|). Which of the two buffers holds the contents (R-07) does not affect the result and
  is not modeled; the parallel partition that moves them is proved in `ParallelPartition.lean`.
- One step pops the top segment, partitions its contents around `piv xs`, **finalizes** the gap
  (every pivot-equal position, R-06), and turns the two parts into child segments: the lower part
  at [b, b + L) and the upper part at [e − G, e). A child with at least `S` elements is pushed
  — **the longer first, then the shorter**, so the shorter is on top (R-13). A child with fewer
  than `S` elements is finalized at once by the alternative sort (R-15), modeled as a plain sort.
- The machine's output is the list of finalized (position, value) writes.
-/

namespace GpuQuicksortSpec.GpuQuicksort.PhaseTwo

open GpuQuicksortSpec.GpuQuicksort.Spec
open GpuQuicksortSpec.GpuQuicksort.Model
open GpuQuicksortSpec.GpuQuicksort.Theorems

/-- A pending segment: it covers [b, b + |xs|) and currently holds `xs`. -/
structure Seg where
  b : Nat
  xs : List Nat
deriving DecidableEq, Repr

/-- The correct writes for [b, b + m) when the sorted result is `tgt`: position i gets `tgt[i]`. -/
def cw (tgt : List Nat) (b m : Nat) : List (Nat × Nat) := (List.range' b m).zip ((tgt.drop b).take m)

/-- R-13 — the lower child: [b, b + L) holding the below-pivot elements. -/
def lowerSeg (piv : List Nat → Nat) (g : Seg) : Seg := ⟨g.b, lowerPart (piv g.xs) g.xs⟩
/-- R-13 — the upper child: [e − G, e) holding the above-pivot elements. -/
def upperSeg (piv : List Nat → Nat) (g : Seg) : Seg :=
  ⟨g.b + g.xs.length - (upperPart (piv g.xs) g.xs).length, upperPart (piv g.xs) g.xs⟩
/-- R-06 — the gap writes: the pivot at every position of [b + L, e − G). -/
def gapW (piv : List Nat → Nat) (g : Seg) : List (Nat × Nat) :=
  (List.range' (g.b + (lowerPart (piv g.xs) g.xs).length) (g.xs.count (piv g.xs))).zip
    (List.replicate (g.xs.count (piv g.xs)) (piv g.xs))
/-- R-15 — a child shorter than S is finalized at once by the alternative sort. -/
def smallW (S : Nat) (c : Seg) : List (Nat × Nat) :=
  if c.xs.length < S then (List.range' c.b c.xs.length).zip (c.xs.mergeSort leB) else []
/-- R-13 — a child with at least S elements is pushed. -/
def pushIf (S : Nat) (c : Seg) : List Seg := if S ≤ c.xs.length then [c] else []

/-- R-13 — one step: pop the top, finalize the gap and the small children, push the longer child
then the shorter one (the stack's head is its top). -/
def step2 (S : Nat) (piv : List Nat → Nat) : List Seg × List (Nat × Nat) → List Seg × List (Nat × Nat)
  | ([], fin) => ([], fin)
  | (g :: rest, fin) =>
    let lo := lowerSeg piv g
    let hi := upperSeg piv g
    let longer := if hi.xs.length ≤ lo.xs.length then lo else hi
    let shorter := if hi.xs.length ≤ lo.xs.length then hi else lo
    (pushIf S shorter ++ pushIf S longer ++ rest, fin ++ gapW piv g ++ smallW S lo ++ smallW S hi)

/-- R-13 — run the machine for `fuel` steps (a step on an empty stack changes nothing). -/
def run2 (S : Nat) (piv : List Nat → Nat) : Nat → List Seg × List (Nat × Nat) → List Seg × List (Nat × Nat)
  | 0, st => st
  | k + 1, st => run2 S piv k (step2 S piv st)

/-- R-13, R-15, E-03 — the start state for a sequence: a short one is alternative-sorted at once,
a long one is pushed as the only stack entry. -/
def start2 (S : Nat) (xs : List Nat) : List Seg × List (Nat × Nat) :=
  if xs.length < S then ([], smallW S ⟨0, xs⟩) else ([⟨0, xs⟩], [])

/-- K-08 — the depth invariant on a top-first stack: the entry with k entries below it holds at
most n / 2^k elements. -/
def depthOK (n : Nat) : List Seg → Prop
  | [] => True
  | g :: gs => g.xs.length * 2 ^ gs.length ≤ n ∧ depthOK n gs

/-! ## Proofs -/

/-- **(lemma)**: a window of a sorted list is sorted. -/
theorem sliceSorted (tgt : List Nat) (ht : tgt.Pairwise (· ≤ ·)) (b m : Nat) :
    ((tgt.drop b).take m).Pairwise (· ≤ ·) :=
  ht.sublist ((List.take_sublist m _).trans (List.drop_sublist b _))

/-- **(lemma)**: partitioning a sorted list reproduces it: lower part, then gap, then upper part. -/
theorem sortedSplit (p : Nat) (t : List Nat) (ht : t.Pairwise (· ≤ ·)) : partition3 p t = t := by
  apply sortedPermUnique _ _ _ ht (partitionPerm p t)
  simp only [partition3, lowerPart, gapPart, upperPart]
  rw [List.pairwise_append, List.pairwise_append]
  refine ⟨⟨ht.filter _, List.pairwise_replicate.2 (Or.inr (Nat.le_refl p)), ?_⟩, ht.filter _, ?_⟩
  · intro a ha b hb
    simp only [List.mem_filter, decide_eq_true_eq, List.mem_replicate] at ha hb; omega
  · intro a ha b hb
    simp only [List.mem_filter, decide_eq_true_eq, List.mem_append, List.mem_replicate] at ha hb; omega

/-- **(lemma)**: a sorted window of length m, when the window fits. -/
theorem sliceLength (tgt : List Nat) (b m : Nat) (h : b + m ≤ tgt.length) : ((tgt.drop b).take m).length = m := by
  simp; omega

/-- **(lemma)**: splitting a pending segment. If the segment holds a permutation of its sorted
window, then its lower child holds exactly the first L sorted values, its upper child exactly
the last G, and the correct writes of the segment are those of the lower child, then the gap,
then those of the upper child. -/
theorem segSplit (piv : List Nat → Nat) (tgt : List Nat) (ht : tgt.Pairwise (· ≤ ·)) (g : Seg)
    (hp : g.xs.Perm ((tgt.drop g.b).take g.xs.length)) (hfit : g.b + g.xs.length ≤ tgt.length) :
    (lowerSeg piv g).xs.Perm ((tgt.drop (lowerSeg piv g).b).take (lowerSeg piv g).xs.length) ∧
    (upperSeg piv g).xs.Perm ((tgt.drop (upperSeg piv g).b).take (upperSeg piv g).xs.length) ∧
    (lowerSeg piv g).xs.length + (upperSeg piv g).xs.length + g.xs.count (piv g.xs) = g.xs.length ∧
    (upperSeg piv g).b + (upperSeg piv g).xs.length = g.b + g.xs.length ∧
    cw tgt g.b g.xs.length =
      cw tgt (lowerSeg piv g).b (lowerSeg piv g).xs.length ++ gapW piv g ++
        cw tgt (upperSeg piv g).b (upperSeg piv g).xs.length := by
  simp only [lowerSeg, upperSeg, cw, gapW]
  generalize piv g.xs = p
  generalize hm : g.xs.length = m at *
  obtain ⟨X, hX⟩ : ∃ X, tgt.drop g.b = X := ⟨_, rfl⟩
  rw [hX] at hp
  have hXlen : m ≤ X.length := by rw [← hX]; simp; omega
  have hs : (X.take m).Pairwise (· ≤ ·) := by rw [← hX]; exact sliceSorted tgt ht g.b m
  have hsplit := sortedSplit p (X.take m) hs
  simp only [partition3] at hsplit
  have hLp := hp.filter (fun x => decide (x < p))
  have hGp := hp.filter (fun x => decide (p < x))
  have hcnt : g.xs.count p = (X.take m).count p := hp.count_eq p
  change (lowerPart p g.xs).Perm (lowerPart p (X.take m)) at hLp
  change (upperPart p g.xs).Perm (upperPart p (X.take m)) at hGp
  generalize hA : lowerPart p (X.take m) = A at hsplit hLp
  generalize hB : gapPart p (X.take m) = B at hsplit
  generalize hC : upperPart p (X.take m) = C at hsplit hGp
  have hL : (lowerPart p g.xs).length = A.length := hLp.length_eq
  have hG : (upperPart p g.xs).length = C.length := hGp.length_eq
  have hBrep : B = List.replicate (g.xs.count p) p := by rw [← hB, hcnt]; rfl
  have hlens : A.length + B.length + C.length = m := by
    have := congrArg List.length hsplit; simp only [List.length_append, List.length_take] at this; omega
  have hBlen : B.length = g.xs.count p := by rw [hBrep, List.length_replicate]
  have takeA : X.take A.length = A := by
    have : X.take A.length = (X.take m).take A.length := by rw [List.take_take]; congr 1; omega
    rw [this, ← hsplit, List.append_assoc, List.take_left' rfl]
  have dropC : (X.drop (A.length + B.length)).take C.length = C := by
    have e1 : (X.take m).drop (A.length + B.length) = C := by
      rw [← hsplit, List.drop_left' (by simp)]
    rw [List.drop_take] at e1
    rw [show C.length = m - (A.length + B.length) by omega, e1]
  have hub : g.b + m - C.length = g.b + (A.length + B.length) := by omega
  have hdrop : tgt.drop (g.b + (A.length + B.length)) = X.drop (A.length + B.length) := by
    rw [← hX, List.drop_drop]
  rw [hL, hG, hub, hdrop, hX, takeA, dropC]
  refine ⟨hLp, hGp, by omega, by omega, ?_⟩
  have hr : List.range' g.b m = List.range' g.b A.length ++ List.range' (g.b + A.length) B.length ++
      List.range' (g.b + (A.length + B.length)) C.length := by
    have h1 : List.range' g.b A.length ++ List.range' (g.b + A.length) B.length =
        List.range' g.b (A.length + B.length) := List.range'_append_1
    have h2 : List.range' g.b (A.length + B.length) ++ List.range' (g.b + (A.length + B.length)) C.length =
        List.range' g.b (A.length + B.length + C.length) := List.range'_append_1
    rw [h1, h2, hlens]
  rw [hr, ← hsplit, List.zip_append (by simp), List.zip_append (by simp), hBrep]
  simp only [List.length_replicate]

/-- The correct writes a stack still owes: each pending segment's window of the sorted result. -/
def owed (tgt : List Nat) (st : List Seg) : List (Nat × Nat) := st.flatMap (fun g => cw tgt g.b g.xs.length)

/-- A well-formed pending segment: it holds a permutation of its sorted window, the window fits, and
it has at least S elements (only such children are pushed, R-13). -/
def good (S : Nat) (tgt : List Nat) (g : Seg) : Prop :=
  g.xs.Perm ((tgt.drop g.b).take g.xs.length) ∧ g.b + g.xs.length ≤ tgt.length ∧ S ≤ g.xs.length

/-- The number of elements on the stack: the termination measure. -/
def mass (st : List Seg) : Nat := (st.map (·.xs.length)).sum

theorem owed_append (tgt : List Nat) (a c : List Seg) : owed tgt (a ++ c) = owed tgt a ++ owed tgt c := by
  simp [owed]

theorem owed_cons (tgt : List Nat) (g : Seg) (c : List Seg) :
    owed tgt (g :: c) = cw tgt g.b g.xs.length ++ owed tgt c := by
  simp [owed]

theorem mass_append (a c : List Seg) : mass (a ++ c) = mass a + mass c := by simp [mass]

theorem mass_pushIf (S : Nat) (c : Seg) : mass (pushIf S c) ≤ c.xs.length := by
  unfold pushIf; split <;> simp [mass]

theorem length_pushIf (S : Nat) (c : Seg) : (pushIf S c).length ≤ 1 := by
  unfold pushIf; split <;> simp

/-- **(lemma)**: a child's accounting. What the step finalizes for a child now (its alternative
sort, if it is short) plus what the child still owes once pushed (if it is long) is exactly the
child's correct writes. -/
theorem childAcct (S : Nat) (tgt : List Nat) (ht : tgt.Pairwise (· ≤ ·)) (c : Seg)
    (hp : c.xs.Perm ((tgt.drop c.b).take c.xs.length)) :
    smallW S c ++ owed tgt (pushIf S c) = cw tgt c.b c.xs.length := by
  unfold smallW pushIf
  by_cases h : c.xs.length < S
  · have hn : ¬ S ≤ c.xs.length := by omega
    simp only [h, hn, ↓reduceIte, owed, List.flatMap_nil, List.append_nil, cw]
    congr 1
    exact sortedPermUnique _ _ (mergeSortSorted _) (sliceSorted tgt ht c.b _)
      ((List.mergeSort_perm _ _).trans hp)
  · have hn : S ≤ c.xs.length := by omega
    simp [h, hn, owed]

/-- **(lemma)**: pushed children are well-formed. -/
theorem pushGood (S : Nat) (tgt : List Nat) (c : Seg)
    (hp : c.xs.Perm ((tgt.drop c.b).take c.xs.length)) (hfit : c.b + c.xs.length ≤ tgt.length) :
    ∀ x ∈ pushIf S c, good S tgt x := by
  unfold pushIf; split
  · intro x hx; simp only [List.mem_singleton] at hx; subst hx; exact ⟨hp, hfit, by assumption⟩
  · simp

/-- **(lemma)**: the depth invariant survives pushing at most one entry `l` and then at most one
entry `s` onto `rest`, when each fits its new depth. -/
theorem depthPush (n : Nat) (rest l s : List Seg) (hr : depthOK n rest)
    (hl1 : l.length ≤ 1) (hs1 : s.length ≤ 1)
    (hl : ∀ c ∈ l, c.xs.length * 2 ^ rest.length ≤ n)
    (hs : ∀ c ∈ s, c.xs.length * 2 ^ (l.length + rest.length) ≤ n) : depthOK n (s ++ l ++ rest) := by
  have hlr : depthOK n (l ++ rest) := by
    match l, hl1 with
    | [], _ => simpa using hr
    | [c], _ => exact ⟨hl c (by simp), hr⟩
  match s, hs1 with
  | [], _ => simpa using hlr
  | [c], _ => exact ⟨by simpa [Nat.add_comm] using hs c (by simp), hlr⟩

/-- **(lemma)**: one step of the machine on a non-empty stack. The step keeps every entry
well-formed and the depth invariant; it trades the popped segment's owed writes for exactly the
finalized writes plus the children's owed writes; and it removes at least the gap from the stack. -/
theorem stepFacts (S n : Nat) (piv : List Nat → Nat) (tgt : List Nat) (ht : tgt.Pairwise (· ≤ ·))
    (g : Seg) (rest : List Seg) (fin : List (Nat × Nat))
    (hg : good S tgt g) (hdep : depthOK n (g :: rest)) :
    (∀ x ∈ (step2 S piv (g :: rest, fin)).1, x ∈ rest ∨ good S tgt x) ∧
    depthOK n (step2 S piv (g :: rest, fin)).1 ∧
    ((step2 S piv (g :: rest, fin)).2 ++ owed tgt (step2 S piv (g :: rest, fin)).1).Perm
      (fin ++ owed tgt (g :: rest)) ∧
    mass (step2 S piv (g :: rest, fin)).1 + g.xs.count (piv g.xs) ≤ mass (g :: rest) := by
  obtain ⟨hp, hfit, _⟩ := hg
  obtain ⟨h1, h2, h3, h4, h5⟩ := segSplit piv tgt ht g hp hfit
  have hlofit : (lowerSeg piv g).b + (lowerSeg piv g).xs.length ≤ tgt.length := by
    simp only [lowerSeg] at h3 ⊢; omega
  have hhifit : (upperSeg piv g).b + (upperSeg piv g).xs.length ≤ tgt.length := by omega
  have alo := childAcct S tgt ht (lowerSeg piv g) h1
  have ahi := childAcct S tgt ht (upperSeg piv g) h2
  have glo := pushGood S tgt (lowerSeg piv g) h1 hlofit
  have ghi := pushGood S tgt (upperSeg piv g) h2 hhifit
  have mlo := mass_pushIf S (lowerSeg piv g)
  have mhi := mass_pushIf S (upperSeg piv g)
  obtain ⟨hdg, hdr⟩ := hdep
  simp only [step2]
  generalize lowerSeg piv g = lo at *
  generalize upperSeg piv g = hi at *
  have hmass : mass (g :: rest) = g.xs.length + mass rest := by simp [mass]
  -- the shorter child fits twice into the parent, the longer once
  have key : ∀ (sh lg : Seg), sh.xs.length ≤ lg.xs.length →
      sh.xs.length + lg.xs.length + g.xs.count (piv g.xs) = g.xs.length →
      ∀ (l s : List Seg), l = pushIf S lg → s = pushIf S sh →
      depthOK n (s ++ l ++ rest) := by
    intro sh lg hle hsum l s hl hs
    have hb : g.xs.length * 2 ^ rest.length ≤ n := by simpa using hdg
    apply depthPush n rest l s hdr (hl ▸ length_pushIf S lg) (hs ▸ length_pushIf S sh)
    · intro c hc; rw [hl] at hc; unfold pushIf at hc; split at hc
      · simp only [List.mem_singleton] at hc; subst hc
        exact Nat.le_trans (Nat.mul_le_mul_right _ (by omega)) hb
      · simp at hc
    · intro c hc; rw [hs] at hc; unfold pushIf at hc; split at hc
      · simp only [List.mem_singleton] at hc; subst hc
        have hl1 := hl ▸ length_pushIf S lg
        have hpow : 2 ^ (l.length + rest.length) ≤ 2 * 2 ^ rest.length := by
          rw [Nat.pow_add]; exact Nat.mul_le_mul_right _ (by
            rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hl1 with h | h <;> simp [h])
        calc c.xs.length * 2 ^ (l.length + rest.length)
            ≤ c.xs.length * (2 * 2 ^ rest.length) := Nat.mul_le_mul_left _ hpow
          _ = (2 * c.xs.length) * 2 ^ rest.length := by rw [← Nat.mul_assoc, Nat.mul_comm c.xs.length 2]
          _ ≤ g.xs.length * 2 ^ rest.length := Nat.mul_le_mul_right _ (by omega)
          _ ≤ n := hb
      · simp at hc
  have hperm : ∀ (A B C D E F R Fn : List (Nat × Nat)), (Fn ++ B ++ A ++ C ++ (D ++ E ++ R)).Perm
      (Fn ++ (A ++ D ++ B ++ C ++ E) ++ R) ∧ (Fn ++ B ++ A ++ C ++ (E ++ D ++ R)).Perm
      (Fn ++ (A ++ D ++ B ++ C ++ E) ++ R) := by
    intro A B C D E F R Fn
    constructor <;> exact List.perm_iff_count.2 (fun a => by simp only [List.count_append]; omega)
  by_cases hc : hi.xs.length ≤ lo.xs.length
  · simp only [hc, ↓reduceIte]
    refine ⟨?_, key hi lo hc (by omega) _ _ rfl rfl, ?_, ?_⟩
    · intro x hx; simp only [List.mem_append] at hx
      rcases hx with (hx | hx) | hx
      · exact Or.inr (ghi x hx)
      · exact Or.inr (glo x hx)
      · exact Or.inl hx
    · rw [owed_append, owed_append, owed_cons, h5, ← alo, ← ahi]
      have := (hperm (smallW S lo) (gapW piv g) (smallW S hi) (owed tgt (pushIf S lo))
        (owed tgt (pushIf S hi)) [] (owed tgt rest) fin).2
      simpa only [List.append_assoc] using this
    · rw [mass_append, mass_append, hmass]; omega
  · simp only [hc, ↓reduceIte]
    refine ⟨?_, key lo hi (by omega) (by omega) _ _ rfl rfl, ?_, ?_⟩
    · intro x hx; simp only [List.mem_append] at hx
      rcases hx with (hx | hx) | hx
      · exact Or.inr (glo x hx)
      · exact Or.inr (ghi x hx)
      · exact Or.inl hx
    · rw [owed_append, owed_append, owed_cons, h5, ← alo, ← ahi]
      have := (hperm (smallW S lo) (gapW piv g) (smallW S hi) (owed tgt (pushIf S lo))
        (owed tgt (pushIf S hi)) [] (owed tgt rest) fin).1
      simpa only [List.append_assoc] using this
    · rw [mass_append, mass_append, hmass]; omega

/-- The machine's invariant for a sequence whose sorted result is `tgt` (n = |tgt|): every pending
entry is well-formed, the depth invariant holds, and the finalized writes plus the owed writes are
exactly the correct writes for [0, n). -/
def Inv (S : Nat) (tgt : List Nat) (st : List Seg × List (Nat × Nat)) : Prop :=
  (∀ g ∈ st.1, good S tgt g) ∧ depthOK tgt.length st.1 ∧
    (st.2 ++ owed tgt st.1).Perm (cw tgt 0 tgt.length)

/-- **(lemma)**: one step keeps the invariant and does not grow the stack's mass. -/
theorem stepInv (S : Nat) (piv : List Nat → Nat) (tgt : List Nat) (ht : tgt.Pairwise (· ≤ ·))
    (st : List Seg × List (Nat × Nat)) (h : Inv S tgt st) :
    Inv S tgt (step2 S piv st) ∧ mass (step2 S piv st).1 ≤ mass st.1 := by
  obtain ⟨stk, fin⟩ := st
  match stk, h with
  | [], h => exact ⟨h, Nat.le_refl _⟩
  | g :: rest, ⟨hg, hd, hp⟩ =>
    obtain ⟨a, b, c, d⟩ := stepFacts S tgt.length piv tgt ht g rest fin (hg g (by simp)) hd
    refine ⟨⟨fun x hx => ?_, b, c.trans hp⟩, Nat.le_trans (Nat.le_add_right _ _) d⟩
    rcases a x hx with h | h
    · exact hg x (by simp [h])
    · exact h

/-- **(lemma)**: running the machine keeps the invariant. -/
theorem runInv (S : Nat) (piv : List Nat → Nat) (tgt : List Nat) (ht : tgt.Pairwise (· ≤ ·)) :
    ∀ (k : Nat) (st : List Seg × List (Nat × Nat)), Inv S tgt st → Inv S tgt (run2 S piv k st)
  | 0, _, h => h
  | k + 1, st, h => runInv S piv tgt ht k _ (stepInv S piv tgt ht st h).1

/-- **(lemma)**: termination. With S ≥ 1 and a pivot drawn from the sequence (R-14), every step on a
non-empty stack removes at least one element, so `mass` steps empty the stack. -/
theorem runEmpties (S : Nat) (hS : 0 < S) (piv : List Nat → Nat)
    (hpiv : ∀ ys : List Nat, ys ≠ [] → piv ys ∈ ys) (tgt : List Nat) (ht : tgt.Pairwise (· ≤ ·)) :
    ∀ (k : Nat) (st : List Seg × List (Nat × Nat)), Inv S tgt st → mass st.1 ≤ k →
      (run2 S piv k st).1 = []
  | 0, ⟨[], _⟩, _, _ => rfl
  | 0, ⟨g :: rest, _⟩, ⟨hg, _, _⟩, hm => by
    have := (hg g (by simp)).2.2
    have hm' : mass (g :: rest) ≤ 0 := hm
    simp only [mass, List.map_cons, List.sum_cons] at hm'; omega
  | k + 1, ⟨[], fin⟩, h, _ => runEmpties S hS piv hpiv tgt ht k ⟨[], fin⟩ h (by simp [mass])
  | k + 1, ⟨g :: rest, fin⟩, ⟨hg, hd, hp⟩, hm => by
    have hgood := hg g (by simp)
    obtain ⟨_, _, _, d⟩ := stepFacts S tgt.length piv tgt ht g rest fin hgood hd
    have hne : g.xs ≠ [] := by
      intro e; have h2 := hgood.2.2; rw [e, List.length_nil] at h2; omega
    have hc : 0 < g.xs.count (piv g.xs) := List.count_pos_iff.2 (hpiv _ hne)
    exact runEmpties S hS piv hpiv tgt ht k _ (stepInv S piv tgt ht _ ⟨hg, hd, hp⟩).1 (by
      have hm' : mass (g :: rest) ≤ k + 1 := hm
      show mass (step2 S piv (g :: rest, fin)).1 ≤ k
      omega)

/-- **(lemma)**: the start state satisfies the invariant, with mass at most n. -/
theorem startInv (S : Nat) (xs : List Nat) :
    Inv S (xs.mergeSort leB) (start2 S xs) ∧ mass (start2 S xs).1 ≤ xs.length := by
  have hlen : (xs.mergeSort leB).length = xs.length := List.length_mergeSort _
  have htk : (xs.mergeSort leB).take xs.length = xs.mergeSort leB := List.take_of_length_le (by omega)
  unfold start2
  by_cases h : xs.length < S
  · simp only [h, ↓reduceIte]
    refine ⟨⟨by simp, by simp [depthOK], ?_⟩, by simp [mass]⟩
    simp [smallW, h, owed, cw, hlen, htk]
  · simp only [h, ↓reduceIte]
    refine ⟨⟨?_, ?_, ?_⟩, by simp [mass]⟩
    · intro g hg; simp only [List.mem_singleton] at hg; subst hg
      refine ⟨?_, by simp [hlen], by simp; omega⟩
      simp only [List.drop_zero]; rw [← hlen, List.take_length]; exact (List.mergeSort_perm _ _).symm
    · simp [depthOK, hlen]
    · simp [owed, hlen]

/-- **R-13** (T-11, T-17): the phase-two stack machine sorts. For any threshold S ≥ 1 and any pivot
rule that picks an element of the sequence (R-14's median of three does, `medianOfThreeMem`),
started on a sequence of n elements, n steps empty the stack, and the finalized writes are exactly
the pairs (i, i-th smallest element) for i ∈ [0, n), up to order. Not a re-reading of `step2`: the
machine only ever sees unsorted child contents, and this says its scattered writes assemble the sort. -/
theorem phaseTwoSorts (S : Nat) (hS : 0 < S) (piv : List Nat → Nat)
    (hpiv : ∀ ys : List Nat, ys ≠ [] → piv ys ∈ ys) (xs : List Nat) (k : Nat) (hk : xs.length ≤ k) :
    (run2 S piv k (start2 S xs)).1 = [] ∧
    (run2 S piv k (start2 S xs)).2.Perm ((List.range xs.length).zip (xs.mergeSort leB)) := by
  have ht := mergeSortSorted xs
  have hlen : (xs.mergeSort leB).length = xs.length := List.length_mergeSort _
  have htk : (xs.mergeSort leB).take xs.length = xs.mergeSort leB := List.take_of_length_le (by omega)
  obtain ⟨h0, hm⟩ := startInv S xs
  have hinv := runInv S piv _ ht k _ h0
  have hemp := runEmpties S hS piv hpiv _ ht k _ h0 (by omega)
  refine ⟨hemp, ?_⟩
  have := hinv.2.2
  rw [hemp] at this
  simpa [owed, cw, hlen, htk, List.range_eq_range'] using this

/-- **I-008** (T-16): in phase two every position of the sequence is finalized **exactly once**:
the positions of the finalized writes are a permutation of [0, n), so none is missed and none is
written twice. Each write comes from a gap fill (`gapW`) or an alternative-sort write-back
(`smallW`); the partition's own moves are not finalizing writes. Scope: this is I-008 for one
phase-two sequence; for one phase-one partition, `ParallelPartition.partitionExactlyOnce` shows the
cursors and the gap fill cover each index once. That the phase-one gaps and the phase-two sequences
tile [0, n) is not proven here. -/
theorem phaseTwoExactlyOnce (S : Nat) (hS : 0 < S) (piv : List Nat → Nat)
    (hpiv : ∀ ys : List Nat, ys ≠ [] → piv ys ∈ ys) (xs : List Nat) (k : Nat) (hk : xs.length ≤ k) :
    ((run2 S piv k (start2 S xs)).2.map Prod.fst).Perm (List.range xs.length) ∧
    ((run2 S piv k (start2 S xs)).2.map Prod.fst).Nodup := by
  have hp := ((phaseTwoSorts S hS piv hpiv xs k hk).2).map Prod.fst
  rw [List.map_fst_zip (by simp [List.length_mergeSort])] at hp
  exact ⟨hp, hp.nodup_iff.2 List.nodup_range⟩

/-- **(lemma)**: a stack satisfying the depth invariant, whose entries all hold at least S
elements, has at most log2(n / S) + 1 entries. -/
theorem depthBound (S n : Nat) (hS : 0 < S) :
    ∀ st : List Seg, depthOK n st → (∀ g ∈ st, S ≤ g.xs.length) → st.length ≤ Nat.log2 (n / S) + 1
  | [], _, _ => by simp
  | g :: gs, ⟨hg, _⟩, hall => by
    have h1 : S * 2 ^ gs.length ≤ n :=
      Nat.le_trans (Nat.mul_le_mul_right _ (hall g (by simp))) hg
    have h2 : 2 ^ gs.length ≤ n / S := (Nat.le_div_iff_mul_le hS).2 (by rw [Nat.mul_comm]; exact h1)
    have h3 : gs.length ≤ Nat.log2 (n / S) :=
      (Nat.le_log2 (by have := Nat.one_le_two_pow (n := gs.length); omega)).2 h2
    simp; omega

/-- **K-08** (T-11, T-40): the shorter-first rule bounds the stack. In every state the machine
reaches on a sequence of ℓ elements, the stack holds at most log2(ℓ / S) + 1 entries, whatever the
pivot rule (so under E-13's lopsided pivots too); with ℓ ≤ 2^31 − 1 (K-01) and S ≥ 64 (K-04)
that is at most 25, below the 32-entry capacity and the spec's bound of 27. -/
theorem phaseTwoDepth (S : Nat) (hS : 0 < S) (piv : List Nat → Nat) (xs : List Nat) (k : Nat) :
    (run2 S piv k (start2 S xs)).1.length ≤ Nat.log2 (xs.length / S) + 1 ∧
    (xs.length ≤ keyCap → minseqFloor ≤ S → (run2 S piv k (start2 S xs)).1.length ≤ 25) := by
  have hlen : (xs.mergeSort leB).length = xs.length := List.length_mergeSort _
  have hinv := runInv S piv _ (mergeSortSorted xs) k _ (startInv S xs).1
  have hb := depthBound S _ hS _ hinv.2.1 (fun g hg => (hinv.1 g hg).2.2)
  rw [hlen] at hb
  refine ⟨hb, fun hl hm => ?_⟩
  have := stackArithmetic xs.length S hl hm
  omega

/-- **(lemma)**: R-14's median-of-three pivot satisfies the hypothesis of `phaseTwoSorts`. -/
theorem medianOfThreePicks : ∀ ys : List Nat, ys ≠ [] → medianOfThree ys ∈ ys := medianOfThreeMem

end GpuQuicksortSpec.GpuQuicksort.PhaseTwo
