import GpuQuicksortSpec.GpuQuicksort.Spec
import GpuQuicksortSpec.GpuQuicksort.Model
import GpuQuicksortSpec.GpuQuicksort.Theorems
import GpuQuicksortSpec.GpuQuicksort.PhaseTwo

/-!
# GpuQuicksortSpec.GpuQuicksort.Pipeline
========================================

The **whole sort**: phase one (R-08) on actual sequences, then phase two (R-12, R-13) on every
sequence phase one leaves, proved to write every index of D exactly once with its final value
(I-008).

## The model

- Phase one is `Model.p1Loop` with sequences carried as segments (start, contents) rather than
  lengths. One iteration partitions every `work` sequence around its pivot, **finalizes its gap**
  (the `gqsort_fill` of R-06/R-10), drops empty children (E-17), and sends each child to `done` if
  shorter than `minlength`, to `work` otherwise. The loop condition and the iteration cap are
  `p1Loop`'s. The partition itself is the list-level one; `ParallelPartition.lean` proves the
  threadgroups compute exactly it.
- The phase-one pivot is **any** function of the sequence (`pv`), so O-2's min/max average, D-20's
  median-of-three root and R-11's `medianOfThree` are all instances; correctness does not use it.
- Phase two then runs the `PhaseTwo` stack machine on every sequence of `done ++ work` (R-12: work
  merged into done), each on its own, and its writes are placed at the sequence's start.
-/

namespace GpuQuicksortSpec.GpuQuicksort.Pipeline

open GpuQuicksortSpec.GpuQuicksort.Spec
open GpuQuicksortSpec.GpuQuicksort.Model
open GpuQuicksortSpec.GpuQuicksort.Theorems
open GpuQuicksortSpec.GpuQuicksort.PhaseTwo

/-- R-08 — the phase-one state on segments: pending sequences, finished sequences, the finalized
gap writes, and `p1Loop`'s counters. -/
structure P1S where
  work : List Seg
  done : List Seg
  fin : List (Nat × Nat)
  iterations : Nat
  capReached : Bool

/-- R-04, R-06 — a phase-one partition of `g` around `pv g`: its two children. -/
def split1 (pv : Seg → Nat) (g : Seg) : List Seg :=
  [lowerSeg (fun _ => pv g) g, upperSeg (fun _ => pv g) g]

/-- R-06, R-10 — the gap fill of a phase-one partition. -/
def gap1 (pv : Seg → Nat) (g : Seg) : List (Nat × Nat) := gapW (fun _ => pv g) g

/-- R-08, E-17 — one iteration, as `Model.p1Step` on segments. -/
def p1StepS (pv : Seg → Nat) (minlength : Nat) (st : P1S) : P1S :=
  let kids := (st.work.flatMap (split1 pv)).filter (fun c => decide (0 < c.xs.length))
  { work := kids.filter (fun c => decide (minlength ≤ c.xs.length)),
    done := st.done ++ kids.filter (fun c => decide (c.xs.length < minlength)),
    fin := st.fin ++ st.work.flatMap (gap1 pv),
    iterations := st.iterations + 1, capReached := st.capReached }

/-- R-08, K-07 — the loop, as `Model.p1Loop` on segments. -/
def p1LoopS (pv : Seg → Nat) (minlength M maxIter : Nat) : Nat → P1S → P1S
  | 0, st => st
  | fuel + 1, st =>
    if st.work ≠ [] ∧ st.work.length + st.done.length < M then
      if st.iterations = maxIter then { st with capReached := true }
      else p1LoopS pv minlength M maxIter fuel (p1StepS pv minlength st)
    else st

/-- R-12 — one phase-two threadgroup's writes for a sequence, placed at the sequence's start. -/
def phaseTwoWrites (S : Nat) (piv : List Nat → Nat) (k : Nat) (g : Seg) : List (Nat × Nat) :=
  (run2 S piv k (start2 S g.xs)).2.map (fun w => (g.b + w.1, w.2))

/-- R-03, R-08, R-12 — the whole sort's finalizing writes to D: phase one's gap fills, then
phase two on every sequence of `done ++ work`. -/
def gpuQuicksort (S : Nat) (pv : Seg → Nat) (piv : List Nat → Nat)
    (minlength M maxIter fuel k : Nat) (xs : List Nat) : List (Nat × Nat) :=
  let st := p1LoopS pv minlength M maxIter fuel ⟨[⟨0, xs⟩], [], [], 0, false⟩
  st.fin ++ (st.done ++ st.work).flatMap (phaseTwoWrites S piv k)

/-! ## Proofs -/

/-- A segment holding a permutation of its window of the sorted result, and fitting in it. -/
def win (tgt : List Nat) (g : Seg) : Prop :=
  g.xs.Perm ((tgt.drop g.b).take g.xs.length) ∧ g.b + g.xs.length ≤ tgt.length

/-- The phase-one invariant: every pending or finished sequence holds its window, and the gap
writes so far plus the writes the sequences still owe are exactly the correct writes. -/
def InvP (tgt : List Nat) (st : P1S) : Prop :=
  (∀ g ∈ st.work ++ st.done, win tgt g) ∧
    (st.fin ++ owed tgt (st.work ++ st.done)).Perm (cw tgt 0 tgt.length)

/-- **(lemma)**: `flatMap` respects pointwise permutation. -/
theorem flatMap_perm_congr {α β : Type} (f g : α → List β) :
    ∀ l : List α, (∀ a ∈ l, (f a).Perm (g a)) → (l.flatMap f).Perm (l.flatMap g)
  | [], _ => List.Perm.refl _
  | a :: l, h => by
    simp only [List.flatMap_cons]
    exact (h a List.mem_cons_self).append
      (flatMap_perm_congr f g l fun b hb => h b (List.mem_cons_of_mem _ hb))

/-- **(lemma)**: dropping empty sequences does not change what they owe. -/
theorem owed_filter_pos (tgt : List Nat) :
    ∀ l : List Seg, owed tgt (l.filter (fun c => decide (0 < c.xs.length))) = owed tgt l
  | [] => rfl
  | c :: l => by
    by_cases h : 0 < c.xs.length
    · rw [List.filter_cons_of_pos (by simpa using h), owed_cons, owed_cons, owed_filter_pos tgt l]
    · rw [List.filter_cons_of_neg (by simpa using h), owed_cons, owed_filter_pos tgt l]
      have : c.xs.length = 0 := by omega
      simp [cw, this]

/-- **(lemma)**: a phase-one iteration's gap writes plus what the children owe is exactly what
the partitioned sequences owed, and every child holds its window. -/
theorem gapsKids (tgt : List Nat) (ht : tgt.Pairwise (· ≤ ·)) (pv : Seg → Nat) :
    ∀ work : List Seg, (∀ g ∈ work, win tgt g) →
      (work.flatMap (gap1 pv) ++ owed tgt (work.flatMap (split1 pv))).Perm (owed tgt work) ∧
      ∀ c ∈ work.flatMap (split1 pv), win tgt c
  | [], _ => ⟨by simp [owed], by simp⟩
  | g :: ws, h => by
    obtain ⟨ih1, ih2⟩ := gapsKids tgt ht pv ws fun c hc => h c (List.mem_cons_of_mem _ hc)
    obtain ⟨hp, hfit⟩ := h g List.mem_cons_self
    obtain ⟨s1, s2, s3, s4, s5⟩ := segSplit (fun _ => pv g) tgt ht g hp hfit
    have hlofit : (lowerSeg (fun _ => pv g) g).b + (lowerSeg (fun _ => pv g) g).xs.length ≤ tgt.length := by
      simp only [lowerSeg] at s3 ⊢; omega
    refine ⟨?_, ?_⟩
    · simp only [List.flatMap_cons, owed_append, owed_cons]
      rw [s5]
      rw [List.perm_iff_count]; intro v
      have := ih1.count_eq v
      simp only [owed, gap1, split1, List.flatMap_cons, List.flatMap_nil, List.append_nil,
        List.count_append] at this ⊢; omega
    · intro c hc
      simp only [List.flatMap_cons, List.mem_append, split1, List.mem_cons, List.mem_nil_iff,
        or_false] at hc
      rcases hc with (rfl | rfl) | hc
      · exact ⟨s1, hlofit⟩
      · exact ⟨s2, by omega⟩
      · exact ih2 c hc

/-- **(lemma)**: one phase-one iteration keeps the invariant. -/
theorem stepInvP (tgt : List Nat) (ht : tgt.Pairwise (· ≤ ·)) (pv : Seg → Nat) (minlength : Nat)
    (st : P1S) (h : InvP tgt st) : InvP tgt (p1StepS pv minlength st) := by
  obtain ⟨hw, hp⟩ := h
  obtain ⟨k1, k2⟩ := gapsKids tgt ht pv st.work fun g hg => hw g (List.mem_append_left _ hg)
  simp only [p1StepS]
  generalize hK : (st.work.flatMap (split1 pv)) = K at k1 k2
  generalize hKp : K.filter (fun c => decide (0 < c.xs.length)) = Kp
  have hf : Kp.filter (fun c => decide (c.xs.length < minlength)) =
      Kp.filter (fun c => !decide (minlength ≤ c.xs.length)) := by
    apply List.filter_congr; intro c _
    by_cases h1 : c.xs.length < minlength <;> simp [h1] <;> omega
  have k2' : ∀ c ∈ Kp, win tgt c := fun c hc => by
    rw [← hKp] at hc; exact k2 c (List.mem_filter.1 hc).1
  refine ⟨fun g hg => ?_, ?_⟩
  · simp only [List.mem_append, List.mem_filter] at hg
    rcases hg with ⟨hg, _⟩ | hg | ⟨hg, _⟩
    · exact k2' g hg
    · exact hw g (List.mem_append_right _ hg)
    · exact k2' g hg
  · -- what the new lists owe: the old done list plus all children
    have e1 : (owed tgt (Kp.filter (fun c => decide (minlength ≤ c.xs.length)) ++
        (st.done ++ Kp.filter (fun c => decide (c.xs.length < minlength))))).Perm
        (owed tgt st.done ++ owed tgt K) := by
      rw [hf, ← owed_filter_pos tgt K, hKp, ← owed_append]
      apply List.Perm.flatMap_right
      refine List.perm_append_comm.trans ?_
      rw [List.append_assoc]
      exact (List.Perm.append_left _ (List.perm_append_comm.trans (List.filter_append_perm _ _)))
    rw [List.perm_iff_count]; intro v
    have c0 := hp.count_eq v
    have c1 := e1.count_eq v
    have c2 := k1.count_eq v
    simp only [owed_append, List.count_append] at c0 c1 c2 ⊢; omega

/-- **(lemma)**: the phase-one loop keeps the invariant, whatever it does. -/
theorem loopInvP (tgt : List Nat) (ht : tgt.Pairwise (· ≤ ·)) (pv : Seg → Nat) (minlength M maxIter : Nat) :
    ∀ (fuel : Nat) (st : P1S), InvP tgt st → InvP tgt (p1LoopS pv minlength M maxIter fuel st)
  | 0, _, h => h
  | fuel + 1, st, h => by
    simp only [p1LoopS]
    split
    · split
      · exact h
      · exact loopInvP tgt ht pv minlength M maxIter fuel _ (stepInvP tgt ht pv minlength st h)
    · exact h

/-- **(lemma)**: phase two on one sequence holding its window writes exactly that window. -/
theorem phaseTwoWindow (S : Nat) (hS : 0 < S) (piv : List Nat → Nat)
    (hpiv : ∀ ys : List Nat, ys ≠ [] → piv ys ∈ ys) (tgt : List Nat) (ht : tgt.Pairwise (· ≤ ·))
    (g : Seg) (hg : win tgt g) (k : Nat) (hk : g.xs.length ≤ k) :
    (phaseTwoWrites S piv k g).Perm (cw tgt g.b g.xs.length) := by
  have h := ((phaseTwoSorts S hS piv hpiv g.xs k hk).2).map (fun w => (g.b + w.1, w.2))
  have hw : g.xs.mergeSort leB = (tgt.drop g.b).take g.xs.length :=
    sortedPermUnique _ _ (mergeSortSorted _) (sliceSorted tgt ht g.b _)
      ((List.mergeSort_perm _ _).trans hg.1)
  refine h.trans ?_
  rw [hw, cw, List.range'_eq_map_range, List.zip_map_left, List.range_eq_range']
  rfl

/-- **R-12** (T-02, T-07): the two phases compose to the sort. Run phase one on the whole input
with any pivot rule, any `minlength`, `maxseq` and iteration cap, for any number of iterations;
merge `work` into `done`; sort every resulting sequence on its own with the phase-two machine. The
finalizing writes (phase one's gap fills, then phase two's) are then exactly the pairs
(i, i-th smallest element) for i ∈ [0, n), up to order. Not a re-reading of the model: phase one
never sorts anything, phase two never sees another sequence, and this says their writes assemble
the sort. -/
theorem gpuQuicksortSorts (S : Nat) (hS : 0 < S) (pv : Seg → Nat) (piv : List Nat → Nat)
    (hpiv : ∀ ys : List Nat, ys ≠ [] → piv ys ∈ ys) (minlength M maxIter fuel k : Nat)
    (xs : List Nat) (hk : xs.length ≤ k) :
    (gpuQuicksort S pv piv minlength M maxIter fuel k xs).Perm
      ((List.range xs.length).zip (xs.mergeSort leB)) := by
  have ht := mergeSortSorted xs
  have hlen : (xs.mergeSort leB).length = xs.length := List.length_mergeSort _
  have htk : (xs.mergeSort leB).take xs.length = xs.mergeSort leB := List.take_of_length_le (by omega)
  have h0 : InvP (xs.mergeSort leB) ⟨[⟨0, xs⟩], [], [], 0, false⟩ := by
    refine ⟨fun g hg => ?_, by simp [owed]⟩
    simp only [List.append_nil, List.mem_singleton] at hg; subst hg
    refine ⟨?_, by simp [hlen]⟩
    simp only [List.drop_zero, htk]; exact (List.mergeSort_perm _ _).symm
  obtain ⟨hw, hp⟩ := loopInvP _ ht pv minlength M maxIter fuel _ h0
  simp only [gpuQuicksort]
  generalize p1LoopS pv minlength M maxIter fuel ⟨[⟨0, xs⟩], [], [], 0, false⟩ = st at hw hp
  have e2 : ((st.done ++ st.work).flatMap (phaseTwoWrites S piv k)).Perm
      (owed (xs.mergeSort leB) (st.work ++ st.done)) := by
    refine (flatMap_perm_congr _ _ _ fun g hg => ?_).trans (List.Perm.flatMap_right _ List.perm_append_comm)
    have hg' := hw g (List.mem_append.2 ((List.mem_append.1 hg).symm))
    exact phaseTwoWindow S hS piv hpiv _ ht g hg' k (by have := hg'.2; omega)
  refine (List.Perm.append_left _ e2).trans (hp.trans ?_)
  simp [cw, hlen, htk, List.range_eq_range']

/-- **I-008** (T-16): every index i ∈ [0, n) of D receives its final value **exactly once**,
over the whole sort — from a phase-one gap fill or from phase two (a gap fill or an
alternative-sort write-back) — and that value is the i-th smallest element. -/
theorem gpuQuicksortExactlyOnce (S : Nat) (hS : 0 < S) (pv : Seg → Nat) (piv : List Nat → Nat)
    (hpiv : ∀ ys : List Nat, ys ≠ [] → piv ys ∈ ys) (minlength M maxIter fuel k : Nat)
    (xs : List Nat) (hk : xs.length ≤ k) :
    ((gpuQuicksort S pv piv minlength M maxIter fuel k xs).map Prod.fst).Perm (List.range xs.length) ∧
    ((gpuQuicksort S pv piv minlength M maxIter fuel k xs).map Prod.fst).Nodup ∧
    ∀ w ∈ gpuQuicksort S pv piv minlength M maxIter fuel k xs,
      w.1 < xs.length ∧ (xs.mergeSort leB)[w.1]? = some w.2 := by
  have h := gpuQuicksortSorts S hS pv piv hpiv minlength M maxIter fuel k xs hk
  have hlen : (xs.mergeSort leB).length = xs.length := List.length_mergeSort _
  have hp := h.map Prod.fst
  rw [List.map_fst_zip (by simp [hlen])] at hp
  refine ⟨hp, hp.nodup_iff.2 List.nodup_range, fun w hw => ?_⟩
  have hm := h.subset hw
  obtain ⟨i, hi, e⟩ := List.mem_iff_getElem.1 hm
  simp only [List.length_zip, List.length_range, hlen, Nat.min_self] at hi
  rw [← e]; simp [hi, hlen]

end GpuQuicksortSpec.GpuQuicksort.Pipeline
