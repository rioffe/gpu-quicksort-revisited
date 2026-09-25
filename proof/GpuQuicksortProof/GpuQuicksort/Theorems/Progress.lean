import GpuQuicksortProof.GpuQuicksort.Spec
import GpuQuicksortProof.GpuQuicksort.Theorems.Sorter

/-!
# GpuQuicksortProof.GpuQuicksort.Theorems.Progress
==================================================

Progress of the code's phase one: live sequences stay disjoint; every pivot the host uses lies
between two elements of its sequence, so both children are strictly shorter; and on all-equal input
phase one takes exactly one iteration and leaves nothing for phase two.
-/

namespace GpuQuicksort.Theorems

open GpuQuicksort.Model
open GpuQuicksortSpec.GpuQuicksort.Model (lowerPart upperPart leB)
open GpuQuicksortSpec.GpuQuicksort.PhaseTwo (cw Seg owed)
open GpuQuicksortSpec.GpuQuicksort.Pipeline (win)

/-- **(lemma)**: a pivot with an element at or below it and one at or above it leaves both parts
strictly shorter than the sequence. -/
theorem betweenShrinks (p : Nat) (xs : List Nat) (h1 : ∃ x ∈ xs, x ≤ p) (h2 : ∃ y ∈ xs, p ≤ y) :
    (lowerPart p xs).length < xs.length ∧ (upperPart p xs).length < xs.length := by
  obtain ⟨x, hx, hxp⟩ := h1
  obtain ⟨y, hy, hyp⟩ := h2
  constructor
  · exact List.length_filter_lt_length_iff_exists.2 ⟨y, hy, by simp; omega⟩
  · exact List.length_filter_lt_length_iff_exists.2 ⟨x, hx, by simp; omega⟩

theorem existsMin : ∀ (l : List Nat), l ≠ [] → ∃ m ∈ l, ∀ x ∈ l, m ≤ x
  | [], h => absurd rfl h
  | [a], _ => ⟨a, by simp, by simp⟩
  | a :: b :: l, _ => by
    obtain ⟨m, hm, hle⟩ := existsMin (b :: l) (by simp)
    by_cases h : a ≤ m
    · exact ⟨a, by simp, fun x hx => by
        rcases List.mem_cons.1 hx with rfl | hx
        · exact Nat.le_refl _
        · exact Nat.le_trans h (hle x hx)⟩
    · exact ⟨m, List.mem_cons_of_mem _ hm, fun x hx => by
        rcases List.mem_cons.1 hx with rfl | hx
        · omega
        · exact hle x hx⟩

theorem existsMax : ∀ (l : List Nat), l ≠ [] → ∃ m ∈ l, ∀ x ∈ l, x ≤ m
  | [], h => absurd rfl h
  | [a], _ => ⟨a, by simp, by simp⟩
  | a :: b :: l, _ => by
    obtain ⟨m, hm, hle⟩ := existsMax (b :: l) (by simp)
    by_cases h : m ≤ a
    · exact ⟨a, by simp, fun x hx => by
        rcases List.mem_cons.1 hx with rfl | hx
        · exact Nat.le_refl _
        · exact Nat.le_trans (hle x hx) h⟩
    · exact ⟨m, List.mem_cons_of_mem _ hm, fun x hx => by
        rcases List.mem_cons.1 hx with rfl | hx
        · omega
        · exact hle x hx⟩

/-- **(lemma)**: an atomic min that is a greatest lower bound of a non-empty list of 32-bit codes is
the list's minimum; likewise for the max. -/
theorem glbIsMin (l : List Nat) (hl : l ≠ []) (hb : ∀ x ∈ l, x ≤ 0xFFFFFFFF) (v : Nat)
    (h : ∀ z, z ≤ v ↔ z ≤ 0xFFFFFFFF ∧ ∀ x ∈ l, z ≤ x) : v ∈ l ∧ ∀ x ∈ l, v ≤ x := by
  obtain ⟨m, hm, hle⟩ := existsMin l hl
  have h1 := (h m).2 ⟨hb m hm, hle⟩
  have h2 := ((h v).1 (Nat.le_refl _)).2 m hm
  have : v = m := Nat.le_antisymm h2 h1
  subst this; exact ⟨hm, hle⟩

theorem lubIsMax (l : List Nat) (hl : l ≠ []) (v : Nat) (h : ∀ z, v ≤ z ↔ ∀ x ∈ l, x ≤ z) :
    v ∈ l ∧ ∀ x ∈ l, x ≤ v := by
  obtain ⟨m, hm, hle⟩ := existsMax l hl
  have h1 := (h m).2 hle
  have h2 := (h v).1 (Nat.le_refl _) m hm
  have : v = m := Nat.le_antisymm h1 h2
  subst this; exact ⟨hm, hle⟩

/-- **I-005** (T-09, T-13, T-41): disjointness and progress in the code's phase one.
(1) Under the phase-one invariant, the live sequences are pairwise disjoint and disjoint from every
finalized index. (2) A pivot with an element of the sequence at or below it and one at or above it
leaves both children strictly shorter than the parent (and `p1BodyInv` shows every child has the
length of one of its parent's parts). (3) Every pivot the host uses is such a pivot: the root's and
each median-of-three child's pivot is an element of its sequence, and, under `minMaxAverage`,
a child's pivot `lo &+ (hi &- lo) / 2` lies between that child's minimum and maximum, which the O-2
atomics deliver. Phase two's segments progress by the same argument (`lqsortSpec`: the pivot is
an element, R-14). -/
theorem progressSpec :
    (∀ tgt (D0 A0 : Nat → Nat) (st : P1), CInv tgt D0 A0 st →
      (seqsOf st).Pairwise (fun s s' => s.end_ ≤ s'.begin ∨ s'.end_ ≤ s.begin) ∧
      ∀ w ∈ st.fills, ∀ s ∈ seqsOf st, w.1 < s.begin ∨ s.end_ ≤ w.1) ∧
    (∀ (p : Nat) (xs : List Nat), (∃ x ∈ xs, x ≤ p) → (∃ y ∈ xs, p ≤ y) →
      (lowerPart p xs).length < xs.length ∧ (upperPart p xs).length < xs.length) ∧
    (∀ (f : Nat → Nat) b e, b < e → hostMed3 f b e ∈ slice f b (e - b)) ∧
    (∀ (k : Nat) (mem : Mem) (recs : List Rec) (blks : List Blk) (ordL ordG : Nat → List Nat)
      (_pre : DispatchPre recs blks ordL ordG) (j : Nat) (_hj : j < recs.length),
      (recs.getD j dR).lmin = 0xFFFFFFFF ∧ (recs.getD j dR).lmax = 0 ∧
      (recs.getD j dR).gmin = 0xFFFFFFFF ∧ (recs.getD j dR).gmax = 0 →
      let res := partitionDispatch (2 ^ k) (Nat.two_pow_pos k) true mem recs blks ordL ordG
      let r := recs.getD j dR
      let xs := slice (mem.buf r.src) r.start (r.end_ - r.start)
      (∀ x ∈ xs, x ≤ 0xFFFFFFFF) →
      (lowerPart r.pivot xs ≠ [] → ∃ x ∈ lowerPart r.pivot xs, ∃ y ∈ lowerPart r.pivot xs,
        x ≤ minMaxPivotU32 (res.2.getD j dR).lmin (res.2.getD j dR).lmax ∧
        minMaxPivotU32 (res.2.getD j dR).lmin (res.2.getD j dR).lmax ≤ y) ∧
      (upperPart r.pivot xs ≠ [] → ∃ x ∈ upperPart r.pivot xs, ∃ y ∈ upperPart r.pivot xs,
        x ≤ minMaxPivotU32 (res.2.getD j dR).gmin (res.2.getD j dR).gmax ∧
        minMaxPivotU32 (res.2.getD j dR).gmin (res.2.getD j dR).gmax ≤ y)) := by
  refine ⟨fun tgt D0 A0 st h => cinvDisjoint tgt D0 A0 st h, betweenShrinks, fun f b e h => ?_,
    fun k mem recs blks ordL ordG pre j hj hinit => ?_⟩
  · rw [(hostPivots.2 f b e h)]
    apply GpuQuicksortSpec.GpuQuicksort.Theorems.medianOfThreeMem
    intro h0; have := congrArg List.length h0; rw [slice_length] at this; simp at this; omega
  · intro res r xs hbd
    obtain ⟨m1, m2, m3, m4⟩ := minMaxDispatch k mem recs blks ordL ordG pre j hj hinit
    have lb : ∀ x ∈ lowerPart r.pivot xs, x ≤ 0xFFFFFFFF := fun x hx => hbd x (List.mem_filter.1 hx).1
    have ub : ∀ x ∈ upperPart r.pivot xs, x ≤ 0xFFFFFFFF := fun x hx => hbd x (List.mem_filter.1 hx).1
    refine ⟨fun hne => ?_, fun hne => ?_⟩
    · obtain ⟨lo, hlo⟩ := glbIsMin _ hne lb _ m1
      obtain ⟨hi, hhi⟩ := lubIsMax _ hne _ m2
      have hle : (res.2.getD j dR).lmin ≤ (res.2.getD j dR).lmax := hlo _ hi
      have hb2 : (res.2.getD j dR).lmax ≤ 0xFFFFFFFF := lb _ hi
      obtain ⟨_, p1, p2⟩ := hostPivots.1 _ _ hle (by omega)
      exact ⟨_, lo, _, hi, p1, p2⟩
    · obtain ⟨lo, hlo⟩ := glbIsMin _ hne ub _ m3
      obtain ⟨hi, hhi⟩ := lubIsMax _ hne _ m4
      have hle : (res.2.getD j dR).gmin ≤ (res.2.getD j dR).gmax := hlo _ hi
      have hb2 : (res.2.getD j dR).gmax ≤ 0xFFFFFFFF := ub _ hi
      obtain ⟨_, p1, p2⟩ := hostPivots.1 _ _ hle (by omega)
      exact ⟨_, lo, _, hi, p1, p2⟩

/-- **K-10, E-04** (T-08, T-09): on all-equal input (`zero`) with n ≥ minseq, maxseq ≥ 2 and a cap
of at least one iteration, the host's phase one performs exactly one iteration and leaves no
sequence: the root's pivot is the common value, both children are empty, the whole input becomes
the gap fill. So phase two is skipped (E-24): no `lqsort` dispatch, 0 partitions and 0 alternative
sorts. Equal keys never cause non-termination: every run of the whole sort finishes within the
fuel `sortRunSpec` needs, for every input. -/
theorem allEqualCode (k maxseq minseq maxIter fuel n c : Nat) (minMax : Bool) (ords : Nat → Orders)
    (hords : ValidOrders ords) (mem : Mem) (hc : ∀ i < n, mem.D i = c) (hmin : minseq ≤ n) (hn : 1 ≤ n)
    (hM : 2 ≤ maxseq) (hI : 1 ≤ maxIter) :
    ∃ st, p1Iter (2 ^ k) (Nat.two_pow_pos k) maxseq ((n + maxseq - 1) / maxseq) maxIter minMax ords (fuel + 1)
        ⟨mem, [(⟨0, n, 0⟩, hostMed3 mem.D 0 n)], [], 0, false, []⟩ = some st ∧
      st.iteration = 1 ∧ st.work = [] ∧ st.done = [] ∧
      phaseOne (2 ^ k) (Nat.two_pow_pos k) n maxseq minseq maxIter minMax ords (fuel + 1) mem =
        some (st.mem, [], st.fills) := by
  have hT := Nat.two_pow_pos k
  let xs := slice mem.D 0 n
  let tgt := xs.mergeSort leB
  have hxs : ∀ x ∈ xs, x = c := by
    intro x hx; simp only [xs, slice, List.mem_map, List.mem_range] at hx
    obtain ⟨i, hi, rfl⟩ := hx; simp only [Nat.zero_add]; exact hc i hi
  have hpiv : hostMed3 mem.D 0 n = c := by
    simp only [hostMed3, GpuQuicksortSpec.GpuQuicksort.Model.med3]
    rw [hc 0 (by omega), hc _ (by omega), hc _ (by omega)]; simp
  have htlen : tgt.length = n := by simp [tgt, xs, List.length_mergeSort, slice_length]
  have ht : tgt.Pairwise (· ≤ ·) := GpuQuicksortSpec.GpuQuicksort.Theorems.mergeSortSorted _
  have htk : (tgt.drop 0).take n = tgt := by rw [List.drop_zero, ← htlen, List.take_length]
  let st0 : P1 := ⟨mem, [(⟨0, n, 0⟩, hostMed3 mem.D 0 n)], [], 0, false, []⟩
  have h0 : CInv tgt mem.D mem.A st0 := by
    refine ⟨fun s hs => ?_, fun s hs => ?_, ?_, fun w hw => by simp [st0] at hw, fun _ _ => rfl, fun _ _ => rfl⟩
    · simp [seqsOf, st0] at hs; subst hs; exact ⟨show 0 < n by omega, Or.inl rfl⟩
    · simp [seqsOf, st0] at hs; subst hs
      refine ⟨?_, by simp [segD, slice_length, htlen]⟩
      show (slice (mem.buf 0) 0 (n - 0)).Perm ((tgt.drop 0).take (slice (mem.buf 0) 0 (n - 0)).length)
      rw [slice_length, Nat.sub_zero, htk]
      exact (List.mergeSort_perm xs leB).symm
    · simp [seqsOf, st0, owed, segD, slice_length, htlen]
  have hcond : st0.work ≠ [] ∧ st0.work.length + st0.done.length < maxseq := by simp [st0]; omega
  obtain ⟨st1, h1, hinv, hit, _, X, hX, hprov⟩ := p1BodyInv k maxseq ((n + maxseq - 1) / maxseq) minMax (ords 0)
    (fun blks j => hords 0 blks j) tgt ht mem.D mem.A st0 h0
  -- the root's parts are empty, so no child survives
  have noKid : ∀ s ∈ st1.work.map (·.1) ++ X, False := by
    intro s hs
    obtain ⟨j, hj, hlen, _, _⟩ := hprov s hs
    have hj0 : j = 0 := by simp [st0] at hj; omega
    subst hj0
    have e0 : (st0.work.getD 0 dW) = (⟨0, n, 0⟩, hostMed3 mem.D 0 n) := rfl
    rw [e0, hpiv] at hlen
    have hsl : (segD st0.mem (⟨0, n, 0⟩ : SeqD)).xs = xs := rfl
    have hl : lowerPart c xs = [] := by
      unfold lowerPart; rw [List.filter_eq_nil_iff]; intro x hx; simp [hxs x hx]
    have hu : upperPart c xs = [] := by
      unfold upperPart; rw [List.filter_eq_nil_iff]; intro x hx; simp [hxs x hx]
    rw [hsl, hl, hu] at hlen
    have hwf := hinv.wf s (by
      simp only [seqsOf, List.mem_append]
      rcases List.mem_append.1 hs with h | h
      · exact Or.inl h
      · rw [hX]; exact Or.inr (List.mem_append_right _ h))
    simp at hlen; omega
  have hw1 : st1.work = [] := by
    rcases hw : st1.work with _ | ⟨w, ws⟩
    · rfl
    · exact (noKid w.1 (by rw [hw]; simp)).elim
  have hX0 : X = [] := by
    rcases hx : X with _ | ⟨x, xs'⟩
    · rfl
    · exact (noKid x (by rw [hx]; simp)).elim
  have hd1 : st1.done = [] := by rw [hX, hX0]; rfl
  have hiter : st1.iteration = 1 := by rw [hit]
  have hrun : p1Iter (2 ^ k) hT maxseq ((n + maxseq - 1) / maxseq) maxIter minMax ords (fuel + 1) st0 = some st1 := by
    simp only [p1Iter, hcond, ↓reduceIte, show st0.iteration ≠ maxIter by simp [st0]; omega]
    show (match p1Body (2 ^ k) hT maxseq ((n + maxseq - 1) / maxseq) minMax (ords 0) st0 with
      | none => none | some st' => p1Iter (2 ^ k) hT maxseq ((n + maxseq - 1) / maxseq) maxIter minMax ords fuel st') = _
    rw [h1]
    cases fuel with
    | zero => rfl
    | succ f => simp [p1Iter, hw1]
  refine ⟨st1, hrun, hiter, hw1, hd1, ?_⟩
  simp only [phaseOne, show ¬ n < minseq by omega, ↓reduceIte]
  show (match p1Iter (2 ^ k) hT maxseq ((n + maxseq - 1) / maxseq) maxIter minMax ords (fuel + 1) st0 with
    | none => none | some st => some (st.mem, st.done ++ st.work.map (fun s : SeqD × Nat => s.1), st.fills)) = _
  rw [hrun]; simp only [hd1, hw1]; rfl

end GpuQuicksort.Theorems
