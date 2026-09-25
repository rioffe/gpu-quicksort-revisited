import GpuQuicksortProof.GpuQuicksort.Spec
import GpuQuicksortProof.GpuQuicksort.Model.GQSort
import GpuQuicksortProof.GpuQuicksort.Theorems.TGPartition
import GpuQuicksortProof.GpuQuicksort.Theorems.LQSort

/-!
# GpuQuicksortProof.GpuQuicksort.Theorems.GQSort
================================================

The phase-one kernels against the spec model's parallel partition: one `gqsort_partition`
dispatch, for every modification order of each record's two cursors, leaves each record's
below-pivot elements at [start, start + L) and above-pivot elements at [end − G, end) of the other
buffer, advances the cursors by L and G, and reduces the O-2 minima and maxima; `gqsort_fill` then
writes the pivot over [lnext, gnext), each index once.
-/

namespace GpuQuicksort.Theorems

open GpuQuicksort.Model
open GpuQuicksortSpec.GpuQuicksort.Model (lowerPart upperPart)
open GpuQuicksortSpec.GpuQuicksort.ParallelPartition

/-- A block's elements, thread by thread (thread t's values in its reading order). -/
def blockThreads (T : Nat) (hT : 0 < T) (S : Nat → Nat) (bk : Blk) : List (List Nat) :=
  (List.range T).map fun t => (visits T hT bk.begin bk.end_ t).map S

/-- **(lemma)** (R-04, R-05, R-09): a block's pass-2 writes are the spec model's `blockLow` from the
base its `lnext` atomic returned and `blockHigh` from the base its `gnext` atomic returned; its
totals are the numbers of its elements below and above the pivot. -/
theorem blockScatterSpec (k : Nat) (S : Nat → Nat) (p : Nat) (bk : Blk) (lbeg gbeg : Nat) :
    let th := blockThreads (2 ^ k) (Nat.two_pow_pos k) S bk
    (blockScatter (2 ^ k) (Nat.two_pow_pos k) S p bk lbeg gbeg).Perm
      (pairs (blockLow p lbeg th) ++ pairs (blockHigh p gbeg th)) ∧
    (blockScan (2 ^ k) (Nat.two_pow_pos k) S p bk).2.1 = totalLow p th ∧
    (blockScan (2 ^ k) (Nat.two_pow_pos k) S p bk).2.2.2 = totalHigh p th := by
  intro th
  have hT := Nat.two_pow_pos k
  let lt := fun t => ltCount S p (visits (2 ^ k) hT bk.begin bk.end_ t)
  let gt := fun t => gtCount S p (visits (2 ^ k) hT bk.begin bk.end_ t)
  obtain ⟨sL, oL⟩ := scan2Correct k lt
  obtain ⟨sG, oG⟩ := scan2Correct k gt
  let f := fun t => (visits (2 ^ k) hT bk.begin bk.end_ t).map S
  have hth : th = (List.range (2 ^ k)).map f := rfl
  refine ⟨?_, ?_, ?_⟩
  · have c1 : (blockScatter (2 ^ k) hT S p bk lbeg gbeg).Perm ((List.range (2 ^ k)).flatMap fun t =>
        pairs (lowW p (lbeg + Theorems.S lt 0 t) (f t)) ++ pairs (highW p (gbeg + Theorems.S gt 0 t) (f t))) := by
      refine GpuQuicksortSpec.GpuQuicksort.Pipeline.flatMap_perm_congr _ _ _ fun t ht => ?_
      rw [List.mem_range] at ht
      show (passWrites S p (lbeg + (scan2 (2 ^ k) lt).1 t) (gbeg + (scan2 (2 ^ k) gt).1 t) _).Perm _
      rw [oL t ht, oG t ht]
      exact passWritesPerm S p _ _ _
    refine c1.trans ((flatMapAppendPerm _ _ _).trans (List.Perm.of_eq ?_))
    simp only [pairs, ← List.map_flatMap]
    rw [List.range_eq_range', blockLowConv p f (fun t => lbeg + Theorems.S lt 0 t) _ 0 lbeg (fun t _ _ => by
      simp only [Theorems.S, Nat.sub_zero]; congr 2; exact List.map_congr_left (fun u _ => ltCountEq S p _)),
      blockHighConv p f (fun t => gbeg + Theorems.S gt 0 t) _ 0 gbeg (fun t _ _ => by
      simp only [Theorems.S, Nat.sub_zero]; congr 2; exact List.map_congr_left (fun u _ => gtCountEq S p _)),
      ← List.range_eq_range']
    rfl
  · show (scan2 (2 ^ k) lt).2 = _
    rw [sL]; simp only [Theorems.S, totalLow, hth, List.map_map, Nat.sub_zero, List.range_eq_range']
    congr 2; funext t; exact ltCountEq S p _
  · show (scan2 (2 ^ k) gt).2 = _
    rw [sG]; simp only [Theorems.S, totalHigh, hth, List.map_map, Nat.sub_zero, List.range_eq_range']
    congr 2; funext t; exact gtCountEq S p _

/-! ## The atomic orders -/

theorem flatMapCongr {α β : Type} {f g : α → List β} :
    ∀ {l : List α}, (∀ x ∈ l, f x = g x) → l.flatMap f = l.flatMap g
  | [], _ => rfl
  | x :: l, h => by
    rw [List.flatMap_cons, List.flatMap_cons, h x List.mem_cons_self,
      flatMapCongr (fun y hy => h y (List.mem_cons_of_mem _ hy))]

theorem pairs_append (a c : List W) : pairs (a ++ c) = pairs a ++ pairs c := by simp [pairs]

theorem idxOfNe (i0 i : Nat) (rest : List Nat) (hne : i ≠ i0) : (i0 :: rest).idxOf i = rest.idxOf i + 1 := by
  rw [List.idxOf_cons]; simp [Ne.symm hne]

theorem lbegCons (sL : Nat → Nat) (start i0 : Nat) (rest : List Nat) :
    lbegOf sL start (i0 :: rest) i0 = start ∧
    ∀ i ∈ rest, i ≠ i0 → lbegOf sL start (i0 :: rest) i = lbegOf sL (start + sL i0) rest i := by
  refine ⟨by simp [lbegOf], fun i _ hne => ?_⟩
  simp only [lbegOf, idxOfNe i0 i rest hne, List.take_succ_cons, List.map_cons, List.sum_cons]
  omega

theorem gbegCons (sG : Nat → Nat) (end_ i0 : Nat) (rest : List Nat) :
    gbegOf sG end_ (i0 :: rest) i0 = end_ - sG i0 ∧
    ∀ i ∈ rest, i ≠ i0 → gbegOf sG end_ (i0 :: rest) i = gbegOf sG (end_ - sG i0) rest i := by
  refine ⟨by simp [gbegOf], fun i _ hne => ?_⟩
  simp only [gbegOf, idxOfNe i0 i rest hne, List.take_succ_cons, List.map_cons, List.sum_cons]
  omega

/-- **(lemma)** (R-09): the blocks' `lnext` reservations, taken in the location's modification
order, give exactly the spec model's `phaseLow` writes from the record's start. -/
theorem phaseLowOrd (p : Nat) (th : Nat → List (List Nat)) (sL : Nat → Nat) :
    ∀ (l : List Nat) (start : Nat), l.Nodup → (∀ i ∈ l, sL i = totalLow p (th i)) →
      l.flatMap (fun i => pairs (blockLow p (lbegOf sL start l i) (th i))) = pairs (phaseLow p start (l.map th))
  | [], _, _, _ => by simp [phaseLow, pairs]
  | i0 :: rest, start, hnd, hs => by
    rw [List.nodup_cons] at hnd
    obtain ⟨c1, c2⟩ := lbegCons sL start i0 rest
    rw [List.flatMap_cons, c1, List.map_cons, phaseLow, pairs_append, ← hs i0 List.mem_cons_self]
    congr 1
    rw [flatMapCongr (fun i hi => by rw [c2 i hi (fun e => hnd.1 (e ▸ hi))])]
    exact phaseLowOrd p th sL rest _ hnd.2 (fun i hi => hs i (List.mem_cons_of_mem _ hi))

/-- **(lemma)** (R-09): the blocks' `gnext` reservations, in the location's modification order,
give exactly the spec model's `phaseHigh` writes down from the record's end. -/
theorem phaseHighOrd (p : Nat) (th : Nat → List (List Nat)) (sG : Nat → Nat) :
    ∀ (l : List Nat) (end_ : Nat), l.Nodup → (∀ i ∈ l, sG i = totalHigh p (th i)) →
      l.flatMap (fun i => pairs (blockHigh p (gbegOf sG end_ l i) (th i))) = pairs (phaseHigh p end_ (l.map th))
  | [], _, _, _ => by simp [phaseHigh, pairs]
  | i0 :: rest, end_, hnd, hs => by
    rw [List.nodup_cons] at hnd
    obtain ⟨c1, c2⟩ := gbegCons sG end_ i0 rest
    rw [List.flatMap_cons, c1, List.map_cons, phaseHigh, pairs_append, ← hs i0 List.mem_cons_self]
    congr 1
    rw [flatMapCongr (fun i hi => by rw [c2 i hi (fun e => hnd.1 (e ▸ hi))])]
    exact phaseHighOrd p th sG rest _ hnd.2 (fun i hi => hs i (List.mem_cons_of_mem _ hi))

/-! ## Memory after unique-valued writes -/

/-- **(lemma)**: if a list of writes covers [a, a + n) exactly (as positions) and gives every
position one value, the slice read back is a permutation of the values written. -/
theorem sliceOfWrites (ws : List (Nat × Nat)) (a n : Nat) (f : Nat → Nat)
    (hpos : (ws.map Prod.fst).Perm (List.range' a n))
    (hfun : ∀ w ∈ ws, ∀ w' ∈ ws, w.1 = w'.1 → w.2 = w'.2) :
    (slice (applyW ws f) a n).Perm (ws.map Prod.snd) := by
  have hval : ∀ w ∈ ws, applyW ws f w.1 = w.2 := fun w hw =>
    applyW_uniq ws w.1 w.2 (fun w' hw' he => (hfun w hw w' hw' he.symm).symm) f ⟨w, hw, rfl⟩
  have e1 : ws.map Prod.snd = (ws.map Prod.fst).map (applyW ws f) := by
    rw [List.map_map]; apply List.map_congr_left; intro w hw; exact (hval w hw).symm
  rw [e1, slice_eq]
  exact (hpos.map _).symm

/-- **(lemma)**: when every write to x in `ws` also appears in `ws'` ⊆ `ws`, and a slot's writes
agree, x ends the same under both lists. -/
theorem applyW_sub (ws ws' : List (Nat × Nat)) (x : Nat) (hsub : ∀ w ∈ ws', w ∈ ws)
    (hx : ∀ w ∈ ws, w.1 = x → w ∈ ws')
    (hfun : ∀ w ∈ ws, ∀ w' ∈ ws, w.1 = w'.1 → w.2 = w'.2) (f : Nat → Nat) :
    applyW ws f x = applyW ws' f x := by
  by_cases h : ∃ w ∈ ws, w.1 = x
  · obtain ⟨w, hw, he⟩ := h
    rw [applyW_uniq ws x w.2 (fun w' hw' he' => (hfun w hw w' hw' (he.trans he'.symm)).symm) f ⟨w, hw, he⟩,
      applyW_uniq ws' x w.2 (fun w' hw' he' => (hfun w hw w' (hsub w' hw') (he.trans he'.symm)).symm) f
        ⟨w, hx w hw he, he⟩]
  · have n1 : x ∉ ws.map Prod.fst := by
      simp only [List.mem_map, not_exists, not_and]; intro w hw he; exact h ⟨w, hw, he⟩
    have n2 : x ∉ ws'.map Prod.fst := by
      simp only [List.mem_map, not_exists, not_and]; intro w hw he; exact h ⟨w, hsub w hw, he⟩
    rw [applyW_not _ _ _ n1, applyW_not _ _ _ n2]

theorem nodupFstEq : ∀ (ws : List (Nat × Nat)), (ws.map Prod.fst).Nodup →
    ∀ w ∈ ws, ∀ w' ∈ ws, w.1 = w'.1 → w = w'
  | [], _, w, hw, _, _, _ => by simp at hw
  | x :: ws, hnd, w, hw, w', hw', he => by
    rw [List.map_cons, List.nodup_cons] at hnd
    rcases List.mem_cons.1 hw with h1 | h1 <;> rcases List.mem_cons.1 hw' with h2 | h2
    · rw [h1, h2]
    · exact absurd (show x.1 ∈ ws.map Prod.fst by rw [← h1, he]; exact List.mem_map.2 ⟨w', h2, rfl⟩) hnd.1
    · exact absurd (show x.1 ∈ ws.map Prod.fst by rw [← h2, ← he]; exact List.mem_map.2 ⟨w, h1, rfl⟩) hnd.1
    · exact nodupFstEq ws hnd.2 w h1 w' h2 he

theorem totalLowSum (p : Nat) (th : Nat → List (List Nat)) :
    ∀ l : List Nat, ((l.map fun i => totalLow p (th i)).sum) = (lowerPart p (allElems (l.map th))).length
  | [] => by simp [allElems, lowerPart]
  | i :: l => by
    rw [List.map_cons, List.sum_cons, totalLowSum p th l, totalLow_eq]
    simp only [allElems, List.map_cons, List.flatten_cons, lowerPart, List.filter_append, List.length_append]

theorem totalHighSum (p : Nat) (th : Nat → List (List Nat)) :
    ∀ l : List Nat, ((l.map fun i => totalHigh p (th i)).sum) = (upperPart p (allElems (l.map th))).length
  | [] => by simp [allElems, upperPart]
  | i :: l => by
    rw [List.map_cons, List.sum_cons, totalHighSum p th l, totalHigh_eq]
    simp only [allElems, List.map_cons, List.flatten_cons, upperPart, List.filter_append, List.length_append]

/-- **(lemma)** (R-04, R-05, R-09, I-004): the writes of one record's blocks in a `gqsort_partition`
dispatch. Whatever the modification orders of the record's `lnext` and `gnext`, the blocks' totals
are L and G (the numbers of elements below and above the pivot); every write lands in
[start, start + L) or [end − G, end), one value per slot; and reading those ranges back gives
permutations of the below- and above-pivot elements. -/
theorem recordWrites (k : Nat) (S : Nat → Nat) (p start end_ : Nat) (bkOf : Nat → Blk)
    (mine ordL ordG : List Nat) (hnd : mine.Nodup) (hL : ordL.Perm mine) (hG : ordG.Perm mine)
    (hse : start ≤ end_)
    (hcover : (mine.flatMap fun i => List.range' (bkOf i).begin ((bkOf i).end_ - (bkOf i).begin)).Perm
      (List.range' start (end_ - start))) :
    let hT := Nat.two_pow_pos k
    let sL := fun i => (blockScan (2 ^ k) hT S p (bkOf i)).2.1
    let sG := fun i => (blockScan (2 ^ k) hT S p (bkOf i)).2.2.2
    let Wj := mine.flatMap fun i =>
      blockScatter (2 ^ k) hT S p (bkOf i) (lbegOf sL start ordL i) (gbegOf sG end_ ordG i)
    let xs := slice S start (end_ - start)
    let L := (lowerPart p xs).length
    let G := (upperPart p xs).length
    (mine.map sL).sum = L ∧ (mine.map sG).sum = G ∧ L + xs.count p + G = end_ - start ∧
    (∀ w ∈ Wj, (start ≤ w.1 ∧ w.1 < start + L) ∨ (end_ - G ≤ w.1 ∧ w.1 < end_)) ∧
    (∀ w ∈ Wj, ∀ w' ∈ Wj, w.1 = w'.1 → w.2 = w'.2) ∧
    (∀ f, (slice (applyW Wj f) start L).Perm (lowerPart p xs)) ∧
    (∀ f, (slice (applyW Wj f) (end_ - G) G).Perm (upperPart p xs)) := by
  intro hT sL sG Wj xs L G
  let th := fun i => blockThreads (2 ^ k) hT S (bkOf i)
  have hsL : ∀ i, sL i = totalLow p (th i) := fun i => (blockScatterSpec k S p (bkOf i) 0 0).2.1
  have hsG : ∀ i, sG i = totalHigh p (th i) := fun i => (blockScatterSpec k S p (bkOf i) 0 0).2.2
  -- every record element, block by block and thread by thread
  have hthf : ∀ i, (th i).flatten.Perm ((List.range' (bkOf i).begin ((bkOf i).end_ - (bkOf i).begin)).map S) := by
    intro i
    have : (th i).flatten = ((List.range (2 ^ k)).flatMap (visits (2 ^ k) hT (bkOf i).begin (bkOf i).end_)).map S := by
      simp only [th, blockThreads]; rw [← List.flatMap_def, List.map_flatMap]
    rw [this]; exact (stridesPerm _ hT _ _).map S
  have hall : ∀ l : List Nat, l.Perm mine → (allElems (l.map th)).Perm xs := by
    intro l hl
    have e1 : allElems (l.map th) = l.flatMap fun i => (th i).flatten := by
      simp only [allElems, List.map_map]; rw [← List.flatMap_def]; rfl
    rw [e1]
    refine (GpuQuicksortSpec.GpuQuicksort.Pipeline.flatMap_perm_congr _ _ _ fun i _ => hthf i).trans ?_
    show List.Perm _ (slice S start (end_ - start))
    rw [slice_eq, ← List.map_flatMap]
    exact ((hl.flatMap_right _).trans hcover).map S
  have hLlen : (lowerPart p (allElems (ordL.map th))).length = L := ((hall ordL hL).filter _).length_eq
  have hGlen : (upperPart p (allElems (ordG.map th))).length = G := ((hall ordG hG).filter _).length_eq
  have hsum : L + xs.count p + G = end_ - start := by
    have := (GpuQuicksortSpec.GpuQuicksort.Theorems.partitionPerm p xs).length_eq
    simp only [GpuQuicksortSpec.GpuQuicksort.Model.partition3, GpuQuicksortSpec.GpuQuicksort.Model.gapPart,
      List.length_append, List.length_replicate] at this
    rw [this, slice_length]
  -- the record's writes are the phase's low and high writes
  let ZL := pairs (phaseLow p start (ordL.map th))
  let ZH := pairs (phaseHigh p end_ (ordG.map th))
  have hW : Wj.Perm (ZL ++ ZH) := by
    have c1 : Wj.Perm (mine.flatMap fun i =>
        pairs (blockLow p (lbegOf sL start ordL i) (th i)) ++ pairs (blockHigh p (gbegOf sG end_ ordG i) (th i))) :=
      GpuQuicksortSpec.GpuQuicksort.Pipeline.flatMap_perm_congr _ _ _ fun i _ =>
        (blockScatterSpec k S p (bkOf i) _ _).1
    refine c1.trans ((flatMapAppendPerm _ _ _).trans ?_)
    refine List.Perm.append ((List.Perm.flatMap_right _ hL.symm).trans (List.Perm.of_eq ?_))
      ((List.Perm.flatMap_right _ hG.symm).trans (List.Perm.of_eq ?_))
    · exact phaseLowOrd p th sL ordL start (hL.nodup_iff.2 hnd) (fun i _ => hsL i)
    · exact phaseHighOrd p th sG ordG end_ (hG.nodup_iff.2 hnd) (fun i _ => hsG i)
  have zlEq : ZL = (List.range' start L).zip (lowerPart p (allElems (ordL.map th))) := by
    simp only [ZL]; rw [pairsZip, phaseLow_pos, phaseLow_val, hLlen]
  have zhPos : (ZH.map Prod.fst).Perm (List.range' (end_ - G) G) := by
    simp only [ZH, pairs, List.map_map]
    have := phaseHigh_pos p end_ (ordG.map th) (by omega)
    rw [hGlen] at this; exact this
  have zhVal : ZH.map Prod.snd = upperPart p (allElems (ordG.map th)) := by
    simp only [ZH, pairs, List.map_map]; exact phaseHigh_val p end_ (ordG.map th)
  have zlPos : ∀ w ∈ ZL, start ≤ w.1 ∧ w.1 < start + L := by
    intro w hw; rw [zlEq] at hw
    have := List.of_mem_zip hw; exact List.mem_range'_1.1 this.1
  have zhPos' : ∀ w ∈ ZH, end_ - G ≤ w.1 ∧ w.1 < end_ := by
    intro w hw
    have := List.mem_range'_1.1 (zhPos.subset (List.mem_map.2 ⟨w, hw, rfl⟩)); omega
  have hnodup : ((ZL ++ ZH).map Prod.fst).Nodup := by
    rw [List.map_append, List.nodup_append]
    refine ⟨?_, zhPos.nodup_iff.2 List.nodup_range', fun a ha b hb => ?_⟩
    · rw [zlEq, List.map_fst_zip (by rw [hLlen]; simp)]; exact List.nodup_range'
    · obtain ⟨w, hw, rfl⟩ := List.mem_map.1 ha
      obtain ⟨w', hw', rfl⟩ := List.mem_map.1 hb
      have := zlPos w hw; have := zhPos' w' hw'; omega
  have hfun : ∀ w ∈ Wj, ∀ w' ∈ Wj, w.1 = w'.1 → w.2 = w'.2 := by
    intro w hw w' hw' he
    rw [nodupFstEq _ hnodup w (hW.subset hw) w' (hW.subset hw') he]
  refine ⟨?_, ?_, hsum, fun w hw => ?_, hfun, fun f => ?_, fun f => ?_⟩
  · rw [List.map_congr_left (fun i _ => hsL i), totalLowSum]; exact ((hall mine (List.Perm.refl _)).filter _).length_eq
  · rw [List.map_congr_left (fun i _ => hsG i), totalHighSum]; exact ((hall mine (List.Perm.refl _)).filter _).length_eq
  · rcases List.mem_append.1 (hW.subset hw) with h | h
    · exact Or.inl (zlPos w h)
    · exact Or.inr (zhPos' w h)
  · -- the below-pivot range reads back as the lower part
    have e1 : slice (applyW Wj f) start L = slice (applyW ZL f) start L := by
      apply slice_congr; intro x h1 h2
      refine (applyW_sub Wj ZL x (fun w hw => hW.symm.subset (List.mem_append_left _ hw)) (fun w hw he => ?_) hfun f)
      rcases List.mem_append.1 (hW.subset hw) with h | h
      · exact h
      · have := zhPos' w h; omega
    rw [e1]
    have hZLfun : ∀ w ∈ ZL, ∀ w' ∈ ZL, w.1 = w'.1 → w.2 = w'.2 := fun w hw w' hw' he =>
      hfun w (hW.symm.subset (List.mem_append_left _ hw)) w' (hW.symm.subset (List.mem_append_left _ hw')) he
    refine (sliceOfWrites ZL start L f ?_ hZLfun).trans ?_
    · rw [zlEq, List.map_fst_zip (by rw [hLlen]; simp)]
    · rw [zlEq, List.map_snd_zip (by rw [hLlen]; simp)]; exact (hall ordL hL).filter _
  · -- the above-pivot range reads back as the upper part
    have e1 : slice (applyW Wj f) (end_ - G) G = slice (applyW ZH f) (end_ - G) G := by
      apply slice_congr; intro x h1 h2
      refine (applyW_sub Wj ZH x (fun w hw => hW.symm.subset (List.mem_append_right _ hw)) (fun w hw he => ?_) hfun f)
      rcases List.mem_append.1 (hW.subset hw) with h | h
      · have := zlPos w h; omega
      · exact h
    rw [e1]
    have hZHfun : ∀ w ∈ ZH, ∀ w' ∈ ZH, w.1 = w'.1 → w.2 = w'.2 := fun w hw w' hw' he =>
      hfun w (hW.symm.subset (List.mem_append_right _ hw)) w' (hW.symm.subset (List.mem_append_right _ hw')) he
    refine (sliceOfWrites ZH (end_ - G) G f zhPos hZHfun).trans ?_
    rw [zhVal]; exact (hall ordG hG).filter _

/-! ## One dispatch over all records -/

/-- Default record and block (out-of-range reads). -/
def dR : Rec := ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩
def dB : Blk := ⟨0, 0, 0⟩

/-- The blocks of record j, in index order. -/
def mineOf (blks : List Blk) (j : Nat) : List Nat :=
  (List.range blks.length).filter fun i => decide ((blks.getD i dB).seq = j)

theorem mineNodup (blks : List Blk) (j : Nat) : (mineOf blks j).Nodup := List.nodup_range.filter _

theorem mem_mine (blks : List Blk) (j i : Nat) : i ∈ mineOf blks j ↔ i < blks.length ∧ (blks.getD i dB).seq = j := by
  simp [mineOf]

theorem lbegCongr (f g : Nat → Nat) (start : Nat) (ord : List Nat) (i : Nat) (h : ∀ x ∈ ord, f x = g x) :
    lbegOf f start ord i = lbegOf g start ord i := by
  simp only [lbegOf]; congr 2
  exact List.map_congr_left fun x hx => h x (List.mem_of_mem_take hx)

theorem gbegCongr (f g : Nat → Nat) (end_ : Nat) (ord : List Nat) (i : Nat) (h : ∀ x ∈ ord, f x = g x) :
    gbegOf f end_ ord i = gbegOf g end_ ord i := by
  simp only [gbegOf]; congr 2
  exact List.map_congr_left fun x hx => h x (List.mem_of_mem_take hx)

/-- The hypotheses the host establishes before a partition dispatch (`Sorter.swift:124-135`):
records start with lnext = start and gnext = end, in D or A; every block belongs to a record;
record j's blocks tile [start, end); the modification orders are orders of the record's blocks;
records do not overlap. -/
structure DispatchPre (recs : List Rec) (blks : List Blk) (ordL ordG : Nat → List Nat) : Prop where
  rec_ : ∀ j < recs.length, (recs.getD j dR).lnext = (recs.getD j dR).start ∧
    (recs.getD j dR).gnext = (recs.getD j dR).end_ ∧ (recs.getD j dR).start ≤ (recs.getD j dR).end_ ∧
    ((recs.getD j dR).src = 0 ∨ (recs.getD j dR).src = 1)
  seq : ∀ i < blks.length, (blks.getD i dB).seq < recs.length
  cover : ∀ j < recs.length, ((mineOf blks j).flatMap fun i =>
    List.range' (blks.getD i dB).begin ((blks.getD i dB).end_ - (blks.getD i dB).begin)).Perm
      (List.range' (recs.getD j dR).start ((recs.getD j dR).end_ - (recs.getD j dR).start))
  ord : ∀ j < recs.length, (ordL j).Perm (mineOf blks j) ∧ (ordG j).Perm (mineOf blks j)
  disj : ∀ j j', j < recs.length → j' < recs.length → j ≠ j' →
    (recs.getD j dR).end_ ≤ (recs.getD j' dR).start ∨ (recs.getD j' dR).end_ ≤ (recs.getD j dR).start

set_option maxHeartbeats 4000000 in
/-- **R-04, R-05, R-07, R-09** (T-14, T-15, T-17): one `gqsort_partition` dispatch, as transcribed.
Under the host's preconditions and for **every** modification order of every record's two cursors,
each record j with contents xs (in buffer `src`) and pivot p ends with lnext = start + L and
gnext = end − G (L and G the numbers of elements below and above p); the other buffer holds a
permutation of the below-pivot elements at [start, start + L) and of the above-pivot elements at
[end − G, end); the record's own buffer is untouched over [start, end), as is the other buffer's gap
[start + L, end − G); and nothing outside the records changes. Each partition reads one buffer and
writes the other (R-07); the per-thread stride and the two atomics per block are the transcribed
code's (R-05, R-09). -/
theorem partitionDispatchSpec (k : Nat) (minMax : Bool) (mem : Mem) (recs : List Rec) (blks : List Blk)
    (ordL ordG : Nat → List Nat) (pre : DispatchPre recs blks ordL ordG) :
    let res := partitionDispatch (2 ^ k) (Nat.two_pow_pos k) minMax mem recs blks ordL ordG
    (∀ j < recs.length,
      let r := recs.getD j dR
      let xs := slice (mem.buf r.src) r.start (r.end_ - r.start)
      let L := (lowerPart r.pivot xs).length
      let G := (upperPart r.pivot xs).length
      (res.2.getD j dR).lnext = r.start + L ∧ (res.2.getD j dR).gnext = r.end_ - G ∧
      (res.2.getD j dR).start = r.start ∧ (res.2.getD j dR).end_ = r.end_ ∧
      (res.2.getD j dR).pivot = r.pivot ∧ (res.2.getD j dR).src = r.src ∧
      L + xs.count r.pivot + G = r.end_ - r.start ∧
      (slice (res.1.buf (1 - r.src)) r.start L).Perm (lowerPart r.pivot xs) ∧
      (slice (res.1.buf (1 - r.src)) (r.end_ - G) G).Perm (upperPart r.pivot xs) ∧
      (∀ x, r.start ≤ x → x < r.end_ → res.1.buf r.src x = mem.buf r.src x) ∧
      (∀ x, r.start + L ≤ x → x < r.end_ - G → res.1.buf (1 - r.src) x = mem.buf (1 - r.src) x)) ∧
    (∀ s x, (s = 0 ∨ s = 1) → (∀ j < recs.length, x < (recs.getD j dR).start ∨ (recs.getD j dR).end_ ≤ x) →
      res.1.buf s x = mem.buf s x) := by
  intro res
  have hT := Nat.two_pow_pos k
  -- the dispatch's own names
  let rec_ := fun i => recs.getD (blks.getD i dB).seq dR
  let S := fun i => mem.buf (rec_ i).src
  let sc := fun i => blockScan (2 ^ k) hT (S i) (rec_ i).pivot (blks.getD i dB)
  let sL := fun i => (sc i).2.1
  let sG := fun i => (sc i).2.2.2
  let writes := fun i => blockScatter (2 ^ k) hT (S i) (rec_ i).pivot (blks.getD i dB)
      (lbegOf sL (rec_ i).lnext (ordL (blks.getD i dB).seq) i) (gbegOf sG (rec_ i).gnext (ordG (blks.getD i dB).seq) i)
  let toD := (List.range blks.length).flatMap fun i => if (rec_ i).src = 1 then writes i else []
  let toA := (List.range blks.length).flatMap fun i => if (rec_ i).src = 0 then writes i else []
  have hres1 : res.1 = ⟨applyW toD mem.D, applyW toA mem.A⟩ := rfl
  -- record j's writes are `recordWrites`'
  let RW := fun j =>
    let r := recs.getD j dR
    recordWrites k (mem.buf r.src) r.pivot r.start r.end_ (fun i => blks.getD i dB) (mineOf blks j) (ordL j) (ordG j)
  have wEq : ∀ j < recs.length, ∀ i ∈ mineOf blks j,
      writes i = blockScatter (2 ^ k) hT (mem.buf (recs.getD j dR).src) (recs.getD j dR).pivot (blks.getD i dB)
        (lbegOf (fun i => (blockScan (2 ^ k) hT (mem.buf (recs.getD j dR).src) (recs.getD j dR).pivot (blks.getD i dB)).2.1)
          (recs.getD j dR).start (ordL j) i)
        (gbegOf (fun i => (blockScan (2 ^ k) hT (mem.buf (recs.getD j dR).src) (recs.getD j dR).pivot (blks.getD i dB)).2.2.2)
          (recs.getD j dR).end_ (ordG j) i) := by
    intro j hj i hi
    have hseq := ((mem_mine blks j i).1 hi).2
    have hrec : rec_ i = recs.getD j dR := by simp only [rec_, hseq]
    obtain ⟨h1, h2, _, _⟩ := pre.rec_ j hj
    have memb : ∀ x ∈ ordL j, (sc x).2.1 = (blockScan (2 ^ k) hT (mem.buf (recs.getD j dR).src) (recs.getD j dR).pivot (blks.getD x dB)).2.1 := by
      intro x hx
      have hxs := ((mem_mine blks j x).1 ((pre.ord j hj).1.subset hx)).2
      simp only [sc, S, rec_, hxs]
    have membG : ∀ x ∈ ordG j, (sc x).2.2.2 = (blockScan (2 ^ k) hT (mem.buf (recs.getD j dR).src) (recs.getD j dR).pivot (blks.getD x dB)).2.2.2 := by
      intro x hx
      have hxs := ((mem_mine blks j x).1 ((pre.ord j hj).2.subset hx)).2
      simp only [sc, S, rec_, hxs]
    simp only [writes, S, hrec, hseq]
    rw [lbegCongr _ _ _ _ _ memb, gbegCongr _ _ _ _ _ membG, h1, h2]
  -- per-record facts
  have RWf : ∀ j < recs.length, _ := fun j hj =>
    RW j (mineNodup blks j) (pre.ord j hj).1 (pre.ord j hj).2 (pre.rec_ j hj).2.2.1 (pre.cover j hj)
  have WjEq : ∀ j < recs.length, (mineOf blks j).flatMap writes =
      (mineOf blks j).flatMap fun i =>
        blockScatter (2 ^ k) hT (mem.buf (recs.getD j dR).src) (recs.getD j dR).pivot (blks.getD i dB)
          (lbegOf (fun i => (blockScan (2 ^ k) hT (mem.buf (recs.getD j dR).src) (recs.getD j dR).pivot (blks.getD i dB)).2.1)
            (recs.getD j dR).start (ordL j) i)
          (gbegOf (fun i => (blockScan (2 ^ k) hT (mem.buf (recs.getD j dR).src) (recs.getD j dR).pivot (blks.getD i dB)).2.2.2)
            (recs.getD j dR).end_ (ordG j) i) :=
    fun j hj => flatMapCongr (fun i hi => wEq j hj i hi)
  -- where each block's writes land
  have posW : ∀ i < blks.length, ∀ w ∈ writes i,
      let j := (blks.getD i dB).seq
      w ∈ (mineOf blks j).flatMap writes ∧ (recs.getD j dR).start ≤ w.1 ∧ w.1 < (recs.getD j dR).end_ := by
    intro i hi w hw j
    have hj := pre.seq i hi
    have hmem : w ∈ (mineOf blks j).flatMap writes :=
      List.mem_flatMap.2 ⟨i, (mem_mine blks j i).2 ⟨hi, rfl⟩, hw⟩
    refine ⟨hmem, ?_⟩
    have := (RWf j hj).2.2.2.1 w (by rw [← WjEq j hj]; exact hmem)
    have hle := (RWf j hj).2.2.1
    rcases this with h | h <;> omega
  -- unique values per slot across the whole dispatch
  have sameRec : ∀ i < blks.length, ∀ i' < blks.length, ∀ w ∈ writes i, ∀ w' ∈ writes i', w.1 = w'.1 →
      (blks.getD i dB).seq = (blks.getD i' dB).seq := by
    intro i hi i' hi' w hw w' hw' he
    obtain ⟨_, a1, a2⟩ := posW i hi w hw
    obtain ⟨_, b1, b2⟩ := posW i' hi' w' hw'
    by_cases hne : (blks.getD i dB).seq = (blks.getD i' dB).seq
    · exact hne
    · rcases pre.disj _ _ (pre.seq i hi) (pre.seq i' hi') hne with h | h <;> omega
  -- a generic target buffer: writes of blocks whose record's src is c
  have bufLemma : ∀ c : Nat, ∀ j < recs.length, ∀ x, (recs.getD j dR).start ≤ x → x < (recs.getD j dR).end_ →
      ∀ f, applyW ((List.range blks.length).flatMap fun i => if (rec_ i).src = c then writes i else []) f x =
        if (recs.getD j dR).src = c then applyW ((mineOf blks j).flatMap writes) f x else f x := by
    intro c j hj x h1 h2 f
    let toC := (List.range blks.length).flatMap fun i => if (rec_ i).src = c then writes i else []
    have memC : ∀ w ∈ toC, ∃ i < blks.length, (rec_ i).src = c ∧ w ∈ writes i := by
      intro w hw
      obtain ⟨i, hi, hw⟩ := List.mem_flatMap.1 hw
      rw [List.mem_range] at hi
      split at hw
      · exact ⟨i, hi, by assumption, hw⟩
      · simp at hw
    have atX : ∀ w ∈ toC, w.1 = x → (blks.getD (0 : Nat) dB).seq = (blks.getD 0 dB).seq ∧
        ∃ i < blks.length, (blks.getD i dB).seq = j ∧ (rec_ i).src = c ∧ w ∈ writes i := by
      intro w hw he
      obtain ⟨i, hi, hc, hw'⟩ := memC w hw
      obtain ⟨_, a1, a2⟩ := posW i hi w hw'
      refine ⟨rfl, i, hi, ?_, hc, hw'⟩
      by_cases hne : (blks.getD i dB).seq = j
      · exact hne
      · rcases pre.disj _ _ (pre.seq i hi) hj hne with h | h <;> omega
    have hfunC : ∀ w ∈ toC, ∀ w' ∈ toC, w.1 = w'.1 → w.2 = w'.2 := by
      intro w hw w' hw' he
      obtain ⟨i, hi, _, hwi⟩ := memC w hw
      obtain ⟨i', hi', _, hwi'⟩ := memC w' hw'
      have hs := sameRec i hi i' hi' w hwi w' hwi' he
      have hj' := pre.seq i hi
      have m1 : w ∈ (mineOf blks (blks.getD i dB).seq).flatMap writes :=
        List.mem_flatMap.2 ⟨i, (mem_mine blks _ i).2 ⟨hi, rfl⟩, hwi⟩
      have m2 : w' ∈ (mineOf blks (blks.getD i dB).seq).flatMap writes :=
        List.mem_flatMap.2 ⟨i', (mem_mine blks _ i').2 ⟨hi', hs.symm⟩, hwi'⟩
      rw [WjEq _ hj'] at m1 m2
      exact (RWf _ hj').2.2.2.2.1 w m1 w' m2 he
    show applyW toC f x = _
    split
    · next hsrc =>
      refine applyW_sub toC _ x (fun w hw => ?_) (fun w hw he => ?_) hfunC f
      · obtain ⟨i, hi, hw⟩ := List.mem_flatMap.1 hw
        obtain ⟨hil, hseq⟩ := (mem_mine blks j i).1 hi
        refine List.mem_flatMap.2 ⟨i, List.mem_range.2 hil, ?_⟩
        have : (rec_ i).src = c := by simp only [rec_, hseq]; exact hsrc
        simp only [this, ↓reduceIte]; exact hw
      · obtain ⟨_, i, hi, hseq, _, hw'⟩ := atX w hw he
        exact List.mem_flatMap.2 ⟨i, (mem_mine blks j i).2 ⟨hi, hseq⟩, hw'⟩
    · next hsrc =>
      apply applyW_not
      simp only [List.mem_map, not_exists, not_and]
      intro w hw he
      obtain ⟨_, i, hi, hseq, hc, _⟩ := atX w hw he
      exact hsrc (by simp only [rec_, hseq] at hc; exact hc)
  -- reading a buffer after the dispatch
  have bufRes : ∀ sb, (sb = 0 ∨ sb = 1) → res.1.buf sb =
      applyW ((List.range blks.length).flatMap fun i => if (rec_ i).src = 1 - sb then writes i else []) (mem.buf sb) := by
    intro sb hsb
    rw [hres1]
    rcases hsb with rfl | rfl <;> simp [Mem.buf] <;> rfl
  refine ⟨fun j hj => ?_, fun sb x hsb hx => ?_⟩
  · intro r xs L G
    have eS : r.start = (recs.getD j dR).start := rfl
    have eE : r.end_ = (recs.getD j dR).end_ := rfl
    have eSrc : r.src = (recs.getD j dR).src := rfl
    have eL : L = (lowerPart (recs.getD j dR).pivot (slice (mem.buf (recs.getD j dR).src) (recs.getD j dR).start
      ((recs.getD j dR).end_ - (recs.getD j dR).start))).length := rfl
    have eG : G = (upperPart (recs.getD j dR).pivot (slice (mem.buf (recs.getD j dR).src) (recs.getD j dR).start
      ((recs.getD j dR).end_ - (recs.getD j dR).start))).length := rfl
    obtain ⟨sumL, sumG, hsum, posJ, _, sliceL, sliceG⟩ := RWf j hj
    have hsrc := (pre.rec_ j hj).2.2.2
    have hse := (pre.rec_ j hj).2.2.1
    have hsum' : L + xs.count r.pivot + G = r.end_ - r.start := hsum
    have hLG : L + G ≤ r.end_ - r.start := by omega
    have hb1 : ∀ x, x < r.start + L → x < r.end_ := fun x h => by omega
    have hb2 : ∀ x, r.end_ - G ≤ x → r.start ≤ x := fun x h => by omega
    have hb3 : ∀ x, x < r.end_ - G → x < r.end_ := fun x h => by omega
    have hb4 : ∀ x, r.start + L ≤ x → r.start ≤ x := fun x h => by omega
    have hb5 : ∀ x, x < r.end_ - G + G → x < r.end_ := fun x h => by omega
    -- the record fields
    have hrec' : res.2.getD j dR = { r with
        lnext := r.lnext + ((mineOf blks j).map sL).sum
        gnext := r.gnext - ((mineOf blks j).map sG).sum
        lmin := if minMax then ((mineOf blks j).map fun i =>
          (blockMinMax (2 ^ k) hT (S i) r.pivot (blks.getD i dB)).1).foldl min r.lmin else r.lmin
        lmax := if minMax then ((mineOf blks j).map fun i =>
          (blockMinMax (2 ^ k) hT (S i) r.pivot (blks.getD i dB)).2.1).foldl max r.lmax else r.lmax
        gmin := if minMax then ((mineOf blks j).map fun i =>
          (blockMinMax (2 ^ k) hT (S i) r.pivot (blks.getD i dB)).2.2.1).foldl min r.gmin else r.gmin
        gmax := if minMax then ((mineOf blks j).map fun i =>
          (blockMinMax (2 ^ k) hT (S i) r.pivot (blks.getD i dB)).2.2.2).foldl max r.gmax else r.gmax } := by
      show ((List.range recs.length).map _).getD j dR = _
      simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range, hj]; rfl
    have sL' : ((mineOf blks j).map sL).sum = L := by
      refine Eq.trans ?_ sumL; congr 1; apply List.map_congr_left; intro i hi
      have hseq := ((mem_mine blks j i).1 hi).2
      simp only [sL, sc, S, rec_, hseq]
    have sG' : ((mineOf blks j).map sG).sum = G := by
      refine Eq.trans ?_ sumG; congr 1; apply List.map_congr_left; intro i hi
      have hseq := ((mem_mine blks j i).1 hi).2
      simp only [sG, sc, S, rec_, hseq]
    have hdst : 1 - r.src = 0 ∨ 1 - r.src = 1 := by omega
    have dstEq : ∀ x, r.start ≤ x → x < r.end_ →
        res.1.buf (1 - r.src) x = applyW ((mineOf blks j).flatMap writes) (mem.buf (1 - r.src)) x := by
      intro x h1 h2
      rw [bufRes _ hdst, bufLemma (1 - (1 - r.src)) j hj x h1 h2, ifT (by omega)]
    rw [hrec']
    refine ⟨by simp only; rw [sL', (pre.rec_ j hj).1], by simp only; rw [sG', (pre.rec_ j hj).2.1],
      rfl, rfl, rfl, rfl, hsum, ?_, ?_, fun x h1 h2 => ?_, fun x h1 h2 => ?_⟩
    · rw [slice_congr _ (applyW ((mineOf blks j).flatMap writes) (mem.buf (1 - r.src))) _ _
        (fun x h1 h2 => dstEq x h1 (hb1 x h2)), WjEq j hj]
      exact sliceL _
    · rw [slice_congr _ (applyW ((mineOf blks j).flatMap writes) (mem.buf (1 - r.src))) _ _
        (fun x h1 h2 => dstEq x (hb2 x h1) (hb5 x h2)), WjEq j hj]
      exact sliceG _
    · rw [bufRes _ hsrc, bufLemma (1 - r.src) j hj x h1 h2, ifF (by omega)]
    · rw [dstEq x (hb4 x h1) (hb3 x h2), WjEq j hj]
      apply applyW_not
      simp only [List.mem_map, not_exists, not_and]
      intro w hw he
      rcases posJ w hw with h | h <;> omega
  · rw [bufRes sb hsb]
    apply applyW_not
    simp only [List.mem_map, not_exists, not_and]
    intro w hw he
    obtain ⟨i, hi, hw⟩ := List.mem_flatMap.1 hw
    rw [List.mem_range] at hi
    split at hw
    · obtain ⟨_, a1, a2⟩ := posW i hi w hw
      rcases hx _ (pre.seq i hi) with h | h <;> omega
    · simp at hw

/-! ## The gap fill -/

/-- **(lemma)**: chunks of `chunk` slots from gs, the last clipped at ge, tile [gs, gs + min(n·chunk, ge − gs)). -/
theorem chunksTile (gs ge chunk : Nat) :
    ∀ n, (List.range n).flatMap (fun q => List.range' (gs + q * chunk) (min (gs + q * chunk + chunk) ge - (gs + q * chunk))) =
      List.range' gs (min (n * chunk) (ge - gs))
  | 0 => by simp
  | n + 1 => by
    rw [List.range_succ, List.flatMap_append, chunksTile gs ge chunk n, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, Nat.succ_mul]
    by_cases h : gs + n * chunk < ge
    · rw [show min (n * chunk) (ge - gs) = n * chunk by omega, List.range'_append_1]
      congr 1; omega
    · rw [show min (gs + n * chunk + chunk) ge - (gs + n * chunk) = 0 by omega, List.range'_zero, List.append_nil]
      congr 1; omega

theorem ceilMulGe (a nb : Nat) (h : 0 < nb) : a ≤ (a + nb - 1) / nb * nb := by
  have := Nat.div_add_mod (a + nb - 1) nb
  have := Nat.mod_lt (a + nb - 1) h
  rw [Nat.mul_comm]; omega

theorem flatMapIdx {α β : Type} (d : α) (F : α → List β) :
    ∀ l : List α, l.flatMap F = (List.range l.length).flatMap fun i => F (l.getD i d)
  | [] => rfl
  | a :: l => by
    rw [List.flatMap_cons, flatMapIdx d F l, List.length_cons, List.range_succ_eq_map, List.flatMap_cons,
      List.flatMap_map]
    rfl

/-- What the host guarantees before the fill (and the partition dispatch delivers): each
record's gap lies inside it; records are disjoint; every block belongs to a record; and record
j's blocks carry the block numbers 0 … nb − 1 once each (`Sorter.swift:129-133`). -/
structure FillPre (recs : List Rec) (blks : List Blk) (bs : Nat) : Prop where
  bs_pos : 0 < bs
  gap : ∀ j < recs.length, (recs.getD j dR).start ≤ (recs.getD j dR).lnext ∧
    (recs.getD j dR).lnext ≤ (recs.getD j dR).gnext ∧ (recs.getD j dR).gnext ≤ (recs.getD j dR).end_
  seq : ∀ i < blks.length, (blks.getD i dB).seq < recs.length
  nums : ∀ j < recs.length, ((mineOf blks j).map fun i => ((blks.getD i dB).begin - (recs.getD j dR).start) / bs).Perm
    (List.range (((recs.getD j dR).end_ - (recs.getD j dR).start + bs - 1) / bs))
  disj : ∀ j j', j < recs.length → j' < recs.length → j ≠ j' →
    (recs.getD j dR).end_ ≤ (recs.getD j' dR).start ∨ (recs.getD j' dR).end_ ≤ (recs.getD j dR).start

/-- **(lemma)**: one fill block writes the pivot over its chunk of the gap, each slot once. -/
theorem fillBlock (T : Nat) (hT : 0 < T) (bs : Nat) (r : Rec) (bk : Blk) :
    let nb := (r.end_ - r.start + bs - 1) / bs
    let q := (bk.begin - r.start) / bs
    let chunk := (r.gnext - r.lnext + nb - 1) / nb
    ((fillWrites T hT bs r bk).map Prod.fst).Perm
      (List.range' (r.lnext + q * chunk) (min (r.lnext + q * chunk + chunk) r.gnext - (r.lnext + q * chunk))) ∧
    ∀ w ∈ fillWrites T hT bs r bk, w.2 = r.pivot := by
  intro nb q chunk
  constructor
  · simp only [fillWrites, List.map_flatMap, List.map_map]
    exact stridesPerm T hT _ _ |>.trans (List.Perm.refl _) |> fun h => by simpa [Function.comp_def] using h
  · intro w hw
    simp only [fillWrites, List.mem_flatMap, List.mem_map] at hw
    obtain ⟨_, _, _, _, rfl⟩ := hw; rfl

theorem countMine (blks : List Blk) (n : Nat) (hseq : ∀ i < blks.length, (blks.getD i dB).seq < n) (i : Nat) :
    ((List.range n).flatMap (mineOf blks)).count i = if i < blks.length then 1 else 0 := by
  rw [List.count_flatMap]
  have e : ∀ j ∈ List.range n, (List.count i ∘ mineOf blks) j =
      if j = (if i < blks.length then (blks.getD i dB).seq else n) then 1 else 0 := by
    intro j hj; rw [List.mem_range] at hj
    simp only [Function.comp, (mineNodup blks j).count, mem_mine]
    by_cases hi : i < blks.length
    · simp only [hi, true_and, ↓reduceIte]
      split <;> split <;> omega
    · simp only [hi, false_and, ↓reduceIte]; simp; omega
  rw [List.map_congr_left e, sumIndicator]
  by_cases hi : i < blks.length
  · have := hseq i hi
    simp only [hi, ↓reduceIte]; rw [ifT this]
  · simp [hi]

theorem minePerm (blks : List Blk) (n : Nat) (hseq : ∀ i < blks.length, (blks.getD i dB).seq < n) :
    ((List.range n).flatMap (mineOf blks)).Perm (List.range blks.length) := by
  rw [List.perm_iff_count]; intro i
  rw [countMine blks n hseq, List.nodup_range.count]; simp only [List.mem_range]

set_option maxHeartbeats 2000000 in
/-- **R-06, R-10, I-004** (T-08, T-09, T-15, T-16): the `gqsort_fill` dispatch, run after the
partition dispatch has completed (R-10), writes each record's pivot over [lnext, gnext) in D —
every index of every gap exactly once (the positions of all its writes are the union of the gaps,
with no repetition) — and changes nothing else. -/
theorem fillDispatchSpec (k bs : Nat) (mem : Mem) (recs : List Rec) (blks : List Blk) (pre : FillPre recs blks bs) :
    let res := fillDispatch (2 ^ k) (Nat.two_pow_pos k) bs mem recs blks
    (∀ j < recs.length, ∀ x, (recs.getD j dR).lnext ≤ x → x < (recs.getD j dR).gnext →
      res.1.D x = (recs.getD j dR).pivot) ∧
    (∀ x, (∀ j < recs.length, x < (recs.getD j dR).lnext ∨ (recs.getD j dR).gnext ≤ x) → res.1.D x = mem.D x) ∧
    res.1.A = mem.A ∧
    (res.2.map Prod.fst).Perm ((List.range recs.length).flatMap fun j =>
      List.range' (recs.getD j dR).lnext ((recs.getD j dR).gnext - (recs.getD j dR).lnext)) := by
  intro res
  have hT := Nat.two_pow_pos k
  let F := fun i => fillWrites (2 ^ k) hT bs (recs.getD (blks.getD i dB).seq dR) (blks.getD i dB)
  have hws : res.2 = (List.range blks.length).flatMap F := by
    show blks.flatMap _ = _; rw [flatMapIdx dB]; rfl
  -- record j's fill positions tile its gap
  have recPos : ∀ j < recs.length, (((mineOf blks j).flatMap F).map Prod.fst).Perm
      (List.range' (recs.getD j dR).lnext ((recs.getD j dR).gnext - (recs.getD j dR).lnext)) := by
    intro j hj
    let r := recs.getD j dR
    let nb := (r.end_ - r.start + bs - 1) / bs
    let chunk := (r.gnext - r.lnext + nb - 1) / nb
    let q := fun i => ((blks.getD i dB).begin - r.start) / bs
    let piece := fun q => List.range' (r.lnext + q * chunk) (min (r.lnext + q * chunk + chunk) r.gnext - (r.lnext + q * chunk))
    have e1 : ((mineOf blks j).flatMap F).map Prod.fst = (mineOf blks j).flatMap fun i => (F i).map Prod.fst := by
      simp [List.map_flatMap]
    rw [e1]
    have step1 : ((mineOf blks j).flatMap fun i => (F i).map Prod.fst).Perm ((mineOf blks j).flatMap fun i => piece (q i)) := by
      refine GpuQuicksortSpec.GpuQuicksort.Pipeline.flatMap_perm_congr _ _ _ fun i hi => ?_
      have hs := ((mem_mine blks j i).1 hi).2
      have := (fillBlock (2 ^ k) hT bs r (blks.getD i dB)).1
      simp only [F, hs]; exact this
    refine step1.trans ?_
    rw [show ((mineOf blks j).flatMap fun i => piece (q i)) = ((mineOf blks j).map q).flatMap piece by
      rw [List.flatMap_map]]
    refine ((pre.nums j hj).flatMap_right piece).trans (List.Perm.of_eq ?_)
    obtain ⟨g1, g2, g3⟩ := pre.gap j hj
    have g1' : r.start ≤ r.lnext := g1
    have g2' : r.lnext ≤ r.gnext := g2
    have g3' : r.gnext ≤ r.end_ := g3
    show (List.range nb).flatMap piece = _
    rw [chunksTile]
    congr 1
    apply Nat.min_eq_right
    by_cases hnb : 0 < nb
    · rw [Nat.mul_comm]; exact ceilMulGe _ _ hnb
    · have hx : r.end_ - r.start + bs - 1 < bs := by
        rcases Nat.lt_or_ge (r.end_ - r.start + bs - 1) bs with h | h
        · exact h
        · exact absurd (Nat.div_pos h pre.bs_pos) hnb
      have : r.gnext - r.lnext = 0 := by omega
      rw [this]; exact Nat.zero_le _
  -- every write lands in its record's gap, with its record's pivot
  have wIn : ∀ i < blks.length, ∀ w ∈ F i,
      let j := (blks.getD i dB).seq
      (recs.getD j dR).lnext ≤ w.1 ∧ w.1 < (recs.getD j dR).gnext ∧ w.2 = (recs.getD j dR).pivot := by
    intro i hi w hw j
    have hj := pre.seq i hi
    have := (recPos j hj).subset (List.mem_map.2 ⟨w, List.mem_flatMap.2 ⟨i, (mem_mine blks j i).2 ⟨hi, rfl⟩, hw⟩, rfl⟩)
    have hr := List.mem_range'_1.1 this
    exact ⟨hr.1, by omega, (fillBlock (2 ^ k) hT bs _ _).2 w hw⟩
  have gapIn : ∀ j < recs.length, ∀ x, (recs.getD j dR).lnext ≤ x → x < (recs.getD j dR).gnext →
      (recs.getD j dR).start ≤ x ∧ x < (recs.getD j dR).end_ := by
    intro j hj x h1 h2; have := pre.gap j hj; omega
  refine ⟨fun j hj x h1 h2 => ?_, fun x hx => ?_, rfl, ?_⟩
  · show applyW res.2 mem.D x = _
    have hx : x ∈ ((mineOf blks j).flatMap F).map Prod.fst :=
      (recPos j hj).symm.subset (List.mem_range'_1.2 ⟨h1, by omega⟩)
    obtain ⟨w, hw, he⟩ := List.mem_map.1 hx
    obtain ⟨i, hi, hwi⟩ := List.mem_flatMap.1 hw
    have hil := ((mem_mine blks j i).1 hi).1
    have hwmem : w ∈ res.2 := by rw [hws]; exact List.mem_flatMap.2 ⟨i, List.mem_range.2 hil, hwi⟩
    refine applyW_uniq _ x _ (fun w' hw' he' => ?_) mem.D ⟨w, hwmem, he⟩
    rw [hws] at hw'
    obtain ⟨i', hi', hw''⟩ := List.mem_flatMap.1 hw'
    rw [List.mem_range] at hi'
    obtain ⟨a1, a2, a3⟩ := wIn i' hi' w' hw''
    rw [a3]
    by_cases hne : (blks.getD i' dB).seq = j
    · rw [hne]
    · exfalso
      have := gapIn _ (pre.seq i' hi') w'.1 a1 a2
      have := gapIn j hj x h1 h2
      rcases pre.disj _ _ (pre.seq i' hi') hj hne with h | h <;> omega
  · show applyW res.2 mem.D x = _
    apply applyW_not
    rw [hws]
    intro hmem
    obtain ⟨w, hw, he⟩ := List.mem_map.1 hmem
    obtain ⟨i, hi, hw'⟩ := List.mem_flatMap.1 hw
    rw [List.mem_range] at hi
    obtain ⟨a1, a2, _⟩ := wIn i hi w hw'
    rcases hx _ (pre.seq i hi) with h | h <;> omega
  · rw [hws, List.map_flatMap]
    refine ((minePerm blks recs.length pre.seq).symm.flatMap_right _).trans ?_
    rw [List.flatMap_assoc]
    refine GpuQuicksortSpec.GpuQuicksort.Pipeline.flatMap_perm_congr _ _ _ fun j hj => ?_
    rw [← List.map_flatMap]
    exact recPos j (List.mem_range.1 hj)

end GpuQuicksort.Theorems
