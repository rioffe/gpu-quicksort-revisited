import GpuQuicksortProof.GpuQuicksort.Spec
import GpuQuicksortProof.GpuQuicksort.Model.LQSort
import GpuQuicksortProof.GpuQuicksort.Theorems.Codec
import GpuQuicksortProof.GpuQuicksort.Theorems.Scan

/-!
# GpuQuicksortProof.GpuQuicksort.Theorems.TGPartition
=====================================================

The threadgroup partition shared by the sorting kernels (pass 1, `scan2`, pass 2, the gap fill)
is the spec model's parallel partition with one block: the scatter writes the below-pivot
elements of the thread-major element order to [b, b + L) and the above-pivot ones to
[e − G, e); the gap fill writes p to [b + L, e − G); nothing else is written.
-/

namespace GpuQuicksort.Theorems

open GpuQuicksort.Model
open GpuQuicksortSpec.GpuQuicksort.Model (lowerPart upperPart)
open GpuQuicksortSpec.GpuQuicksort.ParallelPartition

/-! ## Writes with a unique value per slot -/

/-- **(lemma)**: if every write to slot x carries the value v and at least one exists, slot x ends
holding v (whatever the order of the writes). -/
theorem applyW_uniq (ws : List (Nat × Nat)) (x v : Nat) (hall : ∀ w ∈ ws, w.1 = x → w.2 = v) :
    ∀ m, (∃ w ∈ ws, w.1 = x) → applyW ws m x = v := by
  induction ws with
  | nil => intro m ⟨w, hw, _⟩; simp at hw
  | cons w0 rest ih =>
    intro m hex
    simp only [applyW, List.foldl_cons] at ih ⊢
    by_cases hr : ∃ w ∈ rest, w.1 = x
    · exact ih (fun w hw => hall w (List.mem_cons_of_mem _ hw)) _ hr
    · have hnot : x ∉ rest.map Prod.fst := by
        simp only [List.mem_map, not_exists, not_and]; intro w hw he; exact hr ⟨w, hw, he⟩
      rw [show List.foldl (fun m w => updN m w.1 w.2) (updN m w0.1 w0.2) rest x =
        applyW rest (updN m w0.1 w0.2) x from rfl, applyW_not _ _ _ hnot]
      obtain ⟨w, hw, he⟩ := hex
      rcases List.mem_cons.1 hw with rfl | hw'
      · simp [updN, he, hall w List.mem_cons_self he]
      · exact absurd ⟨w, hw', he⟩ hr

/-- **(lemma)**: applying writes whose positions form the same set with the same values gives the
same memory, when each slot's writes agree. (Used to reorder writes.) -/
theorem applyW_perm (ws ws' : List (Nat × Nat)) (h : ws.Perm ws')
    (hfun : ∀ w ∈ ws, ∀ w' ∈ ws, w.1 = w'.1 → w.2 = w'.2) (m : Nat → Nat) (x : Nat) :
    applyW ws m x = applyW ws' m x := by
  by_cases hx : ∃ w ∈ ws, w.1 = x
  · obtain ⟨w, hw, he⟩ := hx
    have h1 := applyW_uniq ws x w.2 (fun w' hw' he' => (hfun w hw w' hw' (he.trans he'.symm)).symm) m ⟨w, hw, he⟩
    have h2 := applyW_uniq ws' x w.2 (fun w' hw' he' => (hfun w hw w' (h.mem_iff.2 hw') (he.trans he'.symm)).symm)
      m ⟨w, h.mem_iff.1 hw, he⟩
    rw [h1, h2]
  · have n1 : x ∉ ws.map Prod.fst := by
      simp only [List.mem_map, not_exists, not_and]; intro w hw he; exact hx ⟨w, hw, he⟩
    have n2 : x ∉ ws'.map Prod.fst := by
      simp only [List.mem_map, not_exists, not_and]; intro w hw he; exact hx ⟨w, h.mem_iff.2 hw, he⟩
    rw [applyW_not _ _ _ n1, applyW_not _ _ _ n2]

/-! ## Strides from a base -/

theorem strideShift (T : Nat) (hT : 0 < T) (b e : Nat) :
    ∀ s, strideFrom (b + s) T e hT = (strideFrom s T (e - b) hT).map (b + ·) := by
  intro s
  induction s using strideFrom.induct T (e - b) hT with
  | case1 s hs ih =>
    have eL : strideFrom (b + s) T e hT = (b + s) :: strideFrom (b + s + T) T e hT := by
      rw [strideFrom]; simp [show b + s < e by omega]
    have eR : strideFrom s T (e - b) hT = s :: strideFrom (s + T) T (e - b) hT := by
      rw [strideFrom]; simp [hs]
    rw [eL, eR, List.map_cons, show b + s + T = b + (s + T) by omega, ih]
  | case2 s hs =>
    have eL : strideFrom (b + s) T e hT = [] := by rw [strideFrom]; simp [show ¬ b + s < e by omega]
    have eR : strideFrom s T (e - b) hT = [] := by rw [strideFrom]; simp [hs]
    rw [eL, eR, List.map_nil]

/-- **(lemma)** (R-05): T threads, thread t reading b + t, b + t + T, …, below e, together read
every index of [b, e) exactly once. -/
theorem stridesPerm (T : Nat) (hT : 0 < T) (b e : Nat) :
    ((List.range T).flatMap fun t => strideFrom (b + t) T e hT).Perm (List.range' b (e - b)) := by
  have : ((List.range T).flatMap fun t => strideFrom (b + t) T e hT) =
      (gridVisits T (e - b) hT).map (b + ·) := by
    simp only [gridVisits, List.map_flatMap, strideShift]
  rw [this, List.range'_eq_map_range]
  exact (gridPerm T (e - b) hT).map _

/-! ## Pass 2 of one thread -/

/-- The (position, value) pairs of a list of pass-2 writes. -/
def pairs (ws : List W) : List (Nat × Nat) := ws.map fun w => (w.pos, w.val)

theorem lowW_cons_lt (p base v : Nat) (vs : List Nat) (h : v < p) :
    lowW p base (v :: vs) = ⟨base, v⟩ :: lowW p (base + 1) vs := by
  simp [lowW, lowerPart, h, List.range'_succ]

theorem lowW_cons_ge (p base v : Nat) (vs : List Nat) (h : ¬ v < p) :
    lowW p base (v :: vs) = lowW p base vs := by
  simp [lowW, lowerPart, h]

theorem highW_cons_gt (p base v : Nat) (vs : List Nat) (h : p < v) :
    highW p base (v :: vs) = ⟨base, v⟩ :: highW p (base + 1) vs := by
  simp [highW, upperPart, h, List.range'_succ]

theorem highW_cons_le (p base v : Nat) (vs : List Nat) (h : ¬ p < v) :
    highW p base (v :: vs) = highW p base vs := by
  simp [highW, upperPart, h]

/-- **(lemma)** (R-04 pass 2): one thread's scatter writes its below-pivot elements at lfrom, lfrom+1, …
and its above-pivot elements at gfrom, gfrom+1, …, in its reading order. -/
theorem passWritesPerm (S : Nat → Nat) (p : Nat) :
    ∀ (is : List Nat) (lf gf : Nat),
      (passWrites S p lf gf is).Perm (pairs (lowW p lf (is.map S)) ++ pairs (highW p gf (is.map S)))
  | [], lf, gf => by simp [passWrites, pairs, lowW, highW, lowerPart, upperPart]
  | i :: is, lf, gf => by
    have ih := passWritesPerm S p is
    simp only [passWrites, List.map_cons]
    by_cases h1 : S i < p
    · have h2 : ¬ p < S i := by omega
      simp only [h1, ↓reduceIte, lowW_cons_lt _ _ _ _ h1, highW_cons_le _ _ _ _ h2, pairs, List.map_cons,
        List.cons_append]
      exact (ih (lf + 1) gf).cons _
    · by_cases h2 : p < S i
      · simp only [h1, h2, ↓reduceIte, lowW_cons_ge _ _ _ _ h1, highW_cons_gt _ _ _ _ h2, pairs,
          List.map_cons]
        exact ((ih lf (gf + 1)).cons _).trans List.perm_middle.symm
      · simp only [h1, h2, ↓reduceIte, lowW_cons_ge _ _ _ _ h1, highW_cons_le _ _ _ _ h2]
        exact ih lf gf

/-! ## Offsets from the scan are the block's prefix sums -/

theorem blockLowConv (p : Nat) (f : Nat → List Nat) (g : Nat → Nat) :
    ∀ n a base, (∀ t, a ≤ t → t < a + n →
        g t = base + ((List.range' a (t - a)).map fun u => lowCount p (f u)).sum) →
      (List.range' a n).flatMap (fun t => lowW p (g t) (f t)) = blockLow p base ((List.range' a n).map f)
  | 0, a, base, _ => by simp [blockLow, exScan]
  | n + 1, a, base, h => by
    rw [List.range'_succ, List.flatMap_cons, List.map_cons, blockLow_cons]
    have ga : g a = base := by have := h a (Nat.le_refl _) (by omega); simp at this; exact this
    rw [ga, blockLowConv p f g n (a + 1) (base + lowCount p (f a)) (fun t h1 h2 => by
      rw [h t (by omega) (by omega), show t - a = (t - (a + 1)) + 1 by omega, List.range'_succ]
      simp only [List.map_cons, List.sum_cons]; omega)]

theorem blockHighConv (p : Nat) (f : Nat → List Nat) (g : Nat → Nat) :
    ∀ n a base, (∀ t, a ≤ t → t < a + n →
        g t = base + ((List.range' a (t - a)).map fun u => highCount p (f u)).sum) →
      (List.range' a n).flatMap (fun t => highW p (g t) (f t)) = blockHigh p base ((List.range' a n).map f)
  | 0, a, base, _ => by simp [blockHigh, exScan]
  | n + 1, a, base, h => by
    rw [List.range'_succ, List.flatMap_cons, List.map_cons, blockHigh_cons]
    have ga : g a = base := by have := h a (Nat.le_refl _) (by omega); simp at this; exact this
    rw [ga, blockHighConv p f g n (a + 1) (base + highCount p (f a)) (fun t h1 h2 => by
      rw [h t (by omega) (by omega), show t - a = (t - (a + 1)) + 1 by omega, List.range'_succ]
      simp only [List.map_cons, List.sum_cons]; omega)]

theorem pairsZip (ws : List W) : pairs ws = (ws.map (·.pos)).zip (ws.map (·.val)) := by
  induction ws with
  | nil => rfl
  | cons w ws ih => simp [pairs] at *; exact ih

theorem memZipRange (a : Nat) (l : List Nat) (x v : Nat) :
    (x, v) ∈ (List.range' a l.length).zip l ↔ ∃ j, j < l.length ∧ x = a + j ∧ v = l.getD j 0 := by
  rw [List.mem_iff_getElem]
  constructor
  · rintro ⟨j, hj, he⟩
    simp only [List.length_zip, List.length_range', Nat.min_self] at hj
    simp only [List.getElem_zip, List.getElem_range', Prod.mk.injEq] at he
    exact ⟨j, hj, by omega, by rw [← he.2]; simp [List.getD_eq_getElem?_getD, hj]⟩
  · rintro ⟨j, hj, rfl, rfl⟩
    exact ⟨j, by simp [hj], by simp [List.getElem_zip, List.getD_eq_getElem?_getD, hj]⟩

theorem flatMapAppendPerm {α β : Type} [DecidableEq β] (A B : α → List β) :
    ∀ l : List α, (l.flatMap fun x => A x ++ B x).Perm (l.flatMap A ++ l.flatMap B)
  | [] => List.Perm.refl _
  | x :: l => by
    have ih := flatMapAppendPerm A B l
    simp only [List.flatMap_cons]
    rw [List.perm_iff_count]; intro v
    have := ih.count_eq v
    simp only [List.count_append] at this ⊢; omega

theorem ltCountEq (S : Nat → Nat) (p : Nat) (is : List Nat) :
    ltCount S p is = lowCount p (is.map S) := by
  simp [ltCount, lowCount, lowerPart, List.filter_map, Function.comp_def]

theorem gtCountEq (S : Nat → Nat) (p : Nat) (is : List Nat) :
    gtCount S p is = highCount p (is.map S) := by
  simp [gtCount, highCount, upperPart, List.filter_map, Function.comp_def]

/-- **(lemma)** (R-04, R-05, R-06): the threadgroup partition of [b, e) around p, with T = 2^k
threads. Let tm be the elements in thread-major order (a permutation of the slice). Then L and G
are the numbers of elements below and above p; the scatter leaves the below-pivot elements of tm
at [b, b + L) and the above-pivot ones at [e − G, e) and touches nothing else; and the gap fill
writes p exactly over [b + L, e − G). -/
theorem tgPartitionSpec (k : Nat) (S : Nat → Nat) (p b e : Nat) (hbe : b ≤ e) :
    let part := tgPartition (2 ^ k) (Nat.two_pow_pos k) S p b e
    let tm := ((List.range (2 ^ k)).flatMap (visits (2 ^ k) (Nat.two_pow_pos k) b e)).map S
    tm.Perm ((List.range' b (e - b)).map S) ∧
    part.L = (lowerPart p tm).length ∧ part.G = (upperPart p tm).length ∧
    part.L + tm.count p + part.G = e - b ∧
    (∀ Dst i, applyW part.scatter Dst i =
      if b ≤ i ∧ i < b + part.L then (lowerPart p tm).getD (i - b) 0
      else if e - part.G ≤ i ∧ i < e then (upperPart p tm).getD (i - (e - part.G)) 0
      else Dst i) ∧
    (∀ D i, applyW part.gap D i = if b + part.L ≤ i ∧ i < e - part.G then p else D i) := by
  intro part tm
  have hT := Nat.two_pow_pos k
  let th := fun t => (visits (2 ^ k) hT b e t).map S
  have htm : tm = ((List.range (2 ^ k)).map th).flatten := by
    simp only [tm, th, List.map_flatMap, List.flatten_eq_flatMap, List.flatMap_map]
    rfl
  have hperm : tm.Perm ((List.range' b (e - b)).map S) := (stridesPerm _ hT b e).map S
  -- the scan results
  let lt := fun t => ltCount S p (visits (2 ^ k) hT b e t)
  let gt := fun t => gtCount S p (visits (2 ^ k) hT b e t)
  obtain ⟨sL, oL⟩ := scan2Correct k lt
  obtain ⟨sG, oG⟩ := scan2Correct k gt
  have hL : part.L = (lowerPart p tm).length := by
    show (scan2 (2 ^ k) lt).2 = _
    rw [sL, htm, ← totalLow_eq]
    simp only [Theorems.S, totalLow, List.map_map, Nat.sub_zero, List.range_eq_range']
    congr 2; funext t; exact ltCountEq S p _
  have hG : part.G = (upperPart p tm).length := by
    show (scan2 (2 ^ k) gt).2 = _
    rw [sG, htm, ← totalHigh_eq]
    simp only [Theorems.S, totalHigh, List.map_map, Nat.sub_zero, List.range_eq_range']
    congr 2; funext t; exact gtCountEq S p _
  have hlen : (lowerPart p tm).length + tm.count p + (upperPart p tm).length = e - b := by
    have := (GpuQuicksortSpec.GpuQuicksort.Theorems.partitionPerm p tm).length_eq
    simp only [GpuQuicksortSpec.GpuQuicksort.Model.partition3, GpuQuicksortSpec.GpuQuicksort.Model.gapPart,
      List.length_append, List.length_replicate] at this
    rw [this, hperm.length_eq]; simp
  refine ⟨hperm, hL, hG, by omega, fun Dst i => ?_, fun D i => ?_⟩
  · -- the scatter is the block's below- and above-pivot writes
    let lp := lowerPart p tm
    let up := upperPart p tm
    let Z := (List.range' b lp.length).zip lp ++ (List.range' (e - part.G) up.length).zip up
    have hZ : part.scatter.Perm Z := by
      have c1 : part.scatter.Perm ((List.range (2 ^ k)).flatMap fun t =>
          pairs (lowW p (b + Theorems.S lt 0 t) (th t)) ++ pairs (highW p (e - part.G + Theorems.S gt 0 t) (th t))) := by
        refine GpuQuicksortSpec.GpuQuicksort.Pipeline.flatMap_perm_congr _ _ _ fun t ht => ?_
        rw [List.mem_range] at ht
        show (passWrites S p (b + (scan2 (2 ^ k) lt).1 t) (e - part.G + (scan2 (2 ^ k) gt).1 t) _).Perm _
        rw [oL t ht, oG t ht]
        exact passWritesPerm S p _ _ _
      refine c1.trans ((flatMapAppendPerm _ _ _).trans ?_)
      have e1 : ((List.range (2 ^ k)).flatMap fun t => pairs (lowW p (b + Theorems.S lt 0 t) (th t))) =
          (List.range' b lp.length).zip lp := by
        simp only [pairs, ← List.map_flatMap]
        rw [List.range_eq_range', blockLowConv p th (fun t => b + Theorems.S lt 0 t) _ 0 b (fun t _ _ => by
          simp only [Theorems.S, Nat.sub_zero]; congr 2; exact List.map_congr_left (fun u _ => ltCountEq S p _))]
        rw [← pairs, pairsZip, blockLow_pos, blockLow_val, ← List.range_eq_range', totalLow_eq, ← htm]
      have e2 : ((List.range (2 ^ k)).flatMap fun t => pairs (highW p (e - part.G + Theorems.S gt 0 t) (th t))) =
          (List.range' (e - part.G) up.length).zip up := by
        simp only [pairs, ← List.map_flatMap]
        rw [List.range_eq_range', blockHighConv p th (fun t => e - part.G + Theorems.S gt 0 t) _ 0 (e - part.G)
          (fun t _ _ => by simp only [Theorems.S, Nat.sub_zero]; congr 2; exact List.map_congr_left (fun u _ => gtCountEq S p _))]
        rw [← pairs, pairsZip, blockHigh_pos, blockHigh_val, ← List.range_eq_range', totalHigh_eq, ← htm]
      rw [e1, e2]
    have memZ : ∀ w ∈ Z, (∃ j, j < lp.length ∧ w.1 = b + j ∧ w.2 = lp.getD j 0) ∨
        (∃ j, j < up.length ∧ w.1 = e - part.G + j ∧ w.2 = up.getD j 0) := by
      intro w hw
      rcases List.mem_append.1 hw with h | h
      · exact Or.inl ((memZipRange b lp w.1 w.2).1 h)
      · exact Or.inr ((memZipRange _ up w.1 w.2).1 h)
    have hLl : part.L = lp.length := hL
    have hGl : part.G = up.length := hG
    have hfun : ∀ w ∈ part.scatter, ∀ w' ∈ part.scatter, w.1 = w'.1 → w.2 = w'.2 := by
      intro w hw w' hw' he
      rcases memZ w (hZ.mem_iff.1 hw) with ⟨j, hj, h1, h2⟩ | ⟨j, hj, h1, h2⟩ <;>
        rcases memZ w' (hZ.mem_iff.1 hw') with ⟨j', hj', h1', h2'⟩ | ⟨j', hj', h1', h2'⟩
      · rw [h2, h2', show j = j' by omega]
      · omega
      · omega
      · rw [h2, h2', show j = j' by omega]
    rw [applyW_perm _ _ hZ hfun]
    by_cases h1 : b ≤ i ∧ i < b + part.L
    · simp only [h1, and_self, ↓reduceIte]
      refine applyW_uniq Z i _ (fun w hw he => ?_) Dst ?_
      · rcases memZ w hw with ⟨j, hj, e1, e2⟩ | ⟨j, hj, e1, e2⟩
        · rw [e2, show i - b = j by omega]
        · omega
      · refine ⟨(i, lp.getD (i - b) 0), List.mem_append_left _ ((memZipRange b lp _ _).2
          ⟨i - b, by omega, by omega, rfl⟩), rfl⟩
    · simp only [h1, ↓reduceIte]
      by_cases h2 : e - part.G ≤ i ∧ i < e
      · simp only [h2, and_self, ↓reduceIte]
        refine applyW_uniq Z i _ (fun w hw he => ?_) Dst ?_
        · rcases memZ w hw with ⟨j, hj, e1, e2⟩ | ⟨j, hj, e1, e2⟩
          · omega
          · rw [e2, show i - (e - part.G) = j by omega]
        · refine ⟨(i, up.getD (i - (e - part.G)) 0), List.mem_append_right _ ((memZipRange _ up _ _).2
            ⟨i - (e - part.G), by omega, by omega, rfl⟩), rfl⟩
      · simp only [h2, ↓reduceIte]
        apply applyW_not
        simp only [List.mem_map, not_exists, not_and]
        intro w hw he
        rcases memZ w hw with ⟨j, hj, e1, _⟩ | ⟨j, hj, e1, _⟩ <;> omega
  · -- the gap fill writes p exactly over [b + L, e − G)
    have hgap : part.gap = ((List.range (2 ^ k)).flatMap fun t =>
        strideFrom (b + part.L + t) (2 ^ k) (e - part.G) hT).map fun i => (i, p) := by
      simp only [List.map_flatMap]; rfl
    have hpos := stridesPerm (2 ^ k) hT (b + part.L) (e - part.G)
    rw [hgap]
    by_cases h : b + part.L ≤ i ∧ i < e - part.G
    · simp only [h, and_self, ↓reduceIte]
      refine applyW_uniq _ i p (fun w hw _ => ?_) D ?_
      · obtain ⟨_, _, rfl⟩ := List.mem_map.1 hw; rfl
      · refine ⟨(i, p), List.mem_map.2 ⟨i, hpos.mem_iff.2 (List.mem_range'_1.2 ⟨h.1, by omega⟩), rfl⟩, rfl⟩
    · simp only [h, ↓reduceIte]
      apply applyW_not
      simp only [List.map_map, List.mem_map, Function.comp, not_exists, not_and]
      intro x hx he
      have := List.mem_range'_1.1 (hpos.mem_iff.1 hx)
      omega

end GpuQuicksort.Theorems
