import GpuQuicksortProof.GpuQuicksort.Spec
import GpuQuicksortProof.GpuQuicksort.Model.LQSort
import GpuQuicksortProof.GpuQuicksort.Theorems.TGPartition
import GpuQuicksortProof.GpuQuicksort.Theorems.AltSort

/-!
# GpuQuicksortProof.GpuQuicksort.Theorems.LQSort
================================================

The phase-two kernel `lqsort` refines the spec model's stack machine (`PhaseTwo.step2`): each
kernel iteration is `step2` applied to the popped segment in thread-major order, with the pivot
the kernel computes (R-14's median of three). The spec model's invariant therefore holds for the
kernel's state, and the kernel sorts its sequence into D, finalizing every index exactly once,
never overflowing its 32-entry stack.
-/

namespace GpuQuicksort.Theorems

open GpuQuicksort.Model
open GpuQuicksortSpec.GpuQuicksort.Model (lowerPart upperPart med3 medianOfThree leB)
open GpuQuicksortSpec.GpuQuicksort.PhaseTwo

/-- The ℓ values of f at b, b + 1, …. -/
def slice (f : Nat → Nat) (b n : Nat) : List Nat := (List.range n).map fun i => f (b + i)

theorem slice_length (f : Nat → Nat) (b n : Nat) : (slice f b n).length = n := by simp [slice]

theorem ifT {α : Type} {c : Prop} [Decidable c] (h : c) (a b : α) : (if c then a else b) = a := by simp [h]
theorem ifF {α : Type} {c : Prop} [Decidable c] (h : ¬ c) (a b : α) : (if c then a else b) = b := by simp [h]

theorem slice_eq (f : Nat → Nat) (b n : Nat) : slice f b n = (List.range' b n).map f := by
  simp [slice, List.range'_eq_map_range, List.map_map, Function.comp_def]

theorem slice_eq_of (f : Nat → Nat) (b : Nat) (l : List Nat) (h : ∀ i < l.length, f (b + i) = l.getD i 0) :
    slice f b l.length = l := by
  apply List.ext_getElem
  · simp [slice]
  · intro i h1 h2
    simp only [slice, List.getElem_map, List.getElem_range]
    rw [h i h2]; simp [List.getD_eq_getElem?_getD, h2]

theorem slice_congr (f g : Nat → Nat) (b n : Nat) (h : ∀ i, b ≤ i → i < b + n → f i = g i) :
    slice f b n = slice g b n := by
  simp only [slice]; apply List.map_congr_left; intro i hi; rw [List.mem_range] at hi
  exact h _ (by omega) (by omega)

theorem slice_getD (f : Nat → Nat) (b n i : Nat) (hi : i < n) : (slice f b n).getD i 0 = f (b + i) := by
  simp [slice, List.getD_eq_getElem?_getD, hi]

theorem medianGetD (xs : List Nat) (h : xs ≠ []) :
    medianOfThree xs = med3 (xs.getD 0 0) (xs.getD (xs.length / 2) 0) (xs.getD (xs.length - 1) 0) := by
  cases xs with
  | nil => exact absurd rfl h
  | cons a t => rfl

/-- **(lemma)** (R-14): the kernel's pivot `med3(S[b], S[(b+e)/2], S[e−1])` is the spec model's
median of three of the sequence's current contents. -/
theorem kernelPivot (f : Nat → Nat) (b n : Nat) (hn : 0 < n) :
    med3 (f b) (f ((b + (b + n)) / 2)) (f (b + n - 1)) = medianOfThree (slice f b n) := by
  have hne : slice f b n ≠ [] := by
    intro h; have := congrArg List.length h; rw [slice_length] at this; simp at this; omega
  rw [medianGetD _ hne, slice_length, slice_getD _ _ _ _ hn, slice_getD _ _ _ _ (by omega),
    slice_getD _ _ _ _ (by omega)]
  congr 2 <;> omega

/-- What reading a buffer gives after writing a list into one of the two buffers. -/
theorem write_buf (m : Mem) (d s : Nat) (ws : List (Nat × Nat)) (hd : d = 0 ∨ d = 1) (hs : s = 0 ∨ s = 1) :
    (m.write d ws).buf s = if s = d then applyW ws (m.buf s) else m.buf s := by
  rcases hd with rfl | rfl <;> rcases hs with rfl | rfl <;> simp [Mem.write, Mem.buf]

/-- Writes all inside [lo, hi) leave every other index alone. -/
theorem applyW_outside (ws : List (Nat × Nat)) (lo hi : Nat) (h : ∀ w ∈ ws, lo ≤ w.1 ∧ w.1 < hi)
    (f : Nat → Nat) (i : Nat) (hi' : i < lo ∨ hi ≤ i) : applyW ws f i = f i := by
  apply applyW_not
  simp only [List.mem_map, not_exists, not_and]
  intro w hw he; have := h w hw; omega

/-! ## The push logic -/

/-- **(lemma)** (R-13, E-10): pushing [longer, shorter] onto `st` with room for both keeps
exactly the children with at least minseq elements, the shorter on top, and records the new
depths. -/
theorem pushChildrenSpec (minseq cap : Nat) (lE sE : StackEntry) (st : List StackEntry) (md : Nat)
    (hroom : st.length + (if minseq ≤ lE.e - lE.b then 1 else 0) + (if minseq ≤ sE.e - sE.b then 1 else 0) ≤ cap) :
    (pushChildren minseq cap [lE, sE] st md false).1 =
      (if minseq ≤ sE.e - sE.b then [sE] else []) ++ (if minseq ≤ lE.e - lE.b then [lE] else []) ++ st ∧
    (pushChildren minseq cap [lE, sE] st md false).2.2 = false ∧
    (pushChildren minseq cap [lE, sE] st md false).2.1 ≤
      max md (st.length + (if minseq ≤ lE.e - lE.b then 1 else 0) + (if minseq ≤ sE.e - sE.b then 1 else 0)) := by
  by_cases h1 : minseq ≤ lE.e - lE.b <;> by_cases h2 : minseq ≤ sE.e - sE.b <;>
    simp only [h1, h2, ↓reduceIte] at hroom ⊢
  · have c1 : ¬ lE.e - lE.b < minseq := by omega
    have c2 : ¬ sE.e - sE.b < minseq := by omega
    have k1 : ¬ cap ≤ st.length := by omega
    have k2 : ¬ cap ≤ st.length + 1 := by omega
    simp only [pushChildren, c1, c2, k1, List.length_cons, k2, ↓reduceIte, List.cons_append]
    exact ⟨by simp, trivial, by omega⟩
  · have c1 : ¬ lE.e - lE.b < minseq := by omega
    have c2 : sE.e - sE.b < minseq := by omega
    have k1 : ¬ cap ≤ st.length := by omega
    simp only [pushChildren, c1, c2, k1, ↓reduceIte]
    exact ⟨by simp, trivial, by omega⟩
  · have c1 : lE.e - lE.b < minseq := by omega
    have c2 : ¬ sE.e - sE.b < minseq := by omega
    have k2 : ¬ cap ≤ st.length := by omega
    simp only [pushChildren, c1, c2, k2, ↓reduceIte]
    exact ⟨by simp, trivial, by omega⟩
  · have c1 : lE.e - lE.b < minseq := by omega
    have c2 : sE.e - sE.b < minseq := by omega
    simp only [pushChildren, c1, c2, ↓reduceIte]
    exact ⟨by simp, trivial, by omega⟩

/-! ## One iteration's memory effects -/

theorem write_buf_other (m : Mem) (d s : Nat) (ws : List (Nat × Nat)) (hd : d = 0 ∨ d = 1)
    (hs : s = 0 ∨ s = 1) (hne : s ≠ d) : (m.write d ws).buf s = m.buf s := by
  rw [write_buf m d s ws hd hs]; simp [hne]

theorem write_buf_same (m : Mem) (d : Nat) (ws : List (Nat × Nat)) (hd : d = 0 ∨ d = 1) :
    (m.write d ws).buf d = applyW ws (m.buf d) := by
  rw [write_buf m d d ws hd hd]; simp

theorem write_buf_outside (m : Mem) (d s : Nat) (ws : List (Nat × Nat)) (hd : d = 0 ∨ d = 1)
    (hs : s = 0 ∨ s = 1) (lo hi : Nat) (h : ∀ w ∈ ws, lo ≤ w.1 ∧ w.1 < hi) (i : Nat) (hi' : i < lo ∨ hi ≤ i) :
    (m.write d ws).buf s i = m.buf s i := by
  rw [write_buf m d s ws hd hs]; split
  · exact applyW_outside ws lo hi h _ i hi'
  · rfl

theorem memD (m : Mem) : m.D = m.buf 0 := by simp [Mem.buf]

theorem altPositions (T : Nat) (hT : 0 < T) (S : Nat → Nat) (b len : Nat) (hx : ∀ i < len, S (b + i) ≤ 0xFFFFFFFF) :
    ∀ w ∈ altsortK T hT S b len, b ≤ w.1 ∧ w.1 < b + len := by
  intro w hw
  have := ((altsortSpec T hT S b len hx).2.1).subset (List.mem_map.2 ⟨w, hw, rfl⟩)
  exact List.mem_range'_1.1 this

/-- **(lemma)**: the memory side of one `lqsort` iteration on [b, e) of buffer `src` (T = 2^k), with
tm the elements in thread-major order. It changes nothing outside [b, e) in either buffer; a
child with at least minseq elements is left in the other buffer — the below-pivot part of tm at
[b, b + L), the above-pivot part at [e − G, e); D holds p over the gap; and a shorter non-empty
child is written sorted into D, each of its indices once. -/
theorem iterMemSpec (k minseq : Nat) (mem : Mem) (b e src p : Nat) (hbe : b ≤ e) (hsrc : src = 0 ∨ src = 1)
    (hbd : ∀ i, b ≤ i → i < e → mem.buf src i ≤ 0xFFFFFFFF) :
    let it := iterMem (2 ^ k) (Nat.two_pow_pos k) minseq mem b e src p
    let tm := ((List.range (2 ^ k)).flatMap (visits (2 ^ k) (Nat.two_pow_pos k) b e)).map (mem.buf src)
    let L := it.2.1.L
    let G := it.2.1.G
    tm.Perm (slice (mem.buf src) b (e - b)) ∧
    L = (lowerPart p tm).length ∧ G = (upperPart p tm).length ∧ L + tm.count p + G = e - b ∧
    (∀ s, (s = 0 ∨ s = 1) → ∀ i, (i < b ∨ e ≤ i) → it.1.buf s i = mem.buf s i) ∧
    (minseq ≤ L → slice (it.1.buf (1 - src)) b L = lowerPart p tm) ∧
    (minseq ≤ G → slice (it.1.buf (1 - src)) (e - G) G = upperPart p tm) ∧
    (∀ w ∈ it.2.1.gap, b + L ≤ w.1 ∧ w.1 < e - G ∧ w.2 = p ∧ it.1.D w.1 = w.2) ∧
    (it.2.1.gap.map Prod.fst).Perm (List.range' (b + L) (e - G - (b + L))) ∧
    (∀ w ∈ it.2.2.1, b ≤ w.1 ∧ w.1 < b + L ∧ it.1.D w.1 = w.2) ∧
    it.2.2.1.Perm (if 0 < L ∧ L < minseq then (List.range' b L).zip ((lowerPart p tm).mergeSort leB) else []) ∧
    (∀ w ∈ it.2.2.2, e - G ≤ w.1 ∧ w.1 < e ∧ it.1.D w.1 = w.2) ∧
    it.2.2.2.Perm (if 0 < G ∧ G < minseq then (List.range' (e - G) G).zip ((upperPart p tm).mergeSort leB) else []) := by
  intro it tm L G
  have hT := Nat.two_pow_pos k
  obtain ⟨hperm, hL, hG, hsum, hsc, hgap⟩ := tgPartitionSpec k (mem.buf src) p b e hbe
  have hperm' : tm.Perm (slice (mem.buf src) b (e - b)) := by rw [slice_eq]; exact hperm
  -- the pieces of `iterMem`
  let part := tgPartition (2 ^ k) hT (mem.buf src) p b e
  let dst := 1 - src
  have hdst : dst = 0 ∨ dst = 1 := by omega
  have hsd : src ≠ dst := by omega
  let lo := lowerPart p tm
  let up := upperPart p tm
  have hLp : L = part.L := rfl
  have hGp : G = part.G := rfl
  have hLl : part.L = lo.length := hL
  have hGl : part.G = up.length := hG
  have hsum' : part.L + tm.count p + part.G = e - b := hsum
  have hLG : b + part.L ≤ e - part.G := by omega
  -- every element of either part is an element of the slice, hence a 32-bit code
  have memBd : ∀ x ∈ tm, x ≤ 0xFFFFFFFF := by
    intro x hx
    have := hperm'.subset hx
    rw [slice_eq] at this
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 this
    have := List.mem_range'_1.1 hi; exact hbd i (by omega) (by omega)
  have loBd : ∀ j < lo.length, lo.getD j 0 ≤ 0xFFFFFFFF := fun j hj => memBd _ (by
    have : lo.getD j 0 ∈ lo := by simp [List.getD_eq_getElem?_getD, hj]
    exact (List.mem_filter.1 this).1)
  have upBd : ∀ j < up.length, up.getD j 0 ≤ 0xFFFFFFFF := fun j hj => memBd _ (by
    have : up.getD j 0 ∈ up := by simp [List.getD_eq_getElem?_getD, hj]
    exact (List.mem_filter.1 this).1)
  -- memory after each write
  let m0 := mem.write dst part.scatter
  let m1 := m0.write 0 part.gap
  have h0d : ∀ i, m0.buf dst i = if b ≤ i ∧ i < b + part.L then lo.getD (i - b) 0
      else if e - part.G ≤ i ∧ i < e then up.getD (i - (e - part.G)) 0 else mem.buf dst i := by
    intro i; rw [write_buf_same _ _ _ hdst]; exact hsc _ i
  have h0s : m0.buf src = mem.buf src := write_buf_other _ _ _ _ hdst hsrc hsd
  have h1 : ∀ s, (s = 0 ∨ s = 1) → ∀ i, m1.buf s i =
      if s = 0 ∧ b + part.L ≤ i ∧ i < e - part.G then p else m0.buf s i := by
    intro s hs i
    rw [write_buf _ _ _ _ (Or.inl rfl) hs]
    by_cases h : s = 0
    · subst h; simp only [↓reduceIte, true_and]; rw [← memD]; exact hgap _ i
    · simp [h]
  have lo1 : slice (m1.buf dst) b part.L = lo := by
    rw [hLl]; apply slice_eq_of; intro i hi
    rw [h1 dst hdst, ifF (by omega), h0d, ifT (by omega), Nat.add_sub_cancel_left]
  let wl := if 0 < part.L ∧ part.L < minseq then altsortK (2 ^ k) hT (m1.buf dst) b part.L else []
  let m2 := m1.write 0 wl
  have wlSpec : ∀ D i, applyW wl D i = if 0 < part.L ∧ part.L < minseq ∧ b ≤ i ∧ i < b + part.L
      then (lo.mergeSort leB).getD (i - b) 0 else D i := by
    intro D i
    by_cases hc : 0 < part.L ∧ part.L < minseq
    · show applyW (if 0 < part.L ∧ part.L < minseq then altsortK (2 ^ k) hT (m1.buf dst) b part.L else []) D i = _
      rw [ifT hc]
      rw [(altsortSpec (2 ^ k) hT (m1.buf dst) b part.L (fun j hj => by
        have := congrArg (fun l => l.getD j 0) lo1
        rw [← slice_getD (m1.buf dst) b _ _ hj, this]; exact loBd j (by omega))).1 D i]
      rw [show (List.map (fun i => m1.buf dst (b + i)) (List.range part.L)) = lo from lo1]
      by_cases hr : b ≤ i ∧ i < b + part.L
      · rw [ifT hr, ifT ⟨hc.1, hc.2, hr⟩]
      · rw [ifF hr, ifF (fun h => hr h.2.2)]
    · have hn : ¬ (0 < part.L ∧ part.L < minseq ∧ b ≤ i ∧ i < b + part.L) := fun h => hc ⟨h.1, h.2.1⟩
      show applyW (if 0 < part.L ∧ part.L < minseq then altsortK (2 ^ k) hT (m1.buf dst) b part.L else []) D i = _
      rw [ifF hc, ifF hn]; rfl
  have h2 : ∀ s, (s = 0 ∨ s = 1) → ∀ i, m2.buf s i =
      if s = 0 ∧ 0 < part.L ∧ part.L < minseq ∧ b ≤ i ∧ i < b + part.L then (lo.mergeSort leB).getD (i - b) 0
      else m1.buf s i := by
    intro s hs i
    rw [write_buf _ _ _ _ (Or.inl rfl) hs]
    by_cases h : s = 0
    · subst h; simp only [↓reduceIte, true_and]; exact wlSpec _ i
    · simp [h]
  have up2 : slice (m2.buf dst) (e - part.G) part.G = up := by
    rw [hGl]; apply slice_eq_of; intro i hi
    rw [h2 dst hdst, ifF (by omega), h1 dst hdst, ifF (by omega), h0d, ifF (by omega), ifT (by omega)]
    congr 1; omega
  let wg := if 0 < part.G ∧ part.G < minseq then altsortK (2 ^ k) hT (m2.buf dst) (e - part.G) part.G else []
  let m3 := m2.write 0 wg
  have wgSpec : ∀ D i, applyW wg D i = if 0 < part.G ∧ part.G < minseq ∧ e - part.G ≤ i ∧ i < e
      then (up.mergeSort leB).getD (i - (e - part.G)) 0 else D i := by
    intro D i
    by_cases hc : 0 < part.G ∧ part.G < minseq
    · show applyW (if 0 < part.G ∧ part.G < minseq then altsortK (2 ^ k) hT (m2.buf dst) (e - part.G) part.G else []) D i = _
      rw [ifT hc]
      rw [(altsortSpec (2 ^ k) hT (m2.buf dst) (e - part.G) part.G (fun j hj => by
        have := congrArg (fun l => l.getD j 0) up2
        rw [← slice_getD (m2.buf dst) (e - part.G) _ _ hj, this]; exact upBd j (by omega))).1 D i]
      rw [show (List.map (fun i => m2.buf dst (e - part.G + i)) (List.range part.G)) = up from up2,
        show e - part.G + part.G = e by omega]
      by_cases hr : e - part.G ≤ i ∧ i < e
      · rw [ifT hr, ifT ⟨hc.1, hc.2, hr⟩]
      · rw [ifF hr, ifF (fun h => hr h.2.2)]
    · have hn : ¬ (0 < part.G ∧ part.G < minseq ∧ e - part.G ≤ i ∧ i < e) := fun h => hc ⟨h.1, h.2.1⟩
      show applyW (if 0 < part.G ∧ part.G < minseq then altsortK (2 ^ k) hT (m2.buf dst) (e - part.G) part.G else []) D i = _
      rw [ifF hc, ifF hn]; rfl
  have h3 : ∀ s, (s = 0 ∨ s = 1) → ∀ i, m3.buf s i =
      if s = 0 ∧ 0 < part.G ∧ part.G < minseq ∧ e - part.G ≤ i ∧ i < e then
        (up.mergeSort leB).getD (i - (e - part.G)) 0
      else m2.buf s i := by
    intro s hs i
    rw [write_buf _ _ _ _ (Or.inl rfl) hs]
    by_cases h : s = 0
    · subst h; simp only [↓reduceIte, true_and]; exact wgSpec _ i
    · simp [h]
  have hL' : L = lo.length := hL
  have hG' : G = up.length := hG
  -- the written lists, as the sorted parts at their positions
  have wlPerm : wl.Perm (if 0 < part.L ∧ part.L < minseq then (List.range' b part.L).zip (lo.mergeSort leB) else []) := by
    by_cases hc : 0 < part.L ∧ part.L < minseq
    · show (if 0 < part.L ∧ part.L < minseq then altsortK (2 ^ k) hT (m1.buf dst) b part.L else []).Perm _
      rw [ifT hc, ifT hc]
      have := (altsortSpec (2 ^ k) hT (m1.buf dst) b part.L (fun j hj => by
        have := congrArg (fun l => l.getD j 0) lo1
        rw [← slice_getD (m1.buf dst) b _ _ hj, this]; exact loBd j (by omega))).2.2
      rwa [show (List.map (fun i => m1.buf dst (b + i)) (List.range part.L)) = lo from lo1] at this
    · show (if 0 < part.L ∧ part.L < minseq then altsortK (2 ^ k) hT (m1.buf dst) b part.L else []).Perm _
      rw [ifF hc, ifF hc]
  have wgPerm : wg.Perm (if 0 < part.G ∧ part.G < minseq then (List.range' (e - part.G) part.G).zip (up.mergeSort leB) else []) := by
    by_cases hc : 0 < part.G ∧ part.G < minseq
    · show (if 0 < part.G ∧ part.G < minseq then altsortK (2 ^ k) hT (m2.buf dst) (e - part.G) part.G else []).Perm _
      rw [ifT hc, ifT hc]
      have := (altsortSpec (2 ^ k) hT (m2.buf dst) (e - part.G) part.G (fun j hj => by
        have := congrArg (fun l => l.getD j 0) up2
        rw [← slice_getD (m2.buf dst) (e - part.G) _ _ hj, this]; exact upBd j (by omega))).2.2
      rwa [show (List.map (fun i => m2.buf dst (e - part.G + i)) (List.range part.G)) = up from up2] at this
    · show (if 0 < part.G ∧ part.G < minseq then altsortK (2 ^ k) hT (m2.buf dst) (e - part.G) part.G else []).Perm _
      rw [ifF hc, ifF hc]
  have hgapDef : part.gap = ((List.range (2 ^ k)).flatMap fun t =>
      strideFrom (b + part.L + t) (2 ^ k) (e - part.G) hT).map fun i => (i, p) := by
    simp only [List.map_flatMap]; rfl
  have sortedLen : (lo.mergeSort leB).length = part.L := by rw [List.length_mergeSort]; exact hLl.symm
  have sortedLenG : (up.mergeSort leB).length = part.G := by rw [List.length_mergeSort]; exact hGl.symm
  refine ⟨hperm', hL, hG, hsum', ?_, ?_, ?_, ?_, ?_, ?_, wlPerm, ?_, wgPerm⟩
  · -- frame
    intro s hs i hi
    show m3.buf s i = _
    rw [h3 s hs, ifF (by omega), h2 s hs, ifF (by omega), h1 s hs, ifF (by omega)]
    by_cases hsd' : s = dst
    · subst hsd'; rw [h0d, ifF (by omega), ifF (by omega)]
    · have : s = src := by omega
      subst this; rw [h0s]
  · -- the lower child, when pushed
    intro hm
    show slice (m3.buf dst) b L = lo
    rw [hL']
    apply slice_eq_of; intro i hi
    rw [h3 dst hdst, ifF (by omega), h2 dst hdst, ifF (by omega), h1 dst hdst, ifF (by omega), h0d,
      ifT (by omega)]
    congr 1; omega
  · -- the upper child, when pushed
    intro hm
    show slice (m3.buf dst) (e - G) G = up
    have e1 : slice (m3.buf dst) (e - part.G) up.length = up := by
      apply slice_eq_of; intro i hi
      rw [h3 dst hdst, ifF (by omega), h2 dst hdst, ifF (by omega), h1 dst hdst, ifF (by omega), h0d,
        ifF (by omega), ifT (by omega)]
      congr 1; omega
    rw [show G = up.length from hG', show e - up.length = e - part.G by omega]; exact e1
  · -- the gap
    intro w hw
    rw [show it.2.1.gap = part.gap from rfl, hgapDef] at hw
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hw
    have := List.mem_range'_1.1 ((stridesPerm (2 ^ k) hT (b + part.L) (e - part.G)).subset hi)
    refine ⟨by omega, by omega, rfl, ?_⟩
    show m3.D i = p
    rw [memD, h3 0 (Or.inl rfl), ifF (by omega), h2 0 (Or.inl rfl), ifF (by omega), h1 0 (Or.inl rfl),
      ifT (by omega)]
  · show (part.gap.map Prod.fst).Perm (List.range' (b + part.L) (e - part.G - (b + part.L)))
    rw [hgapDef, List.map_map]
    have := stridesPerm (2 ^ k) hT (b + part.L) (e - part.G)
    simpa [Function.comp_def] using this
  · -- the lower child's write-back
    intro w hw
    have hw' := wlPerm.subset hw
    by_cases hc : 0 < part.L ∧ part.L < minseq
    · rw [ifT hc] at hw'
      rw [← sortedLen] at hw'
      obtain ⟨j, hj, e1, e2⟩ := (memZipRange b _ w.1 w.2).1 hw'
      refine ⟨by omega, by omega, ?_⟩
      show m3.D w.1 = w.2
      rw [memD, h3 0 (Or.inl rfl), ifF (by omega), h2 0 (Or.inl rfl), ifT ⟨rfl, hc.1, hc.2, by omega, by omega⟩, e2]
      congr 1; omega
    · rw [ifF hc] at hw'; simp at hw'
  · -- the upper child's write-back
    intro w hw
    have hw' := wgPerm.subset hw
    by_cases hc : 0 < part.G ∧ part.G < minseq
    · rw [ifT hc] at hw'
      rw [← sortedLenG] at hw'
      obtain ⟨j, hj, e1, e2⟩ := (memZipRange _ _ w.1 w.2).1 hw'
      refine ⟨by omega, by omega, ?_⟩
      show m3.D w.1 = w.2
      rw [memD, h3 0 (Or.inl rfl), ifT ⟨rfl, hc.1, hc.2, by omega, by omega⟩, e2]
      congr 1; omega
    · rw [ifF hc] at hw'; simp at hw' 

end GpuQuicksort.Theorems
