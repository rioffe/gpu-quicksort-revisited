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

/-! ## The kernel state, read as the spec model's state -/

/-- The spec-model segment a stack entry stands for (positions relative to the root start b0). -/
def segOf (b0 : Nat) (m : Mem) (e : StackEntry) : Seg := ⟨e.b - b0, slice (m.buf e.src) e.b (e.e - e.b)⟩

/-- The finalization log, relative to b0. -/
def finOf (b0 : Nat) (fin : List (Nat × Nat)) : List (Nat × Nat) := fin.map fun w => (w.1 - b0, w.2)

theorem depthOK_head (n : Nat) (g g' : Seg) (r : List Seg) (h : g'.xs.length = g.xs.length)
    (hd : depthOK n (g :: r)) : depthOK n (g' :: r) := ⟨by rw [h]; exact hd.1, hd.2⟩

theorem cwPos (tgt : List Nat) (b m : Nat) (h : b + m ≤ tgt.length) :
    (cw tgt b m).map Prod.fst = List.range' b m := by
  simp only [cw]; exact List.map_fst_zip (by simp; omega)

theorem owed_cons' (tgt : List Nat) (g g' : Seg) (r : List Seg) (hb : g'.b = g.b)
    (hl : g'.xs.length = g.xs.length) : owed tgt (g' :: r) = owed tgt (g :: r) := by
  simp [owed, hb, hl]

/-- **(lemma)**: under the spec model's invariant, the top segment's positions are disjoint from
every finalized position and from every other pending segment. -/
theorem invDisjoint (S : Nat) (hS : 0 < S) (tgt : List Nat) (g : Seg) (rs : List Seg) (fin : List (Nat × Nat))
    (h : Inv S tgt (g :: rs, fin)) :
    (∀ w ∈ fin, w.1 < g.b ∨ g.b + g.xs.length ≤ w.1) ∧
    (∀ g2 ∈ rs, g2.b + g2.xs.length ≤ g.b ∨ g.b + g.xs.length ≤ g2.b) := by
  obtain ⟨hgood, _, hp⟩ := h
  have hnd : ((fin ++ owed tgt (g :: rs)).map Prod.fst).Nodup := by
    have := hp.map Prod.fst
    rw [cwPos tgt 0 _ (by omega)] at this
    exact this.nodup_iff.2 List.nodup_range'
  rw [owed_cons, List.map_append, List.map_append] at hnd
  have gg := hgood g List.mem_cons_self
  rw [cwPos tgt _ _ gg.2.1] at hnd
  obtain ⟨_, hnd2, hdisj⟩ := List.nodup_append.1 hnd
  obtain ⟨_, _, hdisj2⟩ := List.nodup_append.1 hnd2
  constructor
  · intro w hw
    by_cases hc : w.1 < g.b ∨ g.b + g.xs.length ≤ w.1
    · exact hc
    exfalso
    exact hdisj _ (List.mem_map.2 ⟨w, hw, rfl⟩) _ (List.mem_append_left _ (List.mem_range'_1.2 ⟨by omega, by omega⟩)) rfl
  · intro g2 hg2
    by_cases hc : g2.b + g2.xs.length ≤ g.b ∨ g.b + g.xs.length ≤ g2.b
    · exact hc
    exfalso
    have g2g := hgood g2 (List.mem_cons_of_mem _ hg2)
    have l1 := gg.2.2
    have l2 := g2g.2.2
    let i := max g.b g2.b
    have hi2 : i ∈ (owed tgt rs).map Prod.fst := by
      simp only [owed, List.map_flatMap, List.mem_flatMap]
      exact ⟨g2, hg2, by rw [cwPos tgt _ _ g2g.2.1]; exact List.mem_range'_1.2 ⟨by omega, by omega⟩⟩
    exact hdisj2 i (List.mem_range'_1.2 ⟨by omega, by omega⟩) i hi2 rfl

theorem zipReplicate (l : List Nat) (c : Nat) : l.zip (List.replicate l.length c) = l.map (·, c) := by
  induction l with
  | nil => rfl
  | cons x l ih => simp [List.replicate_succ, ih]

theorem range'Shift (a n b0 : Nat) (h : b0 ≤ a) : (List.range' a n).map (· - b0) = List.range' (a - b0) n := by
  rw [List.range'_eq_map_range, List.range'_eq_map_range, List.map_map]
  apply List.map_congr_left; intro i _; simp only [Function.comp]; omega

/-- The kernel's invariant: the spec model's `Inv` for the state read off the kernel, every
finalized position holds its logged value, nothing outside the sequence has changed, no error,
and the recorded depth is within the K-08 bound. -/
structure KInv (S b0 : Nat) (tgt : List Nat) (D0 A0 : Nat → Nat) (st : KS) : Prop where
  entries : ∀ e ∈ st.stack, b0 ≤ e.b ∧ e.b ≤ e.e ∧ (e.src = 0 ∨ e.src = 1)
  inv : Inv S tgt (st.stack.map (segOf b0 st.mem), finOf b0 st.fin)
  finPos : ∀ w ∈ st.fin, b0 ≤ w.1 ∧ st.mem.D w.1 = w.2
  frameD : ∀ i, (i < b0 ∨ b0 + tgt.length ≤ i) → st.mem.D i = D0 i
  frameA : ∀ i, (i < b0 ∨ b0 + tgt.length ≤ i) → st.mem.A i = A0 i
  noErr : st.serr = false
  depth : st.maxDepth ≤ Nat.log2 (tgt.length / S) + 1

theorem mapIf {α β : Type} (c : Prop) [Decidable c] (x : α) (f : α → β) :
    (if c then [x] else []).map f = if c then [f x] else [] := by split <;> rfl

theorem finOfZip (b0 a n : Nat) (h : b0 ≤ a) (X : List Nat) :
    finOf b0 ((List.range' a n).zip X) = (List.range' (a - b0) n).zip X := by
  simp only [finOf]
  rw [← range'Shift a n b0 h, List.zip_map_left]; rfl

theorem pushIfLen (S : Nat) (c : Seg) : (pushIf S c).length = if S ≤ c.xs.length then 1 else 0 := by
  unfold pushIf; split <;> rfl

set_option maxHeartbeats 20000000 in
/-- **(lemma)** (R-13, R-14, E-10, K-08): one `lqsort` iteration preserves the kernel invariant and
removes at least one element from the pending segments. -/
theorem kStepInv (k S cap b0 : Nat) (tgt : List Nat) (D0 A0 : Nat → Nat) (hS : 0 < S)
    (ht : tgt.Pairwise (· ≤ ·)) (hbd : ∀ x ∈ tgt, x ≤ 0xFFFFFFFF)
    (hcap : Nat.log2 (tgt.length / S) + 1 < cap) (st : KS) (h : KInv S b0 tgt D0 A0 st)
    (top : StackEntry) (rest : List StackEntry) (hst : st.stack = top :: rest) :
    KInv S b0 tgt D0 A0 (kStep (2 ^ k) (Nat.two_pow_pos k) S cap st) ∧
    mass ((kStep (2 ^ k) (Nat.two_pow_pos k) S cap st).stack.map
        (segOf b0 (kStep (2 ^ k) (Nat.two_pow_pos k) S cap st).mem)) <
      mass (st.stack.map (segOf b0 st.mem)) := by
  obtain ⟨m, stk, serr, parts, alts, md, fin⟩ := st
  simp only at hst; subst hst
  have hT := Nat.two_pow_pos k
  let n := tgt.length
  let b := top.b
  let e := top.e
  let src := top.src
  let S0 := m.buf src
  let len := e - b
  obtain ⟨hent, hinv, hfinPos, hfD, hfA, hnoErr, hdep⟩ := h
  simp only at hent hinv hfinPos hfD hfA hnoErr hdep
  obtain ⟨hb0, hbe, hsrc⟩ := hent top List.mem_cons_self
  let g := segOf b0 m top
  let restS := rest.map (segOf b0 m)
  let finL := finOf b0 fin
  have hinv' : Inv S tgt (g :: restS, finL) := hinv
  have gg : good S tgt g := hinv'.1 g List.mem_cons_self
  have hglen : g.xs.length = len := slice_length _ _ _
  have hgb : g.b = b - b0 := rfl
  have hlen : 0 < len := by have := gg.2.2; omega
  have hfit : b - b0 + len ≤ n := by have := gg.2.1; omega
  -- the pivot
  let p := med3 (S0 b) (S0 ((b + e) / 2)) (S0 (e - 1))
  have hp : p = medianOfThree g.xs := by
    show med3 (S0 b) (S0 ((b + e) / 2)) (S0 (e - 1)) = medianOfThree (slice S0 b len)
    rw [← kernelPivot S0 b len hlen, show b + len = e by omega]
  -- the slice holds 32-bit codes
  have winBd : ∀ x ∈ g.xs, x ≤ 0xFFFFFFFF := fun x hx =>
    hbd x (List.mem_of_mem_drop (List.mem_of_mem_take (gg.1.subset hx)))
  have hbd' : ∀ i, b ≤ i → i < e → S0 i ≤ 0xFFFFFFFF := by
    intro i h1 h2
    apply winBd
    show S0 i ∈ slice S0 b len
    rw [slice_eq]; exact List.mem_map.2 ⟨i, List.mem_range'_1.2 ⟨h1, by omega⟩, rfl⟩
  -- the iteration's memory effects
  obtain ⟨hperm, hL, hG, hsum, hframe, hlo, hup, hgapF, hgapP, hwlF, hwlP, hwgF, hwgP⟩ :=
    iterMemSpec k S m b e src p hbe hsrc hbd'
  let it := iterMem (2 ^ k) hT S m b e src p
  let tm := ((List.range (2 ^ k)).flatMap (visits (2 ^ k) hT b e)).map S0
  let L := it.2.1.L
  let G := it.2.1.G
  let dst := 1 - src
  have hL' : L = (lowerPart p tm).length := hL
  have hG' : G = (upperPart p tm).length := hG
  have hsum' : L + tm.count p + G = e - b := hsum
  have htmlen : tm.length = len := by rw [hperm.length_eq, slice_length]
  have hdst : dst = 0 ∨ dst = 1 := by omega
  -- the spec model's step on the reordered segment
  let g' : Seg := ⟨b - b0, tm⟩
  have gg' : good S tgt g' := by
    refine ⟨?_, by show b - b0 + tm.length ≤ n; omega, by show S ≤ tm.length; have := gg.2.2; omega⟩
    show tm.Perm ((tgt.drop (b - b0)).take tm.length)
    rw [htmlen, ← hglen]; exact hperm.trans gg.1
  have hdep' : depthOK n (g' :: restS) :=
    depthOK_head n g g' restS (by show tm.length = g.xs.length; omega) hinv'.2.1
  obtain ⟨f1, f2, f3, f4⟩ := stepFacts S n (fun _ => p) tgt ht g' restS finL gg' hdep'
  let lo : Seg := ⟨b - b0, lowerPart p tm⟩
  let hi : Seg := ⟨b - b0 + tm.length - (upperPart p tm).length, upperPart p tm⟩
  let newSegs := (step2 S (fun _ => p) (g' :: restS, finL)).1
  have hnew : newSegs = pushIf S (if hi.xs.length ≤ lo.xs.length then hi else lo) ++
      pushIf S (if hi.xs.length ≤ lo.xs.length then lo else hi) ++ restS := rfl
  have hnewFin : (step2 S (fun _ => p) (g' :: restS, finL)).2 =
      finL ++ gapW (fun _ => p) g' ++ smallW S lo ++ smallW S hi := rfl
  -- every new segment has at least S elements, so the new stack fits (K-08)
  have newGood : ∀ x ∈ newSegs, good S tgt x := by
    intro x hx
    rcases f1 x hx with h | h
    · exact hinv'.1 x (List.mem_cons_of_mem _ h)
    · exact h
  have newLen : newSegs.length ≤ Nat.log2 (n / S) + 1 :=
    depthBound S n hS _ f2 (fun x hx => (newGood x hx).2.2)
  -- the kernel's pushes
  let lFirst := decide (L ≥ G)
  let lb := if lFirst then b else e - G
  let ll := if lFirst then L else G
  let shb := if lFirst then e - G else b
  let shl := if lFirst then G else L
  let lE : StackEntry := ⟨lb, lb + ll, dst⟩
  let sE : StackEntry := ⟨shb, shb + shl, dst⟩
  let pushed := pushChildren S cap [lE, sE] rest md serr
  have hk : kStep (2 ^ k) hT S cap ⟨m, top :: rest, serr, parts, alts, md, fin⟩ =
      { mem := it.1, stack := pushed.1, serr := pushed.2.2, partitions := parts + 1,
        alts := alts + (if 0 < L ∧ L < S then 1 else 0) + (if 0 < G ∧ G < S then 1 else 0),
        maxDepth := pushed.2.1, fin := fin ++ it.2.1.gap ++ it.2.2.1 ++ it.2.2.2 } := rfl
  rw [hk]
  -- the rest of the stack is untouched
  have hrest : rest.map (segOf b0 it.1) = restS := by
    apply List.map_congr_left
    intro x hx
    obtain ⟨hx0, hxe, hxs⟩ := hent x (List.mem_cons_of_mem _ hx)
    have hd := (invDisjoint S hS tgt g restS finL hinv').2 (segOf b0 m x) (List.mem_map.2 ⟨x, hx, rfl⟩)
    simp only [segOf, slice_length, hgb, hglen] at hd
    simp only [segOf]
    congr 1
    exact slice_congr _ _ _ _ fun i h1 h2 => hframe x.src hxs i (by omega)
  -- a pushed lower child is lo, a pushed upper child is hi
  have eqLo : S ≤ L → segOf b0 it.1 ⟨b, b + L, dst⟩ = lo := by
    intro hS'; simp only [segOf, show b + L - b = L by omega]; rw [hlo hS']
  have eqHi : S ≤ G → segOf b0 it.1 ⟨e - G, e - G + G, dst⟩ = hi := by
    intro hS'; simp only [segOf, show e - G + G - (e - G) = G by omega]; rw [hup hS']
    show (⟨e - G - b0, upperPart p tm⟩ : Seg) = ⟨b - b0 + tm.length - (upperPart p tm).length, upperPart p tm⟩
    rw [← hG']; simp only [Seg.mk.injEq, and_true]; omega
  have hlolen : lo.xs.length = L := hL'.symm
  have hhilen : hi.xs.length = G := hG'.symm
  have hroom : rest.length + (if S ≤ lE.e - lE.b then 1 else 0) + (if S ≤ sE.e - sE.b then 1 else 0) ≤ cap := by
    have : newSegs.length = rest.length + (if S ≤ L then 1 else 0) + (if S ≤ G then 1 else 0) := by
      rw [hnew, List.length_append, List.length_append, pushIfLen, pushIfLen, List.length_map]
      by_cases hc : G ≤ L
      · rw [ifT (show hi.xs.length ≤ lo.xs.length by omega), ifT (show hi.xs.length ≤ lo.xs.length by omega),
          hlolen, hhilen]; omega
      · rw [ifF (show ¬ hi.xs.length ≤ lo.xs.length by omega), ifF (show ¬ hi.xs.length ≤ lo.xs.length by omega),
          hlolen, hhilen]; omega
    have newLen' : newSegs.length ≤ Nat.log2 (tgt.length / S) + 1 := newLen
    by_cases hc : G ≤ L
    · simp only [lE, sE, lb, ll, shb, shl, lFirst, show L ≥ G from hc, decide_true, ↓reduceIte,
        show b + L - b = L by omega, show e - G + G - (e - G) = G by omega]
      by_cases s1 : S ≤ L <;> by_cases s2 : S ≤ G <;> simp only [s1, s2, ↓reduceIte] at this ⊢ <;> omega
    · simp only [lE, sE, lb, ll, shb, shl, lFirst, show ¬ L ≥ G by omega, decide_false,
        Bool.false_eq_true, ↓reduceIte, show b + L - b = L by omega, show e - G + G - (e - G) = G by omega]
      by_cases s1 : S ≤ L <;> by_cases s2 : S ≤ G <;> simp only [s1, s2, ↓reduceIte] at this ⊢ <;> omega
  obtain ⟨hp1, hp2, hp3⟩ := pushChildrenSpec S cap lE sE rest md hroom
  have hpushed1 : pushed.1 = (if S ≤ sE.e - sE.b then [sE] else []) ++ (if S ≤ lE.e - lE.b then [lE] else []) ++ rest := by
    show (pushChildren S cap [lE, sE] rest md serr).1 = _; rw [hnoErr]; exact hp1
  have hstack : pushed.1.map (segOf b0 it.1) = newSegs := by
    rw [hpushed1, List.map_append, List.map_append, mapIf, mapIf, hrest, hnew]
    by_cases hc : G ≤ L
    · have c1 : hi.xs.length ≤ lo.xs.length := by omega
      simp only [↓reduceIte, pushIf, hlolen, hhilen, lE, sE, lb, ll, shb, shl, lFirst,
        show L ≥ G from hc, decide_true, show b + L - b = L by omega, show e - G + G - (e - G) = G by omega]
      by_cases s1 : S ≤ G <;> by_cases s2 : S ≤ L <;> simp only [s1, s2, ↓reduceIte, eqLo, eqHi]
    · have c1 : ¬ hi.xs.length ≤ lo.xs.length := by omega
      simp only [↓reduceIte, pushIf, hlolen, hhilen, lE, sE, lb, ll, shb, shl, lFirst,
        show ¬ L ≥ G by omega, decide_false, Bool.false_eq_true, show b + L - b = L by omega,
        show e - G + G - (e - G) = G by omega]
      by_cases s1 : S ≤ G <;> by_cases s2 : S ≤ L <;> simp only [s1, s2, ↓reduceIte, eqLo, eqHi]
  -- the finalization log is the spec model's finalized writes, up to order
  have hcnt : e - G - (b + L) = tm.count p := by omega
  have gapPerm : (finOf b0 it.2.1.gap).Perm (gapW (fun _ => p) g') := by
    have e1 : finOf b0 it.2.1.gap = (it.2.1.gap.map Prod.fst).map fun i => (i - b0, p) := by
      simp only [finOf, List.map_map]
      apply List.map_congr_left; intro w hw
      simp only [Function.comp, (hgapF w hw).2.2.1]
    rw [e1]
    refine (hgapP.map _).trans (List.Perm.of_eq ?_)
    rw [show (fun i => (i - b0, p)) = (fun i => (i, p)) ∘ (· - b0) from rfl, ← List.map_map,
      range'Shift _ _ _ (by omega), hcnt]
    simp only [gapW, g']
    rw [← hL', show b + L - b0 = b - b0 + L by omega]
    have := zipReplicate (List.range' (b - b0 + L) (tm.count p)) p
    rw [List.length_range'] at this; exact this.symm
  have wlPerm : (finOf b0 it.2.2.1).Perm (smallW S lo) := by
    refine (hwlP.map _).trans (List.Perm.of_eq ?_)
    simp only [smallW, hlolen]
    by_cases c1 : 0 < L ∧ L < S
    · rw [ifT c1, ifT c1.2]; exact finOfZip b0 b L hb0 _
    · by_cases c2 : L < S
      · rw [ifF c1, ifT c2, show L = 0 by omega]; rfl
      · rw [ifF c1, ifF c2]; rfl
  have wgPerm : (finOf b0 it.2.2.2).Perm (smallW S hi) := by
    refine (hwgP.map _).trans (List.Perm.of_eq ?_)
    simp only [smallW, hhilen]
    have hib : hi.b = e - G - b0 := by
      show b - b0 + tm.length - (upperPart p tm).length = _
      rw [← hG', htmlen]
      have h1 : G ≤ e - b := by omega
      have h2 : len = e - b := rfl
      generalize G = x at h1 ⊢
      omega
    by_cases c1 : 0 < G ∧ G < S
    · rw [ifT c1, ifT c1.2, hib]; exact finOfZip b0 (e - G) G (by omega) _
    · by_cases c2 : G < S
      · rw [ifF c1, ifT c2, show G = 0 by omega]; rfl
      · rw [ifF c1, ifF c2]; rfl
  have finPerm : (finOf b0 (fin ++ it.2.1.gap ++ it.2.2.1 ++ it.2.2.2)).Perm
      (step2 S (fun _ => p) (g' :: restS, finL)).2 := by
    rw [hnewFin]
    simp only [finOf, List.map_append]
    exact ((List.Perm.refl _).append gapPerm |>.append wlPerm).append wgPerm
  -- lengths of the new stack
  have hlen1 : pushed.1.length = newSegs.length := by rw [← hstack, List.length_map]
  have hlen2 : pushed.1.length = rest.length + (if S ≤ lE.e - lE.b then 1 else 0) + (if S ≤ sE.e - sE.b then 1 else 0) := by
    rw [hpushed1]; simp only [List.length_append]
    split <;> split <;> simp <;> omega
  have hmd : pushed.2.1 ≤ Nat.log2 (tgt.length / S) + 1 := by
    have h3 : pushed.2.1 ≤ max md (rest.length + (if S ≤ lE.e - lE.b then 1 else 0) + (if S ≤ sE.e - sE.b then 1 else 0)) := by
      show (pushChildren S cap [lE, sE] rest md serr).2.1 ≤ _; rw [hnoErr]; exact hp3
    have newLen' : newSegs.length ≤ Nat.log2 (tgt.length / S) + 1 := newLen
    generalize (if S ≤ lE.e - lE.b then 1 else 0) = x at h3 hlen2
    generalize (if S ≤ sE.e - sE.b then 1 else 0) = y at h3 hlen2
    omega
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, hmd⟩, ?_⟩
  · -- entries
    intro x hx
    rw [hpushed1] at hx
    simp only [List.mem_append] at hx
    have hGe : G ≤ e - b := by omega
    rcases hx with (hx | hx) | hx
    · split at hx
      · simp only [List.mem_singleton] at hx; subst hx
        simp only [sE, shb, shl, lFirst]; split <;> refine ⟨by omega, by omega, hdst⟩
      · simp at hx
    · split at hx
      · simp only [List.mem_singleton] at hx; subst hx
        simp only [lE, lb, ll, lFirst]; split <;> refine ⟨by omega, by omega, hdst⟩
      · simp at hx
    · exact hent x (List.mem_cons_of_mem _ hx)
  · -- the spec model's invariant
    show Inv S tgt (pushed.1.map (segOf b0 it.1), finOf b0 (fin ++ it.2.1.gap ++ it.2.2.1 ++ it.2.2.2))
    rw [hstack]
    refine ⟨newGood, f2, ?_⟩
    refine (finPerm.append_right _).trans (f3.trans ?_)
    rw [owed_cons' tgt g g' restS rfl (by show tm.length = g.xs.length; omega)]
    exact hinv'.2.2
  · -- finalized positions
    intro w hw
    simp only [List.mem_append] at hw
    rcases hw with ((hw | hw) | hw) | hw
    · obtain ⟨h1, h2⟩ := hfinPos w hw
      have hd := (invDisjoint S hS tgt g restS finL hinv').1 (w.1 - b0, w.2) (List.mem_map.2 ⟨w, hw, rfl⟩)
      simp only [hgb, hglen] at hd
      refine ⟨h1, ?_⟩
      show it.1.D w.1 = w.2
      rw [memD, hframe 0 (Or.inl rfl) w.1 (by omega), ← memD, h2]
    · obtain ⟨h1, _, _, h4⟩ := hgapF w hw; exact ⟨by omega, h4⟩
    · obtain ⟨h1, _, h3⟩ := hwlF w hw; exact ⟨by omega, h3⟩
    · obtain ⟨h1, _, h3⟩ := hwgF w hw; exact ⟨by omega, h3⟩
  · intro i hi
    show it.1.D i = D0 i
    rw [memD, hframe 0 (Or.inl rfl) i (by omega), ← memD]; exact hfD i hi
  · intro i hi
    show it.1.A i = A0 i
    have := hframe 1 (Or.inr rfl) i (by omega)
    simp only [Mem.buf, show (1 : Nat) ≠ 0 by decide, ↓reduceIte] at this
    rw [this]; exact hfA i hi
  · show (pushChildren S cap [lE, sE] rest md serr).2.2 = false; rw [hnoErr]; exact hp2
  · -- the mass drops by the pivot's multiplicity, at least one
    show mass (pushed.1.map (segOf b0 it.1)) < mass (g :: restS)
    rw [hstack]
    have hmem : p ∈ g.xs := by
      rw [hp]; refine medianOfThreePicks _ (fun h0 => ?_)
      have := congrArg List.length h0; rw [hglen] at this; simp at this; omega
    have hc : 0 < tm.count p := by rw [hperm.count_eq]; exact List.count_pos_iff.2 hmem
    have hm : mass (g' :: restS) = mass (g :: restS) := by
      simp only [mass, List.map_cons, List.sum_cons]; congr 1; show tm.length = g.xs.length; omega
    have f4' : mass newSegs + tm.count p ≤ mass (g' :: restS) := f4
    omega

/-- **(lemma)**: the kernel loop keeps the invariant, and `mass` iterations empty the stack. -/
theorem kRunInv (k S cap b0 : Nat) (tgt : List Nat) (D0 A0 : Nat → Nat) (hS : 0 < S)
    (ht : tgt.Pairwise (· ≤ ·)) (hbd : ∀ x ∈ tgt, x ≤ 0xFFFFFFFF)
    (hcap : Nat.log2 (tgt.length / S) + 1 < cap) :
    ∀ fuel (st : KS), KInv S b0 tgt D0 A0 st →
      KInv S b0 tgt D0 A0 (kRun (2 ^ k) (Nat.two_pow_pos k) S cap fuel st) ∧
      (mass (st.stack.map (segOf b0 st.mem)) ≤ fuel → (kRun (2 ^ k) (Nat.two_pow_pos k) S cap fuel st).stack = [])
  | 0, st, h => by
    refine ⟨h, fun hm => ?_⟩
    simp only [kRun]
    cases hs : st.stack with
    | nil => rfl
    | cons top rest =>
      exfalso
      have gg := h.inv.1 (segOf b0 st.mem top) (by rw [hs]; exact List.mem_cons_self)
      rw [hs] at hm
      simp only [mass, List.map_cons, List.sum_cons] at hm
      have := gg.2.2; omega
  | f + 1, st, h => by
    simp only [kRun]
    by_cases hc : st.stack = [] ∨ st.serr = true
    · simp only [hc, ↓reduceIte]
      refine ⟨h, fun _ => ?_⟩
      rcases hc with hc | hc
      · exact hc
      · rw [h.noErr] at hc; cases hc
    · simp only [hc, ↓reduceIte]
      obtain ⟨top, rest, hst⟩ : ∃ top rest, st.stack = top :: rest := by
        cases hs : st.stack with
        | nil => exact absurd (Or.inl hs) hc
        | cons top rest => exact ⟨top, rest, rfl⟩
      obtain ⟨h1, h2⟩ := kStepInv k S cap b0 tgt D0 A0 hS ht hbd hcap st h top rest hst
      obtain ⟨i1, i2⟩ := kRunInv k S cap b0 tgt D0 A0 hS ht hbd hcap f _ h1
      exact ⟨i1, fun hm => i2 (by omega)⟩

theorem write_nil (m : Mem) (d : Nat) : m.write d [] = m := by
  cases m; simp only [Mem.write]; split <;> rfl

/-- **(lemma)** (E-03): the kernel's start satisfies the invariant: a root with at least minseq
elements is the only stack entry; a shorter non-empty root is alternative-sorted into D at once. -/
theorem kStartInv (k S b0 e0 src0 : Nat) (m : Mem) (hbe : b0 ≤ e0) (hsrc : src0 = 0 ∨ src0 = 1)
    (hbd : ∀ i, b0 ≤ i → i < e0 → m.buf src0 i ≤ 0xFFFFFFFF) :
    let xs := slice (m.buf src0) b0 (e0 - b0)
    KInv S b0 (xs.mergeSort leB) m.D m.A (kStart (2 ^ k) (Nat.two_pow_pos k) S m b0 e0 src0) ∧
      mass ((kStart (2 ^ k) (Nat.two_pow_pos k) S m b0 e0 src0).stack.map
        (segOf b0 (kStart (2 ^ k) (Nat.two_pow_pos k) S m b0 e0 src0).mem)) ≤ e0 - b0 := by
  intro xs
  have hT := Nat.two_pow_pos k
  have hxlen : xs.length = e0 - b0 := slice_length _ _ _
  have htlen : (xs.mergeSort leB).length = e0 - b0 := by rw [List.length_mergeSort, hxlen]
  obtain ⟨sI, _⟩ := startInv S xs
  have depth0 : 1 ≤ Nat.log2 ((xs.mergeSort leB).length / S) + 1 := by omega
  by_cases hn : S ≤ e0 - b0
  · -- the root is pushed
    have hk : kStart (2 ^ k) hT S m b0 e0 src0 =
        { mem := m, stack := [⟨b0, e0, src0⟩], serr := false, partitions := 0, alts := 0, maxDepth := 1,
          fin := [] } := by
      simp only [kStart, ge_iff_le, hn, ↓reduceIte, show ¬ (0 < e0 - b0 ∧ e0 - b0 < S) by omega, write_nil]
    rw [hk]
    have hs2 : start2 S xs = ([⟨0, xs⟩], []) := by simp [start2, hxlen, show ¬ e0 - b0 < S by omega]
    rw [hs2] at sI
    refine ⟨⟨fun x hx => ?_, ?_, fun w hw => by simp at hw, fun _ _ => rfl, fun _ _ => rfl, rfl, depth0⟩, ?_⟩
    · simp only [List.mem_singleton] at hx; subst hx; exact ⟨Nat.le_refl _, hbe, hsrc⟩
    · show Inv S _ ([segOf b0 m ⟨b0, e0, src0⟩], finOf b0 [])
      simpa [segOf, finOf, xs] using sI
    · simp [segOf, mass, slice_length]
  · -- the root is short: alternative-sorted at once (nothing when it is empty)
    let wr := if 0 < e0 - b0 ∧ e0 - b0 < S then altsortK (2 ^ k) hT (m.buf src0) b0 (e0 - b0) else []
    have hk : kStart (2 ^ k) hT S m b0 e0 src0 =
        { mem := m.write 0 wr, stack := [], serr := false, partitions := 0,
          alts := if 0 < e0 - b0 ∧ e0 - b0 < S then 1 else 0, maxDepth := 0, fin := wr } := by
      simp only [kStart, ge_iff_le, hn, ↓reduceIte, wr]
    rw [hk]
    have hs2 : start2 S xs = ([], smallW S ⟨0, xs⟩) := by simp [start2, hxlen, show e0 - b0 < S by omega]
    rw [hs2] at sI
    have spec := altsortSpec (2 ^ k) hT (m.buf src0) b0 (e0 - b0) (fun i hi => hbd _ (by omega) (by omega))
    have wrPerm : (finOf b0 wr).Perm (smallW S ⟨0, xs⟩) := by
      simp only [smallW, hxlen, show e0 - b0 < S by omega, ↓reduceIte]
      by_cases hz : 0 < e0 - b0
      · simp only [wr, hz, show e0 - b0 < S by omega, and_self, ↓reduceIte]
        refine (spec.2.2.map _).trans (List.Perm.of_eq ?_)
        rw [show List.map (fun w : Nat × Nat => (w.fst - b0, w.snd)) = finOf b0 from rfl,
          finOfZip b0 b0 _ (Nat.le_refl _), Nat.sub_self]; rfl
      · simp only [wr, show e0 - b0 = 0 by omega]; rfl
    have wrD : ∀ w ∈ wr, b0 ≤ w.1 ∧ (m.write 0 wr).D w.1 = w.2 := by
      intro w hw
      by_cases hz : 0 < e0 - b0 ∧ e0 - b0 < S
      · have hw' : w ∈ altsortK (2 ^ k) hT (m.buf src0) b0 (e0 - b0) := by simpa [wr, hz] using hw
        have hz' : (w.1, w.2) ∈ (List.range' b0 (xs.mergeSort leB).length).zip (xs.mergeSort leB) := by
          rw [htlen]; exact spec.2.2.subset hw'
        obtain ⟨j, hj, e1, e2⟩ := (memZipRange b0 _ w.1 w.2).1 hz'
        refine ⟨by omega, ?_⟩
        rw [memD, write_buf_same _ _ _ (Or.inl rfl)]
        simp only [wr, hz, and_self, ↓reduceIte]
        rw [spec.1, ifT (by omega), e2]; congr 1; omega
      · simp [wr, hz] at hw
    refine ⟨⟨fun x hx => by simp at hx, ?_, wrD, fun i hi => ?_, fun i _ => ?_, rfl, by simp⟩, by simp [mass]⟩
    · show Inv S _ ([], finOf b0 wr)
      obtain ⟨_, _, hp⟩ := sI
      exact ⟨by simp, by simp [depthOK], (wrPerm.append_right _).trans hp⟩
    · show (m.write 0 wr).D i = m.D i
      rw [memD, write_buf_same _ _ _ (Or.inl rfl), ← memD]
      by_cases hz : 0 < e0 - b0 ∧ e0 - b0 < S
      · simp only [wr, hz, and_self, ↓reduceIte]
        rw [spec.1, ifF (by omega)]
      · simp only [wr, hz, ↓reduceIte]; rfl
    · show (m.write 0 wr).A i = m.A i
      simp only [Mem.write, ↓reduceIte]

/-- **R-13, R-14, K-08, E-10** (T-11, T-12, T-17, T-40): the kernel `lqsort`, as transcribed, sorts
its sequence. For a threadgroup of T = 2^k threads, any minseq ≥ 1 and a stack capacity above
⌊log₂(ℓ/minseq)⌋ + 1 (32 under K-01 and K-04), started on [b0, e0) of either buffer holding 32-bit
codes and run for at least ℓ iterations: the stack is empty and no error is flagged; D holds the
sequence sorted at [b0, e0); every index of [b0, e0) is finalized exactly once (the `GQS_FINALIZE`
events); no index outside [b0, e0) of either buffer changes; and the recorded depth is at most
⌊log₂(ℓ/minseq)⌋ + 1. The kernel's own pushes, pivot, partition and alternative sort are what is
proved here, through their refinement of the spec model's machine. -/
theorem lqsortSpec (k S cap fuel b0 e0 src0 : Nat) (m : Mem) (hS : 0 < S) (hbe : b0 ≤ e0)
    (hsrc : src0 = 0 ∨ src0 = 1) (hbd : ∀ i, b0 ≤ i → i < e0 → m.buf src0 i ≤ 0xFFFFFFFF)
    (hcap : Nat.log2 ((e0 - b0) / S) + 1 < cap) (hfuel : e0 - b0 ≤ fuel) :
    let st := lqsort (2 ^ k) (Nat.two_pow_pos k) S cap fuel m b0 e0 src0
    let xs := slice (m.buf src0) b0 (e0 - b0)
    st.stack = [] ∧ st.serr = false ∧
    (∀ i < e0 - b0, st.mem.D (b0 + i) = (xs.mergeSort leB).getD i 0) ∧
    (st.fin.map Prod.fst).Perm (List.range' b0 (e0 - b0)) ∧
    (∀ i, (i < b0 ∨ e0 ≤ i) → st.mem.D i = m.D i ∧ st.mem.A i = m.A i) ∧
    st.maxDepth ≤ Nat.log2 ((e0 - b0) / S) + 1 := by
  intro st xs
  let tgt := xs.mergeSort leB
  have htlen : tgt.length = e0 - b0 := by simp [tgt, xs, List.length_mergeSort, slice_length]
  have ht : tgt.Pairwise (· ≤ ·) := GpuQuicksortSpec.GpuQuicksort.Theorems.mergeSortSorted xs
  have hbdT : ∀ x ∈ tgt, x ≤ 0xFFFFFFFF := by
    intro x hx
    have := (List.mergeSort_perm xs leB).subset hx
    simp only [xs, slice, List.mem_map, List.mem_range] at this
    obtain ⟨i, hi, rfl⟩ := this; exact hbd _ (by omega) (by omega)
  obtain ⟨h0, hm0⟩ := kStartInv k S b0 e0 src0 m hbe hsrc hbd
  have hcap' : Nat.log2 (tgt.length / S) + 1 < cap := by rw [htlen]; exact hcap
  obtain ⟨hI, hE⟩ := kRunInv k S cap b0 tgt m.D m.A hS ht hbdT hcap' fuel _ h0
  have hempty : st.stack = [] := hE (by omega)
  have hI' : KInv S b0 tgt m.D m.A st := hI
  obtain ⟨_, ⟨_, _, hp⟩, hfinPos, hfD, hfA, hnoErr, hdep⟩ := hI'
  rw [hempty] at hp
  simp only [List.map_nil, owed, List.flatMap_nil, List.append_nil, htlen] at hp
  -- the log, relative to b0, is exactly the pairs (i, tgt[i])
  have hcw : cw tgt 0 (e0 - b0) = (List.range' 0 (e0 - b0)).zip tgt := by
    simp only [cw, List.drop_zero]; rw [← htlen, List.take_length]
  rw [hcw] at hp
  refine ⟨hempty, hnoErr, fun i hi => ?_, ?_, fun i hi => ⟨hfD i (by omega), hfA i (by omega)⟩,
    by rw [← htlen]; exact hdep⟩
  · have hmem : (i, tgt.getD i 0) ∈ finOf b0 st.fin := by
      refine hp.symm.subset ?_
      rw [← htlen]; exact (memZipRange 0 tgt i _).2 ⟨i, by omega, by omega, rfl⟩
    obtain ⟨w, hw, he⟩ := List.mem_map.1 hmem
    simp only [Prod.mk.injEq] at he
    obtain ⟨h1, h2⟩ := hfinPos w hw
    rw [show b0 + i = w.1 by omega, h2, he.2]
  · have hpos := hp.map Prod.fst
    rw [List.map_fst_zip (by simp [htlen])] at hpos
    have e1 : (finOf b0 st.fin).map Prod.fst = (st.fin.map Prod.fst).map (· - b0) := by
      simp [finOf, List.map_map, Function.comp_def]
    rw [e1] at hpos
    have hge : ∀ x ∈ st.fin.map Prod.fst, b0 ≤ x := by
      intro x hx; obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hx; exact (hfinPos w hw).1
    have := hpos.map (b0 + ·)
    rw [List.map_map] at this
    rw [show ((fun x => b0 + x) ∘ fun x => x - b0) = fun x => b0 + (x - b0) from rfl] at this
    rw [List.map_congr_left (fun x hx => show b0 + (x - b0) = x by have := hge x hx; omega), List.map_id',
      List.range'_eq_map_range, List.map_map] at this
    rw [List.range'_eq_map_range]
    simpa [Function.comp_def] using this

end GpuQuicksort.Theorems
