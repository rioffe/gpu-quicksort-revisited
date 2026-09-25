import GpuQuicksortProof.GpuQuicksort.Spec
import GpuQuicksortProof.GpuQuicksort.Model.Sorter
import GpuQuicksortProof.GpuQuicksort.Theorems.Codec
import GpuQuicksortProof.GpuQuicksort.Theorems.GQSort
import GpuQuicksortProof.GpuQuicksort.Theorems.LQSort

/-!
# GpuQuicksortProof.GpuQuicksort.Theorems.Sorter
================================================

The whole sort as the host runs it: phase one's loop over the proven dispatches, phase two's
`lqsort` threadgroups, and the codec, composed. For every choice of atomic modification orders,
`run` leaves the caller's keys sorted (in the C-04 order), finalizing every index exactly once.
-/

namespace GpuQuicksort.Theorems

open GpuQuicksort.Model
open GpuQuicksortSpec.GpuQuicksort.Model (lowerPart upperPart leB)
open GpuQuicksortSpec.GpuQuicksort.PhaseTwo (cw Seg lowerSeg upperSeg gapW segSplit)

/-! ## The host's block layout (K-06) -/

theorem ceilStep (x bs : Nat) (h : 0 < bs) (hx : bs < x) : (x + bs - 1) / bs = (x - bs + bs - 1) / bs + 1 := by
  rw [show x + bs - 1 = (x - bs + bs - 1) + bs by omega, Nat.add_div_right _ h]

theorem range'Split (b m e : Nat) (h1 : b ≤ m) (h2 : m ≤ e) :
    List.range' b (m - b) ++ List.range' m (e - m) = List.range' b (e - b) := by
  have := List.range'_append_1 (s := b) (m := m - b) (n := e - m)
  rw [show b + (m - b) = m by omega, show m - b + (e - m) = e - b by omega] at this; exact this

theorem blocksOfTile (bs : Nat) (hbs : 0 < bs) (j e : Nat) :
    ∀ b, b ≤ e → (blocksOf bs hbs j e b).flatMap (fun bk => List.range' bk.begin (bk.end_ - bk.begin)) =
      List.range' b (e - b) := by
  intro b
  induction b using blocksOf.induct bs hbs e with
  | case1 b hb ih =>
    intro _
    rw [blocksOf]; simp only [hb, ↓reduceIte, List.flatMap_cons]
    rw [ih (by omega)]; exact range'Split _ _ _ (by omega) (by omega)
  | case2 b hb =>
    intro _
    rw [blocksOf]; simp only [hb, ↓reduceIte, List.flatMap_nil]
    rw [show e - b = 0 by omega]; rfl

theorem blocksOfSeq (bs : Nat) (hbs : 0 < bs) (j e : Nat) : ∀ b, ∀ bk ∈ blocksOf bs hbs j e b, bk.seq = j := by
  intro b
  induction b using blocksOf.induct bs hbs e with
  | case1 b hb ih =>
    intro bk hbk; rw [blocksOf] at hbk; simp only [hb, ↓reduceIte, List.mem_cons] at hbk
    rcases hbk with rfl | h
    · rfl
    · exact ih bk h
  | case2 b hb => intro bk hbk; rw [blocksOf] at hbk; simp [hb] at hbk

/-- **(lemma)** (K-06): block q of a sequence starts at begin + q·bs; the blocks carry the numbers
0 … ⌈ℓ/bs⌉ − 1. -/
theorem blocksOfNums (bs : Nat) (hbs : 0 < bs) (j e b0 : Nat) :
    ∀ n q, e - (b0 + q * bs) ≤ n → b0 + q * bs ≤ e →
      (blocksOf bs hbs j e (b0 + q * bs)).map (fun bk => (bk.begin - b0) / bs) =
        List.range' q ((e - (b0 + q * bs) + bs - 1) / bs)
  | 0, q, hn, _ => by
    rw [blocksOf]; simp only [show ¬ b0 + q * bs < e by omega, ↓reduceIte, List.map_nil]
    rw [show e - (b0 + q * bs) = 0 by omega, Nat.zero_add, Nat.div_eq_of_lt (by omega)]; rfl
  | n + 1, q, hn, hle => by
    by_cases hb : b0 + q * bs < e
    · rw [blocksOf]; simp only [hb, ↓reduceIte, List.map_cons]
      have hq : (b0 + q * bs - b0) / bs = q := by
        rw [show b0 + q * bs - b0 = q * bs by omega, Nat.mul_div_cancel _ hbs]
      rw [hq]
      have hs : (q + 1) * bs = q * bs + bs := Nat.succ_mul q bs
      by_cases hlt : b0 + q * bs + bs < e
      · have e1 : min (b0 + q * bs + bs) e = b0 + (q + 1) * bs := by
          rw [Nat.min_eq_left (by omega), hs]; omega
        rw [e1, blocksOfNums bs hbs j e b0 n (q + 1) (by rw [hs]; omega) (by rw [hs]; omega),
          ceilStep (e - (b0 + q * bs)) _ hbs (by omega), List.range'_succ, hs,
          show e - (b0 + q * bs) - bs = e - (b0 + (q * bs + bs)) by omega]
      · have hm : min (b0 + q * bs + bs) e = e := Nat.min_eq_right (by omega)
        rw [hm, blocksOf]; simp only [Nat.lt_irrefl, ↓reduceIte, List.map_nil]
        have : (e - (b0 + q * bs) + bs - 1) / bs = 1 :=
          Nat.div_eq_of_lt_le (by omega) (by omega)
        rw [this]; rfl
    · rw [blocksOf]; simp only [hb, ↓reduceIte, List.map_nil]
      rw [show e - (b0 + q * bs) = 0 by omega, Nat.zero_add, Nat.div_eq_of_lt (by omega)]; rfl

/-- **(lemma)**: the indices of the blocks with a given `seq`, read back, are exactly those blocks. -/
theorem mineRead (l : List Blk) (j : Nat) : (mineOf l j).map (fun i => l.getD i dB) = l.filter fun bk => decide (bk.seq = j) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [mineOf, List.length_cons, List.range_succ_eq_map, List.filter_cons, List.getD_cons_zero,
      List.filter_map] at ih ⊢
    split
    · simp only [List.map_cons, List.getD_cons_zero, List.map_map]
      congr 1
    · simp only [List.map_map]; exact ih

/-! ## Records and blocks of one iteration -/

def dW : SeqD × Nat := (⟨0, 0, 0⟩, 0)

theorem mkRecsLen (work : List (SeqD × Nat)) : (mkRecs work).length = work.length := by simp [mkRecs]

theorem mkRecsGet (work : List (SeqD × Nat)) (j : Nat) (hj : j < work.length) :
    (mkRecs work).getD j dR = ⟨(work.getD j dW).1.begin, (work.getD j dW).1.end_, (work.getD j dW).1.begin,
      (work.getD j dW).1.end_, (work.getD j dW).2, (work.getD j dW).1.src, 0xFFFFFFFF, 0, 0xFFFFFFFF, 0⟩ := by
  simp [mkRecs, List.getD_eq_getElem?_getD, hj]

theorem flatMapSingle {β : Type} (W j : Nat) (hj : j < W) (X : List β) :
    (List.range W).flatMap (fun j' => if j' = j then X else []) = X := by
  induction W with
  | zero => omega
  | succ W ih =>
    rw [List.range_succ, List.flatMap_append]
    by_cases h : j < W
    · rw [ih h]; simp [show W ≠ j by omega]
    · have : j = W := by omega
      subst this
      have hz : (List.range j).flatMap (fun j' => if j' = j then X else []) = [] := by
        rw [List.flatMap_eq_nil_iff]; intro a ha; rw [List.mem_range] at ha; simp [show a ≠ j by omega]
      simp [hz]

theorem mkBlocksFilter (bs : Nat) (hbs : 0 < bs) (work : List (SeqD × Nat)) (j : Nat) (hj : j < work.length) :
    (mkBlocks bs hbs work).filter (fun bk => decide (bk.seq = j)) =
      blocksOf bs hbs j (work.getD j dW).1.end_ (work.getD j dW).1.begin := by
  simp only [mkBlocks, List.filter_flatMap]
  rw [show (fun j' => (blocksOf bs hbs j' (work.getD j' (⟨0, 0, 0⟩, 0)).1.end_ (work.getD j' (⟨0, 0, 0⟩, 0)).1.begin).filter
      fun bk => decide (bk.seq = j)) = fun j' => if j' = j then blocksOf bs hbs j (work.getD j dW).1.end_ (work.getD j dW).1.begin else [] by
    funext j'
    by_cases h : j' = j
    · subst h; simp only [↓reduceIte]
      exact List.filter_eq_self.2 (fun bk hbk => by simp [blocksOfSeq bs hbs j' _ _ bk hbk])
    · simp only [h, ↓reduceIte]
      rw [List.filter_eq_nil_iff]; intro bk hbk; simp [blocksOfSeq bs hbs j' _ _ bk hbk, h]]
  exact flatMapSingle _ _ hj _

theorem mkBlocksSeq (bs : Nat) (hbs : 0 < bs) (work : List (SeqD × Nat)) :
    ∀ i < (mkBlocks bs hbs work).length, ((mkBlocks bs hbs work).getD i dB).seq < work.length := by
  intro i hi
  have hmem : (mkBlocks bs hbs work).getD i dB ∈ mkBlocks bs hbs work := by
    simp [List.getD_eq_getElem?_getD, hi]
  simp only [mkBlocks, List.mem_flatMap, List.mem_range] at hmem
  obtain ⟨j, hj, hbk⟩ := hmem
  have := blocksOfSeq bs hbs j _ _ _ hbk
  rw [show ((mkBlocks bs hbs work).getD i dB).seq = j from this]; exact hj

/-- The oracle's orders are modification orders: for every block layout and record, each is an
order of exactly that record's blocks. -/
def ValidOrders (ords : Nat → Orders) : Prop :=
  ∀ it (blks : List Blk) j, ((ords it blks).1 j).Perm (mineOf blks j) ∧ ((ords it blks).2 j).Perm (mineOf blks j)

/-- **(lemma)** (K-06): the host's records and blocks meet the partition dispatch's preconditions. -/
theorem hostDispatchPre (bs : Nat) (hbs : 0 < bs) (work : List (SeqD × Nat)) (o : Orders)
    (ho : ∀ j, ((o (mkBlocks bs hbs work)).1 j).Perm (mineOf (mkBlocks bs hbs work) j) ∧
      ((o (mkBlocks bs hbs work)).2 j).Perm (mineOf (mkBlocks bs hbs work) j))
    (hwf : ∀ w ∈ work, w.1.begin ≤ w.1.end_ ∧ (w.1.src = 0 ∨ w.1.src = 1))
    (hdisj : ∀ j j', j < work.length → j' < work.length → j ≠ j' →
      (work.getD j dW).1.end_ ≤ (work.getD j' dW).1.begin ∨ (work.getD j' dW).1.end_ ≤ (work.getD j dW).1.begin) :
    DispatchPre (mkRecs work) (mkBlocks bs hbs work) (o (mkBlocks bs hbs work)).1 (o (mkBlocks bs hbs work)).2 := by
  have wmem : ∀ j < work.length, work.getD j dW ∈ work := fun j hj => by
    simp [List.getD_eq_getElem?_getD, hj]
  refine ⟨fun j hj => ?_, fun i hi => ?_, fun j hj => ?_, fun j _ => ho j, fun j j' hj hj' hne => ?_⟩
  · rw [mkRecsLen] at hj; rw [mkRecsGet work j hj]
    exact ⟨rfl, rfl, (hwf _ (wmem j hj)).1, (hwf _ (wmem j hj)).2⟩
  · rw [mkRecsLen]; exact mkBlocksSeq bs hbs work i hi
  · rw [mkRecsLen] at hj; rw [mkRecsGet work j hj]
    rw [show ((mineOf (mkBlocks bs hbs work) j).flatMap fun i => List.range' ((mkBlocks bs hbs work).getD i dB).begin
        (((mkBlocks bs hbs work).getD i dB).end_ - ((mkBlocks bs hbs work).getD i dB).begin)) =
        ((mineOf (mkBlocks bs hbs work) j).map fun i => (mkBlocks bs hbs work).getD i dB).flatMap
          fun bk => List.range' bk.begin (bk.end_ - bk.begin) by rw [List.flatMap_map],
      mineRead, mkBlocksFilter bs hbs work j hj, blocksOfTile bs hbs j _ _ (hwf _ (wmem j hj)).1]
  · rw [mkRecsLen] at hj hj'; rw [mkRecsGet work j hj, mkRecsGet work j' hj']
    exact hdisj j j' hj hj' hne

/-! ## The phase-one invariant -/

open GpuQuicksortSpec.GpuQuicksort.PhaseTwo (owed)
open GpuQuicksortSpec.GpuQuicksort.Pipeline (win)

/-- The spec-model segment a host sequence stands for. -/
def segD (mem : Mem) (s : SeqD) : Seg := ⟨s.begin, slice (mem.buf s.src) s.begin (s.end_ - s.begin)⟩

/-- Every sequence the host holds: `work` then `done`. -/
def seqsOf (st : P1) : List SeqD := st.work.map (·.1) ++ st.done

/-- The phase-one invariant, for the sorted target `tgt` of the n codes. -/
structure CInv (tgt : List Nat) (D0 A0 : Nat → Nat) (st : P1) : Prop where
  wf : ∀ s ∈ seqsOf st, s.begin < s.end_ ∧ (s.src = 0 ∨ s.src = 1)
  win : ∀ s ∈ seqsOf st, win tgt (segD st.mem s)
  perm : (st.fills ++ owed tgt ((seqsOf st).map (segD st.mem))).Perm (cw tgt 0 tgt.length)
  fillsD : ∀ w ∈ st.fills, st.mem.D w.1 = w.2
  frameD : ∀ i, tgt.length ≤ i → st.mem.D i = D0 i
  frameA : ∀ i, tgt.length ≤ i → st.mem.A i = A0 i

theorem cwPosS (tgt : List Nat) (g : Seg) (h : g.b + g.xs.length ≤ tgt.length) :
    (cw tgt g.b g.xs.length).map Prod.fst = List.range' g.b g.xs.length := cwPos tgt g.b _ h

/-- **(lemma)**: under the invariant, distinct sequences occupy disjoint ranges, and no fill lies
inside any sequence. -/
theorem cinvDisjoint (tgt : List Nat) (D0 A0 : Nat → Nat) (st : P1) (h : CInv tgt D0 A0 st) :
    (seqsOf st).Pairwise (fun s s' => s.end_ ≤ s'.begin ∨ s'.end_ ≤ s.begin) ∧
    ∀ w ∈ st.fills, ∀ s ∈ seqsOf st, w.1 < s.begin ∨ s.end_ ≤ w.1 := by
  have hnd : ((st.fills ++ owed tgt ((seqsOf st).map (segD st.mem))).map Prod.fst).Nodup := by
    have := h.perm.map Prod.fst
    rw [cwPos tgt 0 _ (by omega)] at this
    exact this.nodup_iff.2 List.nodup_range'
  rw [List.map_append, List.nodup_append] at hnd
  obtain ⟨_, hnd2, hdisj⟩ := hnd
  have posOf : ∀ s ∈ seqsOf st, ∀ x, s.begin ≤ x → x < s.end_ →
      x ∈ (owed tgt ((seqsOf st).map (segD st.mem))).map Prod.fst := by
    intro s hs x h1 h2
    simp only [owed, List.map_flatMap, List.mem_flatMap, List.mem_map]
    refine ⟨segD st.mem s, ⟨s, hs, rfl⟩, ?_⟩
    have hw := h.win s hs
    have hm : x ∈ (cw tgt (segD st.mem s).b (segD st.mem s).xs.length).map Prod.fst := by
      rw [cwPosS tgt _ hw.2]; simp only [segD, slice_length]; exact List.mem_range'_1.2 ⟨h1, by omega⟩
    exact List.mem_map.1 hm
  constructor
  · -- pairwise: by induction on the list, using the nodup of the owed positions
    have key : ∀ (l : List SeqD), (∀ s ∈ l, s.begin < s.end_ ∧ win tgt (segD st.mem s)) →
        ((owed tgt (l.map (segD st.mem))).map Prod.fst).Nodup →
        l.Pairwise (fun s s' => s.end_ ≤ s'.begin ∨ s'.end_ ≤ s.begin) := by
      intro l
      induction l with
      | nil => intros; exact List.Pairwise.nil
      | cons s l ih =>
        intro hall hnd
        simp only [List.map_cons, owed, List.flatMap_cons, List.map_append, List.nodup_append] at hnd
        obtain ⟨_, hnd2, hdj⟩ := hnd
        refine List.Pairwise.cons (fun s' hs' => ?_) (ih (fun s' hs' => hall s' (List.mem_cons_of_mem _ hs')) hnd2)
        obtain ⟨hs1, hs2⟩ := hall s List.mem_cons_self
        obtain ⟨hs1', hs2'⟩ := hall s' (List.mem_cons_of_mem _ hs')
        by_cases hc : s.end_ ≤ s'.begin ∨ s'.end_ ≤ s.begin
        · exact hc
        · exfalso
          let x := max s.begin s'.begin
          have ha : x ∈ (cw tgt (segD st.mem s).b (segD st.mem s).xs.length).map Prod.fst := by
            rw [cwPosS tgt _ hs2.2]; simp only [segD, slice_length]
            exact List.mem_range'_1.2 ⟨by omega, by omega⟩
          have hb : x ∈ (owed tgt (l.map (segD st.mem))).map Prod.fst := by
            simp only [owed, List.map_flatMap, List.mem_flatMap, List.mem_map]
            refine ⟨segD st.mem s', ⟨s', hs', rfl⟩, ?_⟩
            have hm : x ∈ (cw tgt (segD st.mem s').b (segD st.mem s').xs.length).map Prod.fst := by
              rw [cwPosS tgt _ hs2'.2]; simp only [segD, slice_length]
              exact List.mem_range'_1.2 ⟨by omega, by omega⟩
            exact List.mem_map.1 hm
          exact hdj x ha x (by simpa [owed, List.map_flatMap] using hb) rfl
    exact key _ (fun s hs => ⟨(h.wf s hs).1, h.win s hs⟩) hnd2
  · intro w hw s hs
    by_cases hc : w.1 < s.begin ∨ s.end_ ≤ w.1
    · exact hc
    · exfalso
      exact hdisj w.1 (List.mem_map.2 ⟨w, hw, rfl⟩) w.1 (posOf s hs w.1 (by omega) (by omega)) rfl

end GpuQuicksort.Theorems
