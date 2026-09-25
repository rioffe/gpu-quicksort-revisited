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

/-! ## One phase-one iteration -/

/-- The non-empty children of a record, as sequences. -/
def childSeqs (r : Rec) : List SeqD :=
  ([⟨r.start, r.lnext, 1 - r.src⟩, ⟨r.gnext, r.end_, 1 - r.src⟩] : List SeqD).filter fun c => decide (c.begin < c.end_)

theorem childrenSeqs (minMax : Bool) (minlength : Nat) (mem : Mem) (r : Rec) :
    (childrenOf minMax minlength mem r).map (·.1) = childSeqs r := by
  simp only [childrenOf, childSeqs, List.map_map]
  by_cases h1 : r.start < r.lnext <;> by_cases h2 : r.gnext < r.end_ <;>
    simp [h1, h2, Function.comp_def]

theorem cwZero (tgt : List Nat) (b : Nat) : cw tgt b 0 = [] := by simp [cw]

theorem owedChild (tgt : List Nat) (mem : Mem) (r : Rec) (h1 : r.start ≤ r.lnext) (h2 : r.gnext ≤ r.end_) :
    owed tgt ((childSeqs r).map (segD mem)) = cw tgt r.start (r.lnext - r.start) ++ cw tgt r.gnext (r.end_ - r.gnext) := by
  simp only [childSeqs]
  by_cases c1 : r.start < r.lnext <;> by_cases c2 : r.gnext < r.end_ <;>
    simp [c1, c2, owed, segD, slice_length] <;>
    first
      | rfl
      | exact cwZero _ _
      | (rw [show r.end_ - r.gnext = 0 by omega]; exact cwZero _ _)
      | (rw [show r.lnext - r.start = 0 by omega]; exact cwZero _ _)
      | (rw [show r.lnext - r.start = 0 by omega, show r.end_ - r.gnext = 0 by omega, cwZero, cwZero]; exact ⟨rfl, rfl⟩)

theorem partitionLen (T : Nat) (hT : 0 < T) (minMax : Bool) (mem : Mem) (recs : List Rec) (blks : List Blk)
    (oL oG : Nat → List Nat) : (partitionDispatch T hT minMax mem recs blks oL oG).2.length = recs.length := by
  simp [partitionDispatch]

theorem getDMem' {α : Type} (l : List α) (j : Nat) (d : α) (hj : j < l.length) : l.getD j d ∈ l := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]; exact List.getElem_mem hj

theorem getDMap {α β : Type} (l : List α) (f : α → β) (j : Nat) (d : α) (hj : j < l.length) :
    (l.map f).getD j (f d) = f (l.getD j d) := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]

theorem pairwiseIdx {α : Type} (R : α → α → Prop) (hsym : ∀ a b, R a b → R b a) (l : List α) (d : α)
    (h : l.Pairwise R) : ∀ i j, i < l.length → j < l.length → i ≠ j → R (l.getD i d) (l.getD j d) := by
  intro i j hi hj hne
  rw [List.pairwise_iff_getElem] at h
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hj, Option.getD_some]
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · exact h i j hi hj hlt
  · exact hsym _ _ (h j i hj hi hlt)

set_option maxHeartbeats 20000000 in
/-- **(lemma)** (R-08, R-10, E-10, E-17, O-2): one phase-one iteration of the host keeps the
invariant: the read-back guard passes, the fills are the gaps, and each child holds its window. -/
theorem p1BodyInv (k m minlength : Nat) (minMax : Bool) (o : Orders)
    (ho : ∀ blks j, ((o blks).1 j).Perm (mineOf blks j) ∧ ((o blks).2 j).Perm (mineOf blks j))
    (tgt : List Nat) (ht : tgt.Pairwise (· ≤ ·)) (D0 A0 : Nat → Nat) (st : P1) (h : CInv tgt D0 A0 st) :
    ∃ st', p1Body (2 ^ k) (Nat.two_pow_pos k) m minlength minMax o st = some st' ∧ CInv tgt D0 A0 st' ∧
      st'.iteration = st.iteration + 1 ∧ st'.capReached = st.capReached := by
  have hT := Nat.two_pow_pos k
  let work := st.work
  let W := work.length
  let total := (work.map fun w => w.1.end_ - w.1.begin).sum
  let bs := max (2 ^ k) ((total + m - 1) / m)
  have hbs : 0 < bs := Nat.lt_of_lt_of_le hT (Nat.le_max_left _ _)
  let recs := mkRecs work
  let blks := mkBlocks bs hbs work
  have hrecsLen : recs.length = W := mkRecsLen work
  have wmem : ∀ j < W, (work.getD j dW).1 ∈ seqsOf st := fun j hj => by
    simp only [seqsOf, List.mem_append, List.mem_map]
    exact Or.inl ⟨work.getD j dW, getDMem' work j dW hj, rfl⟩
  have hwf : ∀ w ∈ work, w.1.begin ≤ w.1.end_ ∧ (w.1.src = 0 ∨ w.1.src = 1) := fun w hw => by
    have := h.wf w.1 (by simp only [seqsOf, List.mem_append, List.mem_map]; exact Or.inl ⟨w, hw, rfl⟩)
    exact ⟨Nat.le_of_lt this.1, this.2⟩
  obtain ⟨hpw, hfillOut⟩ := cinvDisjoint tgt D0 A0 st h
  have hpwWork : (work.map (·.1)).Pairwise (fun s s' => s.end_ ≤ s'.begin ∨ s'.end_ ≤ s.begin) :=
    (List.pairwise_append.1 hpw).1
  have hdisj : ∀ j j', j < W → j' < W → j ≠ j' →
      (work.getD j dW).1.end_ ≤ (work.getD j' dW).1.begin ∨ (work.getD j' dW).1.end_ ≤ (work.getD j dW).1.begin := by
    intro j j' hj hj' hne
    have := pairwiseIdx _ (fun a b h => h.symm) (work.map (·.1)) (dW.1) hpwWork j j' (by simp; exact hj)
      (by simp; exact hj') hne
    rwa [getDMap work (·.1) j dW hj, getDMap work (·.1) j' dW hj'] at this
  have pre := hostDispatchPre bs hbs work o (ho blks) hwf hdisj
  obtain ⟨PDr, PDg⟩ := partitionDispatchSpec k minMax st.mem recs blks (o blks).1 (o blks).2 pre
  let pd := partitionDispatch (2 ^ k) hT minMax st.mem recs blks (o blks).1 (o blks).2
  have hpdLen : pd.2.length = W := by rw [partitionLen, hrecsLen]
  -- per record, in the host's terms
  let gOf := fun j => segD st.mem (work.getD j dW).1
  let pOf := fun j => (work.getD j dW).2
  have recFacts : ∀ j < W,
      let r' := pd.2.getD j dR
      let g := gOf j
      let L := (lowerPart (pOf j) g.xs).length
      let G := (upperPart (pOf j) g.xs).length
      r'.start = g.b ∧ r'.end_ = g.b + g.xs.length ∧ r'.lnext = g.b + L ∧ r'.gnext = g.b + g.xs.length - G ∧
      r'.pivot = pOf j ∧ r'.src = (work.getD j dW).1.src ∧ L + g.xs.count (pOf j) + G = g.xs.length ∧
      (slice (pd.1.buf (1 - r'.src)) r'.start L).Perm (lowerPart (pOf j) g.xs) ∧
      (slice (pd.1.buf (1 - r'.src)) (r'.end_ - G) G).Perm (upperPart (pOf j) g.xs) := by
    intro j hj r' g L G
    have hj' : j < recs.length := by rw [hrecsLen]; exact hj
    obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, _, _⟩ := PDr j hj'
    have hrj : recs.getD j dR = ⟨(work.getD j dW).1.begin, (work.getD j dW).1.end_, (work.getD j dW).1.begin,
      (work.getD j dW).1.end_, (work.getD j dW).2, (work.getD j dW).1.src, 0xFFFFFFFF, 0, 0xFFFFFFFF, 0⟩ :=
      mkRecsGet work j hj
    have hbe := (hwf _ (getDMem' work j dW hj)).1
    have hlen : g.xs.length = (work.getD j dW).1.end_ - (work.getD j dW).1.begin := slice_length _ _ _
    have hgb : g.b = (work.getD j dW).1.begin := rfl
    have hLd : L = (lowerPart (work.getD j dW).2 (slice (st.mem.buf (work.getD j dW).1.src) (work.getD j dW).1.begin
      ((work.getD j dW).1.end_ - (work.getD j dW).1.begin))).length := rfl
    have hGd : G = (upperPart (work.getD j dW).2 (slice (st.mem.buf (work.getD j dW).1.src) (work.getD j dW).1.begin
      ((work.getD j dW).1.end_ - (work.getD j dW).1.begin))).length := rfl
    rw [hrj] at a1 a2 a3 a4 a5 a6 a7 a8 a9
    dsimp only at a1 a2 a3 a4 a5 a6 a7 a8 a9
    refine ⟨a3, by rw [a4, hlen]; omega, a1, by rw [a2, hlen]; omega, a5, a6, by rw [hlen]; exact a7, ?_, ?_⟩
    · show (slice (pd.1.buf (1 - r'.src)) r'.start L).Perm _
      rw [a6, a3]; exact a8
    · show (slice (pd.1.buf (1 - r'.src)) (r'.end_ - G) G).Perm _
      rw [a6, a4]; exact a9
  have fpre : FillPre pd.2 blks bs := by
    refine ⟨hbs, fun j hj => ?_, fun i hi => ?_, fun j hj => ?_, fun j j' hj hj' hne => ?_⟩
    · rw [hpdLen] at hj
      obtain ⟨a1, a2, a3, a4, _, _, a7, _, _⟩ := recFacts j hj
      rw [a1, a3, a4, a2]; omega
    · rw [hpdLen]; exact mkBlocksSeq bs hbs work i hi
    · rw [hpdLen] at hj
      obtain ⟨a1, a2, _, _, _, _, _, _, _⟩ := recFacts j hj
      have hbe := (hwf _ (getDMem' work j dW hj)).1
      have hlen : (gOf j).xs.length = (work.getD j dW).1.end_ - (work.getD j dW).1.begin := slice_length _ _ _
      have e1 : (pd.2.getD j dR).start = (work.getD j dW).1.begin := a1
      have e2 : (pd.2.getD j dR).end_ = (work.getD j dW).1.end_ := by rw [a2, hlen]; show _ + _ = _; omega
      rw [e1, e2]
      rw [show ((mineOf blks j).map fun i => ((blks.getD i dB).begin - (work.getD j dW).1.begin) / bs) =
          ((mineOf blks j).map fun i => blks.getD i dB).map (fun bk => (bk.begin - (work.getD j dW).1.begin) / bs) by
        rw [List.map_map]; rfl, mineRead, mkBlocksFilter bs hbs work j hj]
      have := blocksOfNums bs hbs j (work.getD j dW).1.end_ (work.getD j dW).1.begin
        ((work.getD j dW).1.end_ - (work.getD j dW).1.begin) 0 (by omega) (by omega)
      simp only [Nat.zero_mul, Nat.add_zero] at this
      rw [this, List.range_eq_range']
    · rw [hpdLen] at hj hj'
      obtain ⟨a1, a2, _, _, _, _, _, _, _⟩ := recFacts j hj
      obtain ⟨b1, b2, _, _, _, _, _, _, _⟩ := recFacts j' hj'
      have hlen : (gOf j).xs.length = (work.getD j dW).1.end_ - (work.getD j dW).1.begin := slice_length _ _ _
      have hlen' : (gOf j').xs.length = (work.getD j' dW).1.end_ - (work.getD j' dW).1.begin := slice_length _ _ _
      have hbe := (hwf _ (getDMem' work j dW hj)).1
      have hbe' := (hwf _ (getDMem' work j' dW hj')).1
      have e1 : (pd.2.getD j dR).start = (work.getD j dW).1.begin := a1
      have e2 : (pd.2.getD j dR).end_ = (work.getD j dW).1.end_ := by rw [a2, hlen]; show _ + _ = _; omega
      have e1' : (pd.2.getD j' dR).start = (work.getD j' dW).1.begin := b1
      have e2' : (pd.2.getD j' dR).end_ = (work.getD j' dW).1.end_ := by rw [b2, hlen']; show _ + _ = _; omega
      rw [e1, e2, e1', e2']; exact hdisj j j' hj hj' hne
  obtain ⟨FDg, FDout, FDa, FDpos, FDval⟩ := fillDispatchSpec k bs pd.1 pd.2 blks fpre
  let fd := fillDispatch (2 ^ k) hT bs pd.1 pd.2 blks
  have hguard : (pd.2.all fun r => decide (r.start ≤ r.lnext ∧ r.lnext ≤ r.gnext ∧ r.gnext ≤ r.end_)) = true := by
    rw [List.all_eq_true]; intro r hr
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hr
    have hj' : j < W := by rw [← hpdLen]; exact hj
    have := fpre.gap j hj
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some] at this
    simpa using this
  let kids := pd.2.flatMap (childrenOf minMax minlength fd.1)
  have hbody : p1Body (2 ^ k) hT m minlength minMax o st =
      some { mem := fd.1, work := (kids.filter fun c => !c.2.2).map fun c => (c.1, c.2.1),
             done := st.done ++ (kids.filter fun c => c.2.2).map fun c => c.1,
             iteration := st.iteration + 1, capReached := st.capReached, fills := st.fills ++ fd.2 } := by
    show (if (pd.2.all fun r => decide (r.start ≤ r.lnext ∧ r.lnext ≤ r.gnext ∧ r.gnext ≤ r.end_)) then _ else none) = _
    rw [ifT hguard]
  refine ⟨_, hbody, ?_, rfl, rfl⟩
  -- the sequences after the iteration
  let cws := fun j => childSeqs (pd.2.getD j dR)
  have hkidsSeqs : kids.map (·.1) = (List.range W).flatMap cws := by
    simp only [kids, List.map_flatMap, childrenSeqs]
    rw [flatMapIdx dR childSeqs pd.2, hpdLen]
  have hseqs : (seqsOf ⟨fd.1, (kids.filter fun c => !c.2.2).map (fun c => (c.1, c.2.1)),
      st.done ++ (kids.filter fun c => c.2.2).map (fun c => c.1), st.iteration + 1, st.capReached,
      st.fills ++ fd.2⟩).Perm (st.done ++ (List.range W).flatMap cws) := by
    simp only [seqsOf, List.map_map]
    rw [← hkidsSeqs]
    have e1 : ((kids.filter fun c => !c.2.2).map ((·.1) ∘ fun c => (c.1, c.2.1))) = (kids.filter fun c => !c.2.2).map (·.1) := by
      apply List.map_congr_left; intro c _; rfl
    rw [e1]
    have e2 := (List.filter_append_perm (fun c : SeqD × Nat × Bool => !c.2.2) kids).map (·.1)
    simp only [Bool.not_not, List.map_append] at e2
    refine List.perm_append_comm.trans ?_
    rw [List.append_assoc]
    exact List.Perm.append_left _ (List.perm_append_comm.trans e2)
  -- where the records, gaps and children are
  have recRange : ∀ j < W, ∀ x, (pd.2.getD j dR).start ≤ x → x < (pd.2.getD j dR).end_ →
      (work.getD j dW).1.begin ≤ x ∧ x < (work.getD j dW).1.end_ := by
    intro j hj x h1 h2
    obtain ⟨a1, a2, _, _, _, _, _, _, _⟩ := recFacts j hj
    have hlen : (gOf j).xs.length = (work.getD j dW).1.end_ - (work.getD j dW).1.begin := slice_length _ _ _
    have hbe := (hwf _ (getDMem' work j dW hj)).1
    have e1 : (pd.2.getD j dR).start = (work.getD j dW).1.begin := a1
    have e2 : (pd.2.getD j dR).end_ = (work.getD j dW).1.end_ := by rw [a2, hlen]; show _ + _ = _; omega
    rw [e1] at h1; rw [e2] at h2; exact ⟨h1, h2⟩
  have gapIn : ∀ j < W, ∀ x, (pd.2.getD j dR).lnext ≤ x → x < (pd.2.getD j dR).gnext →
      (pd.2.getD j dR).start ≤ x ∧ x < (pd.2.getD j dR).end_ := by
    intro j hj x h1 h2
    have := fpre.gap j (by rw [hpdLen]; exact hj); omega
  -- outside every work sequence, nothing changed
  have outside : ∀ sb, (sb = 0 ∨ sb = 1) → ∀ x, (∀ j < W, x < (work.getD j dW).1.begin ∨ (work.getD j dW).1.end_ ≤ x) →
      fd.1.buf sb x = st.mem.buf sb x := by
    intro sb hsb x hx
    have hpdx : pd.1.buf sb x = st.mem.buf sb x := PDg sb x hsb (fun j hj => by
      rw [hrecsLen] at hj; rw [mkRecsGet work j hj]; exact hx j hj)
    rcases hsb with rfl | rfl
    · rw [← memD, ← memD, FDout x (fun j hj => by
        rw [hpdLen] at hj
        by_cases hc : x < (pd.2.getD j dR).lnext ∨ (pd.2.getD j dR).gnext ≤ x
        · exact hc
        · exfalso; have := gapIn j hj x (by omega) (by omega); have := recRange j hj x this.1 this.2
          rcases hx j hj with h | h <;> omega)]
      rw [memD, memD]; exact hpdx
    · show fd.1.A x = st.mem.A x
      rw [FDa]; exact hpdx
  -- inside a record but outside its gap, the fill changed nothing
  have notGap : ∀ j < W, ∀ sb, (sb = 0 ∨ sb = 1) → ∀ x, (pd.2.getD j dR).start ≤ x → x < (pd.2.getD j dR).end_ →
      (x < (pd.2.getD j dR).lnext ∨ (pd.2.getD j dR).gnext ≤ x) → fd.1.buf sb x = pd.1.buf sb x := by
    intro j hj sb hsb x h1 h2 h3
    rcases hsb with rfl | rfl
    · rw [← memD, ← memD, FDout x (fun j' hj' => ?_)]
      rw [hpdLen] at hj'
      by_cases hjj : j' = j
      · subst hjj; exact h3
      · by_cases hc : x < (pd.2.getD j' dR).lnext ∨ (pd.2.getD j' dR).gnext ≤ x
        · exact hc
        · exfalso
          have a := gapIn j' hj' x (by omega) (by omega)
          have b := recRange j' hj' x a.1 a.2
          have c := recRange j hj x h1 h2
          rcases hdisj j j' hj hj' (Ne.symm hjj) with d | d <;> omega
    · show fd.1.A x = pd.1.A x; rw [FDa]
  -- the owed writes of a record's children
  have owedKids : ∀ j < W, owed tgt ((cws j).map (segD fd.1)) =
      cw tgt (gOf j).b (lowerPart (pOf j) (gOf j).xs).length ++
      cw tgt ((gOf j).b + (gOf j).xs.length - (upperPart (pOf j) (gOf j).xs).length) (upperPart (pOf j) (gOf j).xs).length := by
    intro j hj
    obtain ⟨a1, a2, a3, a4, _, _, a7, _, _⟩ := recFacts j hj
    have g := fpre.gap j (by rw [hpdLen]; exact hj)
    rw [owedChild tgt fd.1 _ g.1 g.2.2]
    have hlo : (pd.2.getD j dR).lnext - (pd.2.getD j dR).start = (lowerPart (pOf j) (gOf j).xs).length := by
      rw [a1, a3]; omega
    have hhi : (pd.2.getD j dR).end_ - (pd.2.getD j dR).gnext = (upperPart (pOf j) (gOf j).xs).length := by
      rw [a2, a4]; omega
    rw [hlo, hhi, a1, a4]
  -- the spec model's split of each record
  have SS : ∀ j < W, _ := fun j hj =>
    segSplit (fun _ => pOf j) tgt ht (gOf j) (h.win _ (wmem j hj)).1 (h.win _ (wmem j hj)).2
  -- the fill writes are the gaps, with the pivots
  have fillPerm : fd.2.Perm ((List.range W).flatMap fun j => gapW (fun _ => pOf j) (gOf j)) := by
    have hv : ∀ w ∈ fd.2, w.2 = fd.1.D w.1 := by
      intro w hw
      obtain ⟨j, hj, h1, h2, h3⟩ := FDval w hw
      rw [h3, FDg j hj w.1 h1 h2]
    have e1 : fd.2 = (fd.2.map Prod.fst).map fun x => (x, fd.1.D x) := by
      rw [List.map_map]
      conv => lhs; rw [← List.map_id fd.2]
      apply List.map_congr_left; intro w hw
      simp only [id, Function.comp]; rw [← hv w hw]
    rw [e1]
    refine (FDpos.map _).trans (List.Perm.of_eq ?_)
    rw [hpdLen, List.map_flatMap]
    apply flatMapCongr; intro j hj; rw [List.mem_range] at hj
    obtain ⟨a1, a2, a3, a4, a5, _, a7, _, _⟩ := recFacts j hj
    have e2 : List.map (fun x => (x, fd.1.D x)) (List.range' (pd.2.getD j dR).lnext
        ((pd.2.getD j dR).gnext - (pd.2.getD j dR).lnext)) =
        List.map (fun x => (x, pOf j)) (List.range' (pd.2.getD j dR).lnext
          ((pd.2.getD j dR).gnext - (pd.2.getD j dR).lnext)) := by
      apply List.map_congr_left; intro x hx
      have := List.mem_range'_1.1 hx
      rw [FDg j (by rw [hpdLen]; exact hj) x this.1 (by omega), a5]
    rw [e2]
    simp only [gapW]
    have hc : (pd.2.getD j dR).gnext - (pd.2.getD j dR).lnext = (gOf j).xs.count (pOf j) := by rw [a3, a4]; omega
    rw [hc, a3, ← zipReplicate, List.length_range']
  -- facts about work, done and children
  have workDone : ∀ a ∈ work.map (·.1), ∀ b ∈ st.done, a.end_ ≤ b.begin ∨ b.end_ ≤ a.begin :=
    (List.pairwise_append.1 hpw).2.2
  have workEnd : ∀ j < W, (work.getD j dW).1.end_ ≤ tgt.length := by
    intro j hj
    have hw : (gOf j).b + (gOf j).xs.length ≤ tgt.length := (h.win _ (wmem j hj)).2
    have hlen : (gOf j).xs.length = (work.getD j dW).1.end_ - (work.getD j dW).1.begin := slice_length _ _ _
    have hbe := (hwf _ (getDMem' work j dW hj)).1
    have hb : (gOf j).b = (work.getD j dW).1.begin := rfl
    rw [hlen, hb] at hw; omega
  have doneSame : ∀ s ∈ st.done, segD fd.1 s = segD st.mem s := by
    intro s hs
    have hsw := h.wf s (by simp only [seqsOf, List.mem_append]; exact Or.inr hs)
    simp only [segD]; congr 1
    apply slice_congr; intro x h1 h2
    refine outside s.src hsw.2 x (fun j hj => ?_)
    have := workDone _ (List.mem_map.2 ⟨_, getDMem' work j dW hj, rfl⟩) s hs
    omega
  have childMem : ∀ j < W, ∀ c ∈ cws j,
      (c = ⟨(pd.2.getD j dR).start, (pd.2.getD j dR).lnext, 1 - (pd.2.getD j dR).src⟩ ∧
        (pd.2.getD j dR).start < (pd.2.getD j dR).lnext) ∨
      (c = ⟨(pd.2.getD j dR).gnext, (pd.2.getD j dR).end_, 1 - (pd.2.getD j dR).src⟩ ∧
        (pd.2.getD j dR).gnext < (pd.2.getD j dR).end_) := by
    intro j _ c hc
    simp only [cws, childSeqs, List.mem_filter, List.mem_cons, List.mem_nil_iff, or_false, decide_eq_true_eq] at hc
    rcases hc with ⟨rfl | rfl, h2⟩
    · exact Or.inl ⟨rfl, h2⟩
    · exact Or.inr ⟨rfl, h2⟩
  have srcOK : ∀ j < W, 1 - (pd.2.getD j dR).src = 0 ∨ 1 - (pd.2.getD j dR).src = 1 := by
    intro j hj
    obtain ⟨_, _, _, _, _, a6, _, _, _⟩ := recFacts j hj
    have := (hwf _ (getDMem' work j dW hj)).2
    rw [a6]; omega
  have childWin : ∀ j < W, ∀ c ∈ cws j, win tgt (segD fd.1 c) := by
    intro j hj c hc
    obtain ⟨a1, a2, a3, a4, _, _, a7, a8, a9⟩ := recFacts j hj
    obtain ⟨s1, s2, _, _, _⟩ := SS j hj
    have gw := h.win _ (wmem j hj)
    have gw2 : (gOf j).b + (gOf j).xs.length ≤ tgt.length := gw.2
    have hsrc := srcOK j hj
    rcases childMem j hj c hc with ⟨rfl, hlt⟩ | ⟨rfl, hlt⟩
    · have hl : (pd.2.getD j dR).lnext - (pd.2.getD j dR).start = (lowerPart (pOf j) (gOf j).xs).length := by
        rw [a1, a3]; omega
      have e1 : slice (fd.1.buf (1 - (pd.2.getD j dR).src)) (pd.2.getD j dR).start
          ((pd.2.getD j dR).lnext - (pd.2.getD j dR).start) =
          slice (pd.1.buf (1 - (pd.2.getD j dR).src)) (pd.2.getD j dR).start (lowerPart (pOf j) (gOf j).xs).length := by
        rw [hl]; apply slice_congr; intro x h1 h2
        exact notGap j hj _ hsrc x h1 (by omega) (Or.inl (by omega))
      show win tgt ⟨(pd.2.getD j dR).start, slice (fd.1.buf (1 - (pd.2.getD j dR).src)) (pd.2.getD j dR).start
        ((pd.2.getD j dR).lnext - (pd.2.getD j dR).start)⟩
      rw [e1]
      refine ⟨?_, ?_⟩
      · simp only [slice_length]; rw [a1] at a8 ⊢; exact a8.trans s1
      · show (pd.2.getD j dR).start + (slice _ _ (lowerPart (pOf j) (gOf j).xs).length).length ≤ tgt.length
        rw [slice_length, a1]; omega
    · have hg : (pd.2.getD j dR).end_ - (pd.2.getD j dR).gnext = (upperPart (pOf j) (gOf j).xs).length := by
        rw [a2, a4]; omega
      have hge : (pd.2.getD j dR).gnext = (pd.2.getD j dR).end_ - (upperPart (pOf j) (gOf j).xs).length := by
        rw [a2, a4]
      have e1 : slice (fd.1.buf (1 - (pd.2.getD j dR).src)) (pd.2.getD j dR).gnext
          ((pd.2.getD j dR).end_ - (pd.2.getD j dR).gnext) =
          slice (pd.1.buf (1 - (pd.2.getD j dR).src)) ((pd.2.getD j dR).end_ - (upperPart (pOf j) (gOf j).xs).length)
            (upperPart (pOf j) (gOf j).xs).length := by
        rw [hg, ← hge]; apply slice_congr; intro x h1 h2
        exact notGap j hj _ hsrc x (by omega) (by omega) (Or.inr h1)
      show win tgt ⟨(pd.2.getD j dR).gnext, slice (fd.1.buf (1 - (pd.2.getD j dR).src)) (pd.2.getD j dR).gnext
        ((pd.2.getD j dR).end_ - (pd.2.getD j dR).gnext)⟩
      rw [e1]
      refine ⟨?_, ?_⟩
      · simp only [slice_length]; rw [← hge] at a9; rw [a4] at a9 ⊢; rw [a2]; exact a9.trans s2
      · show (pd.2.getD j dR).gnext + (slice _ _ (upperPart (pOf j) (gOf j).xs).length).length ≤ tgt.length
        rw [slice_length, a4]; omega
  -- the owed-writes accounting
  let cwf := fun g : Seg => cw tgt g.b g.xs.length
  have owedWork : owed tgt ((work.map (·.1)).map (segD st.mem)) = (List.range W).flatMap fun j => cwf (gOf j) := by
    simp only [owed, List.map_map]; rw [List.flatMap_map, flatMapIdx dW _ work]; rfl
  have kidsWork : (fd.2 ++ (List.range W).flatMap fun j => owed tgt ((cws j).map (segD fd.1))).Perm
      (owed tgt ((work.map (·.1)).map (segD st.mem))) := by
    rw [owedWork]
    refine (fillPerm.append_right _).trans ((flatMapAppendPerm _ _ _).symm.trans ?_)
    refine GpuQuicksortSpec.GpuQuicksort.Pipeline.flatMap_perm_congr _ _ _ fun j hj => ?_
    rw [List.mem_range] at hj
    rw [owedKids j hj]
    obtain ⟨_, _, _, _, s5⟩ := SS j hj
    show List.Perm _ (cw tgt (gOf j).b (gOf j).xs.length)
    rw [s5]
    show List.Perm (gapW (fun _ => pOf j) (gOf j) ++ (cw tgt (gOf j).b (lowerPart (pOf j) (gOf j).xs).length ++
      cw tgt ((gOf j).b + (gOf j).xs.length - (upperPart (pOf j) (gOf j).xs).length) (upperPart (pOf j) (gOf j).xs).length))
      (cw tgt (gOf j).b (lowerPart (pOf j) (gOf j).xs).length ++ gapW (fun _ => pOf j) (gOf j) ++
      cw tgt ((gOf j).b + (gOf j).xs.length - (upperPart (pOf j) (gOf j).xs).length) (upperPart (pOf j) (gOf j).xs).length)
    rw [← List.append_assoc]
    exact List.Perm.append_right _ List.perm_append_comm
  have newOwed : (owed tgt ((st.done ++ (List.range W).flatMap cws).map (segD fd.1))) =
      owed tgt (st.done.map (segD st.mem)) ++ (List.range W).flatMap fun j => owed tgt ((cws j).map (segD fd.1)) := by
    rw [List.map_append, GpuQuicksortSpec.GpuQuicksort.PhaseTwo.owed_append]
    congr 1
    · congr 1; exact List.map_congr_left doneSame
    · simp only [owed, List.map_flatMap, List.flatMap_assoc]
  refine ⟨fun c hc => ?_, fun c hc => ?_, ?_, fun w hw => ?_, fun i hi => ?_, fun i hi => ?_⟩
  · -- well-formed sequences
    rcases List.mem_append.1 (hseqs.subset hc) with hc | hc
    · exact h.wf c (by simp only [seqsOf, List.mem_append]; exact Or.inr hc)
    · obtain ⟨j, hj, hcj⟩ := List.mem_flatMap.1 hc
      rw [List.mem_range] at hj
      rcases childMem j hj c hcj with ⟨rfl, hlt⟩ | ⟨rfl, hlt⟩
      · exact ⟨hlt, srcOK j hj⟩
      · exact ⟨hlt, srcOK j hj⟩
  · -- windows
    rcases List.mem_append.1 (hseqs.subset hc) with hc | hc
    · rw [doneSame c hc]; exact h.win c (by simp only [seqsOf, List.mem_append]; exact Or.inr hc)
    · obtain ⟨j, hj, hcj⟩ := List.mem_flatMap.1 hc
      rw [List.mem_range] at hj
      exact childWin j hj c hcj
  · -- fills plus owed writes are the correct writes
    have hold := h.perm
    simp only [seqsOf, List.map_append, GpuQuicksortSpec.GpuQuicksort.PhaseTwo.owed_append] at hold
    have hn := (List.Perm.flatMap_right cwf (hseqs.map (segD fd.1)))
    show List.Perm (st.fills ++ fd.2 ++ owed tgt ((seqsOf _).map (segD fd.1))) _
    rw [show owed tgt ((seqsOf ⟨fd.1, (kids.filter fun c => !c.2.2).map (fun c => (c.1, c.2.1)),
        st.done ++ (kids.filter fun c => c.2.2).map (fun c => c.1), st.iteration + 1, st.capReached,
        st.fills ++ fd.2⟩).map (segD fd.1)) = ((seqsOf ⟨fd.1, (kids.filter fun c => !c.2.2).map (fun c => (c.1, c.2.1)),
        st.done ++ (kids.filter fun c => c.2.2).map (fun c => c.1), st.iteration + 1, st.capReached,
        st.fills ++ fd.2⟩).map (segD fd.1)).flatMap cwf from rfl]
    have hn' : List.Perm (((seqsOf ⟨fd.1, (kids.filter fun c => !c.2.2).map (fun c => (c.1, c.2.1)),
        st.done ++ (kids.filter fun c => c.2.2).map (fun c => c.1), st.iteration + 1, st.capReached,
        st.fills ++ fd.2⟩).map (segD fd.1)).flatMap cwf)
        (owed tgt ((st.done ++ (List.range W).flatMap cws).map (segD fd.1))) := hn
    rw [newOwed] at hn'
    rw [List.perm_iff_count]; intro v
    have c1 := hn'.count_eq v
    have c2 := kidsWork.count_eq v
    have c3 := hold.count_eq v
    simp only [List.count_append] at c1 c2 c3 ⊢
    have e' : List.count v (owed tgt (List.map (segD st.mem) (List.map (fun x => x.fst) work))) =
        List.count v (owed tgt (List.map (segD st.mem) (List.map (fun x => x.fst) st.work))) := rfl
    omega
  · -- fills are in memory
    rcases List.mem_append.1 hw with hw | hw
    · rw [show fd.1.D w.1 = fd.1.buf 0 w.1 from rfl, outside 0 (Or.inl rfl) w.1 (fun j hj => ?_)]
      · exact h.fillsD w hw
      · exact hfillOut w hw _ (wmem j hj)
    · obtain ⟨j, hj, h1, h2, h3⟩ := FDval w hw
      rw [h3]; exact FDg j hj w.1 h1 h2
  · show fd.1.buf 0 i = D0 i
    rw [outside 0 (Or.inl rfl) i (fun j hj => Or.inr (Nat.le_trans (workEnd j hj) hi))]; exact h.frameD i hi
  · show fd.1.buf 1 i = A0 i
    rw [outside 1 (Or.inr rfl) i (fun j hj => Or.inr (Nat.le_trans (workEnd j hj) hi))]; exact h.frameA i hi

end GpuQuicksort.Theorems
