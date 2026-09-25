import GpuQuicksortProof.GpuQuicksort.Spec
import GpuQuicksortProof.GpuQuicksort.Model.Scan

/-!
# GpuQuicksortProof.GpuQuicksort.Theorems.Scan
==============================================

`scan2` is an exclusive prefix sum: for T = 2^m threads, entry i of the result is
x[0] + … + x[i − 1], and the total is x[0] + … + x[T − 1]. Within every level, no thread reads
or writes a slot another thread of the level writes, so the barrier-separated parallel levels are
well defined (R-28(a) for the scan).
-/

namespace GpuQuicksort.Theorems

open GpuQuicksort.Model

/-! ## Writes -/

theorem applyW_not (ws : List (Nat × Nat)) (i : Nat) :
    ∀ x, i ∉ ws.map Prod.fst → applyW ws x i = x i := by
  induction ws with
  | nil => intro x _; rfl
  | cons w rest ih =>
    intro x h
    simp only [List.map_cons, List.mem_cons, not_or] at h
    simp only [applyW, List.foldl_cons] at ih ⊢
    rw [ih _ h.2]; simp only [updN]; split
    · next e => exact absurd e h.1
    · rfl

theorem applyW_mem (ws : List (Nat × Nat)) :
    ∀ x, (ws.map Prod.fst).Nodup → ∀ w ∈ ws, applyW ws x w.1 = w.2 := by
  induction ws with
  | nil => intro x _ w hw; simp at hw
  | cons w0 rest ih =>
    intro x hnd w hw
    simp only [List.map_cons, List.nodup_cons] at hnd
    simp only [applyW, List.foldl_cons] at ih ⊢
    rcases List.mem_cons.1 hw with rfl | hw
    · rw [show (List.foldl (fun m w => updN m w.1 w.2) (updN x w.1 w.2) rest) w.1 =
          applyW rest (updN x w.1 w.2) w.1 from rfl, applyW_not _ _ _ hnd.1]; simp [updN]
    · exact ih _ hnd.2 w hw

/-! ## Index arithmetic of a level -/

theorem nodupMap {l : List Nat} (f : Nat → Nat) (hf : ∀ a b, f a = f b → a = b) (h : l.Nodup) :
    (l.map f).Nodup :=
  List.pairwise_map.2 (h.imp fun hab e => hab (hf _ _ e))

theorem mulCancel {o a b : Nat} (ho : 0 < o) (h : o * a = o * b) : a = b :=
  Nat.eq_of_mul_eq_mul_left ho h

/-- **(lemma)** (R-28(a) for the scan): in an up-sweep level the threads write distinct slots, and
no slot a thread reads (its ai) is written by any thread. -/
theorem upRaceFree (o d : Nat) (ho : 0 < o) (x : Nat → Nat) :
    ((upWrites o d x).map Prod.fst).Nodup ∧
    ∀ t t', t < d → t' < d → o * (2 * t + 1) - 1 ≠ o * (2 * t' + 2) - 1 := by
  constructor
  · simp only [upWrites, List.map_map]
    refine nodupMap _ (fun a b h => ?_) List.nodup_range
    simp only [Function.comp] at h
    have h1 : o * (2 * a + 2) ≥ 1 := Nat.le_trans (by omega) (Nat.le_mul_of_pos_right o (by omega))
    have h2 : o * (2 * b + 2) ≥ 1 := Nat.le_trans (by omega) (Nat.le_mul_of_pos_right o (by omega))
    have := mulCancel ho (show o * (2 * a + 2) = o * (2 * b + 2) by omega); omega
  · intro t t' _ _ h
    have h1 : o * (2 * t + 1) ≥ 1 := Nat.le_trans (by omega) (Nat.le_mul_of_pos_right o (by omega))
    have h2 : o * (2 * t' + 2) ≥ 1 := Nat.le_trans (by omega) (Nat.le_mul_of_pos_right o (by omega))
    have := mulCancel ho (show o * (2 * t + 1) = o * (2 * t' + 2) by omega); omega

/-- **(lemma)**: a down-sweep level writes exactly the slots o·r − 1 for r = 1 … 2d, in order. -/
theorem downPositions (o : Nat) (x : Nat → Nat) :
    ∀ d, (downWrites o d x).map Prod.fst = (List.range (2 * d)).map (fun r => o * (r + 1) - 1)
  | 0 => by simp [downWrites]
  | d + 1 => by
    have ih := downPositions o x d
    simp only [downWrites, List.range_succ, List.flatMap_append, List.map_append] at ih ⊢
    rw [ih, show 2 * (d + 1) = (2 * d + 1) + 1 by omega, List.range_succ, List.range_succ]
    simp [List.map_append]

/-- **(lemma)** (R-28(a) for the scan): in a down-sweep level the threads write distinct slots,
each thread only its own pair (ai, bi), so no thread reads a slot another thread writes. -/
theorem downRaceFree (o d : Nat) (ho : 0 < o) (x : Nat → Nat) :
    ((downWrites o d x).map Prod.fst).Nodup := by
  rw [downPositions]
  refine nodupMap _ (fun a b h => ?_) List.nodup_range
  have h1 : o * (a + 1) ≥ 1 := Nat.le_trans (by omega) (Nat.le_mul_of_pos_right o (by omega))
  have h2 : o * (b + 1) ≥ 1 := Nat.le_trans (by omega) (Nat.le_mul_of_pos_right o (by omega))
  have := mulCancel ho (show o * (a + 1) = o * (b + 1) by omega); omega

/-! ## The Blelloch invariants -/

/-- x0[a] + … + x0[b − 1]. -/
def S (x0 : Nat → Nat) (a b : Nat) : Nat := ((List.range' a (b - a)).map x0).sum

theorem S_split (x0 : Nat → Nat) {a b c : Nat} (h1 : a ≤ b) (h2 : b ≤ c) :
    S x0 a b + S x0 b c = S x0 a c := by
  simp only [S]
  rw [← List.sum_append, ← List.map_append]
  congr 2
  rw [show c - a = (b - a) + (c - b) by omega, ← List.range'_append_1, show a + (b - a) = b by omega]

theorem S_one (x0 : Nat → Nat) (i : Nat) : S x0 i (i + 1) = x0 i := by
  simp [S]

/-- The largest 2^j, j ≤ l, dividing i + 1: the width of the block the up-sweep has summed into
slot i after l levels. -/
def wv : Nat → Nat → Nat
  | 0, _ => 1
  | l + 1, i => if (i + 1) % 2 ^ (l + 1) = 0 then 2 ^ (l + 1) else wv l i

theorem wv_le (i : Nat) : ∀ l, 1 ≤ wv l i ∧ wv l i ≤ i + 1
  | 0 => by simp [wv]
  | l + 1 => by
    simp only [wv]
    split
    · next h =>
      exact ⟨Nat.one_le_two_pow, Nat.le_of_dvd (by omega) (Nat.dvd_of_mod_eq_zero h)⟩
    · exact wv_le i l

theorem wv_top (i : Nat) : ∀ l, (i + 1) % 2 ^ l = 0 → wv l i = 2 ^ l
  | 0, _ => rfl
  | l + 1, h => by simp [wv, h]

theorem pow_succ2 (l : Nat) : 2 ^ (l + 1) = 2 * 2 ^ l := by rw [Nat.pow_succ]; omega

/-- mod-zero as a multiple. -/
theorem modZero {a m : Nat} (h : a % m = 0) : ∃ q, a = m * q :=
  ⟨a / m, (Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero h)).symm⟩

theorem mulMod (m q : Nat) : (m * q) % m = 0 := Nat.mul_mod_right m q

/-- After l up-sweep levels, slot i holds the sum of the wv l i inputs ending at i. -/
def UInv (x0 : Nat → Nat) (T l : Nat) (x : Nat → Nat) : Prop :=
  ∀ i < T, x i = S x0 (i + 1 - wv l i) (i + 1)

/-- Thread tid = q − 1's slots, for q ≥ 1: bi + 1 = 2·o·q and ai + 1 + o = 2·o·q. -/
theorem idx (o q : Nat) (hq : 1 ≤ q) :
    o * (2 * (q - 1) + 2) = 2 * (o * q) ∧ o * (2 * (q - 1) + 1) + o = 2 * (o * q) := by
  obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
  simp only [Nat.add_sub_cancel, Nat.mul_add, Nat.mul_one, Nat.mul_left_comm o 2]
  omega

/-- **(lemma)**: one up-sweep level (offset 2^l, 2^(m−l−1) threads) doubles the summed blocks
ending at multiples of 2^(l+1). -/
theorem upLevel (x0 : Nat → Nat) (m l : Nat) (hl : l < m) (x : Nat → Nat) (h : UInv x0 (2 ^ m) l x) :
    UInv x0 (2 ^ m) (l + 1) (applyW (upWrites (2 ^ l) (2 ^ (m - l - 1)) x) x) := by
  have ho : 0 < 2 ^ l := Nat.two_pow_pos l
  have hp := pow_succ2 l
  generalize hd : 2 ^ (m - l - 1) = d
  have hT : 2 ^ m = 2 * 2 ^ l * d := by
    rw [← hd, ← hp, ← Nat.pow_add]; congr 1; omega
  intro i hi
  by_cases hdiv : (i + 1) % (2 * 2 ^ l) = 0
  · obtain ⟨q, hq⟩ := modZero hdiv
    rw [Nat.mul_assoc] at hq
    have q1 : 1 ≤ q := by
      rcases Nat.eq_zero_or_pos q with h0 | h0
      · subst h0; simp at hq
      · exact h0
    have hlq : 2 ^ l ≤ 2 ^ l * q := Nat.le_mul_of_pos_right _ q1
    have qd : q ≤ d := by
      have : 2 ^ l * q ≤ 2 ^ l * d := by rw [Nat.mul_assoc] at hT; omega
      exact Nat.le_of_mul_le_mul_left this ho
    obtain ⟨e1, e2⟩ := idx (2 ^ l) q q1
    have hmem : (i, x i + x (i - 2 ^ l)) ∈ upWrites (2 ^ l) d x := by
      simp only [upWrites, List.mem_map, List.mem_range]
      refine ⟨q - 1, by omega, ?_⟩
      rw [show 2 ^ l * (2 * (q - 1) + 2) - 1 = i by omega,
        show 2 ^ l * (2 * (q - 1) + 1) - 1 = i - 2 ^ l by omega]
    have hv := applyW_mem _ x (upRaceFree _ d ho x).1 _ hmem
    simp only at hv
    rw [hv, h i (by omega), h (i - 2 ^ l) (by omega)]
    have e3 : i + 1 = 2 ^ l * (2 * q) := by rw [hq, Nat.mul_left_comm]
    have e4 : i - 2 ^ l + 1 = 2 ^ l * (2 * q - 1) := by rw [Nat.mul_sub_one, Nat.mul_left_comm]; omega
    have w1 : wv l i = 2 ^ l := wv_top i l (by rw [e3]; exact mulMod _ _)
    have w2 : wv l (i - 2 ^ l) = 2 ^ l := wv_top _ l (by rw [e4]; exact mulMod _ _)
    have w3 : wv (l + 1) i = 2 * 2 ^ l := by
      simp only [wv, hp, hdiv, ↓reduceIte]
    rw [w1, w2, w3, Nat.add_comm, show i - 2 ^ l + 1 = i + 1 - 2 ^ l by omega,
      show i + 1 - 2 ^ l - 2 ^ l = i + 1 - 2 * 2 ^ l by omega]
    exact S_split x0 (by omega) (by omega)
  · have hnot : i ∉ (upWrites (2 ^ l) d x).map Prod.fst := by
      simp only [upWrites, List.map_map, List.mem_map, List.mem_range, Function.comp, not_exists,
        not_and]
      intro t _ he
      apply hdiv
      have e := (idx (2 ^ l) (t + 1) (by omega)).1
      simp only [Nat.add_sub_cancel] at e
      have pos : 2 ^ l ≤ 2 ^ l * (2 * t + 2) := Nat.le_mul_of_pos_right _ (by omega)
      rw [show i + 1 = (2 * 2 ^ l) * (t + 1) by rw [Nat.mul_assoc]; omega]
      exact mulMod _ _
    rw [applyW_not _ _ _ hnot, h i hi]
    have : wv (l + 1) i = wv l i := by
      simp only [wv, hp, hdiv, ↓reduceIte]
    rw [this]

/-- During the down-sweep, with 2^k the next block size: block-end slots hold the exclusive prefix
of their block, all other slots still hold their up-sweep block sums. -/
def DInv (x0 : Nat → Nat) (T k : Nat) (x : Nat → Nat) : Prop :=
  ∀ i < T, x i = if (i + 1) % 2 ^ k = 0 then S x0 0 (i + 1 - 2 ^ k) else S x0 (i + 1 - wv k i) (i + 1)

/-- The products a level's index arithmetic uses, as linear terms in o·t. -/
theorem lin (o t : Nat) :
    o * (2 * t + 1) = 2 * (o * t) + o ∧ o * (2 * t + 2) = 2 * (o * t) + 2 * o ∧
    (2 * o) * (t + 1) = 2 * (o * t) + 2 * o ∧ o * (t + 1) = o * t + o := by
  simp only [Nat.mul_add, Nat.mul_one, Nat.mul_left_comm o 2, Nat.mul_assoc]
  exact ⟨trivial, by rw [Nat.mul_comm o 2], trivial, trivial⟩

theorem oddMod (o t : Nat) (ho : 0 < o) : (o * (2 * t + 1)) % (2 * o) = o := by
  rw [(lin o t).1, show 2 * (o * t) + o = o + (2 * o) * t by rw [Nat.mul_assoc]; omega,
    Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]

/-- **(lemma)**: one down-sweep level (offset 2^l, 2^(m−l−1) threads) turns every slot ending a
2^l block into that block's exclusive prefix. -/
theorem downLevel (x0 : Nat → Nat) (m l : Nat) (hl : l < m) (x : Nat → Nat)
    (h : DInv x0 (2 ^ m) (l + 1) x) :
    DInv x0 (2 ^ m) l (applyW (downWrites (2 ^ l) (2 ^ (m - l - 1)) x) x) := by
  have ho : 0 < 2 ^ l := Nat.two_pow_pos l
  have hp := pow_succ2 l
  generalize hd : 2 ^ (m - l - 1) = d
  have hT : 2 ^ m = 2 * (2 ^ l * d) := by
    rw [← hd, ← Nat.mul_assoc, ← hp, ← Nat.pow_add]; congr 1; omega
  have hnd := downRaceFree (2 ^ l) d ho x
  simp only [DInv, hp] at h ⊢
  intro i hi
  by_cases hdo : (i + 1) % 2 ^ l = 0
  · obtain ⟨r, hr⟩ := modZero hdo
    have r1 : 1 ≤ r := by
      rcases Nat.eq_zero_or_pos r with h0 | h0
      · subst h0; simp at hr
      · exact h0
    have r2d : r ≤ 2 * d := by
      have : 2 ^ l * r ≤ 2 ^ l * (2 * d) := by rw [Nat.mul_left_comm]; omega
      exact Nat.le_of_mul_le_mul_left this ho
    simp only [hdo, ↓reduceIte]
    obtain ⟨t, ht⟩ : ∃ t, r = 2 * t + 1 ∨ r = 2 * t + 2 := ⟨(r - 1) / 2, by omega⟩
    obtain ⟨L1, L2, L3, L4⟩ := lin (2 ^ l) t
    have hle : 2 ^ l * (t + 1) ≤ 2 ^ l * d := Nat.mul_le_mul_left _ (by omega)
    rcases ht with rfl | rfl
    · -- slot ai of thread t: receives x[bi]
      have hmem : (i, x (i + 2 ^ l)) ∈ downWrites (2 ^ l) d x := by
        simp only [downWrites, List.mem_flatMap, List.mem_range, List.mem_cons, List.mem_nil_iff,
          or_false]
        refine ⟨t, by omega, Or.inl ?_⟩
        rw [show 2 ^ l * (2 * t + 1) - 1 = i by omega, show 2 ^ l * (2 * t + 2) - 1 = i + 2 ^ l by omega]
      rw [applyW_mem _ x hnd _ hmem]
      have hb : (i + 2 ^ l + 1) % (2 * 2 ^ l) = 0 := by
        rw [show i + 2 ^ l + 1 = 2 * 2 ^ l * (t + 1) by omega]; exact mulMod _ _
      rw [h _ (by omega)]; simp only [hb, ↓reduceIte]
      congr 1; omega
    · -- slot bi of thread t: receives x[bi] + x[ai]
      have hmem : (i, x i + x (i - 2 ^ l)) ∈ downWrites (2 ^ l) d x := by
        simp only [downWrites, List.mem_flatMap, List.mem_range, List.mem_cons, List.mem_nil_iff,
          or_false]
        refine ⟨t, by omega, Or.inr ?_⟩
        rw [show 2 ^ l * (2 * t + 2) - 1 = i by omega, show 2 ^ l * (2 * t + 1) - 1 = i - 2 ^ l by omega]
      rw [applyW_mem _ x hnd _ hmem]
      have hbi : (i + 1) % (2 * 2 ^ l) = 0 := by
        rw [show i + 1 = 2 * 2 ^ l * (t + 1) by omega]; exact mulMod _ _
      have e1 : i - 2 ^ l + 1 = 2 ^ l * (2 * t + 1) := by omega
      have hai : (i - 2 ^ l + 1) % (2 * 2 ^ l) = 2 ^ l := by rw [e1]; exact oddMod _ _ ho
      have wa : wv (l + 1) (i - 2 ^ l) = 2 ^ l := by
        simp only [wv, hp, hai, show 2 ^ l ≠ 0 by omega, ↓reduceIte]
        exact wv_top _ l (by rw [e1]; exact mulMod _ _)
      rw [h i hi, h (i - 2 ^ l) (by omega)]
      simp only [hbi, hai, show 2 ^ l ≠ 0 by omega, ↓reduceIte, wa]
      rw [show i - 2 ^ l + 1 - 2 ^ l = i + 1 - 2 * 2 ^ l by omega,
        show i - 2 ^ l + 1 = i + 1 - 2 ^ l by omega]
      exact S_split x0 (b := i + 1 - 2 * 2 ^ l) (by omega) (by omega)
  · have hnot : i ∉ (downWrites (2 ^ l) d x).map Prod.fst := by
      rw [downPositions]
      simp only [List.mem_map, List.mem_range, not_exists, not_and]
      intro r _ he
      have : 2 ^ l ≤ 2 ^ l * (r + 1) := Nat.le_mul_of_pos_right _ (by omega)
      apply hdo; rw [show i + 1 = 2 ^ l * (r + 1) by omega]; exact mulMod _ _
    rw [applyW_not _ _ _ hnot, h i hi]
    have hn : ¬ (i + 1) % (2 * 2 ^ l) = 0 := by
      intro h0; apply hdo
      obtain ⟨q, hq⟩ := modZero h0
      rw [hq, Nat.mul_assoc, Nat.mul_left_comm]; exact mulMod _ _
    simp only [hn, hdo, ↓reduceIte, wv, hp]

/-- **(lemma)**: the up-sweep loop, from level l with 2^(m−l)/2 threads, reaches level m with
offset 2^m. -/
theorem upSweepSpec (x0 : Nat → Nat) (m : Nat) :
    ∀ j l (x : Nat → Nat), l + j = m → UInv x0 (2 ^ m) l x →
      (upSweep (2 ^ j / 2) (2 ^ l) x).2 = 2 ^ m ∧ UInv x0 (2 ^ m) m (upSweep (2 ^ j / 2) (2 ^ l) x).1
  | 0, l, x, hj, h => by
    rw [upSweep]; simp only [Nat.pow_zero, Nat.reduceDiv, Nat.lt_irrefl, ↓reduceIte]
    have : l = m := by omega
    subst this; exact ⟨rfl, h⟩
  | j + 1, l, x, hj, h => by
    rw [upSweep]
    have hpos : 0 < 2 ^ (j + 1) / 2 := by rw [pow_succ2]; have := Nat.two_pow_pos j; omega
    simp only [hpos, ↓reduceIte]
    rw [show 2 ^ (j + 1) / 2 = 2 ^ j by rw [pow_succ2]; omega, show 2 * 2 ^ l = 2 ^ (l + 1) by
      rw [pow_succ2]]
    have hd : 2 ^ j = 2 ^ (m - l - 1) := by congr 1; omega
    have := upLevel x0 m l (by omega) x h
    rw [← hd] at this
    exact upSweepSpec x0 m j (l + 1) _ (by omega) this

/-- **(lemma)**: the down-sweep loop, from 2^j threads and offset 2^k with j + k = m, ends with
every slot an exclusive prefix. -/
theorem downSweepSpec (x0 : Nat → Nat) (m : Nat) :
    ∀ k j (x : Nat → Nat), j + k = m → DInv x0 (2 ^ m) k x →
      DInv x0 (2 ^ m) 0 (downSweep (2 ^ m) (2 ^ j) (2 ^ k) x)
  | 0, j, x, hj, h => by
    rw [downSweep]
    have : j = m := by omega
    subst this; simp only [Nat.lt_irrefl, and_false, ↓reduceIte]; exact h
  | k + 1, j, x, hj, h => by
    rw [downSweep]
    have hlt : 2 ^ j < 2 ^ m := Nat.pow_lt_pow_right (by decide) (by omega)
    simp only [Nat.two_pow_pos j, hlt, and_self, ↓reduceIte]
    rw [show 2 ^ (k + 1) / 2 = 2 ^ k by rw [pow_succ2]; omega, show 2 * 2 ^ j = 2 ^ (j + 1) by
      rw [pow_succ2]]
    have hd : 2 ^ j = 2 ^ (m - k - 1) := by congr 1; omega
    have := downLevel x0 m k (by omega) x h
    rw [← hd] at this
    exact downSweepSpec x0 m k (j + 1) _ (by omega) this

/-- **(lemma)** (R-04, D-13): `scan2` over T = 2^m slots is the exclusive prefix sum: slot i ends
holding x[0] + … + x[i − 1], and the total `tx` is x[0] + … + x[T − 1]. -/
theorem scan2Correct (m : Nat) (x0 : Nat → Nat) :
    (scan2 (2 ^ m) x0).2 = S x0 0 (2 ^ m) ∧ ∀ i < 2 ^ m, (scan2 (2 ^ m) x0).1 i = S x0 0 i := by
  have h0 : UInv x0 (2 ^ m) 0 x0 := fun i _ => by simp [wv, S_one]
  obtain ⟨ho, hu⟩ := upSweepSpec x0 m m 0 x0 (by omega) h0
  have hT := Nat.two_pow_pos m
  have htop : wv m (2 ^ m - 1) = 2 ^ m := wv_top _ m (by rw [show 2 ^ m - 1 + 1 = 2 ^ m by omega]; simp)
  simp only [scan2, Nat.pow_zero] at ho hu ⊢
  refine ⟨?_, fun i hi => ?_⟩
  · rw [hu _ (by omega), htop, show 2 ^ m - 1 + 1 = 2 ^ m by omega, Nat.sub_self]
  · have hd : DInv x0 (2 ^ m) m (updN (upSweep (2 ^ m / 2) 1 x0).1 (2 ^ m - 1) 0) := by
      intro i hi
      by_cases he : i = 2 ^ m - 1
      · subst he; simp [updN, show 2 ^ m - 1 + 1 = 2 ^ m by omega, S]
      · have hn : ¬ (i + 1) % 2 ^ m = 0 := by rw [Nat.mod_eq_of_lt (by omega)]; omega
        simp only [updN, he, ↓reduceIte, hn]; exact hu i hi
    have := downSweepSpec x0 m m 0 _ (by omega) hd
    rw [ho]
    have e := this i hi
    simp only [Nat.pow_zero, Nat.mod_one, ↓reduceIte, Nat.add_sub_cancel] at e
    exact e

end GpuQuicksort.Theorems
