import GpuQuicksortSpec.GpuQuicksort.Spec
import GpuQuicksortSpec.GpuQuicksort.Model
import GpuQuicksortSpec.GpuQuicksort.Theorems

/-!
# GpuQuicksortSpec.GpuQuicksort.Bitonic
=======================================

The alternative sort's **bitonic network** (R-15), modeled exactly as the kernel `altsort` runs
it, and proved to sort every input of every power-of-two length.

## The model

The kernel pads the sequence to P = 2^m, then runs

    for k = 2, 4, …, P:  for j = k/2, k/4, …, 1:  for every i:
        ixj = i ^ j;  if ixj > i: compare s[i], s[ixj]; swap unless ordered ascending
        when (i & k) == 0, descending otherwise
    (barrier after every j)

- `rnd k j` is one (k, j) round, as the value each index receives. The pairs {i, i ^ j} are
  disjoint (xor with j is an involution), so every thread of a round reads only values from before
  the round, and the barrier (R-28) ends it; a round is therefore a function of the old array.
- `merge s t` runs the rounds j = 2^(t−1), …, 1 of stage k = 2^s, and `net m` runs stages
  k = 2, …, 2^m. The array is modeled as a function on all indices; an index below 2^m is only ever
  paired with another index below 2^m (`i ^^^ j < 2^m`), so the first 2^m values are exactly the
  kernel's threadgroup array.
- The bit operations are the kernel's own (`^^^`, `&&&`); `xorTwoPow` and `andTwoPow` translate
  them into arithmetic once, and everything after that is arithmetic.

## The proof

1. **The 0-1 principle.** Every comparator commutes with a monotone map, so the network does too
   (`net_comp`). If the network misordered two outputs of some input, thresholding at the larger
   value would give a 0-1 input it misorders.
2. **0-1 inputs.** Invariant `SB s`: after stage s, every aligned block of 2^s is sorted,
   ascending when its block number is even and descending when odd. During stage s, invariant
   `MI s t`: every aligned sub-block of 2^t is *bitonic* (0…1…0 or 1…0…1) and the sub-blocks are
   in order. One round is a half-cleaner on each sub-block of 2^(t+1): it leaves two bitonic
   halves, one of them constant (`halfClean`).
3. **Permutation.** Each round swaps values within disjoint pairs (`roundPerm`).
-/

namespace GpuQuicksortSpec.GpuQuicksort.Bitonic

open GpuQuicksortSpec.GpuQuicksort.Spec
open GpuQuicksortSpec.GpuQuicksort.Model
open GpuQuicksortSpec.GpuQuicksort.Theorems

/-- R-15 — one (k, j) round of `altsort`, as the value index i receives. The thread for the lower
index of each pair {i, i ^ j} puts the smaller value first when `(i & k) == 0`, the larger first
otherwise. -/
def rnd (k j : Nat) (f : Nat → Nat) (i : Nat) : Nat :=
  if i < i ^^^ j then
    (if i &&& k = 0 then min (f i) (f (i ^^^ j)) else max (f i) (f (i ^^^ j)))
  else
    (if (i ^^^ j) &&& k = 0 then max (f (i ^^^ j)) (f i) else min (f (i ^^^ j)) (f i))

/-- R-15 — stage k = 2^s: the rounds j = 2^(t−1), …, 2, 1 (called with t = s, so j starts at k/2). -/
def merge (s : Nat) : Nat → (Nat → Nat) → (Nat → Nat)
  | 0, f => f
  | t + 1, f => merge s t (rnd (2 ^ s) (2 ^ t) f)

/-- R-15 — the whole network for P = 2^m: stages k = 2, 4, …, 2^m. -/
def net : Nat → (Nat → Nat) → (Nat → Nat)
  | 0, f => f
  | s + 1, f => merge (s + 1) (s + 1) (net s f)

/-- R-15 — the load: element i for i < ℓ, the pad value `0xFFFFFFFF` beyond. -/
def padF (xs : List Nat) (i : Nat) : Nat := xs.getD i 0xFFFFFFFF

/-- R-15 — the alternative sort as the kernel computes it for P = 2^m: load and pad, run the
network, write back the first ℓ values. -/
def bitonicAltSort (m : Nat) (xs : List Nat) : List Nat :=
  ((List.range (2 ^ m)).map (net m (padF xs))).take xs.length

/-! ## The bit operations -/

/-- **(lemma)**: flipping bit t with `^^^ 2^t` moves i up by 2^t when that bit is clear, down otherwise. -/
theorem xorTwoPow (i t : Nat) :
    i ^^^ 2 ^ t = if i % 2 ^ (t + 1) < 2 ^ t then i + 2 ^ t else i - 2 ^ t := by
  have hH : 0 < 2 ^ t := Nat.two_pow_pos t
  have h2 : 2 ^ (t + 1) = 2 * 2 ^ t := by rw [Nat.pow_succ, Nat.mul_comm]
  -- i = 2^t * q + r
  obtain ⟨q, r, hr, rfl⟩ : ∃ q r, r < 2 ^ t ∧ i = 2 ^ t * q + r :=
    ⟨i / 2 ^ t, i % 2 ^ t, Nat.mod_lt _ hH, (Nat.div_add_mod i (2 ^ t)).symm⟩
  have hmod : (2 ^ t * q + r) % 2 ^ (t + 1) = 2 ^ t * (q % 2) + r := by
    rw [h2]
    conv => lhs; rw [← Nat.div_add_mod q 2]
    rw [Nat.mul_add, ← Nat.mul_assoc, Nat.mul_comm (2 ^ t) 2, Nat.add_assoc, Nat.mul_add_mod]
    apply Nat.mod_eq_of_lt
    have : q % 2 < 2 := Nat.mod_lt _ (by decide)
    have : 2 ^ t * (q % 2) ≤ 2 ^ t * 1 := Nat.mul_le_mul_left _ (by omega)
    omega
  rw [hmod]
  have hq := Nat.mod_two_eq_zero_or_one q
  apply Nat.eq_of_testBit_eq
  intro n
  rw [Nat.testBit_xor, Nat.testBit_two_pow]
  rcases hq with hq | hq
  · have e : 2 ^ t * (q % 2) + r < 2 ^ t := by rw [hq]; omega
    simp only [e, ↓reduceIte]
    rw [show 2 ^ t * q + r + 2 ^ t = 2 ^ t * (q + 1) + r by rw [Nat.mul_succ]; omega]
    rw [Nat.testBit_two_pow_mul_add _ hr, Nat.testBit_two_pow_mul_add _ hr]
    by_cases hn : n < t
    · have hne : ¬ t = n := by omega
      simp [hn, hne]
    · simp only [hn, ↓reduceIte]
      rcases Nat.lt_or_eq_of_le (Nat.le_of_not_lt hn) with h | h
      · obtain ⟨d, hd⟩ : ∃ d, n - t = d + 1 := ⟨n - t - 1, by omega⟩
        have hne : ¬ t = n := by omega
        rw [hd, Nat.testBit_add_one, Nat.testBit_add_one]
        have : (q + 1) / 2 = q / 2 := by omega
        simp [this, hne]
      · subst h
        have h1 : (q + 1) % 2 = 1 - q % 2 := by omega
        simp only [Nat.sub_self, Nat.testBit_zero, h1, decide_true]
        rcases Nat.mod_two_eq_zero_or_one q with h | h <;> simp [h]
  · have e : ¬ 2 ^ t * (q % 2) + r < 2 ^ t := by rw [hq]; omega
    simp only [e, ↓reduceIte]
    obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
    rw [show 2 ^ t * (q' + 1) + r - 2 ^ t = 2 ^ t * q' + r by rw [Nat.mul_succ]; omega]
    rw [Nat.testBit_two_pow_mul_add _ hr, Nat.testBit_two_pow_mul_add _ hr]
    by_cases hn : n < t
    · have hne : ¬ t = n := by omega
      simp [hn, hne]
    · simp only [hn, ↓reduceIte]
      rcases Nat.lt_or_eq_of_le (Nat.le_of_not_lt hn) with h | h
      · obtain ⟨d, hd⟩ : ∃ d, n - t = d + 1 := ⟨n - t - 1, by omega⟩
        have hne : ¬ t = n := by omega
        rw [hd, Nat.testBit_add_one, Nat.testBit_add_one]
        have : (q' + 1) / 2 = q' / 2 := by omega
        simp [this, hne]
      · subst h
        have h1 : (q' + 1) % 2 = 1 - q' % 2 := by omega
        simp only [Nat.sub_self, Nat.testBit_zero, h1, decide_true]
        rcases Nat.mod_two_eq_zero_or_one q' with h | h <;> simp [h]

/-- **(lemma)**: the kernel's direction test `(i & k) == 0` for k = 2^s reads bit s of i. -/
theorem andTwoPow (i s : Nat) : i &&& 2 ^ s = 0 ↔ (i / 2 ^ s) % 2 = 0 := by
  have e : i &&& 2 ^ s = if (i / 2 ^ s) % 2 = 1 then 2 ^ s else 0 := by
    apply Nat.eq_of_testBit_eq; intro n
    rw [Nat.testBit_and, Nat.testBit_two_pow]
    split
    · rw [Nat.testBit_two_pow]; by_cases h : s = n
      · subst h; simp [Nat.testBit_eq_decide_div_mod_eq, *]
      · simp [h]
    · simp only [Nat.zero_testBit]; by_cases h : s = n
      · subst h; simp [Nat.testBit_eq_decide_div_mod_eq, *]
      · simp [h]
  rw [e]; have := Nat.two_pow_pos s; split <;> omega

/-- **(lemma)**: a round at the lower index of a pair (bit t clear). -/
theorem rndLo (s t : Nat) (f : Nat → Nat) (i : Nat) (hi : i % 2 ^ (t + 1) < 2 ^ t) :
    rnd (2 ^ s) (2 ^ t) f i =
      if (i / 2 ^ s) % 2 = 0 then min (f i) (f (i + 2 ^ t)) else max (f i) (f (i + 2 ^ t)) := by
  have hx : i ^^^ 2 ^ t = i + 2 ^ t := by rw [xorTwoPow]; simp [hi]
  have hlt : i < i + 2 ^ t := by have := Nat.two_pow_pos t; omega
  simp only [rnd, hx, hlt, ↓reduceIte, andTwoPow]

/-- **(lemma)**: a round at the upper index of a pair (bit t set). -/
theorem rndHi (s t : Nat) (f : Nat → Nat) (i : Nat) (hi : 2 ^ t ≤ i % 2 ^ (t + 1)) :
    rnd (2 ^ s) (2 ^ t) f i =
      if ((i - 2 ^ t) / 2 ^ s) % 2 = 0 then max (f (i - 2 ^ t)) (f i) else min (f (i - 2 ^ t)) (f i) := by
  have hx : i ^^^ 2 ^ t = i - 2 ^ t := by rw [xorTwoPow]; simp [Nat.not_lt.2 hi]
  have hle : 2 ^ t ≤ i := Nat.le_trans hi (Nat.mod_le _ _)
  have hlt : ¬ i < i - 2 ^ t := by omega
  simp only [rnd, hx, hlt, ↓reduceIte, andTwoPow]

/-! ## Alignment arithmetic -/

theorem modAligned (P M x : Nat) (hP : P % M = 0) (hx : x < M) : (P + x) % M = x := by
  rw [Nat.add_mod, hP, Nat.zero_add, Nat.mod_mod, Nat.mod_eq_of_lt hx]

theorem alignedLt (M X Y : Nat) (hX : X % M = 0) (hY : Y % M = 0) (h : X < Y) : X + M ≤ Y := by
  have ex := Nat.div_add_mod X M; have ey := Nat.div_add_mod Y M
  rw [hX, Nat.add_zero] at ex; rw [hY, Nat.add_zero] at ey
  have : X / M < Y / M := by
    rcases Nat.lt_or_ge (X / M) (Y / M) with h' | h'
    · exact h'
    · have := Nat.mul_le_mul_left M h'; omega
  have := Nat.mul_le_mul_left M (Nat.succ_le_of_lt this)
  rw [Nat.mul_succ] at this; omega

theorem divSame (N B i : Nat) (hB : B % N = 0) (h1 : B ≤ i) (h2 : i < B + N) : i / N = B / N := by
  have eb := Nat.div_add_mod B N
  rw [hB, Nat.add_zero] at eb
  obtain ⟨y, rfl⟩ : ∃ y, i = B + y := ⟨i - B, by omega⟩
  conv => lhs; rw [← eb]
  rw [Nat.mul_comm, Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt (by omega),
    Nat.zero_add]

theorem pow_succ' (t : Nat) : 2 ^ (t + 1) = 2 ^ t + 2 ^ t := by rw [Nat.pow_succ]; omega

theorem modDvd (a t s : Nat) (h : t ≤ s) (ha : a % 2 ^ s = 0) : a % 2 ^ t = 0 :=
  Nat.mod_eq_zero_of_dvd (Nat.dvd_trans (Nat.pow_dvd_pow 2 h) (Nat.dvd_of_mod_eq_zero ha))

/-! ## The 0-1 principle -/

/-- **(lemma)**: a monotone map commutes with `min` and `max`. -/
theorem monoMinMax (g : Nat → Nat) (hg : ∀ a b, a ≤ b → g a ≤ g b) (a b : Nat) :
    g (min a b) = min (g a) (g b) ∧ g (max a b) = max (g a) (g b) := by
  rcases Nat.le_total a b with h | h
  · have := hg a b h
    rw [Nat.min_eq_left h, Nat.max_eq_right h, Nat.min_eq_left this, Nat.max_eq_right this]; simp
  · have := hg b a h
    rw [Nat.min_eq_right h, Nat.max_eq_left h, Nat.min_eq_right this, Nat.max_eq_left this]; simp

/-- **(lemma)**: a round commutes with a monotone map. -/
theorem rnd_comp (g : Nat → Nat) (hg : ∀ a b, a ≤ b → g a ≤ g b) (k j : Nat) (f : Nat → Nat) :
    rnd k j (g ∘ f) = g ∘ rnd k j f := by
  funext i
  simp only [rnd, Function.comp]
  split <;> split <;> simp [monoMinMax g hg]

theorem merge_comp (g : Nat → Nat) (hg : ∀ a b, a ≤ b → g a ≤ g b) (s : Nat) :
    ∀ (t : Nat) (f : Nat → Nat), merge s t (g ∘ f) = g ∘ merge s t f
  | 0, _ => rfl
  | t + 1, f => by simp only [merge, rnd_comp g hg, merge_comp g hg s t]

/-- **(lemma)**: the network commutes with every monotone map. -/
theorem net_comp (g : Nat → Nat) (hg : ∀ a b, a ≤ b → g a ≤ g b) :
    ∀ (m : Nat) (f : Nat → Nat), net m (g ∘ f) = g ∘ net m f
  | 0, _ => rfl
  | m + 1, f => by simp only [net, net_comp g hg m, merge_comp g hg]

/-- A 0-1 array. -/
def zo (f : Nat → Nat) : Prop := ∀ i, f i ≤ 1

theorem rnd_zo (k j : Nat) (f : Nat → Nat) (h : zo f) : zo (rnd k j f) := by
  intro i; have := h i; have := h (i ^^^ j)
  simp only [rnd]; split <;> split <;> omega

theorem merge_zo (s : Nat) : ∀ (t : Nat) (f : Nat → Nat), zo f → zo (merge s t f)
  | 0, _, h => h
  | t + 1, f, h => merge_zo s t _ (rnd_zo _ _ f h)

theorem net_zo : ∀ (m : Nat) (f : Nat → Nat), zo f → zo (net m f)
  | 0, _, h => h
  | m + 1, f, h => merge_zo _ _ _ (net_zo m f h)

/-! ## Permutation -/

/-- **(lemma)**: ordering each pair (a x, b x) either way permutes the two lists together. -/
theorem pairPerm (xs : List Nat) (a b lo hi : Nat → Nat)
    (h : ∀ x ∈ xs, (lo x = a x ∧ hi x = b x) ∨ (lo x = b x ∧ hi x = a x)) :
    (xs.map lo ++ xs.map hi).Perm (xs.map a ++ xs.map b) := by
  rw [List.perm_iff_count]; intro v
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have ih := ih (fun y hy => h y (List.mem_cons_of_mem _ hy))
    simp only [List.map_cons, List.cons_append, List.count_cons, List.count_append] at ih ⊢
    rcases h x (List.mem_cons_self) with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] <;> omega

/-- **(lemma)**: a round only swaps values within pairs, so on any whole number of aligned blocks
of 2^(t+1) it permutes the array. -/
theorem roundPerm (s t : Nat) (f : Nat → Nat) (hts : t < s) :
    ∀ (q P : Nat), P % 2 ^ (t + 1) = 0 →
      ((List.range' P (2 ^ (t + 1) * q)).map (rnd (2 ^ s) (2 ^ t) f)).Perm
        ((List.range' P (2 ^ (t + 1) * q)).map f)
  | 0, _, _ => by simp
  | q + 1, P, hP => by
    have hH := pow_succ' t
    have hsplit : List.range' P (2 ^ (t + 1) * (q + 1)) =
        List.range' P (2 ^ t) ++ List.range' (P + 2 ^ t) (2 ^ t) ++
          List.range' (P + 2 ^ (t + 1)) (2 ^ (t + 1) * q) := by
      rw [List.range'_append_1, show P + 2 ^ (t + 1) = P + (2 ^ t + 2 ^ t) by omega, List.range'_append_1]
      congr 1; rw [Nat.mul_succ]; omega
    rw [hsplit]; simp only [List.map_append]
    refine List.Perm.append ?_ (roundPerm s t f hts q _ (by rw [Nat.add_mod_right]; exact hP))
    rw [List.range'_eq_map_range, List.range'_eq_map_range,
      List.map_map, List.map_map, List.map_map, List.map_map]
    apply pairPerm
    intro x hx
    rw [List.mem_range] at hx
    have hlo : (P + x) % 2 ^ (t + 1) < 2 ^ t := by rw [modAligned P _ x hP (by omega)]; exact hx
    have hhi : 2 ^ t ≤ (P + 2 ^ t + x) % 2 ^ (t + 1) := by
      rw [Nat.add_assoc, modAligned P _ _ hP (by omega)]; omega
    simp only [Function.comp, rndLo s t f _ hlo, rndHi s t f _ hhi]
    rw [show P + 2 ^ t + x - 2 ^ t = P + x by omega, show P + x + 2 ^ t = P + 2 ^ t + x by omega]
    split
    · rcases Nat.le_total (f (P + x)) (f (P + 2 ^ t + x)) with h | h
      · left; exact ⟨Nat.min_eq_left h, Nat.max_eq_right h⟩
      · right; exact ⟨Nat.min_eq_right h, Nat.max_eq_left h⟩
    · rcases Nat.le_total (f (P + x)) (f (P + 2 ^ t + x)) with h | h
      · right; exact ⟨Nat.max_eq_right h, Nat.min_eq_left h⟩
      · left; exact ⟨Nat.max_eq_left h, Nat.min_eq_right h⟩

theorem rangePow (u m : Nat) (h : u + 1 ≤ m) : List.range (2 ^ m) = List.range' 0 (2 ^ (u + 1) * 2 ^ (m - (u + 1))) := by
  rw [← Nat.pow_add, Nat.add_sub_cancel' h, List.range_eq_range']

theorem mergePerm (m s : Nat) (hs : s ≤ m) :
    ∀ (t : Nat) (f : Nat → Nat), t ≤ s →
      ((List.range (2 ^ m)).map (merge s t f)).Perm ((List.range (2 ^ m)).map f)
  | 0, _, _ => List.Perm.refl _
  | t + 1, f, ht => by
    refine (mergePerm m s hs t _ (by omega)).trans ?_
    rw [rangePow t m (by omega)]
    exact roundPerm s t f (by omega) _ 0 (by simp)

/-- **(lemma)**: the network permutes the first 2^M values, for any M ≥ m. -/
theorem netPerm (M : Nat) : ∀ (m : Nat) (f : Nat → Nat), m ≤ M →
    ((List.range (2 ^ M)).map (net m f)).Perm ((List.range (2 ^ M)).map f)
  | 0, _, _ => List.Perm.refl _
  | m + 1, f, h =>
    (mergePerm M (m + 1) h (m + 1) _ (Nat.le_refl _)).trans (netPerm M m f (by omega))

/-! ## Bitonic 0-1 blocks and the half-cleaner -/

/-- The 0-1 indicator of [a, b). -/
def ind (a b x : Nat) : Nat := if a ≤ x ∧ x < b then 1 else 0

/-- A bitonic 0-1 block of length n (by offset): 0…01…10…0 or its complement 1…10…01…1. -/
def bitoOff (g : Nat → Nat) (n : Nat) : Prop :=
  ∃ a b, (∀ x < n, g x = ind a b x) ∨ (∀ x < n, g x = 1 - ind a b x)

theorem bitoOff_congr (g g' : Nat → Nat) (n : Nat) (h : ∀ x < n, g x = g' x) (hb : bitoOff g' n) :
    bitoOff g n := by
  obtain ⟨a, b, hb | hb⟩ := hb
  · exact ⟨a, b, Or.inl fun x hx => (h x hx).trans (hb x hx)⟩
  · exact ⟨a, b, Or.inr fun x hx => (h x hx).trans (hb x hx)⟩

theorem bitoOff_compl (g : Nat → Nat) (n : Nat) (hb : bitoOff g n) : bitoOff (fun x => 1 - g x) n := by
  obtain ⟨a, b, hb | hb⟩ := hb
  · exact ⟨a, b, Or.inr fun x hx => by show 1 - g x = _; rw [hb x hx]⟩
  · refine ⟨a, b, Or.inl fun x hx => ?_⟩
    show 1 - g x = _; rw [hb x hx]; unfold ind; split <;> rfl

/-- **(lemma)**: the half-cleaner on 0…01…10…0 (offsets [0, 2H)). The pairwise minima and maxima
of (x, H + x) are both bitonic, and every minimum is at most every maximum. -/
theorem halfClean0 (a b H : Nat) :
    bitoOff (fun x => min (ind a b x) (ind a b (H + x))) H ∧
    bitoOff (fun x => max (ind a b x) (ind a b (H + x))) H ∧
    ∀ x x', x < H → x' < H → min (ind a b x) (ind a b (H + x)) ≤ max (ind a b x') (ind a b (H + x')) := by
  refine ⟨⟨a, b - H, Or.inl fun x _ => ?_⟩, ?_, ?_⟩
  · simp only [ind]; (repeat' split) <;> omega
  · by_cases h1 : H ≤ a
    · exact ⟨a - H, b - H, Or.inl fun x _ => by simp only [ind]; (repeat' split) <;> omega⟩
    by_cases h2 : b ≤ H
    · exact ⟨a, b, Or.inl fun x _ => by simp only [ind]; (repeat' split) <;> omega⟩
    by_cases h3 : a ≤ b - H
    · exact ⟨0, H, Or.inl fun x _ => by simp only [ind]; (repeat' split) <;> omega⟩
    · exact ⟨b - H, a, Or.inr fun x _ => by simp only [ind]; (repeat' split) <;> omega⟩
  · intro x x' hx hx'
    simp only [ind]; (repeat' split) <;> omega

/-- **(lemma)**: the half-cleaner on any bitonic 0-1 block of 2H. -/
theorem halfClean (g : Nat → Nat) (H : Nat) (hb : bitoOff g (H + H)) :
    bitoOff (fun x => min (g x) (g (H + x))) H ∧
    bitoOff (fun x => max (g x) (g (H + x))) H ∧
    ∀ x x', x < H → x' < H → min (g x) (g (H + x)) ≤ max (g x') (g (H + x')) := by
  obtain ⟨a, b, hb | hb⟩ := hb
  · obtain ⟨h1, h2, h3⟩ := halfClean0 a b H
    have e : ∀ x < H, g x = ind a b x ∧ g (H + x) = ind a b (H + x) :=
      fun x hx => ⟨hb x (by omega), hb (H + x) (by omega)⟩
    refine ⟨bitoOff_congr _ _ H (fun x hx => by rw [(e x hx).1, (e x hx).2]) h1,
      bitoOff_congr _ _ H (fun x hx => by rw [(e x hx).1, (e x hx).2]) h2, fun x x' hx hx' => ?_⟩
    rw [(e x hx).1, (e x hx).2, (e x' hx').1, (e x' hx').2]; exact h3 x x' hx hx'
  · obtain ⟨h1, h2, h3⟩ := halfClean0 a b H
    have e : ∀ x < H, g x = 1 - ind a b x ∧ g (H + x) = 1 - ind a b (H + x) :=
      fun x hx => ⟨hb x (by omega), hb (H + x) (by omega)⟩
    have i1 : ∀ x, ind a b x ≤ 1 := fun x => by unfold ind; split <;> omega
    refine ⟨bitoOff_congr _ _ H (fun x hx => ?_) (bitoOff_compl _ H h2),
      bitoOff_congr _ _ H (fun x hx => ?_) (bitoOff_compl _ H h1), fun x x' hx hx' => ?_⟩
    · rw [(e x hx).1, (e x hx).2]; have := i1 x; have := i1 (H + x); omega
    · rw [(e x hx).1, (e x hx).2]; have := i1 x; have := i1 (H + x); omega
    · rw [(e x hx).1, (e x hx).2, (e x' hx').1, (e x' hx').2]
      have := h3 x' x hx' hx
      have := i1 x; have := i1 (H + x); have := i1 x'; have := i1 (H + x'); omega

/-- **(lemma)**: a nondecreasing 0-1 block is 0…01…1. -/
theorem monoInd (g : Nat → Nat) : ∀ n, (∀ x < n, g x ≤ 1) → (∀ x x', x < x' → x' < n → g x ≤ g x') →
    ∃ a, a ≤ n ∧ ∀ x < n, g x = ind a n x
  | 0, _, _ => ⟨0, Nat.le_refl _, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  | n + 1, hz, hm => by
    obtain ⟨a, ha, hg⟩ := monoInd g n (fun x hx => hz x (by omega)) (fun x x' h1 h2 => hm x x' h1 (by omega))
    have hn := hz n (by omega)
    by_cases h : g n = 1
    · refine ⟨a, by omega, fun x hx => ?_⟩
      rcases Nat.lt_or_ge x n with h' | h'
      · rw [hg x h']; simp only [ind]; (repeat' split) <;> omega
      · have : x = n := by omega
        subst this; simp only [ind]; (repeat' split) <;> omega
    · refine ⟨n + 1, Nat.le_refl _, fun x hx => ?_⟩
      rcases Nat.lt_or_ge x n with h' | h'
      · have := hm x n h' (by omega); simp only [ind]; (repeat' split) <;> omega
      · have : x = n := by omega
        subst this; simp only [ind]; (repeat' split) <;> omega

/-- **(lemma)**: a nonincreasing 0-1 block is 1…10…0. -/
theorem antiInd (g : Nat → Nat) : ∀ n, (∀ x < n, g x ≤ 1) → (∀ x x', x < x' → x' < n → g x' ≤ g x) →
    ∃ b, b ≤ n ∧ ∀ x < n, g x = ind 0 b x
  | 0, _, _ => ⟨0, Nat.le_refl _, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  | n + 1, hz, hm => by
    obtain ⟨b, hb, hg⟩ := antiInd g n (fun x hx => hz x (by omega)) (fun x x' h1 h2 => hm x x' h1 (by omega))
    have hn := hz n (by omega)
    by_cases h : g n = 0
    · refine ⟨b, by omega, fun x hx => ?_⟩
      rcases Nat.lt_or_ge x n with h' | h'
      · rw [hg x h']
      · have : x = n := by omega
        subst this; simp only [ind]; (repeat' split) <;> omega
    · refine ⟨n + 1, Nat.le_refl _, fun x hx => ?_⟩
      rcases Nat.lt_or_ge x n with h' | h'
      · have := hm x n h' (by omega); have := hz x (by omega); simp only [ind]; (repeat' split) <;> omega
      · have : x = n := by omega
        subst this; simp only [ind]; (repeat' split) <;> omega

/-! ## The stage invariants on 0-1 arrays -/

/-- After stage s: every aligned block of 2^s is sorted, ascending when its block number
B / 2^s is even and descending when odd. -/
def SB (s : Nat) (f : Nat → Nat) : Prop :=
  ∀ B, B % 2 ^ s = 0 → ∀ i i', B ≤ i → i < i' → i' < B + 2 ^ s →
    ((B / 2 ^ s) % 2 = 0 → f i ≤ f i') ∧ ((B / 2 ^ s) % 2 = 1 → f i' ≤ f i)

/-- During stage s, with the rounds down to 2^t still to run: inside every aligned block of 2^s,
each aligned sub-block of 2^t is bitonic, and the sub-blocks are in the block's order. -/
def MI (s t : Nat) (f : Nat → Nat) : Prop :=
  ∀ B, B % 2 ^ s = 0 →
    (∀ C, C % 2 ^ t = 0 → B ≤ C → C + 2 ^ t ≤ B + 2 ^ s → bitoOff (fun x => f (C + x)) (2 ^ t)) ∧
    (∀ C C', C % 2 ^ t = 0 → C' % 2 ^ t = 0 → B ≤ C → C < C' → C' + 2 ^ t ≤ B + 2 ^ s →
      ∀ x x', x < 2 ^ t → x' < 2 ^ t →
        ((B / 2 ^ s) % 2 = 0 → f (C + x) ≤ f (C' + x')) ∧ ((B / 2 ^ s) % 2 = 1 → f (C' + x') ≤ f (C + x)))

/-- **(lemma)**: an aligned sub-block of H is the lower or upper half of an aligned block of 2H
inside the same enclosing block. -/
theorem subParent (H N B C : Nat) (hH : 0 < H) (hBM : B % (H + H) = 0)
    (hNM : N % (H + H) = 0) (hC : C % H = 0) (h1 : B ≤ C) (h2 : C + H ≤ B + N) :
    ∃ P, P % (H + H) = 0 ∧ B ≤ P ∧ P + (H + H) ≤ B + N ∧ (C = P ∨ C = P + H) := by
  have hr : C % (H + H) = 0 ∨ C % (H + H) = H := by
    have e1 : C % (H + H) % H = 0 := by
      rw [Nat.mod_mod_of_dvd _ ⟨2, by omega⟩]; exact hC
    have e2 : C % (H + H) < H + H := Nat.mod_lt _ (by omega)
    have e3 := Nat.div_add_mod (C % (H + H)) H
    rw [e1, Nat.add_zero] at e3
    have e4 : C % (H + H) / H < 2 := by
      rcases Nat.lt_or_ge (C % (H + H) / H) 2 with h | h
      · exact h
      · have := Nat.mul_le_mul_left H h; omega
    generalize C % (H + H) / H = k at e3 e4
    match k, e4 with
    | 0, _ => left; simp at e3; omega
    | 1, _ => right; simp at e3; omega
  have hmod := Nat.mod_lt C (show 0 < H + H by omega)
  have hP : (C - C % (H + H)) % (H + H) = 0 := Nat.sub_mod_eq_zero_of_mod_eq (by rw [Nat.mod_mod])
  have hle := Nat.mod_le C (H + H)
  refine ⟨C - C % (H + H), hP, ?_, ?_, by omega⟩
  · rcases Nat.lt_or_ge (C - C % (H + H)) B with h | h
    · have := alignedLt _ _ _ hP hBM h; have := Nat.mod_le C (H + H); omega
    · exact h
  · have hBN : (B + N) % (H + H) = 0 := by rw [Nat.add_mod, hBM, hNM]; simp
    exact alignedLt _ _ _ hP hBN (by have := Nat.mod_le C (H + H); omega)

/-- **(lemma)**: one round on an aligned pair-block [P, P + 2H) inside an enclosing block of
2^s: lower positions get the minimum (ascending block) or maximum, upper ones the other. -/
theorem pairVals (s t : Nat) (f : Nat → Nat) (B P : Nat) (hB : B % 2 ^ s = 0)
    (hP : P % 2 ^ (t + 1) = 0) (h1 : B ≤ P) (h2 : P + 2 ^ (t + 1) ≤ B + 2 ^ s) (x : Nat) (hx : x < 2 ^ t) :
    rnd (2 ^ s) (2 ^ t) f (P + x) =
      (if (B / 2 ^ s) % 2 = 0 then min (f (P + x)) (f (P + (2 ^ t + x))) else max (f (P + x)) (f (P + (2 ^ t + x)))) ∧
    rnd (2 ^ s) (2 ^ t) f (P + (2 ^ t + x)) =
      (if (B / 2 ^ s) % 2 = 0 then max (f (P + x)) (f (P + (2 ^ t + x))) else min (f (P + x)) (f (P + (2 ^ t + x)))) := by
  have hM := pow_succ' t
  have hlo : (P + x) % 2 ^ (t + 1) < 2 ^ t := by rw [modAligned P _ x hP (by omega)]; exact hx
  have hhi : 2 ^ t ≤ (P + (2 ^ t + x)) % 2 ^ (t + 1) := by rw [modAligned P _ _ hP (by omega)]; omega
  have d1 : (P + x) / 2 ^ s = B / 2 ^ s := divSame _ B _ hB (by omega) (by omega)
  refine ⟨?_, ?_⟩
  · rw [rndLo s t f _ hlo, d1, show P + x + 2 ^ t = P + (2 ^ t + x) by omega]
  · rw [rndHi s t f _ hhi, show P + (2 ^ t + x) - 2 ^ t = P + x by omega, d1]

theorem minMaxOne (d : Prop) [Decidable d] (a b : Nat) :
    ((if d then min a b else max a b) = a ∨ (if d then min a b else max a b) = b) ∧
    ((if d then max a b else min a b) = a ∨ (if d then max a b else min a b) = b) := by
  constructor <;> split <;> omega

/-- **(lemma)**: one round of stage s keeps the stage invariant, one level down. -/
theorem miStep (s t : Nat) (f : Nat → Nat) (hts : t < s) (h : MI s (t + 1) f) :
    MI s t (rnd (2 ^ s) (2 ^ t) f) := by
  intro B hB
  obtain ⟨ha, hb⟩ := h B hB
  have hH := Nat.two_pow_pos t
  have hM := pow_succ' t
  have hBM : B % (2 ^ t + 2 ^ t) = 0 := hM ▸ modDvd B (t + 1) s hts hB
  have hNM : 2 ^ s % (2 ^ t + 2 ^ t) = 0 := hM ▸ modDvd (2 ^ s) (t + 1) s hts (Nat.mod_self _)
  -- every sub-block's parent, and the values a round leaves in it
  have view : ∀ C, C % 2 ^ t = 0 → B ≤ C → C + 2 ^ t ≤ B + 2 ^ s →
      ∃ P, P % 2 ^ (t + 1) = 0 ∧ B ≤ P ∧ P + 2 ^ (t + 1) ≤ B + 2 ^ s ∧ (C = P ∨ C = P + 2 ^ t) := by
    intro C hC h1 h2
    obtain ⟨P, a, b, c, d⟩ := subParent (2 ^ t) (2 ^ s) B C hH hBM hNM hC h1 h2
    exact ⟨P, hM ▸ a, b, hM ▸ c, d⟩
  have valIn : ∀ P, P % 2 ^ (t + 1) = 0 → B ≤ P → P + 2 ^ (t + 1) ≤ B + 2 ^ s →
      ∀ C, (C = P ∨ C = P + 2 ^ t) → ∀ x < 2 ^ t,
        ∃ y < 2 ^ (t + 1), rnd (2 ^ s) (2 ^ t) f (C + x) = f (P + y) := by
    intro P hP h1 h2 C hC x hx
    obtain ⟨v1, v2⟩ := pairVals s t f B P hB hP h1 h2 x hx
    obtain ⟨o1, o2⟩ := minMaxOne ((B / 2 ^ s) % 2 = 0) (f (P + x)) (f (P + (2 ^ t + x)))
    rcases hC with rfl | rfl
    · rw [v1]; rcases o1 with e | e
      · exact ⟨x, by omega, e⟩
      · exact ⟨2 ^ t + x, by omega, e⟩
    · rw [Nat.add_assoc, v2]; rcases o2 with e | e
      · exact ⟨x, by omega, e⟩
      · exact ⟨2 ^ t + x, by omega, e⟩
  refine ⟨fun C hC h1 h2 => ?_, fun C C' hC hC' h1 h12 h2 x x' hx hx' => ?_⟩
  · obtain ⟨P, hP, p1, p2, hCP⟩ := view C hC h1 h2
    have hbito := ha P (hP) p1 p2
    rw [hM] at hbito
    obtain ⟨c1, c2, _⟩ := halfClean (fun y => f (P + y)) (2 ^ t) hbito
    have v := fun x hx => pairVals s t f B P hB hP p1 p2 x hx
    rcases hCP with rfl | rfl
    · by_cases d : (B / 2 ^ s) % 2 = 0
      · exact bitoOff_congr _ _ _ (fun x hx => by simp only [(v x hx).1, d, ↓reduceIte]) c1
      · exact bitoOff_congr _ _ _ (fun x hx => by simp only [(v x hx).1, d, ↓reduceIte]) c2
    · by_cases d : (B / 2 ^ s) % 2 = 0
      · exact bitoOff_congr _ _ _ (fun x hx => by simp only [Nat.add_assoc, (v x hx).2, d, ↓reduceIte]) c2
      · exact bitoOff_congr _ _ _ (fun x hx => by simp only [Nat.add_assoc, (v x hx).2, d, ↓reduceIte]) c1
  · obtain ⟨P, hP, p1, p2, hCP⟩ := view C hC h1 (by omega)
    obtain ⟨P', hP', p1', p2', hCP'⟩ := view C' hC' (by omega) h2
    by_cases hPP : P = P'
    · rw [← hPP] at hCP'
      have e1 : C = P := by omega
      have e2 : C' = P + 2 ^ t := by omega
      rw [e1, e2]
      have hbito := ha P hP p1 p2
      rw [hM] at hbito
      obtain ⟨_, _, c3⟩ := halfClean (fun y => f (P + y)) (2 ^ t) hbito
      rw [(pairVals s t f B P hB hP p1 p2 x hx).1, Nat.add_assoc,
        (pairVals s t f B P hB hP p1 p2 x' hx').2]
      have k1 := c3 x x' hx hx'
      have k2 := c3 x' x hx' hx
      constructor <;> intro d
      · simp only [d, ↓reduceIte]; exact k1
      · simp only [d, show ¬ (1 = 0) from by decide, ↓reduceIte]; exact k2
    · have hlt : P < P' := by
        rcases Nat.lt_or_ge P P' with h | h
        · exact h
        · have : P' < P := by omega
          have := alignedLt _ _ _ hP' hP this; omega
      obtain ⟨y, hy, ey⟩ := valIn P hP p1 p2 C hCP x hx
      obtain ⟨y', hy', ey'⟩ := valIn P' hP' p1' p2' C' hCP' x' hx'
      rw [ey, ey']
      exact hb P P' hP hP' p1 hlt p2' y y' hy hy'

/-- **(lemma)**: the stage invariant at its start, from the previous stage's sorted blocks. -/
theorem miInit (s : Nat) (f : Nat → Nat) (hz : zo f) (h : SB s f) : MI (s + 1) (s + 1) f := by
  intro B hB
  have hH := Nat.two_pow_pos s
  have hM := pow_succ' s
  refine ⟨fun C hC h1 h2 => ?_, fun C C' _ _ h1 h12 h2 _ _ _ _ => by omega⟩
  have hCB : C = B := by omega
  subst hCB
  -- the lower half is ascending, the upper half descending
  obtain ⟨q, hq⟩ : ∃ q, C = (2 ^ s + 2 ^ s) * q := ⟨C / 2 ^ (s + 1), by
    have := Nat.div_add_mod C (2 ^ (s + 1)); rw [hB] at this; rw [← hM]; omega⟩
  have hd0 : C / 2 ^ s = 2 * q := by
    rw [hq, show (2 ^ s + 2 ^ s) * q = 2 ^ s * (2 * q) by rw [← Nat.mul_assoc]; congr 1; omega,
      Nat.mul_div_cancel_left _ hH]
  have hd1 : (C + 2 ^ s) / 2 ^ s = 2 * q + 1 := by
    rw [hq, show (2 ^ s + 2 ^ s) * q + 2 ^ s = 2 ^ s * (2 * q + 1) by
      rw [Nat.mul_add, ← Nat.mul_assoc, Nat.mul_one]; congr 1; congr 1; omega,
      Nat.mul_div_cancel_left _ hH]
  have hm0 : C % 2 ^ s = 0 := modDvd C s (s + 1) (by omega) hB
  have hm1 : (C + 2 ^ s) % 2 ^ s = 0 := by rw [Nat.add_mod_right]; exact hm0
  obtain ⟨a, ha, ea⟩ := monoInd (fun x => f (C + x)) (2 ^ s) (fun x _ => hz _) (fun x x' h1 h2 =>
    ((h C hm0 (C + x) (C + x') (by omega) (by omega) (by omega)).1 (by rw [hd0]; omega)))
  obtain ⟨b, hb, eb⟩ := antiInd (fun y => f (C + 2 ^ s + y)) (2 ^ s) (fun x _ => hz _) (fun y y' h1 h2 =>
    ((h (C + 2 ^ s) hm1 (C + 2 ^ s + y) (C + 2 ^ s + y') (by omega) (by omega) (by omega)).2
      (by rw [hd1]; omega)))
  refine ⟨a, 2 ^ s + b, Or.inl fun x hx => ?_⟩
  rw [hM] at hx
  show f (C + x) = _
  rcases Nat.lt_or_ge x (2 ^ s) with hx' | hx'
  · have := ea x hx'; rw [this]; simp only [ind]; (repeat' split) <;> omega
  · have := eb (x - 2 ^ s) (by omega)
    rw [show C + x = C + 2 ^ s + (x - 2 ^ s) by omega, this]; simp only [ind]; (repeat' split) <;> omega

theorem miMerge (s : Nat) : ∀ (t : Nat) (f : Nat → Nat), t ≤ s → zo f → MI s t f → MI s 0 (merge s t f)
  | 0, _, _, _, h => h
  | t + 1, f, ht, hz, h => miMerge s t _ (by omega) (rnd_zo _ _ f hz) (miStep s t f (by omega) h)

theorem miDone (s : Nat) (f : Nat → Nat) (h : MI s 0 f) : SB s f := by
  intro B hB i i' h1 h2 h3
  have := (h B hB).2 i i' (Nat.mod_one _) (Nat.mod_one _) h1 h2 (by simp; omega) 0 0 (by simp) (by simp)
  simpa using this

/-- **(lemma)**: on 0-1 input, after stage m every aligned block of 2^m is sorted in its direction. -/
theorem netSB : ∀ (m : Nat) (f : Nat → Nat), zo f → SB m (net m f)
  | 0, _, _ => fun B _ i i' h1 h2 h3 => by simp at h3; omega
  | m + 1, f, hz => miDone _ _ (miMerge (m + 1) (m + 1) _ (Nat.le_refl _) (net_zo m f hz)
      (miInit m _ (net_zo m f hz) (netSB m f hz)))

/-- **(lemma)**: the network sorts the first 2^m values of every input (the 0-1 principle). -/
theorem netSorted (m : Nat) (f : Nat → Nat) (i i' : Nat) (h1 : i < i') (h2 : i' < 2 ^ m) :
    net m f i ≤ net m f i' := by
  rcases Nat.lt_or_ge (net m f i') (net m f i) with h | h
  · exfalso
    let g : Nat → Nat := fun v => if net m f i ≤ v then 1 else 0
    have hg : ∀ a b, a ≤ b → g a ≤ g b := fun a b hab => by
      simp only [g]; (repeat' split) <;> omega
    have hz : zo (g ∘ f) := fun j => by simp only [Function.comp, g]; split <;> omega
    have hs := (netSB m (g ∘ f) hz 0 (by simp) i i' (by omega) h1 (by omega)).1 (by simp)
    rw [net_comp g hg] at hs
    simp only [Function.comp, g] at hs
    split at hs <;> split at hs <;> omega
  · exact h

/-! ## The alternative sort -/

/-- **(lemma)**: the padded load, as a list. -/
theorem padList (m : Nat) (xs : List Nat) (h : xs.length ≤ 2 ^ m) :
    (List.range (2 ^ m)).map (padF xs) = xs ++ List.replicate (2 ^ m - xs.length) 0xFFFFFFFF := by
  apply List.ext_getElem
  · simp; omega
  · intro i h1 h2
    simp only [List.getElem_map, List.getElem_range, padF, List.getElem_append]
    split
    · simp [List.getD_eq_getElem?_getD, *]
    · next hi => simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_of_not_lt hi)]

/-- **R-15** (T-07, T-16): the alternative sort, run as the kernel runs it — load and pad with
`0xFFFFFFFF` to P = 2^m ≥ ℓ, the bitonic network with the kernel's own `i ^ j` pairing and
`(i & k) == 0` direction, write back the first ℓ values — returns the sequence sorted, for every
ℓ ≤ P and every input of 32-bit keys. Not a re-reading of `net`: the network never compares more
than two values at a time, and this says those comparisons sort. -/
theorem bitonicSorts (m : Nat) (xs : List Nat) (hlen : xs.length ≤ 2 ^ m)
    (hx : ∀ x ∈ xs, x ≤ 0xFFFFFFFF) : bitonicAltSort m xs = xs.mergeSort leB := by
  have hsorted : ((List.range (2 ^ m)).map (net m (padF xs))).Pairwise (· ≤ ·) := by
    rw [List.pairwise_map]
    exact List.pairwise_lt_range.imp_of_mem fun ha hb hab =>
      netSorted m _ _ _ hab (List.mem_range.1 hb)
  have hperm := netPerm m m (padF xs) (Nat.le_refl _)
  rw [padList m xs hlen] at hperm
  have e := sortedPermUnique _ _ hsorted (mergeSortSorted _)
    (hperm.trans (List.mergeSort_perm _ _).symm)
  rw [bitonicAltSort, e, ← altSortCorrect (2 ^ m) xs hx]
  rfl

/-- **(lemma)**: the kernel's P (the least power of two ≥ ℓ) is a valid choice of m for every ℓ. -/
theorem powAtLeast (l : Nat) : ∃ m, l ≤ 2 ^ m := ⟨l, Nat.le_of_lt Nat.lt_two_pow_self⟩

end GpuQuicksortSpec.GpuQuicksort.Bitonic
