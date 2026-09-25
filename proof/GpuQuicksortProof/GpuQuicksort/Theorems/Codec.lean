import GpuQuicksortProof.GpuQuicksort.Spec
import GpuQuicksortProof.GpuQuicksort.Model.Codec
import Std.Tactic.BVDecide

/-!
# GpuQuicksortProof.GpuQuicksort.Theorems.Codec
===============================================

The codec as the code computes it equals the spec's C-04 codes: the MSL kernels and the Swift
functions, bit for bit on all 2^32 patterns, and the host dispatch over the whole buffer (the
grid-stride loop reaches every index below n exactly once). The spec model's theorems
(`int32CodeOrder`, `float32CodeOrder`, the round trips) then hold for the code.
-/

namespace GpuQuicksort.Theorems

open GpuQuicksort.Model
open GpuQuicksortSpec.GpuQuicksort.Spec (signMask)
open GpuQuicksortSpec.GpuQuicksort.Model (encI decI encF decF)

/-- The spec's C-04 code for a key type (identity for `uint32`). -/
def specCode : KeyType → Bool → BitVec 32 → BitVec 32
  | .uint32, _ => id
  | .int32, true => encI
  | .int32, false => decI
  | .float32, true => encF
  | .float32, false => decF

/-! ## The grid-stride loop -/

/-- **(lemma)**: one thread's grid-stride loop visits exactly start, start + step, … below n. -/
theorem strideMem (step n : Nat) (h : 0 < step) (i : Nat) :
    ∀ s, i ∈ strideFrom s step n h ↔ s ≤ i ∧ i < n ∧ (i - s) % step = 0 := by
  intro s
  induction s using strideFrom.induct step n h with
  | case1 s hs ih =>
    rw [strideFrom]; simp only [hs, ↓reduceIte, List.mem_cons, ih]
    constructor
    · rintro (rfl | ⟨h1, h2, h3⟩)
      · simp; omega
      · refine ⟨by omega, h2, ?_⟩
        rw [show i - s = (i - (s + step)) + step by omega, Nat.add_mod_right]; exact h3
    · rintro ⟨h1, h2, h3⟩
      by_cases he : i = s
      · exact Or.inl he
      · right
        by_cases hlt : i < s + step
        · rw [Nat.mod_eq_of_lt (by omega)] at h3; omega
        · refine ⟨by omega, h2, ?_⟩
          rw [show i - s = (i - (s + step)) + step by omega, Nat.add_mod_right] at h3; exact h3
  | case2 s hs =>
    rw [strideFrom]; simp only [hs, ↓reduceIte]; simp; omega

theorem strideNodup (step n : Nat) (h : 0 < step) : ∀ s, (strideFrom s step n h).Nodup := by
  intro s
  induction s using strideFrom.induct step n h with
  | case1 s hs ih =>
    rw [strideFrom]; simp only [hs, ↓reduceIte, List.nodup_cons]
    exact ⟨fun hm => by have := (strideMem step n h s (s + step)).1 hm; omega, ih⟩
  | case2 s hs => rw [strideFrom]; simp only [hs, ↓reduceIte]; exact List.nodup_nil

theorem sumIndicator (c : Nat) : ∀ g, ((List.range g).map (fun x => if x = c then 1 else 0)).sum =
    if c < g then 1 else 0
  | 0 => by simp
  | g + 1 => by
    rw [List.range_succ, List.map_append, List.sum_append, sumIndicator c g]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    by_cases h1 : c < g
    · have : ¬ g = c := by omega
      simp [h1, this]; omega
    · by_cases h2 : g = c
      · subst h2; simp
      · have : ¬ c < g + 1 := by omega
        simp [h1, h2, this]

/-- **(lemma)** (R-05 for the codec kernels): the grid of gsize threads, each striding by gsize from
its own index, visits every index below n exactly once and no other. -/
theorem gridCount (g n : Nat) (h : 0 < g) (i : Nat) :
    (gridVisits g n h).count i = if i < n then 1 else 0 := by
  rw [gridVisits, List.count_flatMap]
  have e : ∀ gid ∈ List.range g, (List.count i ∘ fun gid => strideFrom gid g n h) gid =
      if gid = (if i < n then i % g else g) then 1 else 0 := by
    intro gid hgid
    rw [List.mem_range] at hgid
    simp only [Function.comp, (strideNodup g n h gid).count, strideMem]
    have key : gid ≤ i ∧ (i - gid) % g = 0 ↔ gid = i % g := by
      have ediv := Nat.div_add_mod i g
      constructor
      · rintro ⟨h1, h2⟩
        have e2 := Nat.div_add_mod (i - gid) g
        rw [h2, Nat.add_zero] at e2
        have : i = gid + g * ((i - gid) / g) := by omega
        rw [this, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hgid]
      · rintro rfl
        refine ⟨Nat.mod_le _ _, ?_⟩
        rw [show i - i % g = g * (i / g) by omega, Nat.mul_mod_right]
    by_cases hn : i < n
    · simp only [hn, true_and, ↓reduceIte]
      by_cases hk : gid ≤ i ∧ (i - gid) % g = 0
      · have e := key.1 hk
        simp only [hk]; simp [e]
      · have : ¬ gid = i % g := fun e => hk (key.2 e)
        simp only [hk, this, ↓reduceIte]
    · have : ¬ gid = g := by omega
      simp only [hn, false_and, and_false, ↓reduceIte, this]
  rw [List.map_congr_left e, sumIndicator]
  by_cases hn : i < n
  · simp [hn, Nat.mod_lt _ h]
  · simp [hn]

theorem gridPerm (g n : Nat) (h : 0 < g) : (gridVisits g n h).Perm (List.range n) := by
  rw [List.perm_iff_count]; intro i
  rw [gridCount, List.nodup_range.count]; simp only [List.mem_range]

theorem gridNodup (g n : Nat) (h : 0 < g) : (gridVisits g n h).Nodup :=
  (gridPerm g n h).nodup_iff.2 List.nodup_range

theorem gridMem (g n : Nat) (h : 0 < g) (i : Nat) : i ∈ gridVisits g n h ↔ i < n := by
  rw [← List.count_pos_iff, gridCount]; split <;> simp_all

/-- **(lemma)**: a kernel over distinct indices writes f(old value) at each visited index and
leaves every other index alone. -/
theorem runKernelAt (f : BitVec 32 → BitVec 32) :
    ∀ (vs : List Nat) (d : Nat → BitVec 32), vs.Nodup →
      ∀ j, runKernel f vs d j = if j ∈ vs then f (d j) else d j
  | [], d, _, j => by simp [runKernel]
  | i :: rest, d, hnd, j => by
    rw [List.nodup_cons] at hnd
    have ih := runKernelAt f rest (upd d i (f (d i))) hnd.2 j
    simp only [runKernel, List.foldl_cons] at ih ⊢
    by_cases hj : j ∈ rest
    · have : j ≠ i := fun e => hnd.1 (e ▸ hj)
      simp [ih, hj, this, upd]
    · by_cases he : j = i
      · subst he; simp [ih, hj, upd]
      · simp [ih, hj, he, upd]

/-! ## The codes -/

/-- **(lemma)**: the MSL helpers compute the spec's codes for both GPU key types. -/
theorem mslIsSpec (key : KeyType) (hk : key ≠ .uint32) (enc : Bool) (b : BitVec 32) :
    (if enc then mslEncode b (codecID key) else mslDecode b (codecID key)) = specCode key enc b := by
  cases key <;> cases enc <;> simp_all [specCode, codecID, mslEncode, mslDecode, encI, decI, encF, decF,
    signMask] <;> bv_decide

/-- **(lemma)** (CPU reference, `CPUReference.swift`): the Swift codec computes the spec's codes
for all three key types. -/
theorem swiftIsSpec (key : KeyType) (b : BitVec 32) :
    swiftEncode b key = specCode key true b ∧ swiftDecode b key = specCode key false b := by
  cases key <;> simp [specCode, swiftEncode, swiftDecode, encI, decI, encF, decF, signMask] <;>
    constructor <;> bv_decide

/-- **C-04** (T-05): the host codec pass, as `Sorter.codec` dispatches it, replaces each of the n
keys in the caller's buffer by its spec C-04 code (identity for `uint32`) and touches nothing
else — for every buffer, n and key type. -/
theorem hostCodecIsSpec (d : Nat → BitVec 32) (n : Nat) (key : KeyType) (enc : Bool) (j : Nat) :
    hostCodec d n key enc j = if j < n then specCode key enc (d j) else d j := by
  unfold hostCodec
  split
  · next h =>
    rw [runKernelAt _ _ _ (gridNodup _ _ _)]
    simp only [gridMem]
    split
    · exact mslIsSpec key h.1 enc (d j)
    · rfl
  · next h =>
    by_cases hj : j < n
    · cases key
      · simp [hj, specCode]
      · exact absurd ⟨by decide, by omega⟩ h
      · exact absurd ⟨by decide, by omega⟩ h
    · simp [hj]

/-- **E-14, E-11** (T-05, T-23): decoding after encoding restores the caller's buffer bit for bit
— every NaN payload, ±0, ±∞ and subnormal — for every key type, including a key type other than
the one the bytes were written as. -/
theorem hostCodecRoundTrip (d : Nat → BitVec 32) (n : Nat) (key : KeyType) (j : Nat) :
    hostCodec (hostCodec d n key true) n key false j = d j := by
  rw [hostCodecIsSpec]
  split
  · next hj =>
    rw [hostCodecIsSpec]; simp only [hj, ↓reduceIte]
    cases key <;> simp [specCode, encI, decI, encF, decF, signMask] <;> bv_decide
  · next hj => rw [hostCodecIsSpec]; simp only [hj, ↓reduceIte]

end GpuQuicksort.Theorems
