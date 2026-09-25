import GpuQuicksortProof.GpuQuicksort.Spec
import GpuQuicksortProof.GpuQuicksort.Model.Gen

/-!
# GpuQuicksortProof.GpuQuicksort.Theorems.Gen
=============================================

The generators: the transcribed MT19937 is the standard engine (its 10000th output from the
default seed is the value the C++ standard pins), and every distribution's key values are the
spec model's C-08 formulas on the engine's draws, hence in [0, 2^31), with no 64-bit overflow.
-/

namespace GpuQuicksort.Theorems

open GpuQuicksort.Model
open GpuQuicksortSpec.GpuQuicksort.Model (uniformV bucketV staggeredV gaussianV)

/-- **(lemma)**: the transcribed engine is MT19937: from the default seed 5489, its first output
is 3499211612 and its 10000th is 4123659995, the value the C++ standard requires of
`std::mt19937` ([rand.predef]). Checked by evaluation (`native_decide`). -/
theorem mtStandard : mtStream 5489 0 = 3499211612 ∧ mtStream 5489 9999 = 4123659995 := by
  native_decide

theorem uDrawMod (a e r : Nat) : uDraw a (2 ^ e) r = a + r % 2 ^ e := by
  simp [uDraw, Nat.and_two_pow_sub_one_eq_mod]

/-- **C-08, R-20** (T-25, T-26): `Distribution.generate`'s key values are exactly the spec's C-08
formulas on the engine's draws — `uniform`, `sorted` (the uniform values sorted), `zero` (one draw
repeated), `bucket`, `gaussian` (four consecutive draws per element) and `staggered` (D-07) — for
every draw stream, so every value lies in [0, 2^31) and converts to `UInt32` exactly; the 64-bit
intermediates `k·p·p` and the four-draw sum stay far below 2^64 for n ≤ 2^31. With the engine above
(`mtStandard`), a given (distribution, n, seed) always yields the same values. -/
theorem genSpec (n : Nat) (r : Nat → Nat) :
    genV .uniform n r = (List.range n).map (fun k => uniformV (r k)) ∧
    genV .sorted n r = ((List.range n).map (fun k => uniformV (r k))).mergeSort GpuQuicksortSpec.GpuQuicksort.Model.leB ∧
    genV .zero n r = (if 0 < n then List.replicate n (uniformV (r 0)) else []) ∧
    genV .bucket n r = (List.range n).map (fun k => bucketV k n (r k)) ∧
    genV .gaussian n r = (List.range n).map (fun k => gaussianV (r (4 * k)) (r (4 * k + 1)) (r (4 * k + 2)) (r (4 * k + 3))) ∧
    genV .staggered n r = (List.range n).map (fun k => staggeredV k n (r k)) ∧
    (∀ d, d ≠ .fullrange → ∀ v ∈ genV d n r, v < 2 ^ 31) ∧
    (n ≤ 2 ^ 31 → ∀ k < n, k * genP * genP < 2 ^ 64 ∧ ∀ a b c e : Nat, a < 2 ^ 31 → b < 2 ^ 31 → c < 2 ^ 31 →
      e < 2 ^ 31 → a + b + c + e < 2 ^ 64) := by
  have hu : ∀ x, uDraw 0 (2 ^ 31) x = uniformV x := fun x => by rw [uDrawMod]; simp [uniformV]
  have e1 : genV .uniform n r = (List.range n).map (fun k => uniformV (r k)) := by
    simp only [genV, hu]
  have e2 : genV .bucket n r = (List.range n).map (fun k => bucketV k n (r k)) := by
    simp only [genV, bucketV, genP, genW, GpuQuicksortSpec.GpuQuicksort.Spec.distP,
      GpuQuicksortSpec.GpuQuicksort.Spec.distW, uDrawMod]
  have e3 : genV .gaussian n r = (List.range n).map (fun k => gaussianV (r (4 * k)) (r (4 * k + 1)) (r (4 * k + 2)) (r (4 * k + 3))) := by
    simp only [genV, hu, gaussianV]
  have e4 : genV .staggered n r = (List.range n).map (fun k => staggeredV k n (r k)) := by
    simp only [genV, staggeredV, genP, genW, GpuQuicksortSpec.GpuQuicksort.Spec.distP,
      GpuQuicksortSpec.GpuQuicksort.Spec.distW, uDrawMod]
    apply List.map_congr_left; intro k _; split <;> next h => simp [h]
  have e5 : genV .sorted n r = ((List.range n).map (fun k => uniformV (r k))).mergeSort GpuQuicksortSpec.GpuQuicksort.Model.leB := by
    simp only [genV, hu]
  have e6 : genV .zero n r = (if 0 < n then List.replicate n (uniformV (r 0)) else []) := by
    simp only [genV, hu]
  refine ⟨e1, e5, e6, e2, e3, e4, fun d hd v hv => ?_, fun _ k hk => ⟨?_, fun a b c e ha hb hc he => by omega⟩⟩
  · have rng := fun k (hk : k < n) => GpuQuicksortSpec.GpuQuicksort.Theorems.distRange k n (r k) (r (4 * k + 1))
      (r (4 * k + 2)) (r (4 * k + 3)) hk
    cases d with
    | uniform => rw [e1] at hv; obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hv; exact (rng k (List.mem_range.1 hk)).1
    | sorted =>
      rw [e5] at hv
      obtain ⟨k, hk, rfl⟩ := List.mem_map.1 ((List.mergeSort_perm _ _).subset hv)
      exact (rng k (List.mem_range.1 hk)).1
    | zero =>
      rw [e6] at hv; split at hv
      · rw [List.eq_of_mem_replicate hv]; exact (rng 0 (by omega)).1
      · simp at hv
    | bucket => rw [e2] at hv; obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hv; exact (rng k (List.mem_range.1 hk)).2.1
    | gaussian =>
      rw [e3] at hv; obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hv
      exact (GpuQuicksortSpec.GpuQuicksort.Theorems.distRange k n (r (4 * k)) (r (4 * k + 1)) (r (4 * k + 2))
        (r (4 * k + 3)) (List.mem_range.1 hk)).2.2.2
    | staggered => rw [e4] at hv; obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hv; exact (rng k (List.mem_range.1 hk)).2.2.1
    | fullrange => exact absurd rfl hd
  · simp only [genP]; omega

end GpuQuicksort.Theorems
