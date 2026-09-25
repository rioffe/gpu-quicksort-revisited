import GpuQuicksortProof.GpuQuicksort.Spec

/-!
# GpuQuicksortProof.GpuQuicksort.Model.Gen
==========================================

Transcription of `Sources/GPUQuicksort/Distributions.swift`: the MT19937 engine and the key values
of `Distribution.generate`.

## Correspondence

| Source | Model |
| ------ | ----- |
| `:2-5` `MT19937` state (624 words, index) | `MT` (`UInt32` words, as in Swift) |
| `:7-12` `init(seed:)` (`init_genrand`, wrapping `&*`, `&+`) | `mtInit` |
| `:14-32` `next()`: twist when idx ≥ 624 (in place), tempering | `mtNext` |
| successive `rng.next()` calls | `mtStream seed j`, the j-th output |
| `:44` `u(a, len) = a + (UInt64(rng.next()) & (len - 1))` | `uDraw` |
| `:48-78` the per-distribution loops, draws consumed in element order | `genV` (draw `r j` is the j-th `next()`: one per element, one at the start for `zero`, four per element for `gaussian`) |
| `:60` `v.sort()` | `List.mergeSort` |
| `:74-77` `Float(v[k]).bitPattern` for `float32` | not modeled (Float rounding of an integer; T-25, T-26 check the bytes) |
-/

namespace GpuQuicksort.Model

/-- `Distributions.swift:2-5` — the engine: 624 words and the next index. -/
structure MT where
  mt : Array UInt32
  idx : Nat

/-- `:7-12` — `mt[0] = seed; mt[i] = 1812433253 &* (mt[i−1] ^ (mt[i−1] >> 30)) &+ i`. -/
def mtInit (seed : UInt32) : MT :=
  let a := (List.range' 1 623).foldl (fun (a : Array UInt32) i =>
    let prev := a[i - 1]!
    a.push ((1812433253 : UInt32) * (prev ^^^ (prev >>> (30 : UInt32))) + i.toUInt32)) #[seed]
  ⟨a, 624⟩

/-- `:16-24` — the in-place twist of all 624 words. -/
def mtTwist (a : Array UInt32) : Array UInt32 :=
  (List.range 624).foldl (fun (a : Array UInt32) i =>
    let y : UInt32 := (a[i]! &&& (0x80000000 : UInt32)) ||| (a[(i + 1) % 624]! &&& (0x7FFFFFFF : UInt32))
    let v : UInt32 := a[(i + 397) % 624]! ^^^ (y >>> (1 : UInt32))
    let v : UInt32 := if y &&& (1 : UInt32) != 0 then v ^^^ (0x9908B0DF : UInt32) else v
    a.set! i v) a

/-- `:14-32` — `next()`: twist if the index ran out, then temper the next word. -/
def mtNext (s : MT) : UInt32 × MT :=
  let s := if s.idx ≥ 624 then ⟨mtTwist s.mt, 0⟩ else s
  let y : UInt32 := s.mt[s.idx]!
  let y : UInt32 := y ^^^ (y >>> (11 : UInt32))
  let y : UInt32 := y ^^^ ((y <<< (7 : UInt32)) &&& (0x9D2C5680 : UInt32))
  let y : UInt32 := y ^^^ ((y <<< (15 : UInt32)) &&& (0xEFC60000 : UInt32))
  let y : UInt32 := y ^^^ (y >>> (18 : UInt32))
  (y, ⟨s.mt, s.idx + 1⟩)

/-- The j-th output of an engine seeded with `seed`. -/
def mtStream (seed : UInt32) (j : Nat) : UInt32 :=
  (mtNext ((List.range j).foldl (fun s _ => (mtNext s).2) (mtInit seed))).1

/-- `:44` — `u(a, len) = a + (UInt64(rng.next()) & (len − 1))` on the draw r. -/
def uDraw (a len r : Nat) : Nat := a + (r &&& (len - 1))

/-- C-08 — the distributions (`fullrange` is test-only). -/
inductive Dist | uniform | sorted | zero | bucket | gaussian | staggered | fullrange

/-- `:36-37` — p = 128, w = 2^24. -/
def genP : Nat := 128
def genW : Nat := 2 ^ 24

/-- `:39-79` — the key values v_k (before any `float32` conversion) for (d, n) on the draw stream
r (r j is the j-th `rng.next()`). -/
def genV (d : Dist) (n : Nat) (r : Nat → Nat) : List Nat :=
  match d with
  | .uniform => (List.range n).map fun k => uDraw 0 (2 ^ 31) (r k)
  | .sorted => ((List.range n).map fun k => uDraw 0 (2 ^ 31) (r k)).mergeSort
      GpuQuicksortSpec.GpuQuicksort.Model.leB
  | .zero => if 0 < n then List.replicate n (uDraw 0 (2 ^ 31) (r 0)) else []
  | .bucket => (List.range n).map fun k => uDraw (k * genP * genP / n % genP * genW) genW (r k)
  | .gaussian => (List.range n).map fun k =>
      (uDraw 0 (2 ^ 31) (r (4 * k)) + uDraw 0 (2 ^ 31) (r (4 * k + 1)) + uDraw 0 (2 ^ 31) (r (4 * k + 2)) +
        uDraw 0 (2 ^ 31) (r (4 * k + 3))) / 4
  | .staggered => (List.range n).map fun k =>
      let i := k * genP / n
      if i < genP / 2 then uDraw ((2 * i + 1) * genW) genW (r k) else uDraw ((2 * i - genP) * genW) genW (r k)
  | .fullrange => (List.range n).map r

end GpuQuicksort.Model
