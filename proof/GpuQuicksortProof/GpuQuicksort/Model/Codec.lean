import GpuQuicksortProof.GpuQuicksort.Spec

/-!
# GpuQuicksortProof.GpuQuicksort.Model.Codec
============================================

Transcription of the key codec: `Sources/GPUQuicksort/KeyCodec.swift` (CPU side), the MSL
helpers and kernels `encode_key`, `decode_key`, `key_encode`, `key_decode`
(`Sources/GPUQuicksort/Metal/GPUQuicksort.metal:10-32`), `KeyType.codecID`
(`Types.swift:8`) and the host dispatch `Sorter.codec` (`Sorter.swift:53-62`). Swift `UInt32`
and MSL `uint` are `BitVec 32`; `&`, `^`, `~` are `&&&`, `^^^`, `~~~`.

## Correspondence

| Source | Model |
| ------ | ----- |
| `Types.swift:4-8` `KeyType`, `codecID` | `KeyType`, `codecID` |
| `KeyCodec.swift:5-11` `encode` | `swiftEncode` |
| `KeyCodec.swift:14-20` `decode` | `swiftDecode` |
| `GPUQuicksort.metal:10-13` `encode_key` | `mslEncode` |
| `GPUQuicksort.metal:15-18` `decode_key` | `mslDecode` |
| `GPUQuicksort.metal:20-32` grid-stride loop `for (i = gid; i < n; i += gsize)` | `strideFrom`, `gridVisits`, `runKernel` |
| `Sorter.swift:54` `guard key != .uint32, n > 0` | `hostCodec` guard |
| `Sorter.swift:60` `groups: min((n + 255) / 256, 4096), threads: 256` | `codecGridSize` |
| `Sorter.swift:55-59` pipeline and buffer binding | not modeled: Metal API calls (T-05 runs them) |

A dispatch is modeled as running every thread's loop in turn. The threads of `key_encode` touch
disjoint indices (`gridVisits` covers each index once, proven), so no interleaving can change
the result; the device memory is a function `Nat → BitVec 32`.
-/

namespace GpuQuicksort.Model

/-- `Types.swift:4` — the three key types. -/
inductive KeyType | uint32 | int32 | float32
deriving DecidableEq, Repr

/-- `Types.swift:8` — `codecID`: 1 for `int32`, 2 otherwise. -/
def codecID : KeyType → BitVec 32
  | .int32 => 1
  | _ => 2

/-- `KeyCodec.swift:5-11`. -/
def swiftEncode (b : BitVec 32) : KeyType → BitVec 32
  | .uint32 => b
  | .int32 => b ^^^ 0x80000000#32
  | .float32 => if (b &&& 0x80000000#32) != 0 then ~~~b else b ^^^ 0x80000000#32

/-- `KeyCodec.swift:14-20`. -/
def swiftDecode (u : BitVec 32) : KeyType → BitVec 32
  | .uint32 => u
  | .int32 => u ^^^ 0x80000000#32
  | .float32 => if (u &&& 0x80000000#32) != 0 then u ^^^ 0x80000000#32 else ~~~u

/-- `GPUQuicksort.metal:10-13` `encode_key(b, keyType)`. -/
def mslEncode (b keyType : BitVec 32) : BitVec 32 :=
  if keyType == 1 then b ^^^ 0x80000000#32
  else if (b &&& 0x80000000#32) != 0 then ~~~b else b ^^^ 0x80000000#32

/-- `GPUQuicksort.metal:15-18` `decode_key(u, keyType)`. -/
def mslDecode (u keyType : BitVec 32) : BitVec 32 :=
  if keyType == 1 then u ^^^ 0x80000000#32
  else if (u &&& 0x80000000#32) != 0 then u ^^^ 0x80000000#32 else ~~~u

/-- The indices one thread visits in a grid-stride loop `for (i = start; i < n; i += step)`. -/
def strideFrom (start step n : Nat) (hstep : 0 < step) : List Nat :=
  if start < n then start :: strideFrom (start + step) step n hstep else []
termination_by n - start

/-- Every index the grid visits, thread by thread: threads gid = 0 … gsize − 1, each from gid in
steps of gsize. -/
def gridVisits (gsize n : Nat) (h : 0 < gsize) : List Nat :=
  (List.range gsize).flatMap (fun gid => strideFrom gid gsize n h)

/-- Point update of device memory. -/
def upd (d : Nat → BitVec 32) (i : Nat) (v : BitVec 32) : Nat → BitVec 32 :=
  fun j => if j = i then v else d j

/-- A kernel whose thread writes `d[i] = f(d[i])` at each visited index, run over the visits. -/
def runKernel (f : BitVec 32 → BitVec 32) (visits : List Nat) (d : Nat → BitVec 32) : Nat → BitVec 32 :=
  visits.foldl (fun m i => upd m i (f (m i))) d

/-- `Sorter.swift:60` — threads per grid: `min((n + 255) / 256, 4096)` groups of 256. -/
def codecGridSize (n : Nat) : Nat := min ((n + 255) / 256) 4096 * 256

/-- `Sorter.swift:53-62` — the host codec pass over the caller's buffer: nothing for `uint32` or
n = 0, otherwise one `key_encode`/`key_decode` dispatch with `CodecParams{n, codecID}`. -/
def hostCodec (d : Nat → BitVec 32) (n : Nat) (key : KeyType) (encode : Bool) : Nat → BitVec 32 :=
  if h : key ≠ .uint32 ∧ 0 < n then
    have hg : 0 < codecGridSize n := by
      unfold codecGridSize; have : 0 < (n + 255) / 256 := by omega
      have := Nat.lt_min.2 ⟨this, (by decide : 0 < 4096)⟩; omega
    runKernel (fun b => if encode then mslEncode b (codecID key) else mslDecode b (codecID key))
      (gridVisits (codecGridSize n) n hg) d
  else d

end GpuQuicksort.Model
