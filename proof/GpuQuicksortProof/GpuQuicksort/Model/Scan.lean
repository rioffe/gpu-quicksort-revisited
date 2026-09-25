import GpuQuicksortProof.GpuQuicksort.Spec

/-!
# GpuQuicksortProof.GpuQuicksort.Model.Scan
===========================================

Transcription of `scan2` (`Sources/GPUQuicksort/Metal/GPUQuicksort.metal:72-98`), the in-place
exclusive Blelloch scan both sorting kernels use for their per-thread offsets (R-04, D-13). It scans
two arrays with the same index arithmetic; the model scans one, and the kernel runs it on
`x` and on `y` independently (they are disjoint halves of `scratch`).

## Correspondence

| Source | Model |
| ------ | ----- |
| `:76` `offset = 1` | the `o` argument of `upSweep`, starting at 1 |
| `:77-85` up-sweep loop `for (d = T >> 1; d > 0; d >>= 1)`, `offset <<= 1` | `upSweep` |
| `:79-83` `if (tid < d) { ai, bi; x[bi] += x[ai]; }` | `upWrites` (one write per thread tid < d) |
| `:78`, `:86` barriers | each level reads the array as the previous level left it |
| `:87` `tx = x[T-1]; x[T-1] = 0` (thread 0) | `scan2`: the total, then the reset |
| `:88-96` down-sweep loop `for (d = 1; d < T; d <<= 1)`, `offset >>= 1` | `downSweep` |
| `:91-95` `t = x[ai]; x[ai] = x[bi]; x[bi] += t` | `downWrites` (two writes per thread tid < d) |
| `:97` final barrier | the result is read after the scan |

A level's threads read the array as the barrier left it and write their own slots; the writes are
computed from that array and then applied (`applyW`). `Theorems/Scan.lean` proves no thread of a
level reads or writes a slot another thread of that level writes, so this is the kernel's result.
Memory is `Nat → Nat`; the counts it scans are sums of at most n < 2^31 ones, so the kernel's
32-bit adds never wrap (K-01).
-/

namespace GpuQuicksort.Model

/-- Point update. -/
def updN (x : Nat → Nat) (i v : Nat) : Nat → Nat := fun j => if j = i then v else x j

/-- Apply a list of writes in order. -/
def applyW (ws : List (Nat × Nat)) (x : Nat → Nat) : Nat → Nat :=
  ws.foldl (fun m w => updN m w.1 w.2) x

/-- `:79-83` — one up-sweep level: thread tid < d adds x[ai] into x[bi]. -/
def upWrites (o d : Nat) (x : Nat → Nat) : List (Nat × Nat) :=
  (List.range d).map fun tid => (o * (2 * tid + 2) - 1, x (o * (2 * tid + 2) - 1) + x (o * (2 * tid + 1) - 1))

/-- `:91-95` — one down-sweep level: thread tid < d swaps x[ai] and x[bi], adding the old x[ai]
into x[bi]. -/
def downWrites (o d : Nat) (x : Nat → Nat) : List (Nat × Nat) :=
  (List.range d).flatMap fun tid =>
    [(o * (2 * tid + 1) - 1, x (o * (2 * tid + 2) - 1)),
     (o * (2 * tid + 2) - 1, x (o * (2 * tid + 2) - 1) + x (o * (2 * tid + 1) - 1))]

/-- `:77-85` — the up-sweep loop from (d, offset); returns the array and the final offset. -/
def upSweep (d o : Nat) (x : Nat → Nat) : (Nat → Nat) × Nat :=
  if 0 < d then upSweep (d / 2) (2 * o) (applyW (upWrites o d x) x) else (x, o)
termination_by d
decreasing_by omega

/-- `:88-96` — the down-sweep loop from (d, offset). (The source starts at d = 1; the model's
`0 < d` guard only makes termination evident.) -/
def downSweep (T d o : Nat) (x : Nat → Nat) : Nat → Nat :=
  if 0 < d ∧ d < T then downSweep T (2 * d) (o / 2) (applyW (downWrites (o / 2) d x) x) else x
termination_by T - d
decreasing_by omega

/-- `:74-98` — `scan2` on one array of T entries: the scanned array and the total `tx`. -/
def scan2 (T : Nat) (x : Nat → Nat) : (Nat → Nat) × Nat :=
  let up := upSweep (T / 2) 1 x
  (downSweep T 1 up.2 (updN up.1 (T - 1) 0), up.1 (T - 1))

end GpuQuicksort.Model
