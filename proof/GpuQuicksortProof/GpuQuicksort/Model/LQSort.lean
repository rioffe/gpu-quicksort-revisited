import GpuQuicksortProof.GpuQuicksort.Spec
import GpuQuicksortProof.GpuQuicksort.Model.Codec
import GpuQuicksortProof.GpuQuicksort.Model.Scan

/-!
# GpuQuicksortProof.GpuQuicksort.Model.LQSort
=============================================

Transcription of the phase-two kernel `lqsort` and its helpers `med3` and `altsort`
(`Sources/GPUQuicksort/Metal/GPUQuicksort.metal:70, 110-235`), for one threadgroup of T threads
sorting one `SortSequence` [b0, e0) of buffer `src0`. Device buffers D and A are functions
`Nat → Nat` holding 32-bit codes; threadgroup arrays likewise.

## Correspondence

| Source | Model |
| ------ | ----- |
| `:70` `med3` | the spec model's `med3` (same formula) |
| `:115-116` `P = 1; while (P < len) P <<= 1` | `padLoop` |
| `:117` load `for (i = tid; i < P; i += T) s[i] = i < len ? S[b+i] : 0xFFFFFFFF` | `altLoad` |
| `:119-131` `for k …; for j …; for (i = tid; i < P; i += T) { ixj; if (ixj > i) {…} }` | `kLoop`, `jLoop`, `roundWrites` |
| `:132` write-back `for (i = tid; i < len; i += T) D[b+i] = s[i]` + `GQS_FINALIZE` | `altsortK` (writes, finalization log) |
| `:163-179` root: `rlen`, push if `rlen ≥ minseq` (`maxDepth = 1`), `altsort` if `0 < rlen < minseq` | `kStart` |
| `:181-185` loop condition `ssp == 0 \|\| serr != 0` → break | `kRun` |
| `:187-192` pop the top, `spivot = med3(S0[b], S0[(b+e)/2], S0[e-1])` | `kStep` (pop, pivot) |
| `:198-203` pass 1 counts with stride T, `scan2` | `ltCount`, `gtCount`, `scan2` |
| `:206-212` pass 2 scatter to `Dst` (`lfrom++`, `gfrom++`) | `passWrites` |
| `:214` gap fill `D[i] = p` over [b+L, e−G) + `GQS_FINALIZE` | `gapWrites` |
| `:218-229` push longer then shorter, skip `cl < minseq`, `serr = 1` at `ssp >= stackCap`, `maxDepth` | `pushChildren` |
| `:231-232` `altsort` children with 0 < len < minseq, from `Dst` into D | `kStep` |
| `:234` `stats[tg] = {partitions, alts, maxDepth, serr}` | the fields of `KS` |
| `:153-155, 166-168` test-hook plumbing | the finalization log `fin` (the `GQS_FINALIZE` events) |
| barriers `:118, 129, 133, 175, 182, 184, 193, 213, 230` | each phase reads what the previous phase left |

Each pass is modeled as its threads' writes, computed from the memory the preceding barrier left,
then applied; the theorems prove the writes of different threads never collide.
-/

namespace GpuQuicksort.Model

open GpuQuicksortSpec.GpuQuicksort.Model (med3)

/-- The two device buffers; `src = 0` reads D, `src = 1` reads A. -/
structure Mem where
  D : Nat → Nat
  A : Nat → Nat

/-- `src ? A : D`. -/
def Mem.buf (m : Mem) (src : Nat) : Nat → Nat := if src = 0 then m.D else m.A

/-- Write a list of (index, value) pairs into buffer `dst` (0 = D, 1 = A). -/
def Mem.write (m : Mem) (dst : Nat) (ws : List (Nat × Nat)) : Mem :=
  if dst = 0 then { m with D := applyW ws m.D } else { m with A := applyW ws m.A }

/-! ## Partition inside one threadgroup -/

/-- The indices thread t visits in `for (i = b + tid; i < e; i += T)`. -/
def visits (T : Nat) (hT : 0 < T) (b e t : Nat) : List Nat := strideFrom (b + t) T e hT

/-- `:200` pass 1: elements `< p` a thread saw. -/
def ltCount (S : Nat → Nat) (p : Nat) (is : List Nat) : Nat := (is.filter (fun i => decide (S i < p))).length
/-- `:200` pass 1: elements `> p` a thread saw. -/
def gtCount (S : Nat → Nat) (p : Nat) (is : List Nat) : Nat := (is.filter (fun i => decide (p < S i))).length

/-- `:207-212` pass 2 of one thread: walk its indices, writing each `< p` value at `lfrom++` and
each `> p` value at `gfrom++`; pivot-equal values are skipped. -/
def passWrites (S : Nat → Nat) (p : Nat) : Nat → Nat → List Nat → List (Nat × Nat)
  | _, _, [] => []
  | lf, gf, i :: is =>
    if S i < p then (lf, S i) :: passWrites S p (lf + 1) gf is
    else if p < S i then (gf, S i) :: passWrites S p lf (gf + 1) is
    else passWrites S p lf gf is

/-- The result of one threadgroup partition of [b, e) around p reading `S`: the scatter writes
(for `Dst`), the totals L and G, and the gap writes (for D). -/
structure TGPart where
  scatter : List (Nat × Nat)
  L : Nat
  G : Nat
  gap : List (Nat × Nat)

/-- `:198-214` — pass 1, `scan2` of both count arrays, pass 2, the gap fill over [b+L, e−G). -/
def tgPartition (T : Nat) (hT : 0 < T) (S : Nat → Nat) (p b e : Nat) : TGPart :=
  let lt := fun t => ltCount S p (visits T hT b e t)
  let gt := fun t => gtCount S p (visits T hT b e t)
  let sl := scan2 T lt
  let sg := scan2 T gt
  let L := sl.2
  let G := sg.2
  { scatter := (List.range T).flatMap fun t =>
      passWrites S p (b + sl.1 t) (e - G + sg.1 t) (visits T hT b e t)
    L := L, G := G
    gap := (List.range T).flatMap fun t => (strideFrom (b + L + t) T (e - G) hT).map fun i => (i, p) }

/-! ## The alternative sort -/

/-- `:115-116` — `P = 1; while (P < len) P <<= 1`. -/
def padLoop (len P : Nat) (hP : 0 < P) : Nat :=
  if P < len then padLoop len (2 * P) (by omega) else P
termination_by len - P

/-- `:117` — the threadgroup array after the load (every i < P is loaded by the thread striding
over it; `Theorems` proves each i < P is visited exactly once). -/
def altLoad (S : Nat → Nat) (b len : Nat) : Nat → Nat :=
  fun i => if i < len then S (b + i) else 0xFFFFFFFF

/-- `:121-128` — one (k, j) round: every thread, for each of its i < P with `ixj > i`, swaps
s[i] and s[ixj] unless they are ordered ascending (`(i & k) == 0`) or descending. -/
def roundWrites (T : Nat) (hT : 0 < T) (P k j : Nat) (s : Nat → Nat) : List (Nat × Nat) :=
  (List.range T).flatMap fun t => (strideFrom t T P hT).flatMap fun i =>
    let ixj := i ^^^ j
    if ixj > i then
      let a := s i
      let c := s ixj
      let up := decide (i &&& k = 0)
      if decide (a > c) = up then [(i, c), (ixj, a)] else []
    else []

/-- `:120-130` — `for (j = k >> 1; j > 0; j >>= 1)`, a barrier after each round. -/
def jLoop (T : Nat) (hT : 0 < T) (P k : Nat) : Nat → (Nat → Nat) → (Nat → Nat)
  | 0, s => s
  | j + 1, s => jLoop T hT P k ((j + 1) / 2) (applyW (roundWrites T hT P k (j + 1) s) s)
termination_by j => j
decreasing_by omega

/-- `:119-131` — `for (k = 2; k <= P; k <<= 1)`. -/
def kLoop (T : Nat) (hT : 0 < T) (P k : Nat) (hk : 0 < k) (s : Nat → Nat) : Nat → Nat :=
  if k ≤ P then kLoop T hT P (2 * k) (by omega) (jLoop T hT P k (k / 2) s) else s
termination_by P + 1 - k

/-- `:113-134` — `altsort(S, D, b, len)`: the writes to D (and the finalization events, one per
index written). -/
def altsortK (T : Nat) (hT : 0 < T) (S : Nat → Nat) (b len : Nat) : List (Nat × Nat) :=
  let P := padLoop len 1 (by decide)
  let s := kLoop T hT P 2 (by decide) (altLoad S b len)
  (List.range T).flatMap fun t => (strideFrom t T len hT).map fun i => (b + i, s i)

/-! ## The kernel -/

/-- One stack entry `{b, e, src}`. -/
structure StackEntry where
  b : Nat
  e : Nat
  src : Nat

/-- The kernel's threadgroup-visible state: memory, the stack (head = top), the error flag,
the statistics, and the finalization log. -/
structure KS where
  mem : Mem
  stack : List StackEntry
  serr : Bool
  partitions : Nat
  alts : Nat
  maxDepth : Nat
  fin : List (Nat × Nat)

/-- `:218-229` — push the longer child, then the shorter, skipping children shorter than
minseq; a push onto a full stack sets `serr` and stops. -/
def pushChildren (minseq cap : Nat) (kids : List StackEntry) (st : List StackEntry) (md : Nat) (serr : Bool) :
    List StackEntry × Nat × Bool :=
  match kids with
  | [] => (st, md, serr)
  | c :: cs =>
    if c.e - c.b < minseq then pushChildren minseq cap cs st md serr
    else if cap ≤ st.length then (st, md, true)
    else pushChildren minseq cap cs (c :: st) (max md (st.length + 1)) serr

/-- `:187-232` — one loop iteration on a non-empty stack. -/
def kStep (T : Nat) (hT : 0 < T) (minseq cap : Nat) (st : KS) : KS :=
  match st.stack with
  | [] => st
  | top :: rest =>
    let b := top.b
    let e := top.e
    let src := top.src
    let S := st.mem.buf src
    let p := med3 (S b) (S ((b + e) / 2)) (S (e - 1))
    let part := tgPartition T hT S p b e
    let dst := 1 - src
    let m1 := (st.mem.write dst part.scatter).write 0 part.gap
    let L := part.L
    let G := part.G
    let lFirst := decide (L ≥ G)
    let lb := if lFirst then b else e - G
    let ll := if lFirst then L else G
    let shb := if lFirst then e - G else b
    let shl := if lFirst then G else L
    let pushed := pushChildren minseq cap [⟨lb, lb + ll, dst⟩, ⟨shb, shb + shl, dst⟩] rest st.maxDepth st.serr
    let Dst := m1.buf dst
    let wl := if 0 < L ∧ L < minseq then altsortK T hT Dst b L else []
    let m2 := m1.write 0 wl
    let wg := if 0 < G ∧ G < minseq then altsortK T hT (m2.buf dst) (e - G) G else []
    let m3 := m2.write 0 wg
    { mem := m3, stack := pushed.1, serr := pushed.2.2, partitions := st.partitions + 1,
      alts := st.alts + (if 0 < L ∧ L < minseq then 1 else 0) + (if 0 < G ∧ G < minseq then 1 else 0),
      maxDepth := pushed.2.1, fin := st.fin ++ part.gap ++ wl ++ wg }

/-- `:181-185` — the loop, bounded by `fuel`: stop when the stack is empty or `serr` is set. -/
def kRun (T : Nat) (hT : 0 < T) (minseq cap : Nat) : Nat → KS → KS
  | 0, st => st
  | f + 1, st => if st.stack = [] ∨ st.serr then st else kRun T hT minseq cap f (kStep T hT minseq cap st)

/-- `:163-179` — the kernel's start for the root sequence [b0, e0) in `src0`. -/
def kStart (T : Nat) (hT : 0 < T) (minseq : Nat) (m : Mem) (b0 e0 src0 : Nat) : KS :=
  let rlen := e0 - b0
  let stack := if rlen ≥ minseq then [⟨b0, e0, src0⟩] else []
  let wr := if 0 < rlen ∧ rlen < minseq then altsortK T hT (m.buf src0) b0 rlen else []
  { mem := m.write 0 wr, stack := stack, serr := false, partitions := 0,
    alts := if 0 < rlen ∧ rlen < minseq then 1 else 0,
    maxDepth := if rlen ≥ minseq then 1 else 0, fin := wr }

/-- `lqsort` for one threadgroup: start, then the loop. -/
def lqsort (T : Nat) (hT : 0 < T) (minseq cap fuel : Nat) (m : Mem) (b0 e0 src0 : Nat) : KS :=
  kRun T hT minseq cap fuel (kStart T hT minseq m b0 e0 src0)

end GpuQuicksort.Model
