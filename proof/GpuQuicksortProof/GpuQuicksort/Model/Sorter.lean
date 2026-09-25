import GpuQuicksortProof.GpuQuicksort.Spec
import GpuQuicksortProof.GpuQuicksort.Model.Codec
import GpuQuicksortProof.GpuQuicksort.Model.LQSort
import GpuQuicksortProof.GpuQuicksort.Model.GQSort

/-!
# GpuQuicksortProof.GpuQuicksort.Model.Sorter
=============================================

Transcription of the host orchestration `Sources/GPUQuicksort/Sorter.swift`: `run`, `phaseOne`,
`phaseTwo` and `medianOfThree`, over the kernel models of `LQSort.lean` and `GQSort.lean`.

## Correspondence

| Source | Model |
| ------ | ----- |
| `:67-81` `run`: encode, phase one, phase two if `done` is non-empty (E-24), decode | `sortRun` |
| `:84` `Seq {begin, end, src}` | `SeqD` |
| `:98-102` `medianOfThree` (64-bit midpoint) | `hostMed3` |
| `:108` `n < minSequenceLength` → `[root]` (E-03) | `phaseOne` |
| `:109-111` `m`, `t`, `minlength = ⌈n/m⌉`, `minMax` | `phaseOne` |
| `:112` root pivot: median of three (D-20) | `phaseOne` |
| `:118-119` loop condition and the iteration cap (K-07) | `p1Iter` |
| `:121-122` `total`, `blocksize = max(t, ⌈total/m⌉)` (K-06) | `p1Body` |
| `:124-135` records (lnext = start, gnext = end, min/max sentinels) and blocks (last takes the remainder) | `mkRecs`, `mkBlocks` |
| `:136-156` the two dispatches in one command buffer | `partitionDispatch`, `fillDispatch`, atomic orders from an oracle |
| `:157-159` test hook `corruptAfterIteration` | not modeled: test-only |
| `:165-170` read-back guard `start ≤ lnext ≤ gnext ≤ end`, else `internalInvariantViolated` (E-10) | `p1Body` returns `none` |
| `:173-185` children in the other buffer, non-empty only (E-17), pivots (O-2 overflow-free / median), `done` if shorter than `minlength` | `childrenOf` |
| `:187-194` `work = nextWork`, observers, diagnostics; `done + work` merged | `p1Iter`, `phaseOne` |
| `:204-241` phase two: one `lqsort` threadgroup per sequence, `stackCap` 32, error flag → `internalInvariantViolated` | `phaseTwo` |
| `:25-31, 45-49, 188-190, 197-200` observers, diagnostics, timing, counters | not modeled: reporting (T-21, T-22) |
| `BufferPool.swift:38-43` `bookkeeping(maxseq:)`: 40 M + 16·2M + 16·2M + 16·2M bytes | `bookkeepingBytes` |
| `GPUQuicksort.swift:118` `report.auxiliaryBytes = 4 * count`; `BufferPool.swift:24-30` the cached A | `auxBytes` |

Phase two's threadgroups each touch only their own sequence (proved per threadgroup in `LQSort`),
so the dispatch is modeled as running them one after another.
-/

namespace GpuQuicksort.Model

/-- `BufferPool.swift:38-43` — the bookkeeping buffers' bytes for maxseq M: records, blocks,
phase-two sequences, phase-two statistics. -/
def bookkeepingBytes (M : Nat) : Nat := 40 * M + 16 * 2 * M + 16 * 2 * M + 16 * 2 * M

/-- `GPUQuicksort.swift:118` — the reported auxiliary bytes. -/
def auxBytes (n : Nat) : Nat := 4 * n

/-- `Sorter.swift:84` — a sequence [begin, end) in buffer `src`. -/
structure SeqD where
  begin : Nat
  end_ : Nat
  src : Nat

/-- `:98-102` — `max(min(x, y), min(max(x, y), z))` of s[b], s[⌊(b+e)/2⌋], s[e−1] (64-bit midpoint). -/
def hostMed3 (s : Nat → Nat) (b e : Nat) : Nat :=
  GpuQuicksortSpec.GpuQuicksort.Model.med3 (s b) (s ((b + e) / 2)) (s (e - 1))

/-- `:179` — `lo &+ (hi &- lo) / 2` in `UInt32`. -/
def minMaxPivotU32 (lo hi : Nat) : Nat := (lo + ((hi + 2 ^ 32 - lo) % 2 ^ 32) / 2) % 2 ^ 32

/-- `:124-127` — the records of this iteration's work. -/
def mkRecs (work : List (SeqD × Nat)) : List Rec :=
  work.map fun w => ⟨w.1.begin, w.1.end_, w.1.begin, w.1.end_, w.2, w.1.src, 0xFFFFFFFF, 0, 0xFFFFFFFF, 0⟩

/-- `:128-134` — the blocks of one sequence: from `b` in steps of `bs`, the last taking the remainder. -/
def blocksOf (bs : Nat) (hbs : 0 < bs) (j e : Nat) (b : Nat) : List Blk :=
  if b < e then ⟨b, min (b + bs) e, j⟩ :: blocksOf bs hbs j e (min (b + bs) e) else []
termination_by e - b
decreasing_by omega

/-- `:124-135` — every work sequence's blocks, in work order. -/
def mkBlocks (bs : Nat) (hbs : 0 < bs) (work : List (SeqD × Nat)) : List Blk :=
  (List.range work.length).flatMap fun j =>
    let w := work.getD j (⟨0, 0, 0⟩, 0)
    blocksOf bs hbs j w.1.end_ w.1.begin

/-- `:173-185` — the non-empty children of one record, with their pivots and `done` flags. -/
def childrenOf (minMax : Bool) (minlength : Nat) (mem : Mem) (r : Rec) : List (SeqD × Nat × Bool) :=
  let childSrc := 1 - r.src
  let kids : List (SeqD × Nat × Nat) :=
    [(⟨r.start, r.lnext, childSrc⟩, r.lmin, r.lmax), (⟨r.gnext, r.end_, childSrc⟩, r.gmin, r.gmax)]
  (kids.filter fun c => decide (c.1.begin < c.1.end_)).map fun c =>
    let pivot := if minMax then minMaxPivotU32 c.2.1 c.2.2 else hostMed3 (mem.buf childSrc) c.1.begin c.1.end_
    (c.1, pivot, decide (c.1.end_ - c.1.begin < minlength))

/-- The atomic modification orders of one iteration, chosen (adversarially) knowing the block
layout: for record j, the orders of its blocks' `lnext` and `gnext` atomics. -/
abbrev Orders := List Blk → (Nat → List Nat) × (Nat → List Nat)

/-- `:118-190` — the phase-one state: memory, work (with pivots), done, iteration count, cap flag,
and the gap fills so far (the `GQS_FINALIZE` events of `gqsort_fill`). -/
structure P1 where
  mem : Mem
  work : List (SeqD × Nat)
  done : List SeqD
  iteration : Nat
  capReached : Bool
  fills : List (Nat × Nat)

/-- `:120-187` — one iteration's body (after the loop test and the cap test): `none` when the
read-back guard throws (E-10). -/
def p1Body (T : Nat) (hT : 0 < T) (m minlength : Nat) (minMax : Bool) (ords : Orders) (st : P1) : Option P1 :=
  let total := (st.work.map fun w => w.1.end_ - w.1.begin).sum
  let bs := max T ((total + m - 1) / m)
  have hbs : 0 < bs := Nat.lt_of_lt_of_le hT (Nat.le_max_left _ _)
  let recs := mkRecs st.work
  let blks := mkBlocks bs hbs st.work
  let pd := partitionDispatch T hT minMax st.mem recs blks (ords blks).1 (ords blks).2
  let fd := fillDispatch T hT bs pd.1 pd.2 blks
  let recs' := pd.2
  if recs'.all fun r => decide (r.start ≤ r.lnext ∧ r.lnext ≤ r.gnext ∧ r.gnext ≤ r.end_) then
    let kids := recs'.flatMap (childrenOf minMax minlength fd.1)
    some { mem := fd.1,
           work := (kids.filter fun c => !c.2.2).map fun c => (c.1, c.2.1),
           done := st.done ++ (kids.filter fun c => c.2.2).map fun c => c.1,
           iteration := st.iteration + 1, capReached := st.capReached,
           fills := st.fills ++ fd.2 }
  else none

/-- `:118-190` — the loop, bounded by `fuel`, with one pair of atomic orders per iteration. -/
def p1Iter (T : Nat) (hT : 0 < T) (m minlength maxIter : Nat) (minMax : Bool) (ords : Nat → Orders) :
    Nat → P1 → Option P1
  | 0, st => some st
  | f + 1, st =>
    if st.work ≠ [] ∧ st.work.length + st.done.length < m then
      if st.iteration = maxIter then some { st with capReached := true }
      else match p1Body T hT m minlength minMax (ords st.iteration) st with
        | none => none
        | some st' => p1Iter T hT m minlength maxIter minMax ords f st'
    else some st

/-- `:105-195` — phase one: `none` if a read-back guard fails; otherwise the memory, `done + work`,
and the gap fills. -/
def phaseOne (T : Nat) (hT : 0 < T) (n m minseq maxIter : Nat) (minMax : Bool) (ords : Nat → Orders)
    (fuel : Nat) (mem : Mem) : Option (Mem × List SeqD × List (Nat × Nat)) :=
  if n < minseq then some (mem, [⟨0, n, 0⟩], [])
  else
    let minlength := (n + m - 1) / m
    let st0 : P1 := ⟨mem, [(⟨0, n, 0⟩, hostMed3 mem.D 0 n)], [], 0, false, []⟩
    match p1Iter T hT m minlength maxIter minMax ords fuel st0 with
    | none => none
    | some st => some (st.mem, st.done ++ st.work.map (·.1), st.fills)

/-- `:204-241` — phase two: every sequence sorted by its own `lqsort` threadgroup; `none` if any
threadgroup flags an error. Returns the memory and all finalization events. -/
def phaseTwo (T : Nat) (hT : 0 < T) (minseq cap fuel : Nat) (mem : Mem) :
    List SeqD → Option (Mem × List (Nat × Nat))
  | [] => some (mem, [])
  | s :: ss =>
    let k := lqsort T hT minseq cap fuel mem s.begin s.end_ s.src
    if k.serr then none
    else match phaseTwo T hT minseq cap fuel k.mem ss with
      | none => none
      | some (m', f) => some (m', k.fin ++ f)

/-- `:67-81` — `run` on n ≥ 2 keys of type `key` in D: encode, phase one, phase two (if any
sequence), decode. `none` is `internalInvariantViolated`. -/
def sortRun (T : Nat) (hT : 0 < T) (n maxseq minseq maxIter : Nat) (minMax : Bool) (key : KeyType)
    (ords : Nat → Orders) (fuel : Nat) (D : Nat → BitVec 32) (A : Nat → Nat) :
    Option ((Nat → BitVec 32) × List (Nat × Nat)) :=
  let enc := hostCodec D n key true
  let mem : Mem := ⟨fun i => (enc i).toNat, A⟩
  match phaseOne T hT n maxseq minseq maxIter minMax ords fuel mem with
  | none => none
  | some (m1, done, fills) =>
    match (if done = [] then some (m1, []) else phaseTwo T hT minseq 32 fuel m1 done) with
    | none => none
    | some (m2, fins) => some (hostCodec (fun i => BitVec.ofNat 32 (m2.D i)) n key false, fills ++ fins)

end GpuQuicksort.Model
