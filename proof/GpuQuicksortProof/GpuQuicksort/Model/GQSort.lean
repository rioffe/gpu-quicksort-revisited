import GpuQuicksortProof.GpuQuicksort.Spec
import GpuQuicksortProof.GpuQuicksort.Model.LQSort

/-!
# GpuQuicksortProof.GpuQuicksort.Model.GQSort
=============================================

Transcription of the phase-one kernels `gqsort_partition` and `gqsort_fill`
(`Sources/GPUQuicksort/Metal/GPUQuicksort.metal:237-346`) for one iteration's dispatches.

## Correspondence

| Source | Model |
| ------ | ----- |
| `SharedTypes.h` `SequenceRecord` (C-05) | `Rec` |
| `SharedTypes.h` `BlockDescriptor` (C-05) | `Blk` |
| `:266-270` the block's record, `src`, pivot, `S`, `Dst` | `blockScan`, `blockScatter` |
| `:273-277` pass 1 with stride T, `scan2` | `blockScan` (the lqsort pass 1 and `scan2`) |
| `:280-284` thread 0: `lbeg = atomic_fetch_add(&r.lnext, sL)`, `gbeg = atomic_fetch_sub(&r.gnext, sG) - sG` | `lbegOf`, `gbegOf`: each record's `lnext` (`gnext`) receives the blocks' adds (subtracts) in an order `ordL j` (`ordG j`) — the modification order of that atomic location |
| `:285-294` barrier; pass 2 scatter from `lbeg + scratch[tid]`, `gbeg + scratch[T + tid]` | `blockScatter` (the lqsort `passWrites`) |
| `:289-294` per-thread `lmn`, `lmx`, `gmn`, `gmx` over the values written | `blockMinMax` |
| `:296-315` `simd_min`/`simd_max`, per-simdgroup slots, thread 0's fold, four atomic min/max | `blockMinMax` (the block's min/max; **assumed**: `simd_min`/`simd_max` return the min/max over the simdgroup's lanes, as the MSL specification states) |
| `:283`, `:313` `GQS_COUNT_ATOMIC` | not modeled: test-hook counter (T-14 counts the atomics) |
| `:321-346` `gqsort_fill` | `fillWrites` |
| `Sorter.swift:150-156` the two dispatches in one serial encoder | `partitionDispatch`, then `fillDispatch` on its result (R-10) |

Non-atomic writes of different blocks go to disjoint slots (proved), so the dispatch applies all of
them; the atomics' results depend only on the modification orders, which the theorems quantify over.
-/

namespace GpuQuicksort.Model

/-- C-05 `SequenceRecord`. -/
structure Rec where
  start : Nat
  end_ : Nat
  lnext : Nat
  gnext : Nat
  pivot : Nat
  src : Nat
  lmin : Nat
  lmax : Nat
  gmin : Nat
  gmax : Nat

/-- C-05 `BlockDescriptor`. -/
structure Blk where
  begin : Nat
  end_ : Nat
  seq : Nat

/-- `:273-277` — a block's pass 1 and scans: per-thread offsets and totals for both sides. -/
def blockScan (T : Nat) (hT : 0 < T) (S : Nat → Nat) (p : Nat) (bk : Blk) :
    (Nat → Nat) × Nat × (Nat → Nat) × Nat :=
  let sl := scan2 T fun t => ltCount S p (visits T hT bk.begin bk.end_ t)
  let sg := scan2 T fun t => gtCount S p (visits T hT bk.begin bk.end_ t)
  (sl.1, sl.2, sg.1, sg.2)

/-- `:286-294` — a block's pass-2 writes, from its reserved bases. -/
def blockScatter (T : Nat) (hT : 0 < T) (S : Nat → Nat) (p : Nat) (bk : Blk) (lbeg gbeg : Nat) :
    List (Nat × Nat) :=
  let sc := blockScan T hT S p bk
  (List.range T).flatMap fun t => passWrites S p (lbeg + sc.1 t) (gbeg + sc.2.2.1 t) (visits T hT bk.begin bk.end_ t)

/-- `:281` — the value `atomic_fetch_add(&r.lnext, sL)` returns to block i of record j: the
record's start plus the adds that precede it in the location's modification order `ord`. -/
def lbegOf (sL : Nat → Nat) (start : Nat) (ord : List Nat) (i : Nat) : Nat :=
  start + ((ord.take (ord.idxOf i)).map sL).sum

/-- `:282` — `atomic_fetch_sub(&r.gnext, sG) - sG`: the record's end minus the subtracts up to
and including block i's in the modification order. -/
def gbegOf (sG : Nat → Nat) (end_ : Nat) (ord : List Nat) (i : Nat) : Nat :=
  end_ - ((ord.take (ord.idxOf i + 1)).map sG).sum

/-- `:289-315` — a block's minimum and maximum of the values it wrote below and above the pivot
(0xFFFFFFFF and 0 when there are none), as its four atomics deliver them. -/
def blockMinMax (T : Nat) (hT : 0 < T) (S : Nat → Nat) (p : Nat) (bk : Blk) : Nat × Nat × Nat × Nat :=
  let vs := ((List.range T).flatMap (visits T hT bk.begin bk.end_)).map S
  let lo := vs.filter (fun v => decide (v < p))
  let hi := vs.filter (fun v => decide (p < v))
  (lo.foldl min 0xFFFFFFFF, lo.foldl max 0, hi.foldl min 0xFFFFFFFF, hi.foldl max 0)

/-- One `gqsort_partition` dispatch over the block list `blks`, with record j's cursors updated in
the orders `ordL j` and `ordG j`: the memory after all blocks' scatters, and the records after all
atomics. -/
def partitionDispatch (T : Nat) (hT : 0 < T) (minMax : Bool) (mem : Mem) (recs : List Rec)
    (blks : List Blk) (ordL ordG : Nat → List Nat) : Mem × List Rec :=
  let rec_ := fun i => recs.getD (blks.getD i ⟨0, 0, 0⟩).seq ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩
  let S := fun i => mem.buf (rec_ i).src
  let sc := fun i => blockScan T hT (S i) (rec_ i).pivot (blks.getD i ⟨0, 0, 0⟩)
  let sL := fun i => (sc i).2.1
  let sG := fun i => (sc i).2.2.2
  let writes := fun i =>
    let bk := blks.getD i ⟨0, 0, 0⟩
    blockScatter T hT (S i) (rec_ i).pivot bk
      (lbegOf sL (rec_ i).lnext (ordL bk.seq) i) (gbegOf sG (rec_ i).gnext (ordG bk.seq) i)
  -- writes land in the other buffer of each block's record
  let toD := (List.range blks.length).flatMap fun i => if (rec_ i).src = 1 then writes i else []
  let toA := (List.range blks.length).flatMap fun i => if (rec_ i).src = 0 then writes i else []
  let mem' : Mem := ⟨applyW toD mem.D, applyW toA mem.A⟩
  let recs' := (List.range recs.length).map fun j =>
    let r := recs.getD j ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩
    let mine := (List.range blks.length).filter fun i => (blks.getD i ⟨0, 0, 0⟩).seq = j
    let mm := fun i => blockMinMax T hT (S i) r.pivot (blks.getD i ⟨0, 0, 0⟩)
    { r with
      lnext := r.lnext + (mine.map sL).sum
      gnext := r.gnext - (mine.map sG).sum
      lmin := if minMax then (mine.map fun i => (mm i).1).foldl min r.lmin else r.lmin
      lmax := if minMax then (mine.map fun i => (mm i).2.1).foldl max r.lmax else r.lmax
      gmin := if minMax then (mine.map fun i => (mm i).2.2.1).foldl min r.gmin else r.gmin
      gmax := if minMax then (mine.map fun i => (mm i).2.2.2).foldl max r.gmax else r.gmax }
  (mem', recs')

/-- `:334-345` — one `gqsort_fill` block's writes: its share of the record's gap [lnext, gnext). -/
def fillWrites (T : Nat) (hT : 0 < T) (bs : Nat) (r : Rec) (bk : Blk) : List (Nat × Nat) :=
  let gs := r.lnext
  let ge := r.gnext
  let nb := (r.end_ - r.start + bs - 1) / bs
  let j := (bk.begin - r.start) / bs
  let chunk := (ge - gs + nb - 1) / nb
  let from_ := gs + j * chunk
  let to := min (from_ + chunk) ge
  (List.range T).flatMap fun t => (strideFrom (from_ + t) T to hT).map fun i => (i, r.pivot)

/-- The `gqsort_fill` dispatch: every block fills its share of its record's gap in D. -/
def fillDispatch (T : Nat) (hT : 0 < T) (bs : Nat) (mem : Mem) (recs : List Rec) (blks : List Blk) :
    Mem × List (Nat × Nat) :=
  let ws := blks.flatMap fun bk => fillWrites T hT bs (recs.getD bk.seq ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩) bk
  (⟨applyW ws mem.D, mem.A⟩, ws)

end GpuQuicksort.Model
