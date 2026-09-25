import GpuQuicksortSpec.GpuQuicksort.Spec
import GpuQuicksortSpec.GpuQuicksort.Model
import GpuQuicksortSpec.GpuQuicksort.Theorems

/-!
# GpuQuicksortSpec.GpuQuicksort.ParallelPartition
==================================================

The **parallel partition** that R-04 and R-09 require (phase one's `gqsort_partition`; phase two
uses the same two-pass scheme within one threadgroup), modeled at the level of threads, prefix sums
and atomic reservations, and proved to produce exactly the list-level partition of `Model.lean`.

## The model

- A sequence occupies indices [s, e). Its elements are divided among **threadgroups** (blocks),
  and each block's elements among its **threads**. The division is *arbitrary*: the theorems only
  assume that the blocks' threads, concatenated, are a permutation of the sequence. The spec's
  splitting (K-06) and its stride-T assignment of indices to threads (R-05) are instances; R-05
  fixes a memory-access pattern for speed, and the proofs show correctness does not depend on it.
- Pass 1: each thread counts its elements below and above the pivot (`lowCount`, `highCount`).
- Prefix sum: each thread's offset is the exclusive prefix sum of the counts (`exScan`, R-04, D-13).
- Reservation: each block performs **one** fetch-and-add on the low cursor (by its total below)
  and **one** fetch-and-subtract on the high cursor (by its total above) (R-09). Atomic operations
  on one cursor are linearizable, so the blocks' reservations take effect in *some* order; the
  list `blocks` is that order, and the theorems quantify over every list, hence every order.
- Pass 2: each thread writes its below-pivot elements to consecutive positions from
  (block's low base + its offset), and its above-pivot elements from (block's high base + its
  offset). Pivot-equal elements are not written (R-04).

## Correspondence

| Spec anchor | Model element |
| ----------- | ------------- |
| R-04 pass 1 | `lowCount`, `highCount` |
| R-04 prefix sum (exclusive) | `exScan` (with `exScan_getElem`: entry i is the sum of counts 0..i−1) |
| R-09 one reservation per side per block | `phaseLow`, `phaseHigh` (cursor threaded through the blocks in atomic order) |
| R-04 pass 2 scatter | `lowW`, `highW`, `blockLow`, `blockHigh` |
| C-05 `lnext`/`gnext` | the `cursor` arguments |
-/

namespace GpuQuicksortSpec.GpuQuicksort.ParallelPartition

open GpuQuicksortSpec.GpuQuicksort.Model

/-- One write of pass 2: a position in the destination buffer and the element written there. -/
structure W where
  pos : Nat
  val : Nat
deriving DecidableEq, Repr

/-- R-04 — a thread's below-pivot writes: its below-pivot elements, in order, at base, base+1, … -/
def lowW (p base : Nat) (xs : List Nat) : List W :=
  ((List.range' base (lowerPart p xs).length).zip (lowerPart p xs)).map (fun x => ⟨x.1, x.2⟩)

/-- R-04 — a thread's above-pivot writes. -/
def highW (p base : Nat) (xs : List Nat) : List W :=
  ((List.range' base (upperPart p xs).length).zip (upperPart p xs)).map (fun x => ⟨x.1, x.2⟩)

/-- R-04 — pass-1 counts of one thread. -/
def lowCount (p : Nat) (xs : List Nat) : Nat := (lowerPart p xs).length
/-- R-04 — pass-1 counts of one thread. -/
def highCount (p : Nat) (xs : List Nat) : Nat := (upperPart p xs).length

/-- R-04, D-13 — the exclusive prefix sum: 0, c₀, c₀ + c₁, … (one entry per count). -/
def exScan : List Nat → List Nat
  | [] => []
  | c :: cs => 0 :: (exScan cs).map (c + ·)

/-- R-04 — a block's below-pivot writes: thread t writes from base + (exclusive prefix sum of the
threads' below counts). -/
def blockLow (p base : Nat) (threads : List (List Nat)) : List W :=
  (threads.zip (exScan (threads.map (lowCount p)))).flatMap (fun x => lowW p (base + x.2) x.1)

/-- R-04 — a block's above-pivot writes, from the block's high base. -/
def blockHigh (p base : Nat) (threads : List (List Nat)) : List W :=
  (threads.zip (exScan (threads.map (highCount p)))).flatMap (fun x => highW p (base + x.2) x.1)

/-- R-09 — a block's total below-pivot count (its fetch-and-add amount). -/
def totalLow (p : Nat) (threads : List (List Nat)) : Nat := (threads.map (lowCount p)).sum
/-- R-09 — a block's total above-pivot count (its fetch-and-subtract amount). -/
def totalHigh (p : Nat) (threads : List (List Nat)) : Nat := (threads.map (highCount p)).sum

/-- R-09 — the low cursor: each block, in atomic order, fetch-adds its total and writes from the
old value. -/
def phaseLow (p cursor : Nat) : List (List (List Nat)) → List W
  | [] => []
  | b :: bs => blockLow p cursor b ++ phaseLow p (cursor + totalLow p b) bs

/-- R-09 — the high cursor: each block, in atomic order, fetch-subtracts its total and writes from
(old value − total). -/
def phaseHigh (p cursor : Nat) : List (List (List Nat)) → List W
  | [] => []
  | b :: bs => blockHigh p (cursor - totalHigh p b) b ++ phaseHigh p (cursor - totalHigh p b) bs

/-! ## Proofs -/

/-- **(lemma)**: `exScan` has one entry per count. -/
theorem exScan_length : ∀ (cs : List Nat), (exScan cs).length = cs.length
  | [] => rfl
  | c :: cs => by simp [exScan, exScan_length cs]

/-- **(lemma)**: `exScan` is the exclusive prefix sum — entry i is the sum of counts 0..i−1. -/
theorem exScan_getElem : ∀ (cs : List Nat) (i : Nat) (h : i < (exScan cs).length),
    (exScan cs)[i] = (cs.take i).sum
  | [], i, h => by simp [exScan] at h
  | c :: cs, 0, _ => by simp [exScan]
  | c :: cs, i + 1, h => by
    simp only [exScan, List.getElem_cons_succ, List.getElem_map, List.take_succ_cons, List.sum_cons]
    rw [exScan_getElem cs i]

/-- **(lemma)**: a thread's below-pivot writes cover consecutive positions from its base. -/
theorem lowW_pos (p base : Nat) (xs : List Nat) :
    (lowW p base xs).map (·.pos) = List.range' base (lowCount p xs) := by
  simp [lowW, lowCount, List.map_map, Function.comp_def]
  exact List.map_fst_zip (by simp)

/-- **(lemma)**: a thread's below-pivot writes carry its below-pivot elements, in order. -/
theorem lowW_val (p base : Nat) (xs : List Nat) : (lowW p base xs).map (·.val) = lowerPart p xs := by
  simp [lowW, List.map_map, Function.comp_def]
  exact List.map_snd_zip (by simp)

/-- **(lemma)**: a thread's above-pivot writes cover consecutive positions from its base. -/
theorem highW_pos (p base : Nat) (xs : List Nat) :
    (highW p base xs).map (·.pos) = List.range' base (highCount p xs) := by
  simp [highW, highCount, List.map_map, Function.comp_def]
  exact List.map_fst_zip (by simp)

/-- **(lemma)**: a thread's above-pivot writes carry its above-pivot elements, in order. -/
theorem highW_val (p base : Nat) (xs : List Nat) : (highW p base xs).map (·.val) = upperPart p xs := by
  simp [highW, List.map_map, Function.comp_def]
  exact List.map_snd_zip (by simp)

/-- **(lemma)**: zipping with a shifted scan shifts every base. -/
theorem flatMap_zip_shift (f : Nat → List Nat → List W) (c : Nat) :
    ∀ (ts : List (List Nat)) (os : List Nat),
      (ts.zip (os.map (c + ·))).flatMap (fun x => f x.2 x.1) =
        (ts.zip os).flatMap (fun x => f (c + x.2) x.1)
  | [], _ => by simp
  | _ :: _, [] => by simp
  | t :: ts, o :: os => by
    simp only [List.map_cons, List.zip_cons_cons, List.flatMap_cons]
    rw [flatMap_zip_shift f c ts os]

/-- **(lemma)**: a block's below-pivot writes are its first thread's, then the rest from the
advanced base. -/
theorem blockLow_cons (p base : Nat) (t : List Nat) (ts : List (List Nat)) :
    blockLow p base (t :: ts) = lowW p base t ++ blockLow p (base + lowCount p t) ts := by
  simp only [blockLow, List.map_cons, exScan, List.zip_cons_cons, List.flatMap_cons, Nat.add_zero]
  congr 1
  rw [flatMap_zip_shift (fun o t => lowW p (base + o) t) (lowCount p t)]
  simp only [Nat.add_assoc]

/-- **(lemma)**: a block's above-pivot writes decompose the same way. -/
theorem blockHigh_cons (p base : Nat) (t : List Nat) (ts : List (List Nat)) :
    blockHigh p base (t :: ts) = highW p base t ++ blockHigh p (base + highCount p t) ts := by
  simp only [blockHigh, List.map_cons, exScan, List.zip_cons_cons, List.flatMap_cons, Nat.add_zero]
  congr 1
  rw [flatMap_zip_shift (fun o t => highW p (base + o) t) (highCount p t)]
  simp only [Nat.add_assoc]

/-- **(lemma)**: a block's below-pivot writes cover exactly [base, base + total) — the prefix sum
gives every thread a disjoint, contiguous slot. -/
theorem blockLow_pos (p : Nat) : ∀ (base : Nat) (ts : List (List Nat)),
    (blockLow p base ts).map (·.pos) = List.range' base (totalLow p ts)
  | base, [] => by simp [blockLow, totalLow, exScan]
  | base, t :: ts => by
    rw [blockLow_cons, List.map_append, lowW_pos, blockLow_pos p (base + lowCount p t) ts]
    simp only [totalLow, List.map_cons, List.sum_cons]
    rw [← List.range'_append]; simp

/-- **(lemma)**: a block's above-pivot writes cover exactly [base, base + total). -/
theorem blockHigh_pos (p : Nat) : ∀ (base : Nat) (ts : List (List Nat)),
    (blockHigh p base ts).map (·.pos) = List.range' base (totalHigh p ts)
  | base, [] => by simp [blockHigh, totalHigh, exScan]
  | base, t :: ts => by
    rw [blockHigh_cons, List.map_append, highW_pos, blockHigh_pos p (base + highCount p t) ts]
    simp only [totalHigh, List.map_cons, List.sum_cons]
    rw [← List.range'_append]; simp

/-- **(lemma)**: a block's below-pivot writes carry the below-pivot elements of its threads, in
thread order. -/
theorem blockLow_val (p : Nat) : ∀ (base : Nat) (ts : List (List Nat)),
    (blockLow p base ts).map (·.val) = lowerPart p ts.flatten
  | base, [] => by simp [blockLow, exScan, lowerPart]
  | base, t :: ts => by
    rw [blockLow_cons, List.map_append, lowW_val, blockLow_val p _ ts]
    simp [lowerPart, List.filter_append]

/-- **(lemma)**: a block's above-pivot writes carry the above-pivot elements of its threads. -/
theorem blockHigh_val (p : Nat) : ∀ (base : Nat) (ts : List (List Nat)),
    (blockHigh p base ts).map (·.val) = upperPart p ts.flatten
  | base, [] => by simp [blockHigh, exScan, upperPart]
  | base, t :: ts => by
    rw [blockHigh_cons, List.map_append, highW_val, blockHigh_val p _ ts]
    simp [upperPart, List.filter_append]

/-- **(lemma)**: the total below count of a block is the length of its below-pivot part. -/
theorem totalLow_eq (p : Nat) (ts : List (List Nat)) : totalLow p ts = (lowerPart p ts.flatten).length := by
  have := congrArg List.length (blockLow_val p 0 ts)
  rw [List.length_map, ← List.length_map (f := (·.pos)), blockLow_pos, List.length_range'] at this
  exact this

/-- **(lemma)**: the total above count of a block is the length of its above-pivot part. -/
theorem totalHigh_eq (p : Nat) (ts : List (List Nat)) : totalHigh p ts = (upperPart p ts.flatten).length := by
  have := congrArg List.length (blockHigh_val p 0 ts)
  rw [List.length_map, ← List.length_map (f := (·.pos)), blockHigh_pos, List.length_range'] at this
  exact this

/-- Everything a sequence's blocks hold, in atomic order. -/
def allElems (blocks : List (List (List Nat))) : List Nat := (blocks.map List.flatten).flatten

/-- **(lemma)**: over all blocks, the low cursor's writes cover exactly [cursor, cursor + L). -/
theorem phaseLow_pos (p : Nat) : ∀ (cursor : Nat) (bs : List (List (List Nat))),
    (phaseLow p cursor bs).map (·.pos) = List.range' cursor (lowerPart p (allElems bs)).length
  | cursor, [] => by simp [phaseLow, allElems, lowerPart]
  | cursor, b :: bs => by
    rw [phaseLow, List.map_append, blockLow_pos, phaseLow_pos p _ bs, totalLow_eq]
    simp only [allElems, List.map_cons, List.flatten_cons, lowerPart, List.filter_append, List.length_append]
    rw [← List.range'_append]; simp

/-- **(lemma)**: over all blocks, the low cursor's writes carry exactly the below-pivot elements. -/
theorem phaseLow_val (p : Nat) : ∀ (cursor : Nat) (bs : List (List (List Nat))),
    (phaseLow p cursor bs).map (·.val) = lowerPart p (allElems bs)
  | cursor, [] => by simp [phaseLow, allElems, lowerPart]
  | cursor, b :: bs => by
    rw [phaseLow, List.map_append, blockLow_val, phaseLow_val p _ bs]
    simp [allElems, lowerPart, List.filter_append]

/-- **(lemma)**: over all blocks, the high cursor's writes carry exactly the above-pivot elements. -/
theorem phaseHigh_val (p : Nat) : ∀ (cursor : Nat) (bs : List (List (List Nat))),
    (phaseHigh p cursor bs).map (·.val) = upperPart p (allElems bs)
  | cursor, [] => by simp [phaseHigh, allElems, upperPart]
  | cursor, b :: bs => by
    rw [phaseHigh, List.map_append, blockHigh_val, phaseHigh_val p _ bs]
    simp [allElems, upperPart, List.filter_append]

/-- **(lemma)**: over all blocks, the high cursor's writes cover exactly [cursor − G, cursor), in
some order (blocks fill downwards, threads upwards within a block). -/
theorem phaseHigh_pos (p : Nat) : ∀ (cursor : Nat) (bs : List (List (List Nat))),
    (upperPart p (allElems bs)).length ≤ cursor →
    ((phaseHigh p cursor bs).map (·.pos)).Perm
      (List.range' (cursor - (upperPart p (allElems bs)).length) (upperPart p (allElems bs)).length)
  | cursor, [], _ => by simp [phaseHigh, allElems, upperPart]
  | cursor, b :: bs, h => by
    have hsplit : (upperPart p (allElems (b :: bs))).length = totalHigh p b + (upperPart p (allElems bs)).length := by
      rw [totalHigh_eq]; simp [allElems, upperPart, List.filter_append]
    rw [hsplit] at h ⊢
    rw [phaseHigh, List.map_append, blockHigh_pos]
    have ih := phaseHigh_pos p (cursor - totalHigh p b) bs (by omega)
    refine (List.Perm.append_left _ ih).trans ?_
    refine List.perm_append_comm.trans ?_
    generalize (upperPart p (allElems bs)).length = G at *
    generalize totalHigh p b = tb at *
    have h1 : List.range' (cursor - tb) tb = List.range' ((cursor - tb - G) + 1 * G) tb := by
      congr 1; omega
    rw [h1, List.range'_append]
    have h2 : cursor - tb - G = cursor - (tb + G) := by omega
    rw [h2, Nat.add_comm G tb]

/-- **R-04, R-09** (T-14, T-15, T-17): the parallel partition is the partition. Let a sequence
occupy [s, e), divided among blocks and threads in any way, with the blocks' atomic reservations
taking effect in any order. Then the low cursor's writes cover exactly [s, s + L) and carry exactly
the below-pivot elements; the high cursor's writes cover exactly [e − G, e) and carry exactly the
above-pivot elements; and the untouched middle has room for exactly the pivot-equal elements
(the gap, R-06). Not a re-reading of the model: the writes are assembled from per-thread counts,
exclusive prefix sums and one fetch-and-add per side per block, and the theorem says those pieces
tile the list-level partition. -/
theorem parallelPartition (p s e : Nat) (seq : List Nat) (blocks : List (List (List Nat)))
    (hperm : (allElems blocks).Perm seq) (hlen : s + seq.length = e) :
    (phaseLow p s blocks).map (·.pos) = List.range' s (lowerPart p seq).length ∧
    ((phaseHigh p e blocks).map (·.pos)).Perm
      (List.range' (e - (upperPart p seq).length) (upperPart p seq).length) ∧
    ((phaseLow p s blocks).map (·.val)).Perm (lowerPart p seq) ∧
    ((phaseHigh p e blocks).map (·.val)).Perm (upperPart p seq) ∧
    s + (lowerPart p seq).length + seq.count p + (upperPart p seq).length = e := by
  have hL : (lowerPart p (allElems blocks)).length = (lowerPart p seq).length :=
    (hperm.filter _).length_eq
  have hG : (upperPart p (allElems blocks)).length = (upperPart p seq).length :=
    (hperm.filter _).length_eq
  have hsum : (lowerPart p seq).length + seq.count p + (upperPart p seq).length = seq.length := by
    have := (Theorems.partitionPerm p seq).length_eq
    simp only [partition3, gapPart, List.length_append, List.length_replicate] at this; omega
  refine ⟨?_, ?_, ?_, ?_, by omega⟩
  · rw [phaseLow_pos, hL]
  · have := phaseHigh_pos p e blocks (by omega)
    rwa [hG] at this
  · rw [phaseLow_val]; exact hperm.filter _
  · rw [phaseHigh_val]; exact hperm.filter _

/-- **(lemma)**: every index of [s, e) is written exactly once by one partition: once by the low
cursor, once by the high cursor, or once by the gap fill (R-06) — none twice, none missed. -/
theorem partitionExactlyOnce (p s e : Nat) (seq : List Nat) (blocks : List (List (List Nat)))
    (hperm : (allElems blocks).Perm seq) (hlen : s + seq.length = e) :
    ((phaseLow p s blocks).map (·.pos) ++ List.range' (s + (lowerPart p seq).length) (seq.count p) ++
      (phaseHigh p e blocks).map (·.pos)).Perm (List.range' s seq.length) := by
  obtain ⟨h1, h2, _, _, h5⟩ := parallelPartition p s e seq blocks hperm hlen
  rw [h1]
  refine (List.Perm.append_left _ h2).trans ?_
  have e1 : e - (upperPart p seq).length = s + (lowerPart p seq).length + seq.count p := by omega
  rw [e1, List.range'_append_1, Nat.add_assoc s, List.range'_append_1]
  have : (lowerPart p seq).length + seq.count p + (upperPart p seq).length = seq.length := by omega
  rw [this]

end GpuQuicksortSpec.GpuQuicksort.ParallelPartition
