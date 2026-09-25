import Std.Tactic.BVDecide

/-!
# GpuQuicksortSpec.GpuQuicksort.Spec
=====================================

The **normative side**: the constants that `SPEC.md` v0.5 (GPU-Quicksort for Metal,
`../SPEC.md`) pins, stated once, each quoting the row that pins it. The file's rule: every
constant quotes the spec's normative text, and every lemma in `section Facts` checks that the
spec's own claims about those constants are mutually consistent (a relation the spec asserts
between two numbers it pins separately), never that a constant equals itself.
-/
namespace GpuQuicksortSpec.GpuQuicksort.Spec

/-- C-04 — the sign bit that the order-preserving key codes flip:
"`int32` encode: u = b XOR 0x8000_0000". -/
@[grind unfold] def signMask : BitVec 32 := 0x80000000#32

/-- K-01 — the index-type cap: "maxKeys = min(2^31 − 1, ⌊maxBufferLength / 4⌋)". -/
@[grind unfold] def keyCap : Nat := 2 ^ 31 - 1

/-- K-08 — "Phase-two stack capacity is 32 entries." -/
@[grind unfold] def stackCapacity : Nat := 32

/-- K-04 — "1 ≤ maxseq ≤ 2^16". -/
@[grind unfold] def maxseqCap : Nat := 2 ^ 16

/-- K-04 — the smallest valid `minseq`: "minseq is a power of two with 64 ≤ minseq". -/
@[grind unfold] def minseqFloor : Nat := 64

/-- K-04 — the thread range: "T is a power of two with 32 ≤ T ≤ min(1024, …)". -/
@[grind unfold] def tFloor : Nat := 32
/-- K-04 — the hard upper bound on T. -/
@[grind unfold] def tCeil : Nat := 1024

/-- K-03 — the fixed words of the phase-two kernel: "(max(2T, minseq) + 3 · 32 + 8) · 4 bytes". -/
@[grind unfold] def phaseTwoFixedWords : Nat := 3 * 32 + 8

/-- K-03 — phase-two threadgroup bytes for T threads and minseq S. -/
@[grind unfold] def phaseTwoBytes (t s : Nat) : Nat := (max (2 * t) s + phaseTwoFixedWords) * 4

/-- K-03 — phase-one threadgroup bytes: "(4T + 16) · 4 bytes". -/
@[grind unfold] def phaseOneBytes (t : Nat) : Nat := (4 * t + 16) * 4

/-- K-02, K-03 — the threadgroup memory of the `apple7`-family reference device (32 KiB),
the budget the K-03 formulas are checked against. -/
@[grind unfold] def refThreadgroupMemory : Nat := 32768

/-- §7.1 — the per-M byte terms: 40 (`SequenceRecord`), 16 · 2 (`BlockDescriptor`),
16 · 2 (`SortSequence`) and 16 · 2 (`SortStats`), plus the constant 2^16. -/
@[grind unfold] def recordBytes : Nat := 40
/-- C-05, C-06 — the 16-byte descriptor size shared by the three other structs. -/
@[grind unfold] def descriptorBytes : Nat := 16
/-- §7.1 — the constant term of the bookkeeping bound. -/
@[grind unfold] def bookkeepingConstant : Nat := 2 ^ 16

/-- C-08 — "p = 128, w = 2^31/p = 2^24". -/
@[grind unfold] def distP : Nat := 128
/-- C-08 — the section width w. -/
@[grind unfold] def distW : Nat := 2 ^ 24

/-- §7.2 — the six CLI exit codes. -/
@[grind unfold] def exitSuccess : Nat := 0
/-- §7.2 — verification failed. -/
@[grind unfold] def exitVerify : Nat := 1
/-- §7.2 — usage or invalid parameters. -/
@[grind unfold] def exitUsage : Nat := 2
/-- §7.2 — Metal, shader library or tuning-table problem. -/
@[grind unfold] def exitEnvironment : Nat := 3
/-- §7.2 — I/O or input format. -/
@[grind unfold] def exitIO : Nat := 4
/-- §7.2 — GPU execution failure or internal invariant violation. -/
@[grind unfold] def exitGPU : Nat := 5

section Facts

/-- K-03 (T-18): the spec writes the fixed words as "3 · 32 + 8"; that is the 32-entry stack
(K-08) of 3-word entries plus 8 scalars, i.e. 104 words. -/
theorem fixedWordsIsStackPlusScalars : phaseTwoFixedWords = 3 * stackCapacity + 8 := by decide

/-- §7.1, K-09 (T-21): the per-M coefficient 136 the spec states equals the sum of its four
buffer terms, 40 + 16 · 2 + 16 · 2 + 16 · 2. -/
theorem bookkeepingCoefficient : recordBytes + descriptorBytes * 2 + descriptorBytes * 2 + descriptorBytes * 2 = 136 := by
  decide

/-- C-08 (T-26): the spec states both "p = 128" and "w = 2^31/p = 2^24"; the two pins agree. -/
theorem sectionWidth : distW * distP = 2 ^ 31 := by decide

/-- K-01 (T-19): the index cap fits a signed 32-bit integer, and twice it still fits an
unsigned 32-bit word — the reason 32-bit index arithmetic like (b + e)/2 cannot overflow. -/
theorem keyCapFitsIndexArithmetic : keyCap + keyCap < 2 ^ 32 := by decide

/-- §7.2, K-12 (T-27): the six exit codes are pairwise distinct. -/
theorem exitCodesDistinct :
    [exitSuccess, exitVerify, exitUsage, exitEnvironment, exitIO, exitGPU].Nodup := by decide

end Facts

end GpuQuicksortSpec.GpuQuicksort.Spec
