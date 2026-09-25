// SharedTypes.h — the one declaration of the host <-> kernel layouts (C-05, C-06).
// Included by the Metal compiler (scripts/build-metallib.sh, -I Sources/CShared/include)
// and by Swift through the CShared target. Swift does not import C11 _Atomic fields, so
// atomic fields go through GQS_ATOMIC_U32 (C-05, F-008).
#ifndef GQS_SHARED_TYPES_H
#define GQS_SHARED_TYPES_H

#ifdef __METAL_VERSION__
  #include <metal_stdlib>
  #define GQS_ATOMIC_U32 metal::atomic_uint
#else
  #include <stdint.h>
  #define GQS_ATOMIC_U32 uint32_t
#endif

// C-05: one per sequence in the current phase-one iteration's work set.
typedef struct {
    uint32_t start;         // oldstart: first index of the sequence
    uint32_t end;           // oldend: one past the last index
    GQS_ATOMIC_U32 lnext;   // sstart: next free index for "< pivot"; host initializes to start
    GQS_ATOMIC_U32 gnext;   // send: one past the last free index for "> pivot"; host initializes to end
    uint32_t pivot;         // encoded pivot code
    uint32_t src;           // 0 = elements currently in D, 1 = in A; writes go to the other
    GQS_ATOMIC_U32 lmin, lmax, gmin, gmax; // O-2 only; host initializes to 0xFFFFFFFF, 0, 0xFFFFFFFF, 0
} SequenceRecord;           // 40 bytes

// C-05: one per threadgroup of a gqsort_partition / gqsort_fill dispatch.
typedef struct {
    uint32_t begin, end;    // [begin, end) section of the parent sequence (K-06)
    uint32_t seq;           // index into the SequenceRecord array
    uint32_t _pad;
} BlockDescriptor;          // 16 bytes

// C-06: one per lqsort threadgroup.
typedef struct { uint32_t begin, end, src, _pad; } SortSequence;

// C-06: one per lqsort threadgroup, written by thread 0 on exit.
typedef struct {
    uint32_t partitions;    // partition steps performed
    uint32_t altSorts;      // alternative sorts performed
    uint32_t maxDepth;      // stack high-water mark (C-02 convention)
    uint32_t error;         // 0 = ok; 1 = stack overflow (E-10)
} SortStats;

// Internal kernel parameter blocks (not part of the spec's contracts).
typedef struct {
    uint32_t minMax;        // 1 = O-2 minMaxAverage: maintain lmin/lmax/gmin/gmax
    uint32_t blocksize;     // K-06 blocksize of this iteration (used by gqsort_fill)
    uint32_t hooks;         // 1 = test-hook counters bound (testhooks metallib only)
    uint32_t _pad;
} PartitionParams;

typedef struct {
    uint32_t minseq;        // R-15 threshold
    uint32_t stackCap;      // K-08 capacity (32; test hooks may lower it)
    uint32_t hooks;
    uint32_t _pad;
} SortParams;

typedef struct {
    uint32_t n;
    uint32_t keyType;       // 1 = int32, 2 = float32 (uint32 needs no dispatch)
    uint32_t _pad0, _pad1;
} CodecParams;

#endif
