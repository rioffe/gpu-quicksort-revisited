// GPUQuicksort.metal — kernels for GPU-Quicksort (Cederman & Tsigas 2009) on Metal.
// Compiled ahead of time by scripts/build-metallib.sh (R-27, C-09); never at runtime.
#include <metal_stdlib>
#include "SharedTypes.h"
using namespace metal;

// ---------------------------------------------------------------------------------------------
// C-04 key codec: order-preserving map between Int32/Float bit patterns and UInt32 codes.
// ---------------------------------------------------------------------------------------------
static inline uint encode_key(uint b, uint keyType) {
    if (keyType == 1) return b ^ 0x80000000u;                                   // int32
    return (b & 0x80000000u) ? ~b : (b ^ 0x80000000u);                          // float32
}

static inline uint decode_key(uint u, uint keyType) {
    if (keyType == 1) return u ^ 0x80000000u;
    return (u & 0x80000000u) ? (u ^ 0x80000000u) : ~u;
}

kernel void key_encode(device uint *d [[buffer(0)]],
                       constant CodecParams &p [[buffer(1)]],
                       uint gid [[thread_position_in_grid]],
                       uint gsize [[threads_per_grid]]) {
    for (uint i = gid; i < p.n; i += gsize) d[i] = encode_key(d[i], p.keyType);
}

kernel void key_decode(device uint *d [[buffer(0)]],
                       constant CodecParams &p [[buffer(1)]],
                       uint gid [[thread_position_in_grid]],
                       uint gsize [[threads_per_grid]]) {
    for (uint i = gid; i < p.n; i += gsize) d[i] = decode_key(d[i], p.keyType);
}

// ---------------------------------------------------------------------------------------------
// T-31: reports sizeof/offsetof of the C-05/C-06 structs as the Metal compiler sees them.
// ---------------------------------------------------------------------------------------------
kernel void layout_probe(device uint *out [[buffer(0)]]) {
    uint i = 0;
    out[i++] = sizeof(SequenceRecord);
    out[i++] = __builtin_offsetof(SequenceRecord, start);
    out[i++] = __builtin_offsetof(SequenceRecord, end);
    out[i++] = __builtin_offsetof(SequenceRecord, lnext);
    out[i++] = __builtin_offsetof(SequenceRecord, gnext);
    out[i++] = __builtin_offsetof(SequenceRecord, pivot);
    out[i++] = __builtin_offsetof(SequenceRecord, src);
    out[i++] = __builtin_offsetof(SequenceRecord, lmin);
    out[i++] = __builtin_offsetof(SequenceRecord, lmax);
    out[i++] = __builtin_offsetof(SequenceRecord, gmin);
    out[i++] = __builtin_offsetof(SequenceRecord, gmax);
    out[i++] = sizeof(BlockDescriptor);
    out[i++] = __builtin_offsetof(BlockDescriptor, begin);
    out[i++] = __builtin_offsetof(BlockDescriptor, end);
    out[i++] = __builtin_offsetof(BlockDescriptor, seq);
    out[i++] = __builtin_offsetof(BlockDescriptor, _pad);
    out[i++] = sizeof(SortSequence);
    out[i++] = __builtin_offsetof(SortSequence, begin);
    out[i++] = __builtin_offsetof(SortSequence, end);
    out[i++] = __builtin_offsetof(SortSequence, src);
    out[i++] = __builtin_offsetof(SortSequence, _pad);
    out[i++] = sizeof(SortStats);
    out[i++] = __builtin_offsetof(SortStats, partitions);
    out[i++] = __builtin_offsetof(SortStats, altSorts);
    out[i++] = __builtin_offsetof(SortStats, maxDepth);
    out[i++] = __builtin_offsetof(SortStats, error);
}
