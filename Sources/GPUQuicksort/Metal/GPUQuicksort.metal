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

// ---------------------------------------------------------------------------------------------
// Shared helpers: median of three (R-14) and the two-array exclusive scan (R-04, D-13).
// ---------------------------------------------------------------------------------------------
static inline uint med3(uint a, uint b, uint c) { return max(min(a, b), min(max(a, b), c)); }

// In-place exclusive Blelloch scan of x[0..T) and y[0..T) (T a power of two); the totals are
// written to tx / ty by thread 0. Ends with a threadgroup barrier.
static void scan2(threadgroup uint *x, threadgroup uint *y, uint tid, uint T,
                  threadgroup uint &tx, threadgroup uint &ty) {
    uint offset = 1;
    for (uint d = T >> 1; d > 0; d >>= 1) {
        threadgroup_barrier(mem_flags::mem_threadgroup);
        if (tid < d) {
            uint ai = offset * (2 * tid + 1) - 1, bi = offset * (2 * tid + 2) - 1;
            x[bi] += x[ai];
            y[bi] += y[ai];
        }
        offset <<= 1;
    }
    threadgroup_barrier(mem_flags::mem_threadgroup);
    if (tid == 0) { tx = x[T - 1]; ty = y[T - 1]; x[T - 1] = 0; y[T - 1] = 0; }
    for (uint d = 1; d < T; d <<= 1) {
        offset >>= 1;
        threadgroup_barrier(mem_flags::mem_threadgroup);
        if (tid < d) {
            uint ai = offset * (2 * tid + 1) - 1, bi = offset * (2 * tid + 2) - 1;
            uint t = x[ai]; x[ai] = x[bi]; x[bi] += t;
            t = y[ai]; y[ai] = y[bi]; y[bi] += t;
        }
    }
    threadgroup_barrier(mem_flags::mem_threadgroup);
}

#ifdef GPUQS_TEST_HOOKS
#define GQS_FIN_PARAM , device atomic_uint *fin, uint hooks
#define GQS_FIN_ARG , fin, prm.hooks
#define GQS_FINALIZE(i) if (hooks) atomic_fetch_add_explicit(&fin[(i)], 1u, memory_order_relaxed)
#else
#define GQS_FIN_PARAM
#define GQS_FIN_ARG
#define GQS_FINALIZE(i)
#endif

// R-15 alternative sort: load S[b..b+len) into threadgroup memory, pad to a power of two with
// 0xFFFFFFFF, bitonic-sort, write the first len elements to D at their final positions.
// R-28(c): the load completes (barrier) before any write-back to D.
static void altsort(device uint *S, device uint *D, uint b, uint len,
                    threadgroup uint *s, uint tid, uint T GQS_FIN_PARAM) {
    uint P = 1;
    while (P < len) P <<= 1;
    for (uint i = tid; i < P; i += T) s[i] = i < len ? S[b + i] : 0xFFFFFFFFu;
    threadgroup_barrier(mem_flags::mem_threadgroup);
    for (uint k = 2; k <= P; k <<= 1) {
        for (uint j = k >> 1; j > 0; j >>= 1) {
            for (uint i = tid; i < P; i += T) {
                uint ixj = i ^ j;
                if (ixj > i) {
                    uint a = s[i], c = s[ixj];
                    bool up = (i & k) == 0;
                    if ((a > c) == up) { s[i] = c; s[ixj] = a; }
                }
            }
            threadgroup_barrier(mem_flags::mem_threadgroup);
        }
    }
    for (uint i = tid; i < len; i += T) { D[b + i] = s[i]; GQS_FINALIZE(b + i); }
    threadgroup_barrier(mem_flags::mem_device | mem_flags::mem_threadgroup);
}

// ---------------------------------------------------------------------------------------------
// Phase two (R-12..R-15, R-28, [P Alg 3]): one threadgroup sorts one sequence to completion,
// keeping pending parts on an explicit stack and always processing the shorter part first.
// Threadgroup memory: `scratch` = max(2T, minseq) words (dynamic) + 32 stack entries + exactly
// 8 scalars = the K-03 bound.
// ---------------------------------------------------------------------------------------------
struct StackEntry { uint b, e, src; };

// The threadgroup scalars below are written by thread 0 and read by all threads only after a
// threadgroup barrier; clang's per-thread initialization analysis cannot see that ordering.
#pragma clang diagnostic ignored "-Wsometimes-uninitialized"

kernel void lqsort(device uint *D [[buffer(0)]],
                   device uint *A [[buffer(1)]],
                   constant SortSequence *seqs [[buffer(2)]],
                   device SortStats *stats [[buffer(3)]],
                   constant SortParams &prm [[buffer(4)]],
#ifdef GPUQS_TEST_HOOKS
                   device atomic_uint *fin [[buffer(5)]],
#endif
                   threadgroup uint *scratch [[threadgroup(0)]],
                   uint tid [[thread_index_in_threadgroup]],
                   uint tg [[threadgroup_position_in_grid]],
                   uint T [[threads_per_threadgroup]]) {
    threadgroup StackEntry stack[32];
    threadgroup uint sb, se, ssrc, spivot, sL, sG, ssp, serr;   // the 8 scalars (K-03)
    uint partitions = 0, alts = 0, maxDepth = 0;                // meaningful in thread 0
    const SortSequence root = seqs[tg];
    const uint minseq = prm.minseq;
    const uint rlen = root.end - root.begin;
#ifdef GPUQS_TEST_HOOKS
    const uint hooks = prm.hooks;
#endif

    if (tid == 0) {
        ssp = 0;
        serr = 0;
        if (rlen >= minseq) { stack[0] = StackEntry{root.begin, root.end, root.src}; ssp = 1; maxDepth = 1; }
    }
    threadgroup_barrier(mem_flags::mem_threadgroup);
    if (rlen > 0 && rlen < minseq) {
        altsort(root.src ? A : D, D, root.begin, rlen, scratch, tid, T GQS_FIN_ARG);
        alts++;
    }

    while (true) {
        threadgroup_barrier(mem_flags::mem_device | mem_flags::mem_threadgroup);   // R-28(b)
        const bool finished = (ssp == 0) || (serr != 0);
        threadgroup_barrier(mem_flags::mem_threadgroup);
        if (finished) break;

        if (tid == 0) {                                  // pop the top: the shorter part (R-13)
            StackEntry t = stack[--ssp];
            sb = t.b; se = t.e; ssrc = t.src;
            device uint *S0 = t.src ? A : D;
            spivot = med3(S0[t.b], S0[(t.b + t.e) / 2], S0[t.e - 1]);             // R-14
        }
        threadgroup_barrier(mem_flags::mem_threadgroup);
        const uint b = sb, e = se, src = ssrc, p = spivot;
        device uint *S = src ? A : D;
        device uint *Dst = src ? D : A;                  // R-07: read one buffer, write the other

        // Pass 1 (R-04, R-05): count < and > pivot with coalesced, stride-T reads.
        uint lt = 0, gt = 0;
        for (uint i = b + tid; i < e; i += T) { uint v = S[i]; lt += v < p; gt += v > p; }
        scratch[tid] = lt;
        scratch[T + tid] = gt;
        scan2(scratch, scratch + T, tid, T, sL, sG);
        const uint L = sL, G = sG;

        // Pass 2: scatter; elements equal to the pivot are not written (R-04).
        uint lfrom = b + scratch[tid], gfrom = e - G + scratch[T + tid];
        for (uint i = b + tid; i < e; i += T) {
            uint v = S[i];
            if (v < p) Dst[lfrom++] = v;
            else if (v > p) Dst[gfrom++] = v;
        }
        threadgroup_barrier(mem_flags::mem_device | mem_flags::mem_threadgroup);   // R-28(a)
        for (uint i = b + L + tid; i < e - G; i += T) { D[i] = p; GQS_FINALIZE(i); } // R-06 gap
        partitions++;

        // Children [b, b+L) and [e-G, e) now live in Dst (src' = 1 - src).
        if (tid == 0) {
            const bool lFirst = L >= G;                  // push the longer, then the shorter
            const uint lb = lFirst ? b : e - G, ll = lFirst ? L : G;
            const uint shb = lFirst ? e - G : b, shl = lFirst ? G : L;
            for (uint k = 0; k < 2; k++) {
                const uint cb = k == 0 ? lb : shb, cl = k == 0 ? ll : shl;
                if (cl < minseq) continue;               // empty or handled by R-15 below
                if (ssp >= prm.stackCap) { serr = 1; break; }                      // E-10
                stack[ssp++] = StackEntry{cb, cb + cl, 1u - src};
                maxDepth = max(maxDepth, ssp);
            }
        }
        threadgroup_barrier(mem_flags::mem_device | mem_flags::mem_threadgroup);   // R-28(b)
        if (L > 0 && L < minseq) { altsort(Dst, D, b, L, scratch, tid, T GQS_FIN_ARG); alts++; }
        if (G > 0 && G < minseq) { altsort(Dst, D, e - G, G, scratch, tid, T GQS_FIN_ARG); alts++; }
    }
    if (tid == 0) stats[tg] = SortStats{partitions, alts, maxDepth, serr};
}

// ---------------------------------------------------------------------------------------------
// Phase one ([P Alg 2], R-04, R-05, R-07, R-09, O-2): several threadgroups cooperate on one
// sequence. Each threadgroup counts its section, scans the counts, reserves output space for the
// whole threadgroup with exactly one atomic fetch-and-add per side, then scatters into the other
// buffer. The pivot gap is filled afterwards by gqsort_fill (R-10, D-03).
// Threadgroup memory: `scratch` = 2T words (dynamic) + 4 scalars <= (4T + 16) words (K-03).
// ---------------------------------------------------------------------------------------------
#ifdef GPUQS_TEST_HOOKS
#define GQS_COUNT_ATOMIC(n) if (prm.hooks) atomic_fetch_add_explicit(&hookAtomics[0], (n), memory_order_relaxed)
#else
#define GQS_COUNT_ATOMIC(n)
#endif

kernel void gqsort_partition(device uint *D [[buffer(0)]],
                             device uint *A [[buffer(1)]],
                             device SequenceRecord *recs [[buffer(2)]],
                             constant BlockDescriptor *blocks [[buffer(3)]],
                             constant PartitionParams &prm [[buffer(4)]],
#ifdef GPUQS_TEST_HOOKS
                             device atomic_uint *hookAtomics [[buffer(5)]],
#endif
                             threadgroup uint *scratch [[threadgroup(0)]],
                             uint tid [[thread_index_in_threadgroup]],
                             uint tg [[threadgroup_position_in_grid]],
                             uint T [[threads_per_threadgroup]],
                             uint lane [[thread_index_in_simdgroup]],
                             uint sg [[simdgroup_index_in_threadgroup]],
                             uint nsg [[simdgroups_per_threadgroup]]) {
    threadgroup uint sL, sG, lbeg, gbeg;
    const BlockDescriptor blk = blocks[tg];
    device SequenceRecord &r = recs[blk.seq];
    const uint src = r.src, p = r.pivot;
    device uint *S = src ? A : D;
    device uint *Dst = src ? D : A;

    // Pass 1: count elements < and > the pivot in this threadgroup's section.
    uint lt = 0, gt = 0;
    for (uint i = blk.begin + tid; i < blk.end; i += T) { uint v = S[i]; lt += v < p; gt += v > p; }
    scratch[tid] = lt;
    scratch[T + tid] = gt;
    scan2(scratch, scratch + T, tid, T, sL, sG);

    // One atomic per side reserves space for the whole threadgroup (R-09).
    if (tid == 0) {
        lbeg = atomic_fetch_add_explicit(&r.lnext, sL, memory_order_relaxed);
        gbeg = atomic_fetch_sub_explicit(&r.gnext, sG, memory_order_relaxed) - sG;
        GQS_COUNT_ATOMIC(2u);
    }
    threadgroup_barrier(mem_flags::mem_threadgroup);
    uint lfrom = lbeg + scratch[tid], gfrom = gbeg + scratch[T + tid];

    // Pass 2: scatter to the other buffer; pivot-equal elements are not written (R-04).
    uint lmn = 0xFFFFFFFFu, lmx = 0u, gmn = 0xFFFFFFFFu, gmx = 0u;
    for (uint i = blk.begin + tid; i < blk.end; i += T) {
        uint v = S[i];
        if (v < p) { Dst[lfrom++] = v; lmn = min(lmn, v); lmx = max(lmx, v); }
        else if (v > p) { Dst[gfrom++] = v; gmn = min(gmn, v); gmx = max(gmx, v); }
    }

    if (prm.minMax) {                                    // O-2: one atomic per field per threadgroup
        lmn = simd_min(lmn); lmx = simd_max(lmx); gmn = simd_min(gmn); gmx = simd_max(gmx);
        threadgroup_barrier(mem_flags::mem_threadgroup); // every thread has read its scan offsets
        if (lane == 0) {
            scratch[4 * sg + 0] = lmn; scratch[4 * sg + 1] = lmx;
            scratch[4 * sg + 2] = gmn; scratch[4 * sg + 3] = gmx;
        }
        threadgroup_barrier(mem_flags::mem_threadgroup);
        if (tid == 0) {
            for (uint k = 1; k < nsg; k++) {
                lmn = min(lmn, scratch[4 * k + 0]); lmx = max(lmx, scratch[4 * k + 1]);
                gmn = min(gmn, scratch[4 * k + 2]); gmx = max(gmx, scratch[4 * k + 3]);
            }
            atomic_fetch_min_explicit(&r.lmin, lmn, memory_order_relaxed);
            atomic_fetch_max_explicit(&r.lmax, lmx, memory_order_relaxed);
            atomic_fetch_min_explicit(&r.gmin, gmn, memory_order_relaxed);
            atomic_fetch_max_explicit(&r.gmax, gmx, memory_order_relaxed);
            GQS_COUNT_ATOMIC(4u);
        }
    }
}

// R-06, R-10: after every gqsort_partition threadgroup of the iteration has completed (a
// separate dispatch), each block fills its proportional slice of its sequence's gap
// [lnext, gnext) in D with the pivot.
kernel void gqsort_fill(device uint *D [[buffer(0)]],
                        device SequenceRecord *recs [[buffer(2)]],
                        constant BlockDescriptor *blocks [[buffer(3)]],
                        constant PartitionParams &prm [[buffer(4)]],
#ifdef GPUQS_TEST_HOOKS
                        device atomic_uint *fin [[buffer(6)]],
#endif
                        uint tid [[thread_index_in_threadgroup]],
                        uint tg [[threadgroup_position_in_grid]],
                        uint T [[threads_per_threadgroup]]) {
#ifdef GPUQS_TEST_HOOKS
    const uint hooks = prm.hooks;
#endif
    const BlockDescriptor blk = blocks[tg];
    device SequenceRecord &r = recs[blk.seq];
    const uint gs = atomic_load_explicit(&r.lnext, memory_order_relaxed);
    const uint ge = atomic_load_explicit(&r.gnext, memory_order_relaxed);
    const uint bs = prm.blocksize;
    const uint nb = (r.end - r.start + bs - 1) / bs;
    const uint j = (blk.begin - r.start) / bs;
    const uint chunk = (ge - gs + nb - 1) / nb;
    const uint from = gs + j * chunk;
    const uint to = min(from + chunk, ge);
    const uint p = r.pivot;
    for (uint i = from + tid; i < to; i += T) { D[i] = p; GQS_FINALIZE(i); }
}
