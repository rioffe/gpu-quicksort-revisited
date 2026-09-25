import Foundation
import Testing

/// Automated structural checks on the MSL kernels: the scripted companion of the recorded T-17
/// inspection, for properties that are visible only in the kernel source.
@Suite("KernelSource") struct KernelSourceTests {
    static let source: String = (try? String(contentsOf: TS.packageRoot
        .appendingPathComponent("Sources/GPUQuicksort/Metal/GPUQuicksort.metal"), encoding: .utf8)) ?? ""

    /// The text of the function whose signature starts with `header`, up to the next top-level
    /// `kernel`/`static` definition.
    static func body(_ header: String) -> String {
        guard let start = source.range(of: header) else { return "" }
        let rest = source[start.upperBound...]
        let next = ["\nkernel void ", "\nstatic ", "\n// ----"].compactMap { rest.range(of: $0)?.lowerBound }.min() ?? rest.endIndex
        return String(rest[..<next])
    }

    static func lines(_ s: String) -> [String] { s.components(separatedBy: "\n") }
    static func firstIndex(_ ls: [String], _ needle: String, after: Int = -1) -> Int? {
        ls.indices.first { $0 > after && ls[$0].contains(needle) }
    }

    /// R-05: in both passes of both partitioning kernels, thread t reads indices b + t, b + t + T,
    /// … — each kernel has exactly two loops of the form `for (uint i = <begin> + tid; i < <end>;
    /// i += T)`, one per pass, and no other read loop over the sequence.
    @Test func coalescedStrideReads() {
        let lq = Self.body("kernel void lqsort("), gq = Self.body("kernel void gqsort_partition(")
        #expect(!lq.isEmpty && !gq.isEmpty)
        #expect(lq.components(separatedBy: "for (uint i = b + tid; i < e; i += T)").count - 1 == 2)            // R-05
        #expect(gq.components(separatedBy: "for (uint i = blk.begin + tid; i < blk.end; i += T)").count - 1 == 2) // R-05
    }

    /// R-04: pass 1 counts `v < p` and `v > p`; pass 2 writes an element only when `v < p` or
    /// `v > p`, so pivot-equal elements are never written by pass 2 (they form the gap).
    @Test func twoPassPartitionSkipsPivotEqual() {
        for k in ["kernel void lqsort(", "kernel void gqsort_partition("] {
            let b = Self.body(k)
            #expect(b.contains("lt += v < p; gt += v > p;"), "\(k) pass 1")                          // R-04
            #expect(b.contains("if (v < p)") && b.contains("else if (v > p)"), "\(k) pass 2")       // R-04
            #expect(!b.contains("v <= p") && !b.contains("v >= p") && !b.contains("v == p"), "\(k)")
            #expect(b.contains("scan2("), "\(k) prefix sum between the passes")                      // R-04
        }
    }

    /// R-28: in lqsort (a) a device + threadgroup barrier separates the pass-2 scatter loop from
    /// the gap-fill loop; (b) a device + threadgroup barrier precedes every pop and the
    /// alternative sorts of freshly scattered children; (c) altsort's load loop is followed by a
    /// barrier before any write-back to D. In gqsort_partition, rule (a): pass 2 starts only
    /// after the barrier that publishes the atomic reservation.
    @Test func barrierPlacement() {
        let dev = "threadgroup_barrier(mem_flags::mem_device | mem_flags::mem_threadgroup)"
        let lq = Self.lines(Self.body("kernel void lqsort("))
        let scatter = Self.firstIndex(lq, "Dst[lfrom++] = v")!
        let fill = Self.firstIndex(lq, "D[i] = p;", after: scatter)!
        #expect((scatter..<fill).contains { lq[$0].contains(dev) })                                   // R-28(a)
        let pop = Self.firstIndex(lq, "stack[--ssp]")!
        let loopTop = Self.firstIndex(lq, "while (true)")!
        #expect((loopTop..<pop).contains { lq[$0].contains(dev) })                                    // R-28(b)
        let childSort = Self.firstIndex(lq, "altsort(Dst, D, b, L", after: fill)!
        #expect((fill..<childSort).contains { lq[$0].contains(dev) })                                 // R-28(b)

        let alt = Self.lines(Self.body("static void altsort("))
        let load = Self.firstIndex(alt, "s[i] = i < len ? S[b + i] : 0xFFFFFFFFu")!
        let write = Self.firstIndex(alt, "D[b + i] = s[i]")!
        #expect(load < write && (load..<write).contains { alt[$0].contains("threadgroup_barrier(") })  // R-28(c)
        #expect(alt[write...].contains { $0.contains(dev) })

        let gq = Self.lines(Self.body("kernel void gqsort_partition("))
        let reserve = Self.firstIndex(gq, "atomic_fetch_add_explicit(&r.lnext")!
        let pass2 = Self.firstIndex(gq, "Dst[lfrom++] = v", after: reserve)!
        #expect((reserve..<pass2).contains { gq[$0].contains("threadgroup_barrier(") })               // R-28(a)
    }

    /// I-007: phase-one kernels touch data shared across threadgroups of the same dispatch
    /// (the SequenceRecord cursors and min/max fields) only through atomic operations; plain
    /// reads of `r.lnext`, `r.gnext`, `r.lmin`, `r.lmax`, `r.gmin`, `r.gmax` never occur, and
    /// gqsort_fill reads the final cursors with atomic loads in a separate dispatch.
    @Test func crossThreadgroupAccessIsAtomic() {
        let gq = Self.body("kernel void gqsort_partition("), fill = Self.body("kernel void gqsort_fill(")
        for field in ["lnext", "gnext", "lmin", "lmax", "gmin", "gmax"] {
            for (name, b) in [("gqsort_partition", gq), ("gqsort_fill", fill)] {
                let uses = b.components(separatedBy: "r.\(field)").count - 1
                let atomicUses = b.components(separatedBy: "_explicit(&r.\(field)").count - 1
                #expect(uses == atomicUses, "\(name): non-atomic access to r.\(field)")              // I-007
            }
        }
        #expect(fill.contains("atomic_load_explicit(&r.lnext") && fill.contains("atomic_load_explicit(&r.gnext"))
        #expect(gq.components(separatedBy: "atomic_fetch_add_explicit(&r.lnext").count - 1 == 1)   // one per side
        #expect(gq.components(separatedBy: "atomic_fetch_sub_explicit(&r.gnext").count - 1 == 1)
    }
}
