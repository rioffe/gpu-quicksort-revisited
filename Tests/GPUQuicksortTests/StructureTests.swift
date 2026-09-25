import Foundation
import Metal
import Testing
@testable import GPUQuicksort

/// §9.2: structural claims checked through the D-21 test hooks (debug builds).
@Suite("Structure", .serialized) struct StructureTests {
    static let q: GPUQuicksort? = try? GPUQuicksort()

    /// T-12: forcing the stack capacity to 2 makes the sort throw `internalInvariantViolated`
    /// and the next sort on the same instance succeeds; corrupting a SequenceRecord cursor after a
    /// phase-one dispatch makes the read-back check throw `internalInvariantViolated`. Proves E-10.
    @Test(.enabled(if: TS.hasGPU)) func invariantViolations() throws {
        let q = try #require(Self.q)
        let input = Distribution.generate(.uniform, n: 1 << 16, seed: 4, key: .uint32)
        q.sorter.stackCapacity = 2
        #expect { _ = try gpuSort(q, input, .uint32, Parameters(maxSequences: 1, minSequenceLength: 64)) } throws: { e in
            if case GPUQuicksortError.internalInvariantViolated(let m) = e { return m.contains("stack overflow") }
            return false
        }
        q.sorter.stackCapacity = 32
        #expect(try gpuSort(q, input, .uint32).0 == CPUReference.sortedReference(input, .uint32))

        q.sorter.corruptAfterIteration = 1
        #expect { _ = try gpuSort(q, input, .uint32, Parameters(minSequenceLength: 64)) } throws: { e in
            if case GPUQuicksortError.internalInvariantViolated(let m) = e { return m.contains("phase one") }
            return false
        }
        q.sorter.corruptAfterIteration = nil
        #expect(try gpuSort(q, input, .uint32).0 == CPUReference.sortedReference(input, .uint32))
    }

    /// T-13: for `uniform` n = 2^22, every phase-one iteration dispatches exactly
    /// Σ ceil(l / blocksize) threadgroups with blocksize from K-06, every child lives in buffer
    /// 1 - src, and each iteration's children are pairwise disjoint, disjoint from the gaps, and
    /// strictly shorter than their parent. Proves R-07, R-08, K-06, I-005, E-17.
    @Test(.enabled(if: TS.hasGPU)) func iterationStructure() throws {
        let q = try #require(Self.q)
        let n = 1 << 22
        let input = Distribution.generate(.uniform, n: n, seed: 42, key: .uint32)
        let p = try q.resolvedParameters(for: n, .automatic)
        var iterations = 0
        q.sorter.phaseOneObserver = { it, _, _ in
            iterations += 1
            let total = it.records.reduce(0) { $0 + Int($1.end - $1.start) }
            #expect(it.blocksize == max(p.threadsPerThreadgroup, (total + p.maxSequences - 1) / p.maxSequences))
            #expect(it.threadgroups == it.records.reduce(0) { $0 + (Int($1.end - $1.start) + it.blocksize - 1) / it.blocksize })
            var ranges: [(UInt32, UInt32)] = []
            for ch in it.children {
                let parent = it.records[ch.parent]
                #expect(ch.src == 1 - parent.src)
                #expect(ch.end > ch.begin && ch.end - ch.begin < parent.end - parent.start)
                ranges.append((ch.begin, ch.end))
            }
            for r in it.records { if r.gnext > r.lnext { ranges.append((r.lnext, r.gnext)) } }
            ranges.sort { $0.0 < $1.0 }
            for (x, y) in zip(ranges, ranges.dropFirst()) { #expect(x.1 <= y.0) }
        }
        defer { q.sorter.phaseOneObserver = nil }
        let (out, r) = try gpuSort(q, input, .uint32)
        #expect(out == CPUReference.sortedReference(input, .uint32))
        #expect(iterations == r.phaseOneIterations && iterations > 1)
    }

    /// T-14: `gqsort_partition` performs exactly 2 device-atomic read-modify-writes per
    /// threadgroup under `medianOfThree` and exactly 6 under `minMaxAverage` (debug counter
    /// buffer). Proves R-09, O-2.
    @Test(.enabled(if: TS.hasGPU)) func atomicsPerThreadgroup() throws {
        let q = try #require(Self.q)
        let input = Distribution.generate(.uniform, n: 1 << 21, seed: 8, key: .uint32)
        for (pivot, perGroup) in [(PhaseOnePivot.medianOfThree, 2), (.minMaxAverage, 6)] {
            let counter = try #require(q.device.makeBuffer(length: 16, options: .storageModeShared))
            memset(counter.contents(), 0, 16)
            q.sorter.atomicCounter = counter
            var groups = 0
            q.sorter.phaseOneObserver = { it, _, _ in groups += it.threadgroups }
            defer { q.sorter.atomicCounter = nil; q.sorter.phaseOneObserver = nil }
            let (out, _) = try gpuSort(q, input, .uint32, Parameters(phaseOnePivot: pivot))
            #expect(out == CPUReference.sortedReference(input, .uint32))
            let count = counter.contents().assumingMemoryBound(to: UInt32.self)[0]
            #expect(groups > 0 && Int(count) == perGroup * groups, "\(pivot): \(count) atomics for \(groups) threadgroups")
        }
    }

    /// T-15: after every phase-one iteration each gap [lnext, gnext) of D holds the pivot, and
    /// the number of pivot-equal elements in the parent's input (snapshotted from the previous
    /// iteration's children, or the input for the root) equals the gap length.
    /// Proves R-06, R-10, I-004.
    @Test(.enabled(if: TS.hasGPU)) func gapsHoldPivots() throws {
        let q = try #require(Self.q)
        let n = 1 << 20
        var input = Distribution.generate(.uniform, n: n, seed: 11, key: .uint32)
        for i in stride(from: 0, to: n, by: 5) { input[i] = input[i] % 1000 }       // many duplicates
        struct Key: Hashable { var b: UInt32, e: UInt32, src: UInt32 }
        var snapshots: [Key: [UInt32]] = [Key(b: 0, e: UInt32(n), src: 0): input]
        var checked = 0
        q.sorter.phaseOneObserver = { it, d, a in
            let dp = d.contents().assumingMemoryBound(to: UInt32.self)
            for r in it.records {
                for i in Int(r.lnext)..<Int(r.gnext) { #expect(dp[i] == r.pivot) }
                if let parent = snapshots[Key(b: r.start, e: r.end, src: r.src)] {
                    #expect(parent.filter { $0 == r.pivot }.count == Int(r.gnext - r.lnext))
                    checked += 1
                }
            }
            snapshots = [:]
            for ch in it.children where !ch.done {
                let buf = (ch.src == 0 ? d : a).contents().assumingMemoryBound(to: UInt32.self)
                snapshots[Key(b: ch.begin, e: ch.end, src: ch.src)] = Array(UnsafeBufferPointer(start: buf + Int(ch.begin), count: Int(ch.end - ch.begin)))
            }
        }
        defer { q.sorter.phaseOneObserver = nil }
        let (out, r) = try gpuSort(q, input, .uint32)
        #expect(out == CPUReference.sortedReference(input, .uint32))
        #expect(checked >= r.phaseOneIterations && checked > 1)
    }

    /// T-16: with per-index finalization counters, every index of D is finalized exactly once
    /// (gap fills of both phases plus alternative-sort write-backs), for `uniform`, `zero`
    /// (E-24 path) and a heavy-duplicate input. Proves I-008, R-15, R-06.
    @Test(.enabled(if: TS.hasGPU)) func finalizedExactlyOnce() throws {
        let q = try #require(Self.q)
        let n = 1 << 20
        let dups = (0..<n).map { UInt32($0 % 17) }
        for input in [Distribution.generate(.uniform, n: n, seed: 3, key: .uint32),
                      Distribution.generate(.zero, n: n, seed: 3, key: .uint32), dups] {
            let fin = try #require(q.device.makeBuffer(length: 4 * n, options: .storageModeShared))
            memset(fin.contents(), 0, 4 * n)
            q.sorter.finalizeCounters = fin
            defer { q.sorter.finalizeCounters = nil }
            let (out, _) = try gpuSort(q, input, .uint32)
            #expect(out == CPUReference.sortedReference(input, .uint32))
            let counts = UnsafeBufferPointer(start: fin.contents().assumingMemoryBound(to: UInt32.self), count: n)
            #expect(counts.allSatisfy { $0 == 1 }, "min \(counts.min()!) max \(counts.max()!)")
        }
    }

    /// T-06 (hook half): n = 0 and n = 1 commit no command buffer. Proves E-01, E-02.
    @Test(.enabled(if: TS.hasGPU)) func tinyInputsCommitNothing() throws {
        let q = try #require(Self.q)
        _ = try gpuSort(q, Distribution.generate(.uniform, n: 5000, seed: 1, key: .uint32), .uint32)
        #expect(q.sorter.runner.commits > 0)
        for n in [0, 1] {
            let buf = APITests.shared([42])
            _ = try q.sort(buf, count: n, keyType: .float32)
            #expect(q.sorter.runner.commits == 0 && q.sorter.runner.dispatches.isEmpty)
        }
    }
}
