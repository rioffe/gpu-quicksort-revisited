// mpsgraph-sort-bench.swift — Apple's MPSGraph sort on n uniform uint32 keys, for comparison with
// the GPU quicksorts (recorded/limit-2g-*). Not part of the package build.
//
//   swiftc -O scripts/mpsgraph-sort-bench.swift -o mpsgraph-sort-bench
//   ./mpsgraph-sort-bench <n> <runs>
//
// The keys are the C-08 `uniform` distribution (MT19937 seeded with 42, r mod 2^31), the same
// bytes `gen --dist uniform` writes. The graph is compiled before timing. Each run is timed around
// the executable's synchronous run (waitUntilCompleted); one warm-up run is discarded; the median,
// min and max of the timed runs are printed, and the output is verified against a CPU sort.
// MPSGraph aborts the process for n > 2^31 - 1 ("NDArray dimension length > INT_MAX").
import Foundation
import Metal
import MetalPerformanceShadersGraph

struct MT { var mt = [UInt32](repeating: 0, count: 624); var i = 624
    init(_ s: UInt32) { mt[0] = s; for k in 1..<624 { mt[k] = 1_812_433_253 &* (mt[k-1] ^ (mt[k-1] >> 30)) &+ UInt32(k) } }
    mutating func next() -> UInt32 {
        if i >= 624 { for k in 0..<624 { let y = (mt[k] & 0x8000_0000) | (mt[(k+1) % 624] & 0x7FFF_FFFF)
            var v = mt[(k+397) % 624] ^ (y >> 1); if y & 1 != 0 { v ^= 0x9908_B0DF }; mt[k] = v }; i = 0 }
        var y = mt[i]; i += 1; y ^= y >> 11; y ^= (y << 7) & 0x9D2C_5680; y ^= (y << 15) & 0xEFC6_0000; y ^= y >> 18; return y } }
let n = Int(CommandLine.arguments[1])!, runs = Int(CommandLine.arguments[2])!
let device = MTLCreateSystemDefaultDevice()!, queue = device.makeCommandQueue()!
let inBuf = device.makeBuffer(length: 4 * n, options: .storageModeShared)!
let p = inBuf.contents().assumingMemoryBound(to: UInt32.self)
var rng = MT(42); for k in 0..<n { p[k] = rng.next() & 0x7FFF_FFFF }
let shape = [NSNumber(value: n)]
let graph = MPSGraph()
let ph = graph.placeholder(shape: shape, dataType: .uInt32, name: "keys")
let sorted = graph.sort(ph, axis: 0, descending: false, name: "sort")
let exe = graph.compile(with: MPSGraphDevice(mtlDevice: device), feeds: [ph: MPSGraphShapedType(shape: shape, dataType: .uInt32)],
                        targetTensors: [sorted], targetOperations: nil, compilationDescriptor: nil)
let outBuf = device.makeBuffer(length: 4 * n, options: .storageModeShared)!
let inData = MPSGraphTensorData(inBuf, shape: shape, dataType: .uInt32), outData = MPSGraphTensorData(outBuf, shape: shape, dataType: .uInt32)
let desc = MPSGraphExecutableExecutionDescriptor(); desc.waitUntilCompleted = true
var times: [Double] = []
for r in 0...runs {
    let t0 = DispatchTime.now().uptimeNanoseconds
    _ = exe.run(with: queue, inputs: [inData], results: [outData], executionDescriptor: desc)
    let dt = Double(DispatchTime.now().uptimeNanoseconds - t0) / 1e6
    if r > 0 { times.append(dt) }
}
var ref = Array(UnsafeBufferPointer(start: p, count: n)); ref.sort()
let ok = memcmp(outBuf.contents(), ref, 4 * n) == 0
times.sort()
print(String(format: "MPSGraph sort uint32 n=%d median_ms=%.3f min_ms=%.3f max_ms=%.3f verified=%@", n, times[times.count / 2], times[0], times.last!, ok ? "true" : "false"))
