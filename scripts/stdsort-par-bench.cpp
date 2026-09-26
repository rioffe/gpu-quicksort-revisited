// stdsort-par-bench.cpp — time parallel std::sort on one raw uint32 key file, the way
// `gpuqsort bench --cpu` times cpu-stdsort-par (R-26, D-23): restore the input (not timed), sort
// with std::execution::par, verify against one sequential std::sort; one warm-up run is
// discarded, then `runs` timed runs are printed as CSV rows `dist,n,run,algorithm,wall_ms`.
// Used by scripts/bench-large.sh for sizes where the other CPU baselines take minutes per run.
// Usage: stdsort-par-bench <keys.bin> <dist-label> [runs=5]
#include <algorithm>
#include <chrono>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <execution>
#include <fstream>
#include <vector>
int main(int argc, char **argv) {
    const char *path = argv[1], *dist = argv[2];
    int runs = argc > 3 ? atoi(argv[3]) : 5;
    std::ifstream f(path, std::ios::binary | std::ios::ate);
    size_t n = size_t(f.tellg()) / 4; f.seekg(0);
    std::vector<uint32_t> in(n); f.read(reinterpret_cast<char *>(in.data()), n * 4);
    std::vector<uint32_t> ref = in;
    std::sort(ref.begin(), ref.end());
    std::vector<uint32_t> v;
    for (int run = 0; run <= runs; run++) {
        v = in;                                                    // restore input: not timed
        auto t0 = std::chrono::steady_clock::now();
        std::sort(std::execution::par, v.begin(), v.end());
        auto t1 = std::chrono::steady_clock::now();
        if (v != ref) { std::fprintf(stderr, "verification failed: %s n=%zu run=%d\n", dist, n, run); return 1; }
        if (run == 0) continue;                                    // warm-up discarded
        std::printf("%s,%zu,%d,cpu-stdsort-par,%.3f\n", dist, n, run,
                    std::chrono::duration<double, std::milli>(t1 - t0).count());
        std::fflush(stdout);
    }
}
