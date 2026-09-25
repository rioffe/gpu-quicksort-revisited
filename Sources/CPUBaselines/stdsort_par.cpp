// C-11, R-26: parallel C++ std::sort baseline behind a C ABI. Uses libc++'s parallel algorithms
// (libdispatch backend), which Apple ships behind -fexperimental-library (D-23).
#include "CPUBaselines.h"
#include <algorithm>
#include <execution>

extern "C" void cpub_stdsort_par_u32(uint32_t *keys, size_t n) {
    std::sort(std::execution::par, keys, keys + n);
}
