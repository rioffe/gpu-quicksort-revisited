// C-11: C++ std::sort baseline behind a C ABI.
#include "CPUBaselines.h"
#include <algorithm>

extern "C" void cpub_stdsort_u32(uint32_t *keys, size_t n) {
    std::sort(keys, keys + n);
}
