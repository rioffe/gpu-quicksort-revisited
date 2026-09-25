// CPUBaselines.h — C-11: CPU baselines callable from Swift (C ABI).
#ifndef GQS_CPU_BASELINES_H
#define GQS_CPU_BASELINES_H
#include <stddef.h>
#include <stdint.h>
#ifdef __cplusplus
extern "C" {
#endif
void cpub_qsort_u32(uint32_t *keys, size_t n);    // libc qsort with a (a>b)-(a<b) comparator
void cpub_stdsort_u32(uint32_t *keys, size_t n);  // std::sort(keys, keys+n), compiled -O3, C++17
#ifdef __cplusplus
}
#endif
#endif
