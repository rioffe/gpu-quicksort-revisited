// C-11: libc qsort baseline.
#include "CPUBaselines.h"
#include <stdlib.h>

static int cmp_u32(const void *a, const void *b) {
    uint32_t x = *(const uint32_t *)a, y = *(const uint32_t *)b;
    return (x > y) - (x < y);
}

void cpub_qsort_u32(uint32_t *keys, size_t n) {
    if (n > 1) qsort(keys, n, sizeof(uint32_t), cmp_u32);
}
