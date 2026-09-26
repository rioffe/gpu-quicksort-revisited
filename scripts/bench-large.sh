#!/usr/bin/env bash
# bench-large.sh — GPU-Quicksort vs. parallel std::sort at very large sizes (PERFORMANCE.md,
# "Very large inputs"). `gpuqsort bench --cpu` runs all four CPU baselines, and the sequential
# ones take minutes per run at these sizes, so the CPU side uses stdsort-par-bench instead:
# the same flags as the CPUBaselines target, the same inputs (from `gpuqsort gen`), the same
# timing rule (warm-up discarded, input restore untimed, every run verified).
#
# Writes recorded/bench-huge.csv (+ .status) for the GPU and recorded/bench-huge-cpu.csv
# (+ .status) for parallel std::sort. The two halves run one after the other so they never
# compete for the machine. Needs about 24 bytes of RAM per key for the largest size
# (1G keys: ~24 GB) and 4 bytes per key of free disk for one input file at a time.
set -uo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
SIZES="${SIZES:-128M,256M,512M,1024M}"
RUNS="${RUNS:-5}"
DISTS="uniform sorted zero bucket gaussian staggered"
B="$ROOT/.build/release/gpuqsort"
TMP="$(mktemp -d)"
trap 'rm -rf "$TMP"' EXIT
cd "$ROOT"

swift build -c release >/dev/null || exit 1
clang++ -std=c++17 -O3 -fexperimental-library scripts/stdsort-par-bench.cpp -lc++experimental \
    -o "$TMP/stdsort-par-bench" 2> >(grep -v "was built for newer" >&2) || exit 1

t0=$(date +%s)
"$B" --verbose bench --dist all --n "$SIZES" --runs "$RUNS" > recorded/bench-huge.csv
echo "exit=$? elapsed_s=$(( $(date +%s) - t0 ))" > recorded/bench-huge.status

t1=$(date +%s)
rc=0
echo "dist,n,run,algorithm,wall_ms" > recorded/bench-huge-cpu.csv
for d in $DISTS; do
    for n in ${SIZES//,/ }; do
        "$B" gen --dist "$d" --n "$n" --out "$TMP/keys.bin" || rc=1
        "$TMP/stdsort-par-bench" "$TMP/keys.bin" "$d" "$RUNS" >> recorded/bench-huge-cpu.csv || rc=1
        rm -f "$TMP/keys.bin"
    done
done
echo "exit=$rc elapsed_s=$(( $(date +%s) - t1 ))" > recorded/bench-huge-cpu.status
