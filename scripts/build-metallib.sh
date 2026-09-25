#!/usr/bin/env bash
# build-metallib.sh — compile the MSL kernels ahead of time (R-27, C-09).
#
# Writes to $OUT_DIR (default Sources/GPUQuicksort/Resources):
#   GPUQuicksort.metallib            release variant
#   GPUQuicksort-testhooks.metallib  compiled with -DGPUQS_TEST_HOOKS (D-21)
#   metallib.sha256                  SHA-256 of GPUQuicksort.metal followed by SharedTypes.h
# Everything is built in a temporary directory and moved into $OUT_DIR only after every step
# succeeded, so a failure leaves the previous outputs untouched.
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
SRC="$ROOT/Sources/GPUQuicksort/Metal/GPUQuicksort.metal"
HDR="$ROOT/Sources/CShared/include/SharedTypes.h"
OUT_DIR="${OUT_DIR:-$ROOT/Sources/GPUQuicksort/Resources}"

TMP="$(mktemp -d)"
trap 'rm -rf "$TMP"' EXIT

build_variant() {
    local name="$1"; shift
    xcrun -sdk macosx metal -std=metal3.1 -mmacosx-version-min=15.0 -O3 "$@" \
        -I "$ROOT/Sources/CShared/include" \
        -c "$SRC" -o "$TMP/$name.air"
    xcrun -sdk macosx metallib "$TMP/$name.air" -o "$TMP/$name.metallib"
}

build_variant GPUQuicksort
build_variant GPUQuicksort-testhooks -DGPUQS_TEST_HOOKS

cat "$SRC" "$HDR" | shasum -a 256 | cut -c1-64 > "$TMP/metallib.sha256"

mkdir -p "$OUT_DIR"
mv -f "$TMP/GPUQuicksort.metallib" "$TMP/GPUQuicksort-testhooks.metallib" "$TMP/metallib.sha256" "$OUT_DIR/"
echo "build-metallib: wrote $OUT_DIR/{GPUQuicksort.metallib,GPUQuicksort-testhooks.metallib,metallib.sha256}"
