#!/usr/bin/env python3
"""Independent reference implementation of SPEC.md C-08 (distributions) for T-25.

Implements MT19937 (32-bit, init_genrand seeding) and the seven C-08 distributions from the
spec text alone, then records the SHA-256 of each `gen` output (little-endian 4-byte keys).

    gen_reference.py            write golden.json next to this script
    gen_reference.py --check    recompute and compare with golden.json (exit 1 on mismatch)
"""
import hashlib
import json
import struct
import sys
from pathlib import Path


class MT19937:
    def __init__(self, seed):
        self.mt = [0] * 624
        self.mt[0] = seed & 0xFFFFFFFF
        for i in range(1, 624):
            self.mt[i] = (1812433253 * (self.mt[i - 1] ^ (self.mt[i - 1] >> 30)) + i) & 0xFFFFFFFF
        self.idx = 624

    def next(self):
        if self.idx >= 624:
            for i in range(624):
                y = (self.mt[i] & 0x80000000) | (self.mt[(i + 1) % 624] & 0x7FFFFFFF)
                v = self.mt[(i + 397) % 624] ^ (y >> 1)
                if y & 1:
                    v ^= 0x9908B0DF
                self.mt[i] = v
            self.idx = 0
        y = self.mt[self.idx]
        self.idx += 1
        y ^= y >> 11
        y ^= (y << 7) & 0x9D2C5680
        y ^= (y << 15) & 0xEFC60000
        y ^= y >> 18
        return y & 0xFFFFFFFF


P = 128
W = (1 << 31) // P  # 2^24


def generate(dist, n, seed):
    """C-08 values v_k as unsigned ints (the uint32 key's bit patterns)."""
    rng = MT19937(seed)

    def U(a, length):
        return a + (rng.next() % length)

    if dist == "uniform":
        return [U(0, 1 << 31) for _ in range(n)]
    if dist == "sorted":
        return sorted(U(0, 1 << 31) for _ in range(n))
    if dist == "zero":
        c = U(0, 1 << 31)
        return [c] * n
    if dist == "bucket":
        return [U(((k * P * P) // n % P) * W, W) for k in range(n)]
    if dist == "gaussian":
        out = []
        for _ in range(n):
            s = sum(U(0, 1 << 31) for _ in range(4))
            out.append(s // 4)
        return out
    if dist == "staggered":
        out = []
        for k in range(n):
            i = (k * P) // n
            out.append(U((2 * i + 1) * W, W) if i < P // 2 else U((2 * i - P) * W, W))
        return out
    if dist == "fullrange":
        return [rng.next() for _ in range(n)]
    raise ValueError(dist)


def as_key_bytes(values, key, dist):
    if key in ("uint32", "int32") or dist == "fullrange":
        return b"".join(struct.pack("<I", v) for v in values)
    if key == "float32":
        return b"".join(struct.pack("<f", float(v)) for v in values)
    raise ValueError(key)


DISTS = ["uniform", "sorted", "zero", "bucket", "gaussian", "staggered", "fullrange"]


def compute():
    golden = {"n": 1024, "seed": 42, "mt19937_seed5489_first": MT19937(5489).next(), "sha256": {}}
    for key in ["uint32", "float32"]:
        for d in DISTS:
            data = as_key_bytes(generate(d, 1024, 42), key, d)
            golden["sha256"][f"{key}/{d}"] = hashlib.sha256(data).hexdigest()
    return golden


def main():
    path = Path(__file__).with_name("golden.json")
    g = compute()
    if "--check" in sys.argv:
        ok = json.loads(path.read_text()) == g
        print("gen_reference: golden.json " + ("matches" if ok else "DIFFERS"))
        sys.exit(0 if ok else 1)
    path.write_text(json.dumps(g, indent=2, sort_keys=True) + "\n")
    print(f"gen_reference: wrote {path}")


if __name__ == "__main__":
    main()
