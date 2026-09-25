/// MT19937 (32-bit), seeded with init_genrand (C-08).
package struct MT19937 {
    private var mt = [UInt32](repeating: 0, count: 624)
    private var idx = 624

    package init(seed: UInt32) {
        mt[0] = seed
        for i in 1..<624 {
            mt[i] = 1_812_433_253 &* (mt[i - 1] ^ (mt[i - 1] >> 30)) &+ UInt32(i)
        }
    }

    package mutating func next() -> UInt32 {
        if idx >= 624 {
            for i in 0..<624 {
                let y = (mt[i] & 0x8000_0000) | (mt[(i + 1) % 624] & 0x7FFF_FFFF)
                var v = mt[(i + 397) % 624] ^ (y >> 1)
                if y & 1 != 0 { v ^= 0x9908_B0DF }
                mt[i] = v
            }
            idx = 0
        }
        var y = mt[idx]
        idx += 1
        y ^= y >> 11
        y ^= (y << 7) & 0x9D2C_5680
        y ^= (y << 15) & 0xEFC6_0000
        y ^= y >> 18
        return y
    }
}

/// C-08: the six input distributions of [P §5.3] plus `fullrange` for tests (R-20).
package enum Distribution: String, CaseIterable, Sendable {
    case uniform, sorted, zero, bucket, gaussian, staggered, fullrange

    static let p: UInt64 = 128
    static let w: UInt64 = 1 << 24                  // 2^31 / p

    /// Returns the key bit patterns for (distribution, n, seed, key). Values v_k are generated per
    /// C-08; for float32 each v_k becomes Float(v_k); `fullrange` returns raw draws as bit patterns.
    package static func generate(_ d: Distribution, n: Int, seed: UInt32, key: KeyType) -> [UInt32] {
        var rng = MT19937(seed: seed)
        // U(a, len) = a + (r mod len); every len is a power of two.
        func u(_ a: UInt64, _ len: UInt64) -> UInt64 { a + (UInt64(rng.next()) & (len - 1)) }
        let n64 = UInt64(n), p = Self.p, w = Self.w
        var v = [UInt32](repeating: 0, count: n)
        switch d {
        case .uniform, .sorted:
            for k in 0..<n { v[k] = UInt32(u(0, 1 << 31)) }
            if d == .sorted { v.sort() }
        case .zero:
            if n > 0 {
                let c = UInt32(u(0, 1 << 31))
                for k in 0..<n { v[k] = c }
            }
        case .bucket:
            for k in 0..<n {
                let s = UInt64(k) * p * p / n64 % p     // 64-bit products (C-08)
                v[k] = UInt32(u(s * w, w))
            }
        case .gaussian:
            for k in 0..<n {
                let sum = u(0, 1 << 31) + u(0, 1 << 31) + u(0, 1 << 31) + u(0, 1 << 31)   // 64-bit sum
                v[k] = UInt32(sum / 4)
            }
        case .staggered:
            for k in 0..<n {
                let i = UInt64(k) * p / n64
                v[k] = UInt32(i < p / 2 ? u((2 * i + 1) * w, w) : u((2 * i - p) * w, w))   // D-07
            }
        case .fullrange:
            for k in 0..<n { v[k] = rng.next() }
            return v
        }
        if key == .float32 {
            for k in 0..<n { v[k] = Float(v[k]).bitPattern }
        }
        return v    // int32: v_k reinterpreted (all non-negative); uint32: v_k
    }
}
