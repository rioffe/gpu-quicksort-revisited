/// C-04: order-preserving map between key bit patterns and UInt32 codes (CPU side; the GPU
/// kernels `key_encode`/`key_decode` implement the same formulas).
package enum KeyCodec {
    @inline(__always)
    package static func encode(_ b: UInt32, _ t: KeyType) -> UInt32 {
        switch t {
        case .uint32: return b
        case .int32: return b ^ 0x8000_0000
        case .float32: return (b & 0x8000_0000) != 0 ? ~b : b ^ 0x8000_0000
        }
    }

    @inline(__always)
    package static func decode(_ u: UInt32, _ t: KeyType) -> UInt32 {
        switch t {
        case .uint32: return u
        case .int32: return u ^ 0x8000_0000
        case .float32: return (u & 0x8000_0000) != 0 ? u ^ 0x8000_0000 : ~u
        }
    }
}
