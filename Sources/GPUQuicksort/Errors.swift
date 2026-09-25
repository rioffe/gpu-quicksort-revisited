/// C-07: every failure of the library is one of these cases (R-18).
public enum GPUQuicksortError: Error, Equatable, Sendable {
    case noMetalDevice
    case unsupportedDevice(String)            // lacks Apple7 GPU family (K-02)
    case shaderLibraryMissing(String)         // resource path of the missing .metallib (E-18)
    case shaderLibraryLoadFailed(String)      // makeLibrary(URL:) / makeFunction / pipeline error text (E-18)
    case tunedParametersInvalid(String)       // C-10 resource missing or fails validation (E-20)
    case invalidParameters(String)            // K-04 violated by an explicit value; names the parameter (E-05)
    case bufferNotShared                      // E-06
    case bufferTooSmall(required: Int, actual: Int)   // E-07
    case tooManyKeys(count: Int, max: Int)    // E-08, K-01
    case allocationFailed(bytes: Int)         // E-12
    case gpuExecutionFailed(String)           // E-09: MTLCommandBuffer.error description
    case internalInvariantViolated(String)    // E-10 and any C-05/C-06 sanity check on read-back
}
