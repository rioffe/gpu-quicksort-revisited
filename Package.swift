// swift-tools-version: 6.0
// C-09: package layout. D-21: test hooks are compiled into debug builds only.
import PackageDescription

let hooks: [SwiftSetting] = [.define("GPUQS_TEST_HOOKS", .when(configuration: .debug))]

let package = Package(
    name: "GPUQuicksort",
    platforms: [.macOS(.v15)],
    products: [
        .library(name: "GPUQuicksort", targets: ["GPUQuicksort"]),
        .executable(name: "gpuqsort", targets: ["gpuqsort"]),
    ],
    dependencies: [
        .package(url: "https://github.com/apple/swift-argument-parser", from: "1.5.0"),
    ],
    targets: [
        .target(name: "CShared"),
        .target(
            name: "CPUBaselines",
            cSettings: [.unsafeFlags(["-O3"])],
            cxxSettings: [.unsafeFlags(["-O3"])]
        ),
        .target(
            name: "GPUQuicksort",
            dependencies: ["CShared"],
            exclude: ["Metal"],
            resources: [.copy("Resources")],
            swiftSettings: hooks
        ),
        .executableTarget(
            name: "gpuqsort",
            dependencies: [
                "GPUQuicksort", "CPUBaselines",
                .product(name: "ArgumentParser", package: "swift-argument-parser"),
            ],
            swiftSettings: hooks
        ),
        .testTarget(
            name: "GPUQuicksortTests",
            dependencies: ["GPUQuicksort", "CPUBaselines", "CShared", "gpuqsort"],
            resources: [.copy("Fixtures")],
            swiftSettings: hooks
        ),
    ],
    cxxLanguageStandard: .cxx17
)
