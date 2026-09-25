import GpuQuicksortSpec

/-!
# GpuQuicksortProof.GpuQuicksort.Spec
=====================================

The **normative side** of the implementation proof. The spec's constants and its own model are
not restated here: they are `proof_from_spec/` (the spec model of `SPEC.md` v0.5), imported as a
path dependency, whose theorems certify that model against the spec. This project's theorems
state that each transcribed source file **equals or refines** an element of that model, so the
spec model's theorems carry over to the code.
-/

namespace GpuQuicksort.Spec

end GpuQuicksort.Spec
