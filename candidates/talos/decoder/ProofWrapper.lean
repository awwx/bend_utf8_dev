/-
ProofWrapper.lean -- the non-vacuity claim `Utf8Boundary.ShippedWrapperCovered`:
the shipped wrapper's calls (decoder.mjs layout constants, pinned in
Boundary.lean and compared with decoder.mjs by check.sh) meet every condition
of StartOk / BufferOk / DoneOk on the module's own memory size.

EXPORTS
  decoderModule_pages      the decoded module's initial memory has 160 pages
  shippedWrapperCovered    the top-level non-vacuity claim
-/
import ProofMain

namespace Utf8Wasm
open Wasm Utf8Boundary

theorem decoderModule_pages :
    (decoderModule.initialStore : Store Unit).mem.pages = shippedMemoryPages := by
  rfl

theorem wrapperCallsCovered : WrapperCallsCovered decoderModule := by
  have hin : (UInt32.ofNat wrapperInputAddr).toNat = 0 := rfl
  have hout : (UInt32.ofNat wrapperOutputAddr).toNat = 1048576 := rfl
  refine ⟨decoderModule_pages, rfl, by decide, by decide, ?_, ?_⟩
  · intro mem hm
    unfold WrapperMem shippedMemoryPages at hm
    refine ⟨by omega, ?_, ?_⟩
    · intro len hlen
      unfold wrapperMaxChunk at hlen
      refine ⟨by omega, ?_, ?_⟩
      · rw [hin, hout]; omega
      · unfold inMem; rw [hout]; omega
    · unfold inMem; rw [hout]; omega
  · intro mem mem' lo len hm ⟨hp, _⟩
    unfold WrapperMem at *
    omega

theorem shippedWrapperCovered : ShippedWrapperCovered :=
  ⟨decoderModule, decoderModule_decodes, wrapperCallsCovered⟩

end Utf8Wasm
