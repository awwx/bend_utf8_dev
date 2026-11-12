import ProofWrapper

-- The top-level claim (Boundary.lean's ShippedModuleCorrect).
#print axioms Utf8Wasm.shippedModuleCorrect
-- Kernel-checked decode of the shipped module's printed text.
#print axioms Utf8Wasm.decoderModule_decodes
-- Exports against the Wasm-level models (see STATUS.txt).
#print axioms Utf8Wasm.start_ok
#print axioms Utf8Wasm.done_runs
#print axioms Utf8Wasm.buffer_runs
-- Per-function call lemmas.
#print axioms Utf8Wasm.call_step
#print axioms Utf8Wasm.loop_correct
-- Model refinement (ProofModel.lean, ProofRefine.lean).
#print axioms Utf8Wasm.stepM_nil
#print axioms Utf8Wasm.stepM_enc
-- Exports in Boundary's form (ProofMain.lean).
#print axioms Utf8Wasm.buffer_ok
#print axioms Utf8Wasm.done_ok
-- Pure layer (unmodified, imported).
#print axioms Utf8Pure.RefDecoder_correct
-- Non-vacuity: the wrapper's calls meet the conditions (ProofWrapper.lean).
#print axioms Utf8Wasm.shippedWrapperCovered
