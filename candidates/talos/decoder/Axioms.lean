import ProofBuffer
import ProofDone
import ProofModel
import Utf8Proofs

-- Kernel-checked decode of the shipped module's printed text.
#print axioms Utf8Wasm.decoderModule_decodes
-- Exports against the Wasm-level models (see STATUS.txt).
#print axioms Utf8Wasm.start_ok
#print axioms Utf8Wasm.done_runs
#print axioms Utf8Wasm.buffer_runs
-- Per-function call lemmas.
#print axioms Utf8Wasm.call_step
#print axioms Utf8Wasm.loop_correct
-- Model refinement, empty-pending case only.
#print axioms Utf8Wasm.stepM_nil
-- Pure layer (unmodified, imported).
#print axioms Utf8Pure.RefDecoder_correct
