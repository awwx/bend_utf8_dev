import Interpreter.Wasm.Decoder.ProofEval
import Interpreter.Wasm.Host.Run
import Interpreter.Wasm.Examples.UIntLemmas
import Lean.Elab.Term

/-!
# Elaborator turning the printed WAT into a Module literal (not trusted)

`spike.printed.wat` is the output of `wasm-tools print spike.wasm`.
`spikeModule` is the AST literal obtained by running Talos's WAT decoder at
elaboration time (`decoderWat%`, a copy of CodeLib's `watModule%`, copied so this
spike does not need to build CodeLib/iris-lean).  The elaborator is NOT
trusted: `spikeModule_decodes` re-runs the decoder on the same text inside the
kernel (via `cbv`) and proves it yields exactly `spikeModule`.
-/

namespace Wasm

open Lean Elab Term

deriving instance Lean.ToExpr for Simd.Shape
deriving instance Lean.ToExpr for Simd.ICmp
deriving instance Lean.ToExpr for Simd.FCmp
deriving instance Lean.ToExpr for Simd.UnOp
deriving instance Lean.ToExpr for Simd.BinOp
deriving instance Lean.ToExpr for Simd.TestOp
deriving instance Lean.ToExpr for Simd.ShiftOp
deriving instance Lean.ToExpr for GcHeapType
deriving instance Lean.ToExpr for ValueType
deriving instance Lean.ToExpr for AnyRef
deriving instance Lean.ToExpr for StorageType
deriving instance Lean.ToExpr for FieldType
deriving instance Lean.ToExpr for Value
deriving instance Lean.ToExpr for CatchClause
deriving instance Lean.ToExpr for GcOp
deriving instance Lean.ToExpr for Instruction
deriving instance Lean.ToExpr for Function
deriving instance Lean.ToExpr for Export
deriving instance Lean.ToExpr for DataSegment
deriving instance Lean.ToExpr for MemDecl
deriving instance Lean.ToExpr for GlobalDecl
deriving instance Lean.ToExpr for FuncType
deriving instance Lean.ToExpr for CompositeType
deriving instance Lean.ToExpr for GcTypeDef
deriving instance Lean.ToExpr for TableDecl
deriving instance Lean.ToExpr for ImportDecl
deriving instance Lean.ToExpr for ElementSegment
deriving instance Lean.ToExpr for Module

syntax (name := decoderWat) "decoderWat% " str : term

@[term_elab decoderWat] def elabDecoderWat : TermElab := fun stx _ => do
  let `(decoderWat% $pathSyntax:str) := stx | throwUnsupportedSyntax
  let source ← IO.FS.readFile pathSyntax.getString
  match Decoder.Wat.decodeForVerification source with
  | .ok module => pure (toExpr module)
  | .error message => throwError "WAT decoder rejected: {message}"

end Wasm

kernel_decoder

namespace Utf8Wasm
open Wasm

/-- The text `wasm-tools print decoder.wasm` produced (checked by `check.sh`). -/
def printedWat : String := include_str "decoder.printed.wat"

/-- The module literal, produced by the (untrusted) elaborator. -/
def decoderModule : Module := decoderWat% "decoder.printed.wat"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Kernel-checked: Talos's verification decoder maps the printed text to
exactly `decoderModule`. -/
theorem decoderModule_decodes :
    Decoder.Wat.decodeForVerification printedWat = .ok decoderModule := by
  cbv

end Utf8Wasm
