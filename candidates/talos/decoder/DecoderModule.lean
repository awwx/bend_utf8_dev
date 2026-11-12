import Interpreter.Wasm.Decoder.ProofEval
import Interpreter.Wasm.Host.Run
import Interpreter.Wasm.Examples.UIntLemmas
import Lean.Elab.Term

/-!
# DecoderModule.lean -- the module literal and its kernel-checked decode

EXPORTS
  printedWat             the text `wasm-tools print decoder.wasm` produced (checked by check.sh)
  decoderModule          the Module literal (built at elaboration time, NOT trusted)
  decoderModule_decodes  Talos's decodeForVerification printedWat = .ok decoderModule

`decoderWat%` runs Talos's WAT decoder at elaboration time and turns the result
into a literal with the derived `ToExpr` instances (a copy of CodeLib's
`watModule%`, copied so that CodeLib/iris-lean need not be built).  The
elaborator is not trusted: `decoderModule_decodes` re-runs the decoder on the
same text by `cbv` (Talos's `kernel_decoder` setup) and proves it yields exactly
`decoderModule`.  That proof is most of this file's 15 s; it uses the default
heartbeat limit (profiled: the `cbv` call is 12.7 s).
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

-- `cbv` recurses through the whole decoder run (default maxRecDepth 512 is too small).
set_option maxRecDepth 100000 in
/-- Kernel-checked: Talos's verification decoder maps the printed text to
exactly `decoderModule`. -/
theorem decoderModule_decodes :
    Decoder.Wat.decodeForVerification printedWat = .ok decoderModule := by
  cbv

end Utf8Wasm
