import Interpreter.Wasm.Decoder.ProofEval
import Interpreter.Wasm.Host.Run
import Lean.Elab.Term
import WasmMemory

/-!
The concrete module is decoded from text printed from the shipped binary.
The elaborator below only constructs a candidate AST: `prefixModule_decodes`
checks that candidate against Talos's decoder inside Lean's kernel. The external
WAT assembler and binary-to-text printer remain trusted artifact adapters.
The small elaborator follows `candidates/talos/spike/Spike.lean`.
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

syntax (name := prefixWat) "prefixWat% " str : term

@[term_elab prefixWat] def elabPrefixWasmWat : TermElab := fun stx _ => do
  let `(prefixWat% $pathSyntax:str) := stx | throwUnsupportedSyntax
  let source ← IO.FS.readFile pathSyntax.getString
  match Decoder.Wat.decodeForVerification source with
  | .ok module => pure (toExpr module)
  | .error message => throwError "WAT decoder rejected: {message}"

end Wasm

kernel_decoder

namespace PrefixWasm
open Wasm

/-- The text `wasm-tools print prefix.wasm` produced (checked by `check.sh`). -/
def printedWat : String := include_str "prefix.printed.wat"

/-- The module the theorems are about. -/
def prefixModule : Module := prefixWat% "prefix.printed.wat"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- Kernel-checked: Talos's verification decoder maps the printed text to
exactly `prefixModule`. -/
theorem prefixModule_decodes :
    Decoder.Wat.decodeForVerification printedWat = .ok prefixModule := by
  cbv


end PrefixWasm
