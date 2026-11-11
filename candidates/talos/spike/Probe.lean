import Interpreter.Wasm.Decoder.ProofEval
import Interpreter.Wasm.Host.Run
import Lean.Elab.Term

/-! Statement-level probes (d). Not part of the spike's verified claims. -/

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
syntax (name := probeWat) "probeWat% " str : term
@[term_elab probeWat] def elabProbeWat : TermElab := fun stx _ => do
  let `(probeWat% $p:str) := stx | throwUnsupportedSyntax
  match Decoder.Wat.decodeForVerification (← IO.FS.readFile p.getString) with
  | .ok module => pure (toExpr module)
  | .error message => throwError "WAT decoder rejected: {message}"
end Wasm

namespace Probe
open Wasm

/-! ## (ii) GC `(array (mut i16))` + `wasm:js-string.fromCharCodeArray` -/

def gcModule : Module := probeWat% "gc.printed.wat"

#eval gcModule.imports.map (fun i => (i.module, i.name))
#eval gcModule.funcs.map (·.body.length)

/-- Host-side model of the JS strings the builtin creates: externref `i`
names `strings[i]`, a list of UTF-16 code units. -/
structure JsHost where
  strings : List (List UInt16) := []
deriving Inhabited

/-- A model of `fromCharCodeArray(array, start, end)`; this is a hand-written
assumption about the engine builtin, not something Talos provides. -/
def fromCharCodeArray : HostFn JsHost where
  params := [.ref true (.concrete 0), .i32, .i32]
  results := [.ref false .extern]
  invoke := fun st args =>
    match args with
    | [.anyref (some (.array a)), .i32 start, .i32 stop] =>
      match st.gcHeap[a]? with
      | some (.array _ elems) =>
        if start ≤ stop ∧ stop.toNat ≤ elems.length then
          let units := (elems.drop start.toNat |>.take (stop - start).toNat).map
            fun | .i32 v => v.toUInt16 | _ => 0
          .Return [.externref (some st.host.strings.length)]
            { st with host := { strings := st.host.strings ++ [units] } }
        else .Trap st "RangeError"
      | _ => .Trap st "TypeError"
    | _ => .Trap st "TypeError"

def jsEnv : HostEnv JsHost := { funcs := [fromCharCodeArray] }

/-- Shape of a theorem about a module that builds a JS string. -/
def HelloSpec : Prop :=
  RunsExportWith jsEnv gcModule "hello" (ExportCall.ofHost gcModule {} [])
    (fun r => ∃ i, r.values = [.externref (some i)] ∧
       r.final.host.strings[i]? = some [104, 105])

def helloResult : String :=
  match startExportConfig? jsEnv gcModule "hello" (ExportCall.ofHost gcModule {} []) with
  | none => "no config"
  | some c => match (SmallStep.runSteps 40 c).result with
    | .success vs st => s!"success {repr vs} strings={st.wasm.host.strings}"
    | .trapped r _ => s!"trap {r.message}"
    | .outOfFuel _ => "out of fuel"
    | .internalError e _ => s!"internal {e.message}"
#eval helloResult

set_option maxRecDepth 100000 in
theorem hello_spec : HelloSpec := by
  refine ⟨_, rfl, ?_⟩
  apply SmallStep.runSteps_result_terminates (fuel := 40)
  cbv
  exact ⟨0, rfl, rfl⟩

/-! ## (i) Several calls on one persistent store -/

/-- Two consecutive calls; the second starts from the first's final store. -/
def TwoCalls (m : Module) (env : HostEnv Unit) (initial : Store Unit)
    (args1 args2 : List Value) (post : ExportReturn Unit → ExportReturn Unit → Prop) : Prop :=
  RunsExportWith env m "count_non_ascii" { initial, arguments := args1.reverse } fun r1 =>
    RunsExportWith env m "count_non_ascii" { initial := r1.final, arguments := args2.reverse } fun r2 =>
      post r1 r2

end Probe
#print axioms Probe.hello_spec
