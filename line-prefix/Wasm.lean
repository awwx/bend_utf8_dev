import WasmModule

/-!
Individual bridge operations and the persistent module-store invariant.
The host records operation arguments without deciding whether the application
selected the correct handles, callbacks, or text. Those facts are proved by the
module and combined-execution theorems. A write copies the memory words into
its event before returning and preserves the complete Wasm store otherwise.
The scheduler interprets recorded writes as FIFO asynchronous work.
-/

namespace PrefixWasm
open Wasm
inductive Event where
  | createInput | createOutput
  | onData (handle callback : UInt32)
  | onClose (handle callback : UInt32)
  | write (handle : UInt32) (text : List UInt32)
  | end (handle : UInt32)
  deriving DecidableEq, Repr
abbrev Host := List Event

abbrev readWords := Wasm.readWords
def createInput : HostFn Host where
  params := []; results := [.i32]
  invoke := fun st _ => .Return [.i32 0] { st with host := st.host ++ [.createInput] }
def createOutput : HostFn Host where
  params := []; results := [.i32]
  invoke := fun st _ => .Return [.i32 1] { st with host := st.host ++ [.createOutput] }
def binary (event : UInt32 → UInt32 → Event) : HostFn Host where
  params := [.i32, .i32]; results := []
  invoke := fun st args => match args with
    | [.i32 a, .i32 b] => .Return [] { st with host := st.host ++ [event a b] }
    | _ => .Trap st "wrong arguments"
def writeOutput : HostFn Host where
  params := [.i32, .i32, .i32]; results := []
  invoke := fun st args => match args with
    | [.i32 h, .i32 p, .i32 n] =>
      if p.toNat % 4 = 0 ∧ p.toNat + 4*n.toNat ≤ st.mem.pages*65536 then
        .Return [] { st with host := st.host ++ [.write h (readWords st.mem p.toNat n.toNat)] }
      else .Trap st "output range out of bounds"
    | _ => .Trap st "wrong arguments"
def endOutput : HostFn Host where
  params := [.i32]; results := []
  invoke := fun st args => match args with
    | [.i32 a] => .Return [] { st with host := st.host ++ [.end a] }
    | _ => .Trap st "wrong arguments"
/-- Import order agrees with `prefixModule`. Callback tokens 1 and 2 designate
`data` and `close` in the bridge; they are not raw Wasm function indices. -/
def env : HostEnv Host :=
  { funcs := [createInput, createOutput, binary .onData, binary .onClose,
      writeOutput, endOutput] }

/-- Canonical persistent store: one line-start flag, input handle 0 and output
handle 1. Memory is arbitrary between callbacks; the bridge may replace only
input storage, while callback proofs account for every output-memory mutation. -/
def store (start : Bool) (log : Host) (mem : Mem) : Store Host :=
  { (prefixModule.initialStore : Store Host) with
    globals := ⟨[.i32 (if start then 1 else 0), .i32 0, .i32 1]⟩
    host := log, mem := mem }
def initial (log : Host) : Store Host :=
  { (prefixModule.initialStore : Store Host) with host := log }
def initialization : Host :=
  [.createInput, .createOutput, .onData 0 1, .onClose 0 2]
def Runs (op : String) (st : Store Host) (args : List Value)
    (out : Store Host) : Prop :=
  RunsExportWith env prefixModule op { initial := st, arguments := args }
    (fun r => r.values = [] ∧ r.final = out)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem init_correct (log : Host) :
    Runs "init" (initial log) []
      (store true (log ++ initialization) (prefixModule.initialStore (α := Host)).mem) := by
  refine ⟨_, rfl, ?_⟩
  apply SmallStep.runSteps_result_terminates (fuel := 40)
  cbv
  congr 1
  cases log with
  | nil => rfl
  | cons a rest => simp [List.append_assoc]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem close_correct (start : Bool) (log : Host) (mem : Mem) :
    Runs "close" (store start log mem) [] (store start (log ++ [.end 1]) mem) := by
  refine ⟨_, rfl, ?_⟩
  apply SmallStep.runSteps_result_terminates (fuel := 20)
  cbv

end PrefixWasm
#print axioms PrefixWasm.prefixModule_decodes
#print axioms PrefixWasm.init_correct
#print axioms PrefixWasm.close_correct
