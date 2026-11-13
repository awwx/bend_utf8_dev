import WasmModule
import GcSupport
import TextSpec

namespace PrefixWasm
open Wasm
inductive Event where
  | createInput | createOutput
  | onData (handle callback : UInt32)
  | onClose (handle callback : UInt32)
  | write (handle : UInt32) (text : List UInt32)
  | end (handle : UInt32)
  deriving DecidableEq, Repr
/-- Host strings are immutable UTF-16 code-unit sequences. References are indices.
The table is an abstract heap; unreachable strings may be collected by Node. -/
structure Host where
  log : List Event := []
  strings : List (List UInt32) := []
  deriving Inhabited

def createInput : HostFn Host where
  params := []; results := [.i32]
  invoke := fun st _ => .Return [.i32 0] { st with host.log := st.host.log ++ [.createInput] }
def createOutput : HostFn Host where
  params := []; results := [.i32]
  invoke := fun st _ => .Return [.i32 1] { st with host.log := st.host.log ++ [.createOutput] }
def binary (event : UInt32 → UInt32 → Event) : HostFn Host where
  params := [.i32, .i32]; results := []
  invoke := fun st args => match args with
    | [.i32 a, .i32 b] => .Return [] { st with host.log := st.host.log ++ [event a b] }
    | _ => .Trap st "wrong arguments"
def writeOutput : HostFn Host where
  params := [.i32, .externref]; results := []
  invoke := fun st args => match args with
    | [.i32 h, .externref (some i)] => match st.host.strings[i]? with
      | some units => .Return [] { st with host.log := st.host.log ++ [.write h units] }
      | none => .Trap st "not a string"
    | _ => .Trap st "wrong arguments"
def endOutput : HostFn Host where
  params := [.i32]; results := []
  invoke := fun st args => match args with
    | [.i32 a] => .Return [] { st with host.log := st.host.log ++ [.end a] }
    | _ => .Trap st "wrong arguments"

/-- The builtin copies code units, not Unicode scalars, into a mutable i16 GC
array. Both the string and destination are validated, and index addition uses
natural numbers rather than wrapping i32 arithmetic. -/
def intoCharCodeArray : HostFn Host where
  params := [.externref, .ref true (.concrete 0), .i32]; results := [.i32]
  invoke := fun st args => match args with
    | [.externref (some i), .anyref (some (.array a)), .i32 start] =>
      match st.host.strings[i]?, st.gcHeap[a]? with
      | some units, some (.array ty elems) =>
        if ty = 0 ∧ start.toNat + units.length ≤ elems.length then
          .Return [.i32 (UInt32.ofNat units.length)]
            { st with gcHeap := st.gcHeap.set a (.array ty
              (elems.take start.toNat ++ units.map Value.i32 ++
                elems.drop (start.toNat + units.length))) }
        else .Trap st "invalid string destination"
      | _, _ => .Trap st "not a string or i16 array"
    | _ => .Trap st "wrong arguments"

def unpackUnits (elems : List Value) : List UInt32 :=
  elems.map fun | .i32 u => u | _ => 0

/-- The builtin produces a new immutable string from [start,stop), before the
mutable GC array can be reused. It preserves all Wasm state except the abstract
host string table. -/
def fromCharCodeArray : HostFn Host where
  params := [.ref true (.concrete 0), .i32, .i32]; results := [.ref false .extern]
  invoke := fun st args => match args with
    | [.anyref (some (.array a)), .i32 start, .i32 stop] =>
      match st.gcHeap[a]? with
      | some (.array ty elems) =>
        if ty = 0 ∧ start.toNat ≤ stop.toNat ∧ stop.toNat ≤ elems.length then
          .Return [.externref (some st.host.strings.length)]
            { st with host.strings := st.host.strings ++
              [unpackUnits ((elems.drop start.toNat).take (stop.toNat-start.toNat))] }
        else .Trap st "invalid string source"
      | _ => .Trap st "not an i16 array"
    | _ => .Trap st "wrong arguments"

/-- Native string length is an unsigned i32 count of UTF-16 units. Reachable
strings are required to fit that representation, as actual Node strings do. -/
def stringLength : HostFn Host where
  params := [.externref]; results := [.i32]
  invoke := fun st args => match args with
    | [.externref (some i)] => match st.host.strings[i]? with
      | some units => .Return [.i32 (UInt32.ofNat units.length)] st
      | none => .Trap st "not a string"
    | _ => .Trap st "wrong arguments"

/-- Native substring clamps the stop index and returns empty for reversed or
out-of-range starts; it does not perform Unicode interpretation. -/
def substring : HostFn Host where
  params := [.externref, .i32, .i32]; results := [.ref false .extern]
  invoke := fun st args => match args with
    | [.externref (some i), .i32 start, .i32 stop] => match st.host.strings[i]? with
      | some units =>
        let result := if stop.toNat < start.toNat ∨ units.length < start.toNat then []
          else (units.drop start.toNat).take (stop.toNat-start.toNat)
        .Return [.externref (some st.host.strings.length)]
          {st with host.strings := st.host.strings ++ [result]}
      | none => .Trap st "not a string"
    | _ => .Trap st "wrong arguments"

/-- Native UTF-16 unit access traps outside the string. -/
def charCodeAt : HostFn Host where
  params := [.externref, .i32]; results := [.i32]
  invoke := fun st args => match args with
    | [.externref (some i), .i32 index] => match st.host.strings[i]? with
      | some units => match units[index.toNat]? with
        | some unit => .Return [.i32 unit] st
        | none => .Trap st "string index out of bounds"
      | none => .Trap st "not a string"
    | _ => .Trap st "wrong arguments"

def env : HostEnv Host :=
  { funcs := [createInput, createOutput, binary .onData, binary .onClose,
      writeOutput, endOutput, intoCharCodeArray, fromCharCodeArray,
      stringLength, substring, charCodeAt] }

def store (start : Bool) (host : Host) (heap : List GcObject) : Store Host :=
  { (prefixModule.initialStore : Store Host) with
    globals := ⟨[.i32 (if start then 1 else 0), .i32 0, .i32 1]⟩
    host := host, gcHeap := heap }
def initial (host : Host) : Store Host :=
  { (prefixModule.initialStore : Store Host) with host := host }
def initialization : List Event :=
  [.createInput, .createOutput, .onData 0 1, .onClose 0 2]
def prepareHost (host : Host) (units : List UInt32) : Host :=
  { host with strings := host.strings ++ [units] }
def callbackHost (start : Bool) (host : Host) (units : List UInt32) : Host :=
  { log := host.log ++ [.write 1 (LinePrefix.run start units).2],
    strings := host.strings ++ [units, (LinePrefix.run start units).2] }
def callbackHeap (start : Bool) (heap : List GcObject) (units : List UInt32) : List GcObject :=
  heap ++ [.array 0 (units.map Value.i32),
    .array 0 (((LinePrefix.run start units).2 ++
      List.replicate (3*units.length-(LinePrefix.run start units).2.length) 0).map Value.i32)]
def Runs (op : String) (st : Store Host) (args : List Value)
    (out : Store Host) : Prop :=
  RunsExportWith env prefixModule op { initial := st, arguments := args }
    (fun r => r.values = [] ∧ r.final = out)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem init_correct (host : Host) :
    Runs "init" (initial host) []
      (store true { host with log := host.log ++ initialization } []) := by
  refine ⟨_, rfl, ?_⟩
  apply SmallStep.runSteps_result_terminates (fuel := 40)
  cbv
  congr 2
  cases host with
  | mk log strings =>
    cases log with
    | nil => rfl
    | cons a rest => simp [List.append_assoc]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem close_correct (start : Bool) (host : Host) (heap : List GcObject) :
    Runs "close" (store start host heap) []
      (store start { host with log := host.log ++ [.end 1] } heap) := by
  refine ⟨_, rfl, ?_⟩
  apply SmallStep.runSteps_result_terminates (fuel := 20)
  cbv

end PrefixWasm
