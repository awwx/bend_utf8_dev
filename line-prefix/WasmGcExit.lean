import WasmGcHosts

namespace PrefixWasm
open Wasm SmallStep PrefixGc

def exitMachine (s : Bool) (host : Host) (heap : List GcObject) : MachineStore Host :=
  { runtime := { instances := #[{ module := prefixModule, host := env }], entry := ⟨0⟩ }
    wasm := store s host heap }

/-- The loop has consumed its input. The remaining code snapshots exactly the
written array prefix as a JS string and submits that immutable string. -/
def loopExit (s : Bool) (host : Host) (heap : List GcObject)
    (input written : List UInt32) (cap i ref : Nat) (c : UInt32) (calls : List CallFrame := []) : Config Host :=
  ⟨.running
    { locals := { params := [.externref (some ref), .i32 0],
                  locals := [.anyref (some (.array heap.length)), .anyref (some (.array (heap.length+1))),
                    .i32 (UInt32.ofNat i), .i32 (UInt32.ofNat written.length), .i32 c] }
      code := [.globalGet 2, .localGet 3, .const 0, .localGet 5, .call 7, .call 4]
      resultArity := 0, callerRemainder := [], calls := calls },
    exitMachine s host (arrayHeap heap input (padded cap written))⟩

theorem exit_correct (s : Bool) (host : Host) (heap : List GcObject)
    (input written : List UInt32) (cap i ref : Nat) (c : UInt32)
    (hw : written.length ≤ cap) (h32 : written.length < 2^32) :
    TerminatesWith (loopExit s host heap input written cap i ref c) (fun vs st =>
      vs = [] ∧ st.wasm =
        store s { log := host.log ++ [.write 1 written], strings := host.strings ++ [written] }
          (arrayHeap heap input (padded cap written))) := by
  let old := store s host (arrayHeap heap input (padded cap written))
  let captured := store s {host with strings := host.strings ++ [written]}
    (arrayHeap heap input (padded cap written))
  have hf : fromCharCodeArray.invoke old [.anyref (some (.array (heap.length+1))),
      .i32 0, .i32 (UInt32.ofNat written.length)] =
      .Return [.externref (some host.strings.length)] captured :=
    from_invoke old heap input written cap rfl hw h32
  have hs : captured.host.strings[host.strings.length]? = some written := by
    simp [captured, store]
  have hwrite : writeOutput.invoke captured [.i32 1, .externref (some host.strings.length)] =
      .Return [] (store s
        {log := host.log ++ [.write 1 written], strings := host.strings ++ [written]}
        (arrayHeap heap input (padded cap written))) :=
    write_invoke captured 1 host.strings.length written hs
  refine ⟨[.instruction (.globalGet 2), .instruction (.localGet 3), .instruction (.const 0),
    .instruction (.localGet 5), .host 7, .host 4, .administrative .finish], [],
    exitMachine s {log := host.log ++ [.write 1 written], strings := host.strings ++ [written]}
      (arrayHeap heap input (padded cap written)), ?_, ⟨rfl,rfl⟩⟩
  wasm_steps [(.globalGet rfl), (.localGet rfl), .const, (.localGet rfl),
    (.callHostReturn (by change 7 < 11; decide) rfl rfl hf),
    (.callHostReturn (by change 4 < 11; decide) rfl rfl hwrite)]
  exact Steps.single .finish

def resumeConfig (caller : CallFrame) (calls : List CallFrame)
    (s : Bool) (host : Host) (heap : List GcObject) : Config Host :=
  ⟨.running
    { locals := caller.locals, code := caller.continuation
      resultArity := caller.resultArity, callerRemainder := caller.callerRemainder
      control := caller.control, calls := calls }, exitMachine s host heap⟩

/-- The same output trace returns into an arbitrary suspended caller. -/
theorem exit_return (s : Bool) (host : Host) (heap : List GcObject)
    (input written : List UInt32) (cap i ref : Nat) (c : UInt32)
    (hw : written.length ≤ cap) (h32 : written.length < 2^32)
    (caller : CallFrame) (calls : List CallFrame) (hcaller : caller.returningInstance = ⟨0⟩) :
    ∃ trace, Steps (loopExit s host heap input written cap i ref c (caller::calls)) trace
      (resumeConfig caller calls s
        { log := host.log ++ [.write 1 written], strings := host.strings ++ [written] }
        (arrayHeap heap input (padded cap written))) := by
  let old := store s host (arrayHeap heap input (padded cap written))
  let captured := store s {host with strings := host.strings ++ [written]}
    (arrayHeap heap input (padded cap written))
  have hf : fromCharCodeArray.invoke old [.anyref (some (.array (heap.length+1))),
      .i32 0, .i32 (UInt32.ofNat written.length)] =
      .Return [.externref (some host.strings.length)] captured :=
    from_invoke old heap input written cap rfl hw h32
  have hs : captured.host.strings[host.strings.length]? = some written := by
    simp [captured, store]
  have hwrite : writeOutput.invoke captured [.i32 1, .externref (some host.strings.length)] =
      .Return [] (store s
        {log := host.log ++ [.write 1 written], strings := host.strings ++ [written]}
        (arrayHeap heap input (padded cap written))) :=
    write_invoke captured 1 host.strings.length written hs
  refine ⟨[.instruction (.globalGet 2), .instruction (.localGet 3), .instruction (.const 0),
    .instruction (.localGet 5), .host 7, .host 4, .administrative .returnFromCall], ?_⟩
  wasm_steps [(.globalGet rfl), (.localGet rfl), .const, (.localGet rfl),
    (.callHostReturn (by change 7 < 11; decide) rfl rfl hf),
    (.callHostReturn (by change 4 < 11; decide) rfl rfl hwrite)]
  exact Steps.single (Step.returnFromCallFallthrough hcaller)

end PrefixWasm
