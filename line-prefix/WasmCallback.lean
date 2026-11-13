import WasmLoop
import WasmGcEntry

namespace PrefixWasm
open Wasm SmallStep PrefixGc

def dataCode : Program := [.block 0 0 [.loop 0 0 loopBody]] ++ afterLoop

theorem data_entry (s : Bool) (host : Host) (heap : List GcObject)
    (units : List UInt32) :
    startExportConfig? env prefixModule "_chunk"
      { initial := store s (prepareHost host units) heap,
        arguments := [.i32 (UInt32.ofNat units.length), .externref (some host.strings.length)] } =
      some (dataStart s host heap units dataCode) := rfl

theorem data_loop_entry (s : Bool) (host : Host) (heap : List GcObject)
    (units : List UInt32) (calls : List CallFrame := []) :
    Steps (dataReady s host heap units dataCode calls)
      [.instruction (.block 0 0 [.loop 0 0 loopBody]), .instruction (.loop 0 0 loopBody)]
      (loopHead s (prepareHost host units) heap units [] (3*units.length)
        0 units.length host.strings.length 0 calls) := by
  wasm_steps [.block, .loop]
  exact Steps.refl _

/-- The concrete GC callback transforms UTF-16 code units, preserving module
state and recording an immutable snapshot of its complete output. -/
theorem data_correct (s : Bool) (host : Host) (heap : List GcObject)
    (units : List UInt32) (hb : units.length ≤ 4096)
    (hu : ∀ u ∈ units, u.toNat < 65536) :
    Runs "_chunk" (store s (prepareHost host units) heap)
      [.i32 (UInt32.ofNat units.length), .externref (some host.strings.length)]
      (store (LinePrefix.run s units).1 (callbackHost s host units)
        (callbackHeap s heap units)) := by
  obtain ⟨entryTrace, hentry⟩ := data_entry_copy s host heap units dataCode hb
  obtain ⟨i', c', loopTrace, hloop⟩ := loop_correct units s (prepareHost host units) heap
    [] [] (3*units.length) host.strings.length 0
    (by simpa using hb) (by simp) (by omega) hu
  have hlen := LinePrefix.run_length s units
  have hexit := exit_correct (LinePrefix.run s units).1 (prepareHost host units) heap
    units (LinePrefix.run s units).2 (3*units.length) i' host.strings.length c'
    hlen (by omega)
  refine ⟨dataStart s host heap units dataCode, data_entry s host heap units, ?_⟩
  obtain ⟨exitTrace, values, final, exitSteps, post⟩ := hexit
  refine ⟨entryTrace ++ [.instruction (.block 0 0 [.loop 0 0 loopBody]),
    .instruction (.loop 0 0 loopBody)] ++ loopTrace ++ exitTrace, values, final, ?_, ?_⟩
  · simpa only [List.append_assoc] using
      (Steps.trans hentry (Steps.trans (data_loop_entry s host heap units)
        (Steps.trans (by simpa using hloop) exitSteps)))
  · rcases post with ⟨hv, hf⟩
    refine ⟨hv, ?_⟩
    simpa [callbackHost, callbackHeap, prepareHost, padded, arrayHeap,
      List.append_assoc] using hf

/-- The bounded helper may return into any suspended same-instance caller. -/
theorem chunk_return (s : Bool) (host : Host) (heap : List GcObject)
    (units : List UInt32) (hb : units.length ≤ 4096)
    (hu : ∀ u ∈ units, u.toNat < 65536)
    (caller : CallFrame) (calls : List CallFrame) (hcaller : caller.returningInstance = ⟨0⟩) :
    ∃ trace, Steps (dataStart s host heap units dataCode (caller::calls)) trace
      (resumeConfig caller calls (LinePrefix.run s units).1
        (callbackHost s host units) (callbackHeap s heap units)) := by
  obtain ⟨entryTrace, hentry⟩ := data_entry_copy s host heap units dataCode hb (caller::calls)
  obtain ⟨i', c', loopTrace, hloop⟩ := loop_correct units s (prepareHost host units) heap
    [] [] (3*units.length) host.strings.length 0
    (by simpa using hb) (by simp) (by omega) hu (caller::calls)
  have hlen := LinePrefix.run_length s units
  obtain ⟨exitTrace, hexit⟩ := exit_return (LinePrefix.run s units).1 (prepareHost host units) heap
    units (LinePrefix.run s units).2 (3*units.length) i' host.strings.length c'
    hlen (by omega) caller calls hcaller
  refine ⟨entryTrace ++ [.instruction (.block 0 0 [.loop 0 0 loopBody]),
    .instruction (.loop 0 0 loopBody)] ++ loopTrace ++ exitTrace, ?_⟩
  have hs := Steps.trans hentry (Steps.trans (data_loop_entry s host heap units (caller::calls))
    (Steps.trans (by simpa using hloop) hexit))
  simpa [callbackHost, callbackHeap, prepareHost, padded, arrayHeap, List.append_assoc] using hs

/-- A call-site with the helper arguments on the operand stack. The caller's
remaining stack and suspended control frames are preserved by the helper. -/
def chunkCall (s : Bool) (host : Host) (heap : List GcObject) (units : List UInt32)
    (caller : CallFrame) (calls : List CallFrame) : Config Host :=
  ⟨.running
    { locals := ⟨caller.locals.params, caller.locals.locals,
        .i32 (UInt32.ofNat units.length) :: .externref (some host.strings.length) :: caller.locals.values⟩
      code := .call 12 :: caller.continuation
      resultArity := caller.resultArity, callerRemainder := caller.callerRemainder
      control := caller.control, calls := calls },
    machine s (prepareHost host units) heap⟩

theorem chunk_call_entry (s : Bool) (host : Host) (heap : List GcObject) (units : List UInt32)
    (caller : CallFrame) (calls : List CallFrame) (hcaller : caller.returningInstance = ⟨0⟩) :
    Step (chunkCall s host heap units caller calls) (.instruction (.call 12))
      (dataStart s host heap units dataCode (caller::calls)) := by
  cases caller with
  | mk locals continuation resultArity callerRemainder control returningInstance =>
    cases hcaller
    cases locals
    exact Step.call (functionIndex := 12)
      (store := machine s (prepareHost host units) heap) (by change ¬ 12 < 11; decide) rfl

theorem chunk_call (s : Bool) (host : Host) (heap : List GcObject)
    (units : List UInt32) (hb : units.length ≤ 4096)
    (hu : ∀ u ∈ units, u.toNat < 65536)
    (caller : CallFrame) (calls : List CallFrame) (hcaller : caller.returningInstance = ⟨0⟩) :
    ∃ trace, Steps (chunkCall s host heap units caller calls) trace
      (resumeConfig caller calls (LinePrefix.run s units).1
        (callbackHost s host units) (callbackHeap s heap units)) := by
  obtain ⟨trace, hs⟩ := chunk_return s host heap units hb hu caller calls hcaller
  exact ⟨_, Steps.cons (chunk_call_entry s host heap units caller calls hcaller) hs⟩

end PrefixWasm
