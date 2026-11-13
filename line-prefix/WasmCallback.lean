import WasmLoop
import WasmGcEntry

namespace PrefixWasm
open Wasm SmallStep PrefixGc

def dataCode : Program := [.block 0 0 [.loop 0 0 loopBody]] ++ afterLoop

theorem data_entry (s : Bool) (host : Host) (heap : List GcObject)
    (units : List UInt32) :
    startExportConfig? env prefixModule "data"
      { initial := store s (prepareHost host units) heap,
        arguments := [.i32 (UInt32.ofNat units.length), .externref (some host.strings.length)] } =
      some (dataStart s host heap units dataCode) := rfl

theorem data_loop_entry (s : Bool) (host : Host) (heap : List GcObject)
    (units : List UInt32) :
    Steps (dataReady s host heap units dataCode)
      [.instruction (.block 0 0 [.loop 0 0 loopBody]), .instruction (.loop 0 0 loopBody)]
      (loopHead s (prepareHost host units) heap units [] (3*units.length)
        0 units.length host.strings.length 0) := by
  wasm_steps [.block, .loop]
  exact Steps.refl _

/-- The concrete GC callback transforms UTF-16 code units, preserving module
state and recording an immutable snapshot of its complete output. -/
theorem data_correct (s : Bool) (host : Host) (heap : List GcObject)
    (units : List UInt32) (hb : units.length ≤ 4096)
    (hu : ∀ u ∈ units, u.toNat < 65536) :
    Runs "data" (store s (prepareHost host units) heap)
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

end PrefixWasm
