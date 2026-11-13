import WasmOuterCall

namespace PrefixWasm
open Wasm SmallStep

/-- Appending immutable strings cannot alter the original callback argument. -/
theorem original_string_preserved (s : Bool) (host : Host) (ref : Nat)
    (all part : List UInt32) (hr : host.strings[ref]? = some all) :
    (callbackHost s host part).strings[ref]? = some all := by
  obtain ⟨hbound, _⟩ := List.getElem?_eq_some_iff.mp hr
  simpa only [callbackHost, List.getElem?_append_left hbound] using hr

/-- The outer loop terminates by consuming a nonempty bounded slice each time.
Every transition is an actual Talos trace, including the internal helper call. -/
theorem outer_loop_correct (rest all : List UInt32) (s : Bool) (host : Host)
    (heap : List GcObject) (ref pos stop : Nat) (unit : UInt32)
    (hr : host.strings[ref]? = some all) (hrest : all.drop pos = rest)
    (hp : pos ≤ all.length) (hlen : all.length < 2^32)
    (hu : ∀ u ∈ all, u.toNat < 65536) :
    TerminatesWith (outerHead s host heap ref all.length pos stop unit)
      (fun values st => values = [] ∧ st.wasm =
        store (processParts s host heap (LinePrefix.Chunking.chunks rest)).atStart
          (processParts s host heap (LinePrefix.Chunking.chunks rest)).host
          (processParts s host heap (LinePrefix.Chunking.chunks rest)).heap) := by
  by_cases hzero : rest = []
  · have hlength := congrArg List.length hrest
    simp only [List.length_drop, hzero, List.length_nil] at hlength
    have hpos : pos = all.length := by omega
    subst pos
    simpa [hzero, LinePrefix.Chunking.chunks, processParts] using outer_done s host heap ref all.length stop unit
  · have hbounds := LinePrefix.Chunking.count_bounds hzero
    let count := LinePrefix.Chunking.count rest
    let part := rest.take count
    have hcount : 0 < count ∧ count ≤ 4096 ∧ count ≤ rest.length := hbounds
    have hlength : rest.length = all.length-pos := by rw [← hrest, List.length_drop]
    obtain ⟨unit', selectTrace, hselect⟩ := outer_select_steps s host heap ref pos stop unit all rest
      hr hrest hp hzero hlen
    have hpart : (all.drop pos).take (pos+count-pos) = part := by simp [part, hrest]
    have hpartunits : ∀ u ∈ (all.drop pos).take (pos+count-pos), u.toNat < 65536 := by
      intro u hu'
      exact hu u (List.mem_of_mem_drop (List.mem_of_mem_take hu'))
    obtain ⟨callTrace, hcall⟩ := outer_call_steps s host heap ref pos (pos+count) unit' all
      hr (by omega) (by omega) hlen (by omega) hpartunits
    rw [hpart] at hcall
    have hnewrest : all.drop (pos+count) = rest.drop count := by
      rw [← List.drop_drop, hrest]
    have hr' := original_string_preserved s host ref all part hr
    have hrec := outer_loop_correct (rest.drop count) all (LinePrefix.run s part).1
      (callbackHost s host part) (callbackHeap s heap part) ref (pos+count) (pos+count) unit'
      hr' hnewrest (by omega) hlen hu
    have hdone := hrec.prependSteps (Steps.trans hselect hcall)
    have hchunks : LinePrefix.Chunking.chunks rest =
        part :: LinePrefix.Chunking.chunks (rest.drop count) := by
      rw [LinePrefix.Chunking.chunks, dite_eq_right hzero]
    simpa only [hchunks, processParts] using hdone
termination_by rest.length
decreasing_by
  simp only [List.length_drop]
  have hb := (LinePrefix.Chunking.count_bounds hzero).1
  change 0 < count at hb
  omega

def outerStart (s : Bool) (host : Host) (heap : List GcObject) (units : List UInt32) : Config Host :=
  ⟨.running
    { locals := { params := [.externref (some host.strings.length)]
                  locals := [.i32 0, .i32 0, .i32 0, .i32 0] }
      code := [.localGet 0, .call 8, .localSet 1, .block 0 0 [.loop 0 0 outerBody]]
      resultArity := 0, callerRemainder := [] },
    outerMachine s (prepareHost host units) heap⟩

theorem outer_entry (s : Bool) (host : Host) (heap : List GcObject) (units : List UInt32) :
    startExportConfig? env prefixModule "data"
      {initial := store s (prepareHost host units) heap,
       arguments := [.externref (some host.strings.length)]} =
      some (outerStart s host heap units) := rfl

theorem outer_entry_steps (s : Bool) (host : Host) (heap : List GcObject) (units : List UInt32) :
    Steps (outerStart s host heap units)
      [.instruction (.localGet 0), .host 8, .instruction (.localSet 1),
       .instruction (.block 0 0 [.loop 0 0 outerBody]), .instruction (.loop 0 0 outerBody)]
      (outerHead s (prepareHost host units) heap host.strings.length units.length 0 0 0) := by
  have hi := length_invoke s (prepareHost host units) heap host.strings.length units
    (prepareHost_lookup host units)
  wasm_steps [(.localGet rfl), (.callHostReturn (by change 8 < 11; decide) rfl rfl hi),
    (.localSet rfl), .block, .loop]
  exact Steps.refl _

/-- The public one-argument callback computes its own length and all chunks. -/
theorem outer_data_correct (s : Bool) (host : Host) (heap : List GcObject)
    (units : List UInt32) (hlen : units.length < 2^32)
    (hu : ∀ u ∈ units, u.toNat < 65536) :
    Runs "data" (store s (prepareHost host units) heap)
      [.externref (some host.strings.length)]
      (store (wholeResult s host heap units).atStart
        (wholeResult s host heap units).host (wholeResult s host heap units).heap) := by
  refine ⟨outerStart s host heap units, outer_entry s host heap units, ?_⟩
  exact (outer_loop_correct units units s (prepareHost host units) heap
    host.strings.length 0 0 0 (prepareHost_lookup host units) rfl (by omega) hlen hu).prependSteps
      (outer_entry_steps s host heap units)

end PrefixWasm
