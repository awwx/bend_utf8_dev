import Wasm

namespace PrefixWasm
open Wasm PrefixGc

/-- Copying a whole immutable string into its freshly allocated i16 array
changes precisely that array, preserving the output array and all host state. -/
theorem into_invoke (st : Store Host) (heap : List GcObject)
    (units output : List UInt32) (i : Nat)
    (hh : st.gcHeap = arrayHeap heap (List.replicate units.length 0) output)
    (hs : st.host.strings[i]? = some units) :
    intoCharCodeArray.invoke st [.externref (some i),
        .anyref (some (.array heap.length)), .i32 0] =
      .Return [.i32 (UInt32.ofNat units.length)]
        { st with gcHeap := arrayHeap heap units output } := by
  simp only [intoCharCodeArray, hs, hh, arrayHeap_input]
  simp [arrayHeap, List.map_replicate]

@[simp] theorem unpack_mapped (units : List UInt32) :
    unpackUnits (units.map Value.i32) = units := by
  simp [unpackUnits, List.map_map, Function.comp_def]

/-- Capturing an output prefix copies it to an immutable host string before
returning. Spare mutable array slots are excluded from the captured string. -/
theorem from_invoke (st : Store Host) (heap : List GcObject)
    (input written : List UInt32) (capacity : Nat)
    (hh : st.gcHeap = arrayHeap heap input (padded capacity written))
    (hw : written.length ≤ capacity) (h32 : written.length < 2^32) :
    fromCharCodeArray.invoke st [.anyref (some (.array (heap.length+1))),
        .i32 0, .i32 (UInt32.ofNat written.length)] =
      .Return [.externref (some st.host.strings.length)]
        { st with host.strings := st.host.strings ++ [written] } := by
  have hnat : (UInt32.ofNat written.length).toNat = written.length :=
    UInt32.toNat_ofNat_of_lt' h32
  simp only [fromCharCodeArray, hh, arrayHeap_output, hnat]
  simp [padded, hw, unpack_mapped]

/-- A write records the already captured immutable string, leaving the GC heap
and every other Wasm component unchanged. -/
theorem write_invoke (st : Store Host) (handle : UInt32) (i : Nat)
    (units : List UInt32) (hs : st.host.strings[i]? = some units) :
    writeOutput.invoke st [.i32 handle, .externref (some i)] =
      .Return [] { st with host.log := st.host.log ++ [.write handle units] } := by
  simp [writeOutput, hs]

@[simp] theorem prepareHost_lookup (host : Host) (units : List UInt32) :
    (prepareHost host units).strings[host.strings.length]? = some units := by
  simp [prepareHost, List.getElem?_append_right]

@[simp] theorem appended_string_lookup (host : Host) (units : List UInt32) :
    (host.strings ++ [units])[host.strings.length]? = some units := by
  simp [List.getElem?_append_right]

end PrefixWasm
