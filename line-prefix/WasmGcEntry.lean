import WasmGcHosts

namespace PrefixWasm
open Wasm SmallStep PrefixGc

theorem alloc_default (st : Store Host) (lc : Locals) (n : UInt32) :
    execGcOp prefixModule st {lc with values := .i32 n :: lc.values}
      (.arrayNewDefault 0) =
    .Fallthrough {st with gcHeap := st.gcHeap ++
        [.array 0 (List.replicate n.toNat (.i32 0))]}
      {lc with values := .anyref (some (.array st.gcHeap.length)) :: lc.values} := by
  rfl

def entryMachine (s : Bool) (host : Host) (heap : List GcObject) : MachineStore Host :=
  { runtime := { instances := #[{ module := prefixModule, host := env }], entry := ⟨0⟩ }
    wasm := store s host heap }

def entryCode : Program :=
  [.localGet 1, .gc (.arrayNewDefault 0), .localSet 2,
   .localGet 1, .const 3, .mul, .gc (.arrayNewDefault 0), .localSet 3,
   .localGet 0, .localGet 2, .const 0, .call 6, .localSet 1]

def dataStart (s : Bool) (host : Host) (heap : List GcObject)
    (units : List UInt32) (code : Program) (calls : List CallFrame := []) : Config Host :=
  ⟨.running
    { locals := { params := [.externref (some host.strings.length), .i32 (UInt32.ofNat units.length)]
                  locals := [.anyref none, .anyref none, .i32 0, .i32 0, .i32 0] }
      code := entryCode ++ code, resultArity := 0, callerRemainder := [], calls := calls },
    entryMachine s (prepareHost host units) heap⟩

def dataReady (s : Bool) (host : Host) (heap : List GcObject)
    (units : List UInt32) (code : Program) (calls : List CallFrame := []) : Config Host :=
  ⟨.running
    { locals := { params := [.externref (some host.strings.length), .i32 (UInt32.ofNat units.length)]
                  locals := [.anyref (some (.array heap.length)),
                    .anyref (some (.array (heap.length+1))), .i32 0, .i32 0, .i32 0] }
      code := code, resultArity := 0, callerRemainder := [], calls := calls },
    entryMachine s (prepareHost host units)
      (arrayHeap heap units (List.replicate (3*units.length) 0))⟩

/-- The callback allocates fresh arrays and faithfully imports the immutable
input string before entering the transformation loop. -/
theorem data_entry_copy (s : Bool) (host : Host) (heap : List GcObject)
    (units : List UInt32) (code : Program) (hb : units.length ≤ 4096) (calls : List CallFrame := []) :
    ∃ trace, Steps (dataStart s host heap units code calls) trace
      (dataReady s host heap units code calls) := by
  have hn : (UInt32.ofNat units.length).toNat = units.length :=
    UInt32.toNat_ofNat_of_lt' (by change _ < 4294967296; omega)
  have hm : (3 * UInt32.ofNat units.length).toNat = 3*units.length := by
    rw [UInt32.toNat_mul, hn]
    change 3 * units.length % 4294967296 = 3*units.length
    rw [Nat.mod_eq_of_lt (by omega)]
  unfold dataStart dataReady entryCode
  refine ⟨([.localGet 1, .gc (.arrayNewDefault 0), .localSet 2,
    .localGet 1, .const 3, .mul, .gc (.arrayNewDefault 0), .localSet 3,
    .localGet 0, .localGet 2, .const 0] : Program).map StepKind.instruction ++
    [.host 6, .instruction (.localSet 1)], ?_⟩
  refine Steps.cons (.localGet rfl) ?_
  refine Steps.cons (.gcFallthrough (alloc_default (store s (prepareHost host units) heap)
    { params := [.externref (some host.strings.length), .i32 (UInt32.ofNat units.length)]
      locals := [.anyref none, .anyref none, .i32 0, .i32 0, .i32 0] }
    (UInt32.ofNat units.length))) ?_
  refine Steps.cons (.localSet rfl) ?_
  refine Steps.cons (.localGet rfl) ?_
  refine Steps.cons .const ?_
  refine Steps.cons .mul ?_
  refine Steps.cons (.gcFallthrough (alloc_default
    { (store s (prepareHost host units) heap) with gcHeap := heap ++
      [.array 0 (List.replicate (UInt32.ofNat units.length).toNat (.i32 0))] }
    { params := [.externref (some host.strings.length), .i32 (UInt32.ofNat units.length)]
      locals := [.anyref (some (.array heap.length)), .anyref none, .i32 0, .i32 0, .i32 0] }
    (3 * UInt32.ofNat units.length))) ?_
  refine Steps.cons (.localSet rfl) ?_
  refine Steps.cons (.localGet rfl) ?_
  refine Steps.cons (.localGet rfl) ?_
  refine Steps.cons .const ?_
  have hargs : prefixModule.imports[6].params.length = 3 := rfl
  have hresults : prefixModule.imports[6].results.length = 1 := rfl
  have hcopy := into_invoke
    (store s (prepareHost host units)
      (arrayHeap heap (List.replicate units.length 0) (List.replicate (3*units.length) 0)))
    heap units (List.replicate (3*units.length) 0) host.strings.length rfl
    (prepareHost_lookup host units)
  refine Steps.cons (.callHostReturn
    (show 6 < prefixModule.imports.length from by decide) rfl rfl
    (by simpa [entryMachine, store, hn, hm, arrayHeap, List.map_replicate,
      List.append_assoc, hargs] using hcopy)) ?_
  refine Steps.cons (.localSet rfl) ?_
  simpa [dataReady, entryMachine, store, hn, hm, arrayHeap, List.map_replicate,
    List.append_assoc, hresults, hargs] using (Steps.refl (dataReady s host heap units code calls))

end PrefixWasm
