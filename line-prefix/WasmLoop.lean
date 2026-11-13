import Wasm
import WasmGcExit
import GcSupport
import Interpreter.Wasm.Examples.UIntLemmas
namespace PrefixWasm
open Wasm SmallStep PrefixGc

def prefixBody : Program :=
  [.localGet 3, .localGet 5, .const 62, .gc (.arraySet 0),
   .localGet 5, .const 1, .add, .localSet 5,
   .localGet 3, .localGet 5, .const 32, .gc (.arraySet 0),
   .localGet 5, .const 1, .add, .localSet 5]
def tailBody : Program :=
  [.localGet 3, .localGet 5, .localGet 6, .gc (.arraySet 0),
   .localGet 5, .const 1, .add, .localSet 5,
   .localGet 6, .const 10, .eq, .globalSet 0,
   .localGet 4, .const 1, .add, .localSet 4,
   .localGet 1, .const 1, .sub, .localSet 1, .br 0]
def loopBody : Program :=
  [.localGet 1, .eqz, .br_if 1,
   .localGet 2, .localGet 4, .gc (.arrayGetU 0), .localSet 6,
   .globalGet 0, .iff 0 0 prefixBody []] ++ tailBody
def afterLoop : Program :=
  [.globalGet 2, .localGet 3, .const 0, .localGet 5, .call 7, .call 4]
def blockFrame : ControlFrame :=
  { kind := .block, paramArity := 0, resultArity := 0,
    body := [.loop 0 0 loopBody], continuation := afterLoop, belowStack := [] }
def loopFrame : ControlFrame :=
  { kind := .loop, paramArity := 0, resultArity := 0,
    body := loopBody, continuation := [], belowStack := [] }
def machine (s : Bool) (host : Host) (heap : List GcObject) : MachineStore Host :=
  { runtime := { instances := #[{ module := prefixModule, host := env }], entry := ⟨0⟩ }
    wasm := store s host heap }
def loopHead (s : Bool) (host : Host) (heap : List GcObject)
    (input written : List UInt32) (cap i n ref : Nat) (c : UInt32) (calls : List CallFrame := []) : Config Host :=
  ⟨.running
    { locals := { params := [.externref (some ref), .i32 (UInt32.ofNat n)],
                  locals := [.anyref (some (.array heap.length)), .anyref (some (.array (heap.length+1))),
                    .i32 (UInt32.ofNat i), .i32 (UInt32.ofNat written.length), .i32 c] }
      code := loopBody, resultArity := 0, callerRemainder := []
      control := [loopFrame, blockFrame], calls := calls },
    machine s host (arrayHeap heap input (padded cap written))⟩

theorem get_eval (s : Bool) (host : Host) (heap : List GcObject) (input output : List UInt32)
    (i : Nat) (cp : UInt32) (hi : i < 2^32) (hc : input[i]? = some cp)
    (params locals vs : List Value) :
    execGcOp prefixModule (store s host (arrayHeap heap input output))
      { params := params, locals := locals, values := .i32 (UInt32.ofNat i) :: .anyref (some (.array heap.length)) :: vs }
      (.arrayGetU 0) =
    .Fallthrough (store s host (arrayHeap heap input output))
      { params := params, locals := locals, values := .i32 cp :: vs } := by
  simp only [execGcOp, store, arrayHeap_input]
  rw [UInt32.toNat_ofNat_of_lt' hi, List.getElem?_map, hc]
  rfl

theorem set_eval (s : Bool) (host : Host) (heap : List GcObject) (input written : List UInt32)
    (cap : Nat) (cp : UInt32) (hc : cp.toNat < 65536)
    (hw : written.length < cap) (hcap : cap < 2^32)
    (params locals vs : List Value) :
    execGcOp prefixModule (store s host (arrayHeap heap input (padded cap written)))
      { params := params, locals := locals, values := [.i32 cp, .i32 (UInt32.ofNat written.length), .anyref (some (.array (heap.length+1)))] ++ vs } (.arraySet 0) =
    .Fallthrough (store s host (arrayHeap heap input (padded cap (written++[cp]))))
      { params := params, locals := locals, values := vs } := by
  have hi : written.length < 2^32 := by omega
  simp only [List.cons_append, List.nil_append, execGcOp, store, arrayHeap_output]
  rw [UInt32.toNat_ofNat_of_lt' hi]
  have hl : ((padded cap written).map Value.i32).length = cap := by
    simp [padded]; omega
  rw [hl, ite_eq_right (by omega)]
  change Continuation.Fallthrough { (store s host (arrayHeap heap input (padded cap written))) with
    gcHeap := (arrayHeap heap input (padded cap written)).set (heap.length+1)
      (.array 0 (((padded cap written).map Value.i32).set written.length (.i32 (cp &&& 65535)))) }
    {params := params, locals := locals, values := vs} = _
  rw [mask16 cp hc, arrayHeap_set_output, padded_push cap written cp hw]
  rfl

def iterTrace (s : Bool) : List StepKind :=
  (([.localGet 1, .eqz, .br_if 1, .localGet 2, .localGet 4, .gc (.arrayGetU 0),
    .localSet 6, .globalGet 0, .iff 0 0 prefixBody []] : Program) ++
    (if s then prefixBody else [])).map StepKind.instruction ++
    [.administrative .exitControl] ++ tailBody.map StepKind.instruction

theorem loop_iter (s : Bool) (host : Host) (heap : List GcObject)
    (input written : List UInt32) (cap i n ref : Nat) (c cp : UInt32)
    (hn : n+1 < 2^32) (hi : i+1 < 2^32)
    (hw : written.length + 3 ≤ cap) (hcap : cap < 2^32)
    (hc : input[i]? = some cp) (hunit : cp.toNat < 65536) (calls : List CallFrame := []) :
    Steps (loopHead s host heap input written cap i (n+1) ref c calls) (iterTrace s)
      (loopHead (cp == 10) host heap input (written ++ LinePrefix.emit s cp)
        cap (i+1) n ref cp calls) := by
  have hn0 : UInt32.ofNat (n+1) ≠ 0 := by
    intro h
    have h' := congrArg UInt32.toNat h
    rw [UInt32.toNat_ofNat_of_lt' hn] at h'
    simp at h'
  have hadd (k : Nat) : 1 + UInt32.ofNat k = UInt32.ofNat (k+1) := by
    simp [UInt32.ofNat_add, UInt32.add_comm]
  have hsub : UInt32.ofNat (n+1) - 1 = UInt32.ofNat n := by simp [UInt32.ofNat_add]
  cases s
  case false =>
    wasm_steps [(.localGet rfl), (.eqz (result := 0) (by simp only [hn0, ↓reduceIte])), .brIfZero,
      (.localGet rfl), (.localGet rfl),
      (.gcFallthrough (store := machine false host (arrayHeap heap input (padded cap written))) (get_eval false host heap input (padded cap written) i cp (by omega) hc _ _ [])),
      (.localSet rfl), (.globalGet rfl), (.iff (by rfl)), (.exitControl rfl),
      (.localGet rfl), (.localGet rfl), (.localGet rfl),
      (.gcFallthrough (store := machine false host (arrayHeap heap input (padded cap written))) (set_eval false host heap input written cap cp hunit (by omega) hcap _ _ [])),
      (.localGet rfl), .const, .add, (.localSet rfl),
      (.localGet rfl), .const, (.eq rfl), (.globalSet rfl),
      (.localGet rfl), .const, .add, (.localSet rfl),
      (.localGet rfl), .const, .sub, (.localSet rfl)]
    simp only [setGlobal_zero_eq, hadd, hsub]
    simp [loopHead, LinePrefix.emit, machine, store]
    exact Steps.single (.br rfl)
  case true =>
    wasm_steps [(.localGet rfl), (.eqz (result := 0) (by simp only [hn0, ↓reduceIte])), .brIfZero,
      (.localGet rfl), (.localGet rfl),
      (.gcFallthrough (store := machine true host (arrayHeap heap input (padded cap written))) (get_eval true host heap input (padded cap written) i cp (by omega) hc _ _ [])),
      (.localSet rfl), (.globalGet rfl), (.iff (by rfl)),
      (.localGet rfl), (.localGet rfl), .const,
      (.gcFallthrough (store := machine true host (arrayHeap heap input (padded cap written))) (set_eval true host heap input written cap 62 (by decide) (by omega) hcap _ _ [])),
      (.localGet rfl), .const, .add, (.localSet rfl)]
    simp only [hadd]
    have hl1 : (written ++ [62]).length = written.length+1 := by simp
    rw [← hl1]
    wasm_steps [(.localGet rfl), (.localGet rfl), .const,
      (.gcFallthrough (store := machine true host (arrayHeap heap input (padded cap (written++[62])))) (set_eval true host heap input (written++[62]) cap 32 (by decide) (by simp; omega) hcap _ _ [])),
      (.localGet rfl), .const, .add, (.localSet rfl), (.exitControl rfl)]
    simp only [hadd]
    have hl2 : ((written ++ [62]) ++ [32]).length = (written++[62]).length+1 := by simp
    rw [← hl2]
    wasm_steps [(.localGet rfl), (.localGet rfl), (.localGet rfl),
      (.gcFallthrough (store := machine true host (arrayHeap heap input (padded cap ((written++[62])++[32])))) (set_eval true host heap input ((written++[62])++[32]) cap cp hunit (by simp; omega) hcap _ _ [])),
      (.localGet rfl), .const, .add, (.localSet rfl),
      (.localGet rfl), .const, (.eq rfl), (.globalSet rfl),
      (.localGet rfl), .const, .add, (.localSet rfl),
      (.localGet rfl), .const, .sub, (.localSet rfl)]
    simp only [setGlobal_zero_eq, hadd, hsub]
    simp [loopHead, LinePrefix.emit, machine, store, List.append_assoc, UInt32.add_assoc]
    exact Steps.single (.br rfl)

theorem loop_exit_steps (s : Bool) (host : Host) (heap : List GcObject)
    (input written : List UInt32) (cap i ref : Nat) (c : UInt32) (calls : List CallFrame := []) :
    Steps (loopHead s host heap input written cap i 0 ref c calls)
      [.instruction (.localGet 1), .instruction .eqz, .instruction (.br_if 1)]
      (loopExit s host heap input written cap i ref c calls) := by
  wasm_steps [(.localGet rfl), (.eqz rfl)]
  exact Steps.single (.brIf (by decide) rfl)

theorem emit_length (s : Bool) (cp : UInt32) : (LinePrefix.emit s cp).length ≤ 3 := by
  cases s <;> simp [LinePrefix.emit]

theorem run_length (s : Bool) (text : List UInt32) :
    (LinePrefix.run s text).2.length ≤ 3*text.length := by
  induction text generalizing s with
  | nil => simp [LinePrefix.run]
  | cons cp rest ih =>
    have he := emit_length s cp
    have hr := ih (cp == 10)
    simp only [LinePrefix.run, List.length_append, List.length_cons]
    omega

theorem loop_correct (rest : List UInt32) (s : Bool) (host : Host) (heap : List GcObject)
    (past written : List UInt32) (cap ref : Nat) (c : UInt32)
    (hinput : past.length + rest.length ≤ 4096)
    (hspace : written.length + 3*rest.length ≤ cap) (hcap : cap ≤ 12288)
    (hunits : ∀ u ∈ rest, u.toNat < 65536) (calls : List CallFrame := []) :
    ∃ i' c' trace,
      Steps (loopHead s host heap (past++rest) written cap past.length rest.length ref c calls) trace
        (loopExit (LinePrefix.run s rest).1 host heap (past++rest)
          (written++(LinePrefix.run s rest).2) cap i' ref c' calls) := by
  induction rest generalizing s past written c with
  | nil =>
    refine ⟨past.length, c, [.instruction (.localGet 1), .instruction .eqz, .instruction (.br_if 1)], ?_⟩
    simpa only [LinePrefix.run, List.append_nil, List.length_nil] using
      (loop_exit_steps s host heap past written cap past.length ref c calls)
  | cons cp rest ih =>
    have hc : (past++cp::rest)[past.length]? = some cp := by
      simp [List.getElem?_append_right]
    have hcp := hunits cp (by simp)
    have he := emit_length s cp
    have hs := loop_iter s host heap (past++cp::rest) written cap past.length rest.length ref c cp
      (by simp only [List.length_cons] at hinput; omega)
      (by simp only [List.length_cons] at hinput; omega)
      (by simp only [List.length_cons] at hspace; omega)
      (by omega) hc hcp calls
    obtain ⟨i', c', trace, ht⟩ := ih (cp == 10) (past++[cp]) (written++LinePrefix.emit s cp) cp
      (by simp_all; omega) (by simp_all; omega) (by intro u hu; exact hunits u (by simp [hu]))
    refine ⟨i', c', iterTrace s ++ trace, ?_⟩
    have ht' : Steps
      (loopHead (cp == 10) host heap (past++cp::rest) (written++LinePrefix.emit s cp)
        cap (past.length+1) rest.length ref cp calls) trace
      (loopExit (LinePrefix.run s (cp::rest)).1 host heap (past++cp::rest)
        (written++(LinePrefix.run s (cp::rest)).2) cap i' ref c' calls) := by
      simpa [LinePrefix.run, List.append_assoc] using ht
    exact Steps.trans hs ht'

end PrefixWasm
