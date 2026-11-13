import Wasm
import WasmTransform
import Interpreter.Wasm.Examples.UIntLemmas
/-!
The instruction proof splits into one iteration, induction on the remaining
word count, and the final imported write. Every transition uses Talos's
`SmallStep.Step`; no independent evaluator supplies the execution relation.
Natural-number loop indices are related to i32 locals with checked bounds.
One memory page holds 4096 input scalar words and 12288 output scalar words.
-/
namespace PrefixWasm
open Wasm SmallStep

def prefixBody : Program :=
  [.localGet 2, .const 62, .store32 0,
   .localGet 2, .const 4, .add, .localSet 2,
   .localGet 2, .const 32, .store32 0,
   .localGet 2, .const 4, .add, .localSet 2]
def tailBody : Program :=
  [.localGet 2, .localGet 3, .store32 0,
   .localGet 2, .const 4, .add, .localSet 2,
   .localGet 3, .const 10, .eq, .globalSet 0,
   .localGet 1, .const 4, .add, .localSet 1,
   .localGet 0, .const 1, .sub, .localSet 0, .br 0]
def loopBody : Program :=
  [.localGet 0, .eqz, .br_if 1,
   .localGet 1, .load32 0, .localSet 3,
   .globalGet 0, .iff 0 0 prefixBody []] ++ tailBody
def afterLoop : Program :=
  [.globalGet 2, .const 16384, .localGet 2, .const 16384, .sub,
   .const 4, .divU, .call 4]
def blockFrame : ControlFrame :=
  { kind := .block, paramArity := 0, resultArity := 0,
    body := [.loop 0 0 loopBody], continuation := afterLoop, belowStack := [] }
def loopFrame : ControlFrame :=
  { kind := .loop, paramArity := 0, resultArity := 0,
    body := loopBody, continuation := [], belowStack := [] }
def machine (s : Bool) (log : Host) (mem : Mem) : MachineStore Host :=
  { runtime := { instances := #[{ module := prefixModule, host := env }], entry := ⟨0⟩ }
    wasm := store s log mem }
def loopHead (s : Bool) (log : Host) (mem : Mem) (p n q : Nat) (c : UInt32) : Config Host :=
  ⟨.running
    { locals := { params := [.i32 (UInt32.ofNat n)],
                  locals := [.i32 (UInt32.ofNat p), .i32 (UInt32.ofNat q), .i32 c] }
      code := loopBody, resultArity := 0, callerRemainder := []
      control := [loopFrame, blockFrame] }, machine s log mem⟩

theorem module_body : prefixModule.funcs[1]?.map (·.body) =
    some ([.const 16384, .localSet 2, .block 0 0 [.loop 0 0 loopBody]] ++ afterLoop) := rfl

def advance (s : Bool) (m : Mem) (p q : Nat) : Bool × Mem × Nat :=
  let cp := m.read32 (UInt32.ofNat p)
  let ys := LinePrefix.emit s cp
  (cp == 10, writeWords m q ys, q + 4*ys.length)

def iterTrace (s : Bool) : List StepKind :=
  (([.localGet 0, .eqz, .br_if 1, .localGet 1, .load32 0, .localSet 3,
    .globalGet 0, .iff 0 0 prefixBody []] : Program) ++ (if s then prefixBody else [])).map
      StepKind.instruction ++ [.administrative .exitControl] ++ tailBody.map StepKind.instruction

theorem loop_iter (s : Bool) (log : Host) (mem : Mem) (p n q : Nat) (c : UInt32)
    (hp : p+4*(n+1) ≤ 16384) (hq : q+12*(n+1) ≤ 65536) (hm : mem.pages = 1) :
    let a := advance s mem p q
    ∃ trace, Steps (loopHead s log mem p (n+1) q c) trace
      (loopHead a.1 log a.2.1 (p+4) n a.2.2 (mem.read32 (UInt32.ofNat p))) := by
  have hn : UInt32.ofNat (n+1) ≠ 0 := by
    intro h
    have h' := congrArg UInt32.toNat h
    rw [UInt32.toNat_ofNat_of_lt' (by simp [UInt32.size]; omega)] at h'
    simp at h'
  have pb : (UInt32.ofNat p).toNat + 0 + 4 ≤ mem.pages * 65536 := by
    rw [UInt32.toNat_ofNat_of_lt' (by simp [UInt32.size]; omega), hm]; omega
  have qb : (UInt32.ofNat q).toNat + 0 + 4 ≤ mem.pages * 65536 := by
    rw [UInt32.toNat_ofNat_of_lt' (by simp [UInt32.size]; omega), hm]; omega
  have qb4 : (4 + UInt32.ofNat q).toNat + 0 + 4 ≤ mem.pages * 65536 := by
    rw [UInt32.toNat_add, UInt32.toNat_ofNat_of_lt' (by simp [UInt32.size]; omega), hm]
    have : 4 + q < 2^32 := by omega
    simp only [UInt32.toNat_ofNat] at *
    rw [Nat.mod_eq_of_lt this]; omega
  have qb8 : (4 + (4 + UInt32.ofNat q)).toNat + 0 + 4 ≤ mem.pages * 65536 := by
    rw [UInt32.toNat_add, UInt32.toNat_add,
      UInt32.toNat_ofNat_of_lt' (by simp [UInt32.size]; omega), hm]
    simp only [UInt32.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega
  have hadd (k : Nat) : 4 + UInt32.ofNat k = UInt32.ofNat (k+4) := by
    simp [UInt32.ofNat_add, UInt32.add_comm]
  have hsub : UInt32.ofNat (n+1) - 1 = UInt32.ofNat n := by
    simp [UInt32.ofNat_add]
  cases s
  case false =>
    refine ⟨iterTrace false, ?_⟩
    wasm_steps [(.localGet rfl), (.eqz (result := 0) (by simp only [hn, ↓reduceIte])), .brIfZero,
      (.localGet rfl), (.load32 rfl (by exact pb)), (.localSet rfl),
      (.globalGet rfl), (.iff (by rfl)), (.exitControl rfl),
      (.localGet rfl), (.localGet rfl), (.store32 rfl (by exact qb)),
      (.localGet rfl), .const, .add, (.localSet rfl),
      (.localGet rfl), .const, (.eq rfl), (.globalSet rfl),
      (.localGet rfl), .const, .add, (.localSet rfl),
      (.localGet rfl), .const, .sub, (.localSet rfl)]
    simp only [UInt32.add_zero, setMemory_eq, setGlobal_zero_eq]
    simp only [hadd, hsub]
    simp [loopHead, advance, LinePrefix.emit, writeWords, machine, store]
    exact Steps.single (.br rfl)

  case true =>
    refine ⟨iterTrace true, ?_⟩
    wasm_steps [(.localGet rfl), (.eqz (result := 0) (by simp only [hn, ↓reduceIte])), .brIfZero,
      (.localGet rfl), (.load32 rfl (by exact pb)), (.localSet rfl),
      (.globalGet rfl), (.iff (by rfl)),
      (.localGet rfl), .const, (.store32 rfl (by exact qb)),
      (.localGet rfl), .const, .add, (.localSet rfl),
      (.localGet rfl), .const, (.store32 rfl (by exact qb4)),
      (.localGet rfl), .const, .add, (.localSet rfl), (.exitControl rfl),
      (.localGet rfl), (.localGet rfl), (.store32 rfl (by exact qb8)),
      (.localGet rfl), .const, .add, (.localSet rfl),
      (.localGet rfl), .const, (.eq rfl), (.globalSet rfl),
      (.localGet rfl), .const, .add, (.localSet rfl),
      (.localGet rfl), .const, .sub, (.localSet rfl)]
    simp only [UInt32.add_zero, setMemory_eq, setGlobal_zero_eq]
    simp only [hadd, hsub]
    simp [loopHead, advance, LinePrefix.emit, writeWords, machine, store, Nat.add_assoc]
    exact Steps.single (.br rfl)

def loopExit (s : Bool) (log : Host) (mem : Mem) (p q : Nat) (c : UInt32) : Config Host :=
  ⟨.running
    { locals := { params := [.i32 0],
                  locals := [.i32 (UInt32.ofNat p), .i32 (UInt32.ofNat q), .i32 c] }
      code := afterLoop, resultArity := 0, callerRemainder := [] }, machine s log mem⟩

theorem loop_exit_steps (s : Bool) (log : Host) (mem : Mem) (p q : Nat) (c : UInt32) :
    ∃ trace, Steps (loopHead s log mem p 0 q c) trace (loopExit s log mem p q c) := by
  refine ⟨[.instruction (.localGet 0), .instruction .eqz, .instruction (.br_if 1)], ?_⟩
  wasm_steps [(.localGet rfl), (.eqz rfl)]
  exact Steps.single (.brIf (by decide) rfl)

theorem loop_correct (n : Nat) (s : Bool) (log : Host) (mem : Mem) (p q : Nat) (c : UInt32)
    (hp : p+4*n ≤ 16384) (hq : q+12*n ≤ 65536) (hm : mem.pages = 1) :
    let r := transform s mem p q n
    ∃ p' c' trace, Steps (loopHead s log mem p n q c) trace
      (loopExit r.1 log r.2.1 p' r.2.2 c') := by
  induction n generalizing s mem p q c with
  | zero =>
    obtain ⟨t, ht⟩ := loop_exit_steps s log mem p q c
    exact ⟨p, c, t, ht⟩
  | succ n ih =>
    obtain ⟨t, ht⟩ := loop_iter s log mem p n q c hp hq hm
    let cp := mem.read32 (UInt32.ofNat p)
    let ys := LinePrefix.emit s cp
    have hlen : ys.length ≤ 3 := emit_length s cp
    obtain ⟨p', c', t', ht'⟩ := ih (cp == 10) (writeWords mem q ys)
      (p+4) (q+4*ys.length) cp (by omega) (by omega) (by rw [writeWords_pages]; exact hm)
    exact ⟨p', c', t ++ t', Steps.trans ht ht'⟩

/-- The imported write snapshots complete scalar words before returning. -/
def exitOutput (q : Nat) (mem : Mem) : List UInt32 :=
  readWords mem 16384 ((UInt32.ofNat q - 16384) / 4).toNat

theorem exit_count (q : Nat) (hlo : 16384 ≤ q) (hhi : q ≤ 65536) :
    ((UInt32.ofNat q - 16384) / 4).toNat = (q-16384)/4 := by
  have hq : (UInt32.ofNat q).toNat = q :=
    UInt32.toNat_ofNat_of_lt' (by simp [UInt32.size]; omega)
  rw [UInt32.toNat_div, UInt32.toNat_sub_of_le _ _ (by
    rw [UInt32.le_iff_toNat_le, hq]; exact hlo), hq]
  rfl

theorem exit_correct (s : Bool) (log : Host) (mem : Mem) (p q : Nat) (c : UInt32)
    (hlo : 16384 ≤ q) (hhi : q ≤ 65536) (hm : mem.pages = 1) :
    TerminatesWith (loopExit s log mem p q c) (fun vs st =>
      vs = [] ∧ st.wasm = store s (log ++ [.write 1 (exitOutput q mem)]) mem) := by
  have hg : 16384 + 4*((UInt32.ofNat q - 16384)/4).toNat ≤ mem.pages*65536 := by
    rw [exit_count q hlo hhi, hm]
    have := Nat.mul_div_le (q-16384) 4
    omega
  have hi : writeOutput.invoke (store s log mem)
      [.i32 1, .i32 16384, .i32 ((UInt32.ofNat q - 16384)/4)] =
      .Return [] (store s (log ++ [.write 1 (exitOutput q mem)]) mem) := by
    simp only [writeOutput, store]
    change (if 16384 % 4 = 0 ∧ 16384 + 4*((UInt32.ofNat q - 16384)/4).toNat ≤ mem.pages*65536 then _ else _) = _
    rw [ite_eq_left ⟨by decide, hg⟩]
    rfl
  refine ⟨[.instruction (.globalGet 2), .instruction (.const 16384),
    .instruction (.localGet 2), .instruction (.const 16384), .instruction .sub,
    .instruction (.const 4), .instruction .divU, .host 4, .administrative .finish],
    [], machine s (log ++ [.write 1 (exitOutput q mem)]) mem, ?_, ⟨rfl, rfl⟩⟩
  wasm_steps [(.globalGet rfl), .const, (.localGet rfl), .const, .sub,
    .const, (.divU (by decide)), (.callHostReturn (by change 4 < 6; decide) rfl rfl hi)]
  exact Steps.single .finish

end PrefixWasm
#print axioms PrefixWasm.loop_iter
#print axioms PrefixWasm.loop_correct
#print axioms PrefixWasm.exit_correct
