import Interpreter.Wasm.Decoder.ProofEval
import Interpreter.Wasm.Host.Run
import Interpreter.Wasm.Examples.UIntLemmas
import Lean.Elab.Term

/-!
# The spike module as a Lean AST, tied to the WAT printed from `spike.wasm`

`spike.printed.wat` is the output of `wasm-tools print spike.wasm`.
`spikeModule` is the AST literal obtained by running Talos's WAT decoder at
elaboration time (`spikeWat%`, a copy of CodeLib's `watModule%`, copied so this
spike does not need to build CodeLib/iris-lean).  The elaborator is NOT
trusted: `spikeModule_decodes` re-runs the decoder on the same text inside the
kernel (via `cbv`) and proves it yields exactly `spikeModule`.
-/

namespace Wasm

open Lean Elab Term

deriving instance Lean.ToExpr for Simd.Shape
deriving instance Lean.ToExpr for Simd.ICmp
deriving instance Lean.ToExpr for Simd.FCmp
deriving instance Lean.ToExpr for Simd.UnOp
deriving instance Lean.ToExpr for Simd.BinOp
deriving instance Lean.ToExpr for Simd.TestOp
deriving instance Lean.ToExpr for Simd.ShiftOp
deriving instance Lean.ToExpr for GcHeapType
deriving instance Lean.ToExpr for ValueType
deriving instance Lean.ToExpr for AnyRef
deriving instance Lean.ToExpr for StorageType
deriving instance Lean.ToExpr for FieldType
deriving instance Lean.ToExpr for Value
deriving instance Lean.ToExpr for CatchClause
deriving instance Lean.ToExpr for GcOp
deriving instance Lean.ToExpr for Instruction
deriving instance Lean.ToExpr for Function
deriving instance Lean.ToExpr for Export
deriving instance Lean.ToExpr for DataSegment
deriving instance Lean.ToExpr for MemDecl
deriving instance Lean.ToExpr for GlobalDecl
deriving instance Lean.ToExpr for FuncType
deriving instance Lean.ToExpr for CompositeType
deriving instance Lean.ToExpr for GcTypeDef
deriving instance Lean.ToExpr for TableDecl
deriving instance Lean.ToExpr for ImportDecl
deriving instance Lean.ToExpr for ElementSegment
deriving instance Lean.ToExpr for Module

syntax (name := spikeWat) "spikeWat% " str : term

@[term_elab spikeWat] def elabSpikeWat : TermElab := fun stx _ => do
  let `(spikeWat% $pathSyntax:str) := stx | throwUnsupportedSyntax
  let source ← IO.FS.readFile pathSyntax.getString
  match Decoder.Wat.decodeForVerification source with
  | .ok module => pure (toExpr module)
  | .error message => throwError "WAT decoder rejected: {message}"

end Wasm

kernel_decoder

namespace Spike
open Wasm

/-- The text `wasm-tools print spike.wasm` produced (checked by `check.sh`). -/
def printedWat : String := include_str "spike.printed.wat"

/-- The module the theorems are about. -/
def spikeModule : Module := spikeWat% "spike.printed.wat"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- Kernel-checked: Talos's verification decoder maps the printed text to
exactly `spikeModule`. -/
theorem spikeModule_decodes :
    Decoder.Wat.decodeForVerification printedWat = .ok spikeModule := by
  cbv


/-! ## Specification (independent of the Wasm code) -/

/-- LAWS.bend `is_surrogate_code_point`: surrogates are U+D800..U+DFFF. -/
def isSurrogateCodePoint (cp : UInt32) : Bool :=
  decide (0xD800 ≤ cp) && decide (cp ≤ 0xDFFF)

/-- LAWS.bend `is_surrogate_code_point_examples`. -/
theorem isSurrogateCodePoint_examples :
    isSurrogateCodePoint 0x0000 = false ∧
    isSurrogateCodePoint 0xD7FF = false ∧
    isSurrogateCodePoint 0xD800 = true ∧
    isSurrogateCodePoint 0xDC00 = true ∧
    isSurrogateCodePoint 0xDFFF = true ∧
    isSurrogateCodePoint 0xE000 = false := by decide

/-- Number of bytes `≥ 0x80` in a byte list. -/
def countNonAscii : List UInt8 → Nat
  | [] => 0
  | b :: bs => (if 0x80 ≤ b then 1 else 0) + countNonAscii bs

/-- The `len` bytes of a memory starting at `ptr`. -/
def bytesAt (bytes : Nat → UInt8) (ptr len : Nat) : List UInt8 :=
  (List.range len).map fun i => bytes (ptr + i)

/-- No host functions: the module has no imports. -/
abbrev env : HostEnv Unit := {}

/-- Fuel-free total correctness of one export call (Talos `RunsExportWith`). -/
abbrev Runs := RunsExportWith env spikeModule

/-- Encode a Bool as Wasm's i32 truth value. -/
def boolI32 (b : Bool) : UInt32 := if b then 1 else 0

/-! ## (a) `is_surrogate_code_point` -/

/-- What the 7 instructions compute, in the interpreter's own terms. -/
private theorem surrogate_body_value (cp : UInt32) :
    ((if cp ≥ 0xD800 then 1 else 0) &&& (if cp ≤ 0xDFFF then 1 else 0) : UInt32) =
      boolI32 (isSurrogateCodePoint cp) := by
  unfold boolI32 isSurrogateCodePoint
  by_cases h1 : (0xD800 : UInt32) ≤ cp <;> by_cases h2 : cp ≤ (0xDFFF : UInt32) <;>
    simp [h1, h2] <;> decide

/-- For every i32 argument, calling the export from the module's initial store
returns 1 for a surrogate and 0 otherwise, and does not trap. -/
theorem is_surrogate_code_point_correct (cp : UInt32) :
    Runs "is_surrogate_code_point" (ExportCall.ofHost spikeModule () [.i32 cp])
      (fun r => r.values = [.i32 (boolI32 (isSurrogateCodePoint cp))]) := by
  refine ⟨_, rfl, ?_⟩
  rw [← surrogate_body_value]
  exact SmallStep.runSteps_values_terminates (fuel := 20) (by rfl)

/-! ## (b) `count_non_ascii` -/

open SmallStep

/-- The loop body of function 1, as decoded (checked by `count_body_eq`). -/
def loopBody : Program := [
  .localGet 1, .eqz, .br_if 1,
  .localGet 0, .load8U 0, .const 0x80, .geU, .localGet 2, .add, .localSet 2,
  .localGet 0, .const 1, .add, .localSet 0,
  .localGet 1, .const 1, .sub, .localSet 1,
  .br 0]

theorem count_body_eq :
    (spikeModule.funcs[1]?.map (·.body)) =
      some [.block 0 0 [.loop 0 0 loopBody], .localGet 2] := by rfl

private def blockFrame : ControlFrame :=
  { kind := .block, paramArity := 0, resultArity := 0,
    body := [.loop 0 0 loopBody], continuation := [.localGet 2], belowStack := [] }

private def loopFrame : ControlFrame :=
  { kind := .loop, paramArity := 0, resultArity := 0,
    body := loopBody, continuation := [], belowStack := [] }

/-- Machine state at the top of the loop: `ptr = p`, `len = l`, `count = c`. -/
private def loopHead (ms : MachineStore Unit) (p l c : UInt32) : Config Unit :=
  ⟨.running
    { locals := { params := [.i32 p, .i32 l], locals := [.i32 c], values := [] }
      code := loopBody, resultArity := 1, callerRemainder := []
      control := [loopFrame, blockFrame] }, ms⟩

private theorem loop_exit (ms : MachineStore Unit) (p c : UInt32) :
    ∃ trace, Steps (loopHead ms p 0 c) trace ⟨.done [.i32 c], ms⟩ := by
  refine ⟨[.instruction (.localGet 1), .instruction .eqz, .instruction (.br_if 1),
    .instruction (.localGet 2), .administrative .finish], ?_⟩
  wasm_steps [(.localGet rfl), (.eqz rfl), (.brIf (by decide) rfl), (.localGet rfl)]
  exact Steps.single .finish

private theorem loop_iter (ms : MachineStore Unit) (p l c : UInt32) (hl : l ≠ 0)
    (hp : p.toNat + 1 ≤ ms.wasm.mem.pages * 65536) :
    ∃ trace, Steps (loopHead ms p l c) trace
      (loopHead ms (1 + p) (l - 1)
        (c + if 0x80 ≤ (ms.wasm.mem.read8 p).toUInt32 then 1 else 0)) := by
  refine ⟨[.instruction (.localGet 1), .instruction .eqz, .instruction (.br_if 1),
    .instruction (.localGet 0), .instruction (.load8U 0), .instruction (.const 0x80),
    .instruction .geU, .instruction (.localGet 2), .instruction .add,
    .instruction (.localSet 2), .instruction (.localGet 0), .instruction (.const 1),
    .instruction .add, .instruction (.localSet 0), .instruction (.localGet 1),
    .instruction (.const 1), .instruction .sub, .instruction (.localSet 1),
    .instruction (.br 0)], ?_⟩
  wasm_steps [(.localGet rfl), (.eqz (result := 0) (by simp [hl])),
    .brIfZero, (.localGet rfl), (.load8U rfl (by simpa using hp)), .const, (.geU rfl),
    (.localGet rfl), .add, (.localSet rfl), (.localGet rfl), .const, .add, (.localSet rfl),
    (.localGet rfl), .const, .sub, (.localSet rfl)]
  simp
  exact Steps.single (.br rfl)

private theorem bytesAt_succ (bytes : Nat → UInt8) (p n : Nat) :
    bytesAt bytes p (n + 1) = bytes p :: bytesAt bytes (p + 1) n := by
  simp [bytesAt, List.range_succ_eq_map, Nat.add_comm, Nat.add_left_comm]

private theorem step_count (b : UInt8) (c : UInt32) (k : Nat) :
    (c + if 0x80 ≤ b.toUInt32 then 1 else 0) + UInt32.ofNat k =
      c + UInt32.ofNat ((if 0x80 ≤ b then 1 else 0) + k) := by
  have hb : ((0x80 : UInt32) ≤ b.toUInt32) ↔ ((0x80 : UInt8) ≤ b) := by
    simp [UInt32.le_iff_toNat_le, UInt8.le_iff_toNat_le]
  by_cases h : (0x80 : UInt8) ≤ b
  · simp only [h, hb.mpr h, ite_true, UInt32.ofNat_add]
    simp [UInt32.add_assoc]
  · simp only [h, mt hb.mp h, ite_false]
    simp

private theorem loop_correct (ms : MachineStore Unit) (hpages : ms.wasm.mem.pages ≤ 65536) :
    ∀ n (p l c : UInt32), l.toNat = n → p.toNat + n ≤ ms.wasm.mem.pages * 65536 →
      ∃ trace, Steps (loopHead ms p l c) trace
        ⟨.done [.i32 (c + UInt32.ofNat
            (countNonAscii (bytesAt ms.wasm.mem.bytes p.toNat n)))], ms⟩ := by
  intro n
  induction n with
  | zero =>
    intro p l c hl _
    have : l = 0 := UInt32.toNat_inj.mp (by simpa using hl)
    subst this
    simpa [bytesAt, countNonAscii] using loop_exit ms p c
  | succ n ih =>
    intro p l c hl hb
    have hl0 : l ≠ 0 := by intro h; subst h; simp at hl
    obtain ⟨t1, h1⟩ := loop_iter ms p l c hl0 (by omega)
    -- `p + 1` may wrap only when no bytes remain to be read.
    have hp1 : n = 0 ∨ (1 + p).toNat = p.toNat + 1 := by
      rcases Nat.eq_zero_or_pos n with h | h
      · exact .inl h
      · right
        rw [UInt32.toNat_add, UInt32.toNat_one, Nat.mod_eq_of_lt (by omega)]
        omega
    have hl1 : (l - 1).toNat = n := by
      rw [UInt32.toNat_sub_one_eq (by omega)]; omega
    have hle : (1 + p).toNat ≤ p.toNat + 1 := by
      rw [UInt32.toNat_add, UInt32.toNat_one]; have := Nat.mod_le (1 + p.toNat) (2 ^ 32); omega
    obtain ⟨t2, h2⟩ := ih (1 + p) (l - 1) _ hl1 (by omega)
    refine ⟨t1 ++ t2, ?_⟩
    have hv : ((c + if 0x80 ≤ (ms.wasm.mem.read8 p).toUInt32 then 1 else 0) +
        UInt32.ofNat (countNonAscii (bytesAt ms.wasm.mem.bytes (1 + p).toNat n))) =
        c + UInt32.ofNat (countNonAscii (bytesAt ms.wasm.mem.bytes p.toNat (n + 1))) := by
      have htail : bytesAt ms.wasm.mem.bytes (1 + p).toNat n =
          bytesAt ms.wasm.mem.bytes (p.toNat + 1) n := by
        rcases hp1 with h | h
        · subst h; rfl
        · rw [h]
      rw [bytesAt_succ, htail]
      simp only [countNonAscii, Mem.read8]
      exact step_count _ _ _
    rw [hv] at h2
    exact Steps.trans h1 h2

/-- The configuration `startExportConfig?` builds for `count_non_ascii`. -/
private def countEntry (initial : Store Unit) (ptr len : UInt32) : Config Unit :=
  ⟨.running
    { locals := { params := [.i32 ptr, .i32 len], locals := [.i32 0] }
      code := [.block 0 0 [.loop 0 0 loopBody], .localGet 2]
      resultArity := 1, callerRemainder := [] },
   { runtime := { instances := #[{ module := spikeModule, host := env }], entry := ⟨0⟩ }
     wasm := initial }⟩

set_option maxRecDepth 100000 in
/-- For every memory (any page count up to 65536, any contents) and every
in-bounds `ptr`/`len`, calling the export returns the number of bytes `≥ 0x80`
among the `len` bytes at `ptr`, does not trap, and leaves the store unchanged. -/
theorem count_non_ascii_correct (bytes : Nat → UInt8) (pages : Nat) (ptr len : UInt32)
    (hpages : pages ≤ 65536) (hbound : ptr.toNat + len.toNat ≤ pages * 65536) :
    let initial : Store Unit := { spikeModule.initialStore with mem := { pages, bytes } }
    Runs "count_non_ascii"
      { ExportCall.ofHost spikeModule () [.i32 ptr, .i32 len] with initial }
      (fun r =>
        r.values = [.i32 (UInt32.ofNat (countNonAscii (bytesAt bytes ptr.toNat len.toNat)))] ∧
        r.final = initial) := by
  intro initial
  refine ⟨countEntry initial ptr len, rfl, ?_⟩
  have hmem : (countEntry initial ptr len).store.wasm.mem = { pages, bytes } := rfl
  obtain ⟨trace, h⟩ := loop_correct (countEntry initial ptr len).store (by rw [hmem]; exact hpages)
    len.toNat ptr len 0 rfl (by rw [hmem]; exact hbound)
  rw [hmem] at h
  refine ⟨_, _, _, Steps.cons .block (Steps.cons .loop h), ?_⟩
  exact ⟨by simp, rfl⟩

end Spike

namespace Spike
open Wasm

/-- End-to-end form: the theorems hold for whatever module Talos's
verification decoder produces from the text `wasm-tools print spike.wasm`. -/
theorem spike_correct (m : Module)
    (hm : Decoder.Wat.decodeForVerification printedWat = .ok m) :
    (∀ cp : UInt32,
      RunsExportWith env m "is_surrogate_code_point" (ExportCall.ofHost m () [.i32 cp])
        (fun r => r.values = [.i32 (boolI32 (isSurrogateCodePoint cp))])) ∧
    (∀ (bytes : Nat → UInt8) (pages : Nat) (ptr len : UInt32),
      pages ≤ 65536 → ptr.toNat + len.toNat ≤ pages * 65536 →
      let initial : Store Unit := { m.initialStore with mem := { pages, bytes } }
      RunsExportWith env m "count_non_ascii"
        { ExportCall.ofHost m () [.i32 ptr, .i32 len] with initial }
        (fun r =>
          r.values = [.i32 (UInt32.ofNat (countNonAscii (bytesAt bytes ptr.toNat len.toNat)))] ∧
          r.final = initial)) := by
  rw [spikeModule_decodes] at hm
  cases hm
  exact ⟨is_surrogate_code_point_correct, fun b p q l h1 h2 => count_non_ascii_correct b p q l h1 h2⟩

/-! ## Probe (d)(i): consecutive calls on one persistent store -/

/-- Two consecutive calls, the second starting from the store the first left. -/
def TwoCalls (op : String) (initial : Store Unit) (args1 args2 : List Value)
    (post : ExportReturn Unit → ExportReturn Unit → Prop) : Prop :=
  Runs op { initial, arguments := args1.reverse } fun r1 =>
    Runs op { initial := r1.final, arguments := args2.reverse } fun r2 => post r1 r2

/-- Example: two counts over different windows of the same memory. -/
theorem count_twice (bytes : Nat → UInt8) (pages : Nat) (p1 l1 p2 l2 : UInt32)
    (hpages : pages ≤ 65536) (h1 : p1.toNat + l1.toNat ≤ pages * 65536)
    (h2 : p2.toNat + l2.toNat ≤ pages * 65536) :
    TwoCalls "count_non_ascii" { spikeModule.initialStore with mem := { pages, bytes } }
      [.i32 p1, .i32 l1] [.i32 p2, .i32 l2] fun r1 r2 =>
        r1.values = [.i32 (UInt32.ofNat (countNonAscii (bytesAt bytes p1.toNat l1.toNat)))] ∧
        r2.values = [.i32 (UInt32.ofNat (countNonAscii (bytesAt bytes p2.toNat l2.toNat)))] := by
  obtain ⟨c1, hc1, ht1⟩ := count_non_ascii_correct bytes pages p1 l1 hpages h1
  refine ⟨c1, hc1, ht1.mono ?_⟩
  rintro v1 s1 ⟨hv1, hs1⟩
  simp only at hs1
  rw [hs1]
  obtain ⟨c2, hc2, ht2⟩ := count_non_ascii_correct bytes pages p2 l2 hpages h2
  exact ⟨c2, hc2, ht2.mono fun v2 s2 ⟨hv2, _⟩ => ⟨hv1, hv2⟩⟩

end Spike

#print axioms Spike.count_twice
#print axioms Spike.spike_correct
#print axioms Spike.spikeModule_decodes
#print axioms Spike.isSurrogateCodePoint_examples
#print axioms Spike.is_surrogate_code_point_correct
#print axioms Spike.count_non_ascii_correct
