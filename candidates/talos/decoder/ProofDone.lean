/-
ProofDone.lean -- `decode_start_state` and `decode_done` against the Talos
small-step semantics, for the literal `decoderModule`; and the state relation.
Proof style: explicit `Steps` traces with Talos's `wasm_steps`, one per path.

EXPORTS
  enc                    packing of the pending bytes into the i32 state
  Rel                    the state relation (witness for Boundary's R)
  enc_eq_zero            enc p = 0 ↔ p = []  (|p| ≤ 3)
  start_ok               decode_start_state returns enc [] and changes nothing
  doneBody               the body of decode_done (checked against the module by `rfl`
                         in done_runs' entry configuration)
  done_runs              decode_done: v = 0 returns out; v ≠ 0 writes U+FFFD at out
-/
import DecoderModule
import Boundary
import Utf8Ref
import Interpreter.Wasm.Examples.UIntLemmas

namespace Utf8Wasm
open Wasm SmallStep Utf8Boundary

/-- Packing of the pending bytes into the i32 state (see decoder.wat):
bits 24..31 hold the count, byte k sits in bits 8k..8k+7. -/
def enc : List UInt8 → UInt32
  | [] => 0
  | [a] => a.toUInt32 ||| 0x1000000
  | [a, b] => a.toUInt32 ||| (b.toUInt32 <<< 8) ||| 0x2000000
  | [a, b, c] => a.toUInt32 ||| (b.toUInt32 <<< 8) ||| (c.toUInt32 <<< 16) ||| 0x3000000
  | _ => 0

/-- The state relation used as the witness for `R` in `Realizes`
(RefDecoder's pending bytes are at most three). -/
def Rel (p : List UInt8) (v : UInt32) : Prop := p.length ≤ 3 ∧ v = enc p

theorem enc_eq_zero {p : List UInt8} (hl : p.length ≤ 3) : enc p = 0 ↔ p = [] := by
  constructor
  · intro h
    match p, hl with
    | [], _ => rfl
    | [a], _ => exfalso; have := congrArg UInt32.toBitVec h; simp [enc] at this
    | [a, b], _ => exfalso; have := congrArg UInt32.toBitVec h; simp [enc] at this
    | [a, b, c], _ => exfalso; have := congrArg UInt32.toBitVec h; simp [enc] at this
  · rintro rfl; rfl

/-! ## decode_start_state -/

theorem start_ok (mem : Mem) (_ : mem.pages ≤ 65536) :
    Calls decoderModule "decode_start_state" mem [] fun ws final =>
      ∃ v, ws = [v] ∧ Rel [] v ∧ final = storeWith decoderModule mem := by
  refine ⟨_, rfl, ?_⟩
  refine ⟨_, _, _, Steps.cons .const (Steps.single .finish), ?_⟩
  exact ⟨[0], rfl, 0, rfl, ⟨by simp, rfl⟩, rfl⟩

/-! ## decode_done -/

def doneBody : Program :=
  [.localGet 0, .eqz, .iff 0 0 [.localGet 1, .ret] [] [] [], .localGet 1,
   .const 65533, .store32 0, .localGet 1, .const 4, .add]

private def doneEntry (mem : Mem) (v out : UInt32) : Config Unit :=
  ⟨.running
    { locals := { params := [.i32 v, .i32 out], locals := [] }
      code := doneBody, resultArity := 1, callerRemainder := [] },
   { runtime := { instances := #[{ module := decoderModule, host := env }], entry := ⟨0⟩ }
     wasm := storeWith decoderModule mem }⟩

private theorem done_zero (mem : Mem) (out : UInt32) :
    ∃ trace, Steps (doneEntry mem 0 out) trace
      ⟨.done [.i32 out], (doneEntry mem 0 out).store⟩ := by
  apply Exists.intro
  unfold doneEntry doneBody
  wasm_steps [(.localGet rfl), (.eqz rfl), (.iff rfl), (.localGet rfl)]
  exact Steps.single .returnFromFunction

private theorem done_nonzero (mem : Mem) (v out : UInt32) (hv : v ≠ 0)
    (hb : out.toNat + 4 ≤ mem.pages * 65536) :
    TerminatesWith (doneEntry mem v out) fun vals st =>
      vals = [.i32 (4 + out)] ∧ st.wasm = storeWith decoderModule (mem.write32 out 65533) := by
  apply Exists.intro; apply Exists.intro; apply Exists.intro
  refine ⟨?_, ?_⟩
  unfold doneEntry doneBody
  wasm_steps [(.localGet rfl), (.eqz (result := 0) (by simp [hv])), (.iff rfl),
    (.exitControl rfl), (.localGet rfl), .const,
    (.store32 rfl (by simpa [storeWith] using hb)), (.localGet rfl), .const, .add]
  exact Steps.single .finish
  constructor
  · rfl
  · simp [setMemory_eq, storeWith]

theorem done_runs (mem : Mem) (v out : UInt32) (hb : out.toNat + 4 ≤ mem.pages * 65536) :
    Calls decoderModule "decode_done" mem [v, out] fun ws final =>
      (v = 0 → ws = [out] ∧ final = storeWith decoderModule mem) ∧
      (v ≠ 0 → ws = [4 + out] ∧ final = storeWith decoderModule (mem.write32 out 65533)) := by
  refine ⟨doneEntry mem v out, rfl, ?_⟩
  by_cases hv : v = 0
  · subst hv
    obtain ⟨tr, h⟩ := done_zero mem out
    exact ⟨tr, _, _, h, ⟨_, rfl, fun _ => ⟨rfl, rfl⟩, fun h => absurd rfl h⟩⟩
  · obtain ⟨tr, vals, st, h, hv', hst⟩ := done_nonzero mem v out hv hb
    refine ⟨tr, vals, st, h, ?_⟩
    subst hv'
    exact ⟨_, rfl, fun h => absurd h hv, fun _ => ⟨rfl, hst⟩⟩

end Utf8Wasm
