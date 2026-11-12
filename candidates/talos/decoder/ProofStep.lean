/-
ProofStep.lean -- call lemma for $step (func 5): one input byte.

Model `stepM` follows the Wasm code (`stepA` is one attempt; on a bad pending
sequence $step calls itself once with state 0); its memory effect is
`writeCps`, the returned output pointer `endAddr`.  `call_step0` (state 0, no
recursion) is proved first and registered with `wcalls` for the recursive call
in `call_step`.

EXPORTS
  writeCps endAddr       code points written as u32le from an address; the end address
  qOf nOf stepA stepM    model of $step
  stepM_len              $step writes at most two code points
  wstore                 tactic: one i32.store, bound from the hypotheses (also a `wcalls` rule)
  call_step0 call_step   call lemmas
-/
import ProofFuncs

namespace Utf8Wasm
open Wasm SmallStep

/-- Write code points as consecutive little-endian u32 from address `a`. -/
def writeCps (mem : Mem) (a : UInt32) : List UInt32 → Mem
  | [] => mem
  | c :: cs => writeCps (mem.write32 a c) (4 + a) cs

/-- The address after the written code points. -/
def endAddr (a : UInt32) : List UInt32 → UInt32
  | [] => a
  | _ :: cs => endAddr (4 + a) cs

/-- Packed sequence `q` = pending bytes plus `b`, as $step computes it. -/
def qOf (s b : UInt32) : UInt32 := (s &&& (16777215 : UInt32)) ||| (b <<< ((s >>> (24 : UInt32) <<< (3 : UInt32)) % 32))
def nOf (s : UInt32) : UInt32 := s >>> (24 : UInt32)

def stepA (s b : UInt32) (k : UInt32 × List UInt32) : UInt32 × List UInt32 :=
  if vsB (qOf s b) (1 + nOf s) then (0, [cpV (qOf s b) (1 + nOf s)])
  else if vspB (qOf s b) (1 + nOf s) then (qOf s b ||| ((1 + nOf s) <<< (24 : UInt32)), [])
  else if nOf s = 0 then (0, [65533])
  else k

/-- Model of $step: new state and the code points written. -/
def stepM (s b : UInt32) : UInt32 × List UInt32 :=
  stepA s b ((stepA 0 b (0, [])).1, 65533 :: (stepA 0 b (0, [])).2)

private theorem stepA0_len (b : UInt32) : (stepA 0 b (0, [])).2.length ≤ 1 := by
  unfold stepA; split <;> (try split) <;> (try split) <;> simp

private theorem stepA_len (s b : UInt32) (k : UInt32 × List UInt32) :
    (stepA s b k).2.length ≤ 1 ∨ stepA s b k = k := by
  unfold stepA; split <;> (try split) <;> (try split) <;> simp

theorem stepM_len (s b : UInt32) : (stepM s b).2.length ≤ 2 := by
  have h0 := stepA0_len b
  unfold stepM
  rcases stepA_len s b ((stepA 0 b (0, [])).1, 65533 :: (stepA 0 b (0, [])).2) with h | h
  · omega
  · rw [h]; simp; omega

/-- One `i32.store` with the bound discharged from the hypotheses. -/
macro "wstore" : tactic => `(tactic|
  refine Reach.cons (Step.store32 rfl (by simp [setMemory_eq, Mem.write32, UInt32.toNat_add] at *; omega)) ?_)

macro_rules | `(tactic| wcalls) => `(tactic| wstore)

theorem call_step0 {w : Store Unit} {b out : UInt32} {params lv values code arity rem controls calls}
    (_hw : w.mem.pages ≤ 65536) (hb : out.toNat + 4 ≤ w.mem.pages * 65536) :
    Reach ⟨.running ⟨⟨params, lv, .i32 out :: .i32 b :: .i32 0 :: values⟩, .call 5 :: code,
              arity, rem, controls, calls⟩, ⟨rt0, w⟩⟩
          ⟨.running ⟨⟨params, lv, .i32 (endAddr out (stepA 0 b (0, [])).2) ::
              .i32 (stepA 0 b (0, [])).1 :: values⟩, code, arity, rem, controls, calls⟩,
            ⟨rt0, { w with mem := writeCps w.mem out (stepA 0 b (0, [])).2 }⟩⟩ := by
  wcall; wauto
  wfinish [stepA, qOf, nOf, writeCps, endAddr]

macro_rules | `(tactic| wcalls) => `(tactic|
  refine Reach.trans (call_step0 (by simp_all [setMemory_eq, Mem.write32])
    (by simp_all [setMemory_eq, Mem.write32, UInt32.toNat_add]; omega)) ?_)

theorem call_step {w : Store Unit} {s b out : UInt32} {params lv values code arity rem controls calls}
    (hw : w.mem.pages ≤ 65536) (hb : out.toNat + 8 ≤ w.mem.pages * 65536) :
    Reach ⟨.running ⟨⟨params, lv, .i32 out :: .i32 b :: .i32 s :: values⟩, .call 5 :: code,
              arity, rem, controls, calls⟩, ⟨rt0, w⟩⟩
          ⟨.running ⟨⟨params, lv, .i32 (endAddr out (stepM s b).2) ::
              .i32 (stepM s b).1 :: values⟩, code, arity, rem, controls, calls⟩,
            ⟨rt0, { w with mem := writeCps w.mem out (stepM s b).2 }⟩⟩ := by
  wcall; wauto
  wfinish [stepM, stepA, qOf, nOf, writeCps, endAddr]

end Utf8Wasm
