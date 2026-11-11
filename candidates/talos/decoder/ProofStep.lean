/-
ProofStep.lean -- call lemma for $step (func 5): one input byte.

Model `stepM` follows the Wasm code; memory effect `writeCps`, returned
output pointer `endAddr`.  `call_step0` (state 0, no recursion) is proved
first and then used by `wcalls` for the recursive call in `call_step`.
-/
import ProofFuncs

namespace Utf8Wasm
open Wasm SmallStep

set_option maxHeartbeats 0

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

/-- One `i32.store` with the bound discharged from the hypotheses. -/
macro "wstore" : tactic => `(tactic|
  refine Reach.cons (Step.store32 rfl (by simp [setMemory_eq, Mem.write32, UInt32.toNat_add] at *; omega)) ?_)

macro "wauto2" : tactic => `(tactic| repeat (any_goals (first | wstep | wnorm | wcalls | wstore | split)))

theorem call_step0 {w : Store Unit} {b out : UInt32} {params lv values code arity rem controls calls}
    (_hw : w.mem.pages ≤ 65536) (hb : out.toNat + 4 ≤ w.mem.pages * 65536) :
    Reach ⟨.running ⟨⟨params, lv, .i32 out :: .i32 b :: .i32 0 :: values⟩, .call 5 :: code,
              arity, rem, controls, calls⟩, ⟨rt0, w⟩⟩
          ⟨.running ⟨⟨params, lv, .i32 (endAddr out (stepA 0 b (0, [])).2) ::
              .i32 (stepA 0 b (0, [])).1 :: values⟩, code, arity, rem, controls, calls⟩,
            ⟨rt0, { w with mem := writeCps w.mem out (stepA 0 b (0, [])).2 }⟩⟩ := by
  wcall; wauto2
  all_goals (simp_all [resumeCaller, Function.numParams, stepA, qOf, nOf, writeCps, endAddr, setMemory_eq]; try wdone)

macro "wstep0" : tactic => `(tactic|
  refine Reach.trans (call_step0 (by simp_all [setMemory_eq, Mem.write32])
    (by simp_all [setMemory_eq, Mem.write32, UInt32.toNat_add]; omega)) ?_)

theorem call_step {w : Store Unit} {s b out : UInt32} {params lv values code arity rem controls calls}
    (hw : w.mem.pages ≤ 65536) (hb : out.toNat + 8 ≤ w.mem.pages * 65536) :
    Reach ⟨.running ⟨⟨params, lv, .i32 out :: .i32 b :: .i32 s :: values⟩, .call 5 :: code,
              arity, rem, controls, calls⟩, ⟨rt0, w⟩⟩
          ⟨.running ⟨⟨params, lv, .i32 (endAddr out (stepM s b).2) ::
              .i32 (stepM s b).1 :: values⟩, code, arity, rem, controls, calls⟩,
            ⟨rt0, { w with mem := writeCps w.mem out (stepM s b).2 }⟩⟩ := by
  wcall
  repeat (any_goals (first | wstep | wnorm | wcalls | wstore | split | wstep0))
  all_goals (simp_all [resumeCaller, Function.numParams, stepM, stepA, qOf, nOf, writeCps, endAddr,
    setMemory_eq]; try wdone)

end Utf8Wasm
