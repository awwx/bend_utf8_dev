/-
ProofFuncs.lean -- call lemmas for the pure helper functions of
decoderModule ($cont, $second, $vs, $vsp, $cp = funcs 0..4).

Each helper gets a *model* (a Lean function on UInt32 computing what the
Wasm code computes) and a call lemma: calling the function from any caller
context pushes the model's value and changes nothing else.  Each proof is
`wcall; wauto; wfinish [model]` (ProofMach.lean).  The models are related to
Utf8Ref's isCont/secondOk/isVS/isVSP/cpOf in ProofModel.lean / ProofRefine.lean.

EXPORTS
  contB secondB          models of $cont, $second
  by1 by2 by3 by4        bytes of a packed sequence, as the code extracts them
  vsB vspB cpV           models of $vs, $vsp, $cp
  call_cont call_second call_vs call_vsp call_cp   (each registered with `wcalls`)
-/
import ProofMach

namespace Utf8Wasm
open Wasm SmallStep

def contB (b : UInt32) : Bool := decide (b ≥ 128) && decide (b ≤ 191)

theorem call_cont {w : Store Unit} {b : UInt32} {params lv values code arity rem controls calls} :
    Reach ⟨.running ⟨⟨params, lv, .i32 b :: values⟩, .call 0 :: code, arity, rem, controls, calls⟩, ⟨rt0, w⟩⟩
          ⟨.running ⟨⟨params, lv, .i32 (b2i (contB b)) :: values⟩, code, arity, rem, controls, calls⟩, ⟨rt0, w⟩⟩ := by
  wcall; wauto
  wfinish [contB]
macro_rules | `(tactic| wcalls) => `(tactic| refine Reach.trans call_cont ?_)

def secondB (b1 b2 : UInt32) : Bool :=
  if b1 = 224 then decide (b2 ≥ 160) && decide (b2 ≤ 191)
  else if b1 = 237 then decide (b2 ≥ 128) && decide (b2 ≤ 159)
  else if b1 = 240 then decide (b2 ≥ 144) && decide (b2 ≤ 191)
  else if b1 = 244 then decide (b2 ≥ 128) && decide (b2 ≤ 143)
  else contB b2

theorem call_second {w : Store Unit} {b1 b2 : UInt32} {params lv values code arity rem controls calls} :
    Reach ⟨.running ⟨⟨params, lv, .i32 b2 :: .i32 b1 :: values⟩, .call 1 :: code, arity, rem, controls, calls⟩, ⟨rt0, w⟩⟩
          ⟨.running ⟨⟨params, lv, .i32 (b2i (secondB b1 b2)) :: values⟩, code, arity, rem, controls, calls⟩, ⟨rt0, w⟩⟩ := by
  wcall; wauto
  wfinish [secondB]
macro_rules | `(tactic| wcalls) => `(tactic| refine Reach.trans call_second ?_)

/-- Bytes of a packed sequence, as the Wasm code extracts them. -/
def by1 (q : UInt32) : UInt32 := q &&& 255
def by2 (q : UInt32) : UInt32 := (q >>> 8) &&& 255
def by3 (q : UInt32) : UInt32 := (q >>> 16) &&& 255
def by4 (q : UInt32) : UInt32 := q >>> 24

def vsB (q m : UInt32) : Bool :=
  if m = 1 then decide (by1 q ≤ 127)
  else if m = 2 then (decide (by1 q ≥ 194) && decide (by1 q ≤ 223)) && secondB (by1 q) (by2 q)
  else if m = 3 then
    ((decide (by1 q ≥ 224) && decide (by1 q ≤ 239)) && secondB (by1 q) (by2 q)) && contB (by3 q)
  else if m = 4 then
    (((decide (by1 q ≥ 240) && decide (by1 q ≤ 244)) && secondB (by1 q) (by2 q)) && contB (by3 q))
      && contB (by4 q)
  else false

theorem call_vs {w : Store Unit} {q m : UInt32} {params lv values code arity rem controls calls} :
    Reach ⟨.running ⟨⟨params, lv, .i32 m :: .i32 q :: values⟩, .call 2 :: code, arity, rem, controls, calls⟩, ⟨rt0, w⟩⟩
          ⟨.running ⟨⟨params, lv, .i32 (b2i (vsB q m)) :: values⟩, code, arity, rem, controls, calls⟩, ⟨rt0, w⟩⟩ := by
  wcall; wauto
  wfinish [vsB, by1, by2, by3, by4]
macro_rules | `(tactic| wcalls) => `(tactic| refine Reach.trans call_vs ?_)

def vspB (q m : UInt32) : Bool :=
  if m = 1 then decide (by1 q ≤ 127) || (decide (by1 q ≥ 194) && decide (by1 q ≤ 244))
  else if m = 2 then (decide (by1 q ≥ 194) && decide (by1 q ≤ 244)) && secondB (by1 q) (by2 q)
  else if m = 3 then
    ((decide (by1 q ≥ 224) && decide (by1 q ≤ 244)) && secondB (by1 q) (by2 q)) && contB (by3 q)
  else vsB q m

theorem call_vsp {w : Store Unit} {q m : UInt32} {params lv values code arity rem controls calls} :
    Reach ⟨.running ⟨⟨params, lv, .i32 m :: .i32 q :: values⟩, .call 3 :: code, arity, rem, controls, calls⟩, ⟨rt0, w⟩⟩
          ⟨.running ⟨⟨params, lv, .i32 (b2i (vspB q m)) :: values⟩, code, arity, rem, controls, calls⟩, ⟨rt0, w⟩⟩ := by
  wcall; wauto
  wfinish [vspB, by1, by2, by3]
macro_rules | `(tactic| wcalls) => `(tactic| refine Reach.trans call_vsp ?_)

def cpV (q m : UInt32) : UInt32 :=
  if m = 1 then by1 q
  else if m = 2 then ((by1 q &&& 31) <<< 6) ||| (by2 q &&& 63)
  else if m = 3 then (((by1 q &&& 15) <<< 12) ||| ((by2 q &&& 63) <<< 6)) ||| (by3 q &&& 63)
  else ((((by1 q &&& 7) <<< 18) ||| ((by2 q &&& 63) <<< 12)) ||| ((by3 q &&& 63) <<< 6)) ||| (by4 q &&& 63)

theorem call_cp {w : Store Unit} {q m : UInt32} {params lv values code arity rem controls calls} :
    Reach ⟨.running ⟨⟨params, lv, .i32 m :: .i32 q :: values⟩, .call 4 :: code, arity, rem, controls, calls⟩, ⟨rt0, w⟩⟩
          ⟨.running ⟨⟨params, lv, .i32 (cpV q m) :: values⟩, code, arity, rem, controls, calls⟩, ⟨rt0, w⟩⟩ := by
  wcall; wauto
  wfinish [cpV, by1, by2, by3, by4]
macro_rules | `(tactic| wcalls) => `(tactic| refine Reach.trans call_cp ?_)

end Utf8Wasm
