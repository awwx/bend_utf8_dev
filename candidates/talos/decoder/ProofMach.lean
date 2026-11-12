/-
ProofMach.lean -- symbolic execution of decoderModule on Talos's small-step
semantics (`Wasm.SmallStep.Step`).  Talos's own program logic is not used.

EXPORTS
  Cfg, Reach, Reach.refl/cons/trans   `Reach c c'`: some finite trace leads from c to c'
  rt0                                 the runtime environment of any call of this module
  b2i (+ simp lemmas)                 Bool as an i32 truth value
  wstep    one step, by the rule for the instruction at the head of the code
           (dispatch on the instruction, no trial and error; fails at once on a
           stuck goal: a symbolic `if`, a `call`, a store, or the end)
  wcall    enter a module function (`Step.call`)
  wnorm    normalize `if`-encoded booleans (`b2i`)
  wcalls   extensible (`macro_rules`): one rule per call lemma, later files add
           theirs (ProofFuncs: $cont..$cp; ProofStep: i32.store and $step from state 0)
  wauto    `repeat'` of wstep / wnorm / wcalls / split: runs every path of a
           function body to its end
  wfinish [defs]  close every finished path: simp_all with the model `defs`,
           &&/|| up to AC, then `Reach.refl`

HOW THE PROOF FILES FIT TOGETHER (imports flow downwards)
  DecoderModule   module literal + kernel-checked decode of the printed text
  ProofMach       this file
  ProofFuncs      call lemmas + models for $cont $second $vs $vsp $cp (funcs 0-4)
  ProofStep       call lemma + model `stepM` for $step (func 5); writeCps, endAddr
  ProofLayout     memory layout of written code points (pure Lean on Mem)
  ProofLoop       the decode_buffer loop (func 7) against `runM` (fold of stepM)
  ProofBuffer     decode_buffer export call (Boundary's `Calls` form)
  ProofDone       state packing `enc` / `Rel`; decode_start_state, decode_done
  ProofModel      model facts: stepM on the empty state, contB/secondB vs Utf8Ref
  ProofRefine     stepM refines Utf8Ref.step on packed states (stepM_enc)
  ProofMain       runM refines decodeBuffer; Boundary's StartOk/BufferOk/DoneOk;
                  shippedModuleCorrect
  ProofWrapper    non-vacuity: shippedWrapperCovered

WHAT A CHANGE TO decoder.wat REQUIRES ON THE PROOF SIDE
  The call lemmas are proved by `wcall; wauto; wfinish [model defs]`: the
  execution itself is not scripted, so reordering, adding or removing
  straight-line instructions or `if`s needs no tactic edits, and swapping the
  operands of i32.and / i32.or on booleans needs no edit at all (wfinish
  normalizes up to AC).  What must still match the code:
  * the model (ProofFuncs/ProofStep defs) must compute the same values; a
    change that alters arithmetic (shift amounts, masks, constants) means
    editing the model and then its `_eq` / refinement lemmas (ProofModel,
    ProofRefine);
  * a new instruction kind needs a line in `wstep`'s dispatch table;
  * a new function or a changed signature needs a new call lemma, registered
    with `macro_rules | `(tactic| wcalls) => ...`;
  * ProofLoop (loop_iter/loop_exit) and ProofDone step through decode_buffer
    and decode_done by explicit rule lists and must be edited with them.
  A mismatch between code and model fails within Lean's default heartbeat
  limit with the unsolved path goal (see IMPROVEMENT.txt, mutation m07).
-/
import DecoderModule
import Interpreter.Wasm.Examples.UIntLemmas

namespace Utf8Wasm
open Wasm SmallStep

abbrev Cfg := Config Unit

def Reach (c c' : Cfg) : Prop := ∃ tr, Steps c tr c'

theorem Reach.refl (c : Cfg) : Reach c c := ⟨[], .refl c⟩
theorem Reach.cons {c c' c'' : Cfg} {k} (h : Step c k c') (t : Reach c' c'') : Reach c c'' :=
  let ⟨tr, ht⟩ := t; ⟨k :: tr, .cons h ht⟩
theorem Reach.trans {c c' c'' : Cfg} (h : Reach c c') (t : Reach c' c'') : Reach c c'' :=
  let ⟨tr, ht⟩ := h; let ⟨tr', ht'⟩ := t; ⟨tr ++ tr', Steps.trans ht ht'⟩

/-- The runtime half of the machine store during any call of this module. -/
def rt0 : RuntimeEnv Unit :=
  { instances := #[{ module := decoderModule, host := {} }], entry := ⟨0⟩ }

/-- Booleans as Wasm i32 truth values. -/
def b2i (b : Bool) : UInt32 := if b then 1 else 0

@[simp] theorem b2i_ne_zero (b : Bool) : (b2i b ≠ 0) = (b = true) := by
  cases b <;> simp [b2i]
@[simp] theorem b2i_eq_zero (b : Bool) : (b2i b = 0) = (b = false) := by
  cases b <;> simp [b2i]
@[simp] theorem ite_b2i (p : Prop) [Decidable p] :
    (if p then (1 : UInt32) else 0) = b2i (decide p) := by
  by_cases h : p <;> simp [h, b2i]
@[simp] theorem b2i_and (a b : Bool) : b2i a &&& b2i b = b2i (a && b) := by
  cases a <;> cases b <;> rfl
@[simp] theorem b2i_or (a b : Bool) : b2i a ||| b2i b = b2i (a || b) := by
  cases a <;> cases b <;> rfl

open Lean Meta in
/-- The elements of a list term, each in weak head normal form (none if the
spine is not a literal list after `whnf`). -/
private partial def listElems (e : Expr) : MetaM (Option (List Expr)) := do
  match_expr (← whnf e) with
  | List.nil _ => return some []
  | List.cons _ a t =>
    let some r ← listElems t | return none
    return some ((← whnf a) :: r)
  | _ => return none

open Lean Elab Tactic Meta in
/-- Rewrite (by definitional unfolding) the current frame's `params` and
`locals` in the goal `Reach c c'` to literal lists.  After `Step.call` and
`Step.localSet` they are unevaluated terms (`(values.take n).reverse`,
`List.set (List.map ValueType.zero fn.locals) i v`, ...) that mention the
whole callee record; left alone, every later `local.get` re-evaluates them,
which made the cost of a step grow along a function body. -/
elab "wlocals" : tactic => do
  let g ← getMainGoal
  let ty ← whnfR (← instantiateMVars (← g.getType))
  unless ty.isAppOfArity ``Utf8Wasm.Reach 2 do throwError "wlocals: goal is not `Reach _ _`"
  let c ← whnf ty.appFn!.appArg!
  let .app (.app (.app (.const ``Wasm.SmallStep.Config.mk u1) α) e) st := c
    | throwError "wlocals: no Config"
  let .app (.app (.const ``Wasm.SmallStep.Expr.running u2) α2) th ← whnf e
    | throwError "wlocals: not running"
  let th ← whnf th
  let args := th.getAppArgs
  unless th.isAppOf ``Wasm.SmallStep.ThreadState.mk && args.size == 7 do
    throwError "wlocals: no ThreadState"
  let loc ← whnf args[1]!
  unless loc.isAppOfArity ``Wasm.Locals.mk 3 do throwError "wlocals: no Locals"
  let some ps ← listElems loc.getAppArgs[0]! | throwError "wlocals: params not a list"
  let some ls ← listElems loc.getAppArgs[1]! | throwError "wlocals: locals not a list"
  let vty := mkConst ``Wasm.Value
  let loc' := mkApp3 (mkConst ``Wasm.Locals.mk) (← mkListLit vty ps) (← mkListLit vty ls)
    loc.getAppArgs[2]!
  let th' := mkAppN th.getAppFn (args.set! 1 loc')
  let c' := mkApp3 (.const ``Wasm.SmallStep.Config.mk u1) α
    (mkApp2 (.const ``Wasm.SmallStep.Expr.running u2) α2 th') st
  replaceMainGoal [← g.replaceTargetDefEq (mkApp2 ty.appFn!.appFn! c' ty.appArg!)]

open Lean Elab Tactic Meta in
/-- One small step: reads the instruction at the head of the code in the goal
`Reach c c'` and applies exactly the matching `Step` rule (no trial and error,
so a stuck goal fails at once).  Handles straight-line i32 instructions, `if`
(leaves an `ite` on the condition in the code, for `split`), leaving a control
frame and returning from a call.  Fails on `call`, `i32.store` (see `wcalls`,
`wstore`) and on code that is not a literal list (e.g. an unsplit `if`). -/
elab "wstep" : tactic => do
  let g ← getMainGoal
  let ty ← whnfR (← instantiateMVars (← g.getType))
  let some c := (if ty.isAppOfArity ``Utf8Wasm.Reach 2 then some ty.appFn!.appArg! else none)
    | throwError "wstep: goal is not `Reach _ _`"
  let c ← whnf c
  let .app (.app (.app (.const ``Wasm.SmallStep.Config.mk _) _) e) _ := c | throwError "wstep: no Config"
  let e ← whnf e
  let .app (.app (.const ``Wasm.SmallStep.Expr.running _) _) th := e | throwError "wstep: not running"
  let th ← whnf th
  let args := th.getAppArgs
  unless th.isAppOf ``Wasm.SmallStep.ThreadState.mk && args.size == 7 do throwError "wstep: no ThreadState"
  let code ← whnfR args[2]!
  let rule ← match_expr code with
    | List.nil _ =>
      let ctl ← whnfR args[5]!
      if ctl.isAppOf ``List.cons then `(tactic| refine Reach.cons (Step.exitControl rfl) ?_)
      else if (← whnfR args[6]!).isAppOf ``List.cons then
        `(tactic| refine Reach.cons (Step.returnFromCallFallthrough rfl) ?_)
      else throwError "wstep: function body finished"
    | List.cons _ i _ =>
      let i ← whnfR i
      match i.getAppFn.constName? with
      | some ``Wasm.Instruction.localGet => `(tactic| refine Reach.cons (Step.localGet rfl) ?_)
      | some ``Wasm.Instruction.localSet => `(tactic| (refine Reach.cons (Step.localSet rfl) ?_; wlocals))
      | some ``Wasm.Instruction.const => `(tactic| refine Reach.cons Step.const ?_)
      | some ``Wasm.Instruction.eqz => `(tactic| refine Reach.cons (Step.eqz rfl) ?_)
      | some ``Wasm.Instruction.eq => `(tactic| refine Reach.cons (Step.eq rfl) ?_)
      | some ``Wasm.Instruction.geU => `(tactic| refine Reach.cons (Step.geU rfl) ?_)
      | some ``Wasm.Instruction.leU => `(tactic| refine Reach.cons (Step.leU rfl) ?_)
      | some ``Wasm.Instruction.and => `(tactic| refine Reach.cons Step.and ?_)
      | some ``Wasm.Instruction.or => `(tactic| refine Reach.cons Step.or ?_)
      | some ``Wasm.Instruction.shl => `(tactic| refine Reach.cons Step.shl ?_)
      | some ``Wasm.Instruction.shrU => `(tactic| refine Reach.cons Step.shrU ?_)
      | some ``Wasm.Instruction.add => `(tactic| refine Reach.cons Step.add ?_)
      | some ``Wasm.Instruction.sub => `(tactic| refine Reach.cons Step.sub ?_)
      | some ``Wasm.Instruction.iff => `(tactic| refine Reach.cons (Step.iff rfl) ?_)
      | some ``Wasm.Instruction.ret => `(tactic| refine Reach.cons (Step.returnFromCallExplicit rfl) ?_)
      | n => throwError "wstep: no rule for {n}"
    | _ => throwError "wstep: code is not a literal list"
  evalTactic rule

/-- Enter a call to a module function. -/
macro "wcall" : tactic => `(tactic| (refine Reach.cons (Step.call (Nat.not_lt_zero _) rfl) ?_; wlocals))

/-- Normalize `if`-encoded booleans in the goal (fails without progress). -/
macro "wnorm" : tactic => `(tactic| simp only [ite_b2i, b2i_ne_zero, b2i_eq_zero, b2i_and, b2i_or,
  decide_eq_true_eq, decide_eq_false_iff_not, Bool.and_eq_true, Bool.or_eq_true, ite_true, ite_false,
  ↓reduceIte])

/-- Use a call lemma; extended with `macro_rules` as call lemmas are proved
(later rules are tried first, with backtracking). -/
syntax "wcalls" : tactic
macro_rules | `(tactic| wcalls) => `(tactic| fail "no call lemma applies")

/-- Symbolic execution: step, normalize, use call lemmas, split on symbolic `if`s.
`repeat'` works on each goal until it is stuck and never retries a stuck goal
(the first version used `repeat (any_goals ...)`, which re-ran every rule on
every stuck goal after each step: quadratic, and the main cost of the check). -/
macro "wauto" : tactic => `(tactic| repeat' (first | wstep | wnorm | wcalls | split))

/-- Close a finished path: unfold the model `defs` and the return bookkeeping,
normalize `&&` / `||` up to associativity and commutativity (so the model
need not repeat the operand order of `i32.and` / `i32.or` in the code), use the
path facts, and finish with `Reach.refl`. -/
syntax "wfinish" "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic
macro_rules
  | `(tactic| wfinish [$defs,*]) => `(tactic| all_goals
      (simp_all [resumeCaller, Function.numParams, setMemory_eq, Bool.and_comm, Bool.and_left_comm,
        Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, $defs,*]
       try exact Reach.refl _))

end Utf8Wasm
