/-
ProofMach.lean -- reusable symbolic-execution machinery for decoderModule.

* `Reach c c'`: some finite small-step trace leads from `c` to `c'`
  (the trace itself is never written down).
* `wstep`: one step, trying each instruction rule used by the module with
  its standard side-condition discharger.  `wrun` repeats it, and between
  steps normalizes `if`-encoded booleans with the `wsimp` lemmas plus the
  path facts given to it.
* Each helper function gets a *call lemma* ("calling function k with
  arguments xs from any caller context pushes `f xs`"), so callers never
  re-trace callees: one trace per path per function, not per call path.
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

/-- One small step by the first matching instruction rule. -/
macro "wstep" : tactic => `(tactic| first
  | refine Reach.cons (Step.localGet rfl) ?_
  | refine Reach.cons (Step.localSet rfl) ?_
  | refine Reach.cons Step.const ?_
  | refine Reach.cons (Step.eqz rfl) ?_
  | refine Reach.cons (Step.eq rfl) ?_
  | refine Reach.cons (Step.geU rfl) ?_
  | refine Reach.cons (Step.leU rfl) ?_
  | refine Reach.cons Step.and ?_
  | refine Reach.cons Step.or ?_
  | refine Reach.cons Step.shl ?_
  | refine Reach.cons Step.shrU ?_
  | refine Reach.cons Step.add ?_
  | refine Reach.cons Step.sub ?_
  | refine Reach.cons (Step.iff rfl) ?_
  | refine Reach.cons (Step.exitControl rfl) ?_
  | refine Reach.cons (Step.returnFromCallFallthrough rfl) ?_
  | refine Reach.cons (Step.returnFromCallExplicit rfl) ?_)

/-- Steps until no rule applies (typically at an `if` on a symbolic value,
a call, a memory access, or the end). -/
macro "wrun" : tactic => `(tactic| repeat wstep)

/-- Enter a call to a module function. -/
macro "wcall" : tactic => `(tactic| refine Reach.cons (Step.call (Nat.not_lt_zero _) rfl) ?_)

/-- Normalize `if`-encoded booleans in the goal (fails without progress). -/
macro "wnorm" : tactic => `(tactic| simp only [ite_b2i, b2i_ne_zero, b2i_eq_zero, b2i_and, b2i_or,
  decide_eq_true_eq, decide_eq_false_iff_not, Bool.and_eq_true, Bool.or_eq_true, ite_true, ite_false,
  ↓reduceIte])

/-- Use a call lemma; extended with `macro_rules` as call lemmas are proved
(later rules are tried first, with backtracking). -/
syntax "wcalls" : tactic
macro_rules | `(tactic| wcalls) => `(tactic| fail "no call lemma applies")

/-- Symbolic execution: step, normalize, use call lemmas, split on symbolic `if`s. -/
macro "wauto" : tactic => `(tactic| repeat (any_goals (first | wstep | wnorm | wcalls | split)))

-- Close a finished path (after `simp` with the model definitions).
macro "wdone" : tactic => `(tactic| exact Reach.refl _)

end Utf8Wasm
