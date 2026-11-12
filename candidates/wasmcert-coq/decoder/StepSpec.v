(** * step_spec, assembled from its six cases.

    Exports:  step_spec_proved : forall hs, step_spec hs.
    Case split on the pending state st (Inv st) and the next byte b:
      st = []                                  step_case_empty
      st <> [], vp (st ++ [b]) = false         step_case_reject
      vp = true, vs (st ++ [b]) = false        step_case_extend
      vs = true, length st = 1 / 2 / 3         step_case_complete2 / 3 / 4 *)

From Stdlib Require Import ZArith NArith List Lia.
From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool eqtype seq.
From Wasm Require Import datatypes operations opsem properties.
From Utf8 Require Import Utf8Laws Utf8Ref Utf8Proofs Utf8StepFacts.
From Decoder Require Import Decode StepEmpty StepPending StepComplete.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section StepSpec.

Context `{ho: host}.
Variable hs : host_state.

(** [Inv st] is a premise of [step_case], so it may be assumed. *)
Lemma step_case_of_inv st b : (Inv st -> step_case hs st b) -> step_case hs st b.
Proof. move => H s1 m1 wb L i o junk Hm HI. exact: (H HI s1 m1 wb L i o junk Hm HI). Qed.

Lemma step_case_all st b : step_case hs st b.
Proof.
  apply: step_case_of_inv => HI.
  case: st HI => [|b1 r] HI; first exact: step_case_empty.
  case Evp: (vp (app (b1 :: r) [:: b])); last exact: step_case_reject.
  case Evs: (vs (app (b1 :: r) [:: b])); last exact: step_case_extend.
  have := Inv_len _ HI.
  case: r HI Evp Evs => [|b2 [|b3 [|b4 r]]] HI Evp Evs /= Hl.
  - exact: step_case_complete2.
  - exact: step_case_complete3.
  - exact: step_case_complete4.
  - exfalso. lia.
Qed.

Theorem step_spec_proved : step_spec hs.
Proof. apply: step_spec_of_cases. exact: step_case_all. Qed.

End StepSpec.
