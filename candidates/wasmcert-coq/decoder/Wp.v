(** * A weakest-precondition layer over [exec] (Steps.v), with a tactic
    that runs straight-line code and splits on [if].  Reusable. *)

From Stdlib Require Import ZArith NArith Relations Lia.
From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool eqtype seq.
From Wasm Require Import operations opsem properties.
From Decoder Require Import Steps Control.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Wp.

Context `{ho: host}.
Variable hs : host_state.

Definition wp s f (stk : seq value) (bes : seq basic_instruction)
  (Q : store_record -> frame -> seq value -> Prop) : Prop :=
  exists s' f' stk', exec hs s f stk bes s' f' stk' /\ Q s' f' stk'.

Lemma wp_nil s f stk (Q : _ -> _ -> _ -> Prop) : Q s f stk -> wp s f stk [::] Q.
Proof. move => H; exists s, f, stk; split => //; apply exec_nil. Qed.

Lemma wp_cons s f stk b bes Q s1 f1 stk1 :
  exec hs s f stk [:: b] s1 f1 stk1 -> wp s1 f1 stk1 bes Q -> wp s f stk (b :: bes) Q.
Proof.
  move => H1 [s2 [f2 [stk2 [H2 HQ]]]]; exists s2, f2, stk2; split => //.
  by apply: exec_cons; eauto.
Qed.

Lemma wp_app s f stk b1 b2 Q :
  wp s f stk b1 (fun s1 f1 stk1 => wp s1 f1 stk1 b2 Q) -> wp s f stk (b1 ++ b2) Q.
Proof.
  move => [s1 [f1 [stk1 [H1 [s2 [f2 [stk2 [H2 HQ]]]]]]]].
  exists s2, f2, stk2; split => //. by apply: exec_app; eauto.
Qed.

Lemma wp_mono s f stk bes (Q Q' : _ -> _ -> _ -> Prop) :
  (forall s' f' stk', Q s' f' stk' -> Q' s' f' stk') -> wp s f stk bes Q -> wp s f stk bes Q'.
Proof. move => HQ [s' [f' [stk' [H1 H2]]]]; exists s', f', stk'; split; auto. Qed.

Lemma wp_if s f (c : i32) stk e1 e2 rest Q :
  (c <> Wasm_int.int_zero i32m ->
     wp s f [::] e1 (fun s1 f1 stk1 => stk1 = [::] /\ wp s1 f1 stk rest Q)) ->
  (c = Wasm_int.int_zero i32m ->
     wp s f [::] e2 (fun s1 f1 stk1 => stk1 = [::] /\ wp s1 f1 stk rest Q)) ->
  wp s f (VAL_num (VAL_int32 c) :: stk) (BI_if (BT_valtype None) e1 e2 :: rest) Q.
Proof.
  move => H1 H2.
  case: (Wasm_int.Int32.eq_dec c (Wasm_int.int_zero i32m)) => Hc.
  - case: (H2 Hc) => [s1 [f1 [stk1 [Hx [E [s2 [f2 [stk2 [Hr HQ]]]]]]]]]; subst stk1.
    exists s2, f2, stk2; split => //.
    apply: (exec_cons (s1 := s1) (f1 := f1) (stk1 := stk)) => //.
    apply: (exec_if_branch (e := e2)) => //. by apply exec_block_none.
  - case: (H1 Hc) => [s1 [f1 [stk1 [Hx [E [s2 [f2 [stk2 [Hr HQ]]]]]]]]]; subst stk1.
    exists s2, f2, stk2; split => //.
    apply: (exec_cons (s1 := s1) (f1 := f1) (stk1 := stk)) => //.
    apply: (exec_if_branch (e := e1)) => //. by apply exec_block_none.
Qed.

(** Running a block that leaves one value (used by [done]). *)
Lemma wp_if1 s f (c : i32) stk t e1 e2 rest Q :
  (c <> Wasm_int.int_zero i32m ->
     wp s f [::] e1 (fun s1 f1 stk1 => exists v, stk1 = [:: v] /\ wp s1 f1 (v :: stk) rest Q)) ->
  (c = Wasm_int.int_zero i32m ->
     wp s f [::] e2 (fun s1 f1 stk1 => exists v, stk1 = [:: v] /\ wp s1 f1 (v :: stk) rest Q)) ->
  wp s f (VAL_num (VAL_int32 c) :: stk) (BI_if (BT_valtype (Some t)) e1 e2 :: rest) Q.
Proof.
  move => H1 H2.
  case: (Wasm_int.Int32.eq_dec c (Wasm_int.int_zero i32m)) => Hc.
  - case: (H2 Hc) => [s1 [f1 [stk1 [Hx [v [E [s2 [f2 [stk2 [Hr HQ]]]]]]]]]]; subst stk1.
    exists s2, f2, stk2; split => //.
    apply: (exec_cons (s1 := s1) (f1 := f1) (stk1 := v :: stk)) => //.
    apply: (exec_if_branch (e := e2)) => //. by apply exec_block_one.
  - case: (H1 Hc) => [s1 [f1 [stk1 [Hx [v [E [s2 [f2 [stk2 [Hr HQ]]]]]]]]]]; subst stk1.
    exists s2, f2, stk2; split => //.
    apply: (exec_cons (s1 := s1) (f1 := f1) (stk1 := v :: stk)) => //.
    apply: (exec_if_branch (e := e1)) => //. by apply exec_block_one.
Qed.

End Wp.

(** One symbolic step.  Memory instructions are left to the caller. *)
Ltac wp_step :=
  match goal with
  | |- wp _ _ _ _ [::] _ => apply wp_nil
  | |- wp _ _ _ _ (BI_const_num _ :: _) _ => eapply wp_cons; [apply exec_const|]
  | |- wp _ _ _ _ (BI_local_get _ :: _) _ => eapply wp_cons; [apply exec_local_get; reflexivity|]
  | |- wp _ _ _ _ (BI_local_set _ :: _) _ =>
      eapply wp_cons; [apply exec_local_set; by []|]; cbn [set_nth f_locs f_inst]
  | |- wp _ _ _ _ (BI_binop _ _ :: _) _ =>
      eapply wp_cons; [eapply exec_binop; [reflexivity|reflexivity]|]
  | |- wp _ _ _ _ (BI_relop _ _ :: _) _ =>
      eapply wp_cons; [eapply exec_relop; reflexivity|]
  | |- wp _ _ _ _ (BI_testop T_i32 _ :: _) _ =>
      eapply wp_cons; [eapply exec_testop_i32|]
  end.
