(** * Structured-control rules added to the spike's [Steps.v]:
    [block] / [if] whose bodies complete normally (no branch out of them),
    with block type [None] (no results) or [Some t] (one result).
    Reusable; nothing decoder-specific. *)

From Stdlib Require Import ZArith NArith Relations.
From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool eqtype seq.
From Wasm Require Import operations opsem properties.
From Decoder Require Import Steps.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Control.

Context `{ho: host}.
Variable hs : host_state.

Lemma exec_block_gen s f stk tb t2s body s' f' res :
  expand f.(f_inst) tb = Some (Tf [::] t2s) ->
  length res = length t2s ->
  exec hs s f [::] body s' f' res ->
  exec hs s f stk [:: BI_block tb body] s' f' (res ++ stk).
Proof.
  move => Hexp Hlen Hb.
  have H : steps hs s f [:: AI_basic (BI_block tb body)] s' f' (v_to_e_list (rev res)).
  { eapply steps_trans.
    { apply steps_one. eapply r_block with (vs := [::]) (t1s := [::]); eauto. }
    eapply steps_trans.
    { apply steps_label. rewrite /exec /= in Hb. apply Hb. }
    apply steps_simple. apply rs_label_const. by apply v_to_e_const. }
  move: (steps_ctx (rev stk) [::] H).
  by rewrite /exec /= cats0 rev_cat /v_to_e_list map_cat.
Qed.

Lemma exec_block_none s f stk body s' f' :
  exec hs s f [::] body s' f' [::] ->
  exec hs s f stk [:: BI_block (BT_valtype None) body] s' f' stk.
Proof. move => H. exact: (exec_block_gen stk (tb := BT_valtype None) (t2s := [::]) (res := [::]) erefl erefl H). Qed.

Lemma exec_block_one s f stk t body s' f' v :
  exec hs s f [::] body s' f' [:: v] ->
  exec hs s f stk [:: BI_block (BT_valtype (Some t)) body] s' f' (v :: stk).
Proof. move => H. exact: (exec_block_gen stk (tb := BT_valtype (Some t)) (t2s := [:: t]) (res := [:: v]) erefl erefl H). Qed.

Lemma exec_if_branch s f stk (c : i32) tb e1 e2 e s' f' stk' :
  (c = Wasm_int.int_zero i32m -> e = e2) ->
  (c <> Wasm_int.int_zero i32m -> e = e1) ->
  exec hs s f stk [:: BI_block tb e] s' f' stk' ->
  exec hs s f (VAL_num (VAL_int32 c) :: stk) [:: BI_if tb e1 e2] s' f' stk'.
Proof.
  move => H2 H1 H.
  have Hs : steps hs s f [:: $VN (VAL_int32 c); AI_basic (BI_if tb e1 e2)] s f
              [:: AI_basic (BI_block tb e)].
  { apply steps_simple.
    case: (Wasm_int.Int32.eq_dec c (Wasm_int.int_zero i32m)) => Hc.
    - rewrite (H2 Hc); by apply rs_if_false.
    - rewrite (H1 Hc); by apply rs_if_true. }
  move: (steps_ctx (rev stk) [::] Hs) => Hs'.
  rewrite /exec in H *.
  eapply steps_trans; last by apply H.
  move: Hs'. by rewrite /= rev_cons -cats1 /v_to_e_list map_cat -catA /= ?cats0.
Qed.

Lemma exec_if_true s f stk (c : i32) tb e1 e2 s' f' stk' :
  c <> Wasm_int.int_zero i32m ->
  exec hs s f stk [:: BI_block tb e1] s' f' stk' ->
  exec hs s f (VAL_num (VAL_int32 c) :: stk) [:: BI_if tb e1 e2] s' f' stk'.
Proof. move => Hc H; apply: (exec_if_branch (e := e1)) => //. Qed.

Lemma exec_if_false s f stk tb e1 e2 s' f' stk' :
  exec hs s f stk [:: BI_block tb e2] s' f' stk' ->
  exec hs s f (VAL_num (VAL_int32 (Wasm_int.int_zero i32m)) :: stk) [:: BI_if tb e1 e2] s' f' stk'.
Proof. move => H; apply: (exec_if_branch (e := e2)) => //. Qed.

End Control.
