(** * Correctness of the [is_surrogate_code_point] export. *)

From Stdlib Require Import ZArith NArith Lia.
From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool eqtype seq.
From Wasm Require Import operations opsem properties.
From Spike Require Import Spec Module Steps Instance.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** The i32 result the spec prescribes: 1 for true, 0 for false. *)
Definition surrogate_result (cp : i32) : i32 :=
  wasm_bool (is_surrogate_code_point (Z.to_N (Wasm_int.Int32.unsigned cp))).

Lemma surrogate_arith (cp : i32) :
  Wasm_int.Int32.iand
    (wasm_bool (~~ Wasm_int.Int32.ltu cp (Wasm_int.Int32.repr 0xD800)))
    (wasm_bool (~~ Wasm_int.Int32.ltu (Wasm_int.Int32.repr 0xDFFF) cp))
  = surrogate_result cp.
Proof.
  rewrite /surrogate_result /is_surrogate_code_point /Wasm_int.Int32.ltu.
  rewrite !Wasm_int.Int32.unsigned_repr; try by rewrite /Wasm_int.Int32.max_unsigned /=; lia.
  have R := Wasm_int.Int32.unsigned_range cp.
  set u := Wasm_int.Int32.unsigned cp in R *.
  case: Coqlib.zlt => H1; case: Coqlib.zlt => H2 /=.
  - lia.
  - have -> : N.leb 0xD800 (Z.to_N u) = false by apply N.leb_gt; lia.
    by [].
  - have -> : N.leb 0xD800 (Z.to_N u) = true by apply N.leb_le; lia.
    have -> : N.leb (Z.to_N u) 0xDFFF = false by apply N.leb_gt; lia.
    by [].
  - have -> : N.leb 0xD800 (Z.to_N u) = true by apply N.leb_le; lia.
    have -> : N.leb (Z.to_N u) 0xDFFF = true by apply N.leb_le; lia.
    by [].
Qed.

Section Correct.

Context `{ho: host}.

(** The function body, run in the frame the invocation creates. *)
Lemma surrogate_body_correct hs s cp :
  exec hs s (Build_frame [:: VAL_num (VAL_int32 cp)] inst0) [::] surrogate_body
    s (Build_frame [:: VAL_num (VAL_int32 cp)] inst0)
    [:: VAL_num (VAL_int32 (surrogate_result cp))].
Proof.
  rewrite /surrogate_body.
  eapply exec_cons; first by apply exec_local_get.
  eapply exec_cons; first by apply exec_const.
  eapply exec_cons; first by apply exec_relop.
  eapply exec_cons; first by apply exec_local_get.
  eapply exec_cons; first by apply exec_const.
  eapply exec_cons; first by apply exec_relop.
  eapply exec_cons; first by apply exec_binop.
  apply exec_nil_eq.
  by rewrite -surrogate_arith.
Qed.

(** Invocation on ANY store in which function address 0 holds the
    module's first function closure (as instantiation produces). *)
Theorem is_surrogate_code_point_invoke hs s f0 (cp : i32) :
  lookup_N s.(s_funcs) 0 = Some surrogate_closure ->
  reduce_trans
    (hs, s, f0, [:: AI_basic (BI_const_num (VAL_int32 cp)); AI_invoke N0])
    (hs, s, f0, [:: AI_basic (BI_const_num (VAL_int32 (surrogate_result cp)))]).
Proof.
  move => Hcl.
  eapply invoke_rule with (args := [:: VAL_num (VAL_int32 cp)])
           (res := [:: VAL_num (VAL_int32 (surrogate_result cp))]) (defs := [::]);
    [ exact Hcl | done | done | done | ].
  by apply surrogate_body_correct.
Qed.

End Correct.
