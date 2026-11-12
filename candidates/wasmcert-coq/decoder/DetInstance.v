(** * DetInstance.v: the decoder module is in the determinism fragment of
    ../determinism (logical path [Determinism]), so a call of one of its
    functions that returns has that result as its only outcome.

    (Moved here from ../determinism/DecoderInstance.v and Main.v, so that
    ../determinism depends on nothing but coq-wasm.)

    Exports (PROVED):
    - [decoder_bodies_ok]: every function body of [decoder_module] is
      [bi_ok], by computation.
    - [s0_funcs_ok]: the function closures of the instantiated store [s0]
      (Instance.v) are all native with [bi_ok] bodies, by computation.
    - [decoder_call_cfg_ok]: every call configuration of Boundary.v's
      [call_returns] (arguments, then [AI_invoke a], in a store with
      [s0]'s functions) is [cfg_ok].
    - [decoder_call_outcome]: such a call that reduces to the values
      [res] has that as its only outcome ([deterministic_outcome]),
      from [fragment_deterministic_outcome]. *)

From Stdlib Require Import NArith List.
From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool eqtype seq.
From Wasm Require Import datatypes operations opsem properties.
From Determinism Require Import Fragment ReduceDet Main.
From Decoder Require Import Module Instance.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section DetInstance.

Context `{ho: host}.

Lemma decoder_bodies_ok :
  List.forallb (fun mf => List.forallb bi_ok mf.(modfunc_body)) decoder_module.(mod_funcs).
Proof. vm_compute. reflexivity. Qed.

Lemma s0_funcs_ok : funcs_ok s0.
Proof. vm_compute. reflexivity. Qed.

Lemma decoder_call_cfg_ok s args a :
  s.(s_funcs) = s0.(s_funcs) ->
  cfg_ok s (v_to_e_list args ++ [:: AI_invoke a]).
Proof.
  move => Hf. rewrite /cfg_ok es_ok_cat es_ok_v_to_e /=.
  move: s0_funcs_ok. by rewrite /funcs_ok Hf => ->.
Qed.

Theorem decoder_call_outcome hs s f a args s' res :
  s.(s_funcs) = s0.(s_funcs) ->
  reduce_trans (hs, s, f, v_to_e_list args ++ [:: AI_invoke a]) (hs, s', f, v_to_e_list res) ->
  deterministic_outcome (hs, s, f, v_to_e_list args ++ [:: AI_invoke a]) (hs, s', f, v_to_e_list res).
Proof.
  move => Hf Hr. exact: (fragment_deterministic_outcome (decoder_call_cfg_ok args a Hf) Hr).
Qed.

End DetInstance.
