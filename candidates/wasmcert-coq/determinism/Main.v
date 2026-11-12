(** * Main.v: the unconditional results.

    Exports (PROVED, no premises beyond the fragment):
    - [reduce_det_fragment_proved : reduce_det_fragment] (from Det.v),
    - [fragment_deterministic_outcome]: a fragment configuration that
      reduces to a list of values has that as its only outcome
      ([deterministic_outcome]: every reachable configuration still
      reaches it, no infinite run, every stuck reachable configuration is
      it).
    The instance for the decoder's calls ([decoder_call_outcome]) is in
    ../decoder/DetInstance.v; this directory depends only on coq-wasm. *)

From Stdlib Require Import NArith List.
From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool eqtype seq.
From Wasm Require Import datatypes operations opsem properties.
From Determinism Require Import Fragment ReduceDet Trapped Preservation Det.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Main.

Context `{ho: host}.

Theorem fragment_deterministic_outcome hs s f es hs' s' f' vs :
  cfg_ok s es ->
  reduce_trans (hs, s, f, es) (hs', s', f', v_to_e_list vs) ->
  deterministic_outcome (hs, s, f, es) (hs', s', f', v_to_e_list vs).
Proof.
  exact: (deterministic_outcome_if reduce_det_fragment_proved
            fragment_step_preserved_proved trapped_step_preserved_proved).
Qed.

End Main.
