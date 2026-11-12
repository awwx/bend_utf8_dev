(** * Determinism.v: determinism of WasmCert-Coq's [reduce] on the
    fragment of Fragment.v, and what it gives for [reduce_trans].

    Statements (as [Prop] definitions, so they can be stated before they
    are proved; the build proves the ones marked PROVED):

    - [reduce_det_fragment] (PROVED in Det.v as
      [reduce_det_fragment_proved]): one step from a [cfg_ok]
      configuration has a unique result.
    - [fragment_step_preserved] (PROVED in Preservation.v as
      [fragment_step_preserved_proved]): a step from a [cfg_ok]
      configuration leaves the function closures unchanged and yields an
      [es_ok] list or a [trapped] one.
    - [trapped_step_preserved] (PROVED in Trapped.v as
      [trapped_step_preserved_proved]): a step from a [trapped] list
      yields a [trapped] list.

    PROVED here, with no premises:
    - [const_irreducible]: a list of values does not reduce.

    PROVED here, from the three statements above (the unconditional
    versions, with the three proofs plugged in, are in Main.v):
    - [unique_outcome]: if a [cfg_ok] configuration reaches a list of
      values [C], every configuration reachable from it still reaches [C]
      (so no reachable trap and no other result).
    - [no_infinite_run]: there is no infinite reduction sequence from it.
    - [maximal_run_ends_in_result]: every reachable irreducible
      configuration IS [C].
    Bundled as [deterministic_outcome_if].

    PROVED here, with no premises:
    - [still_reaches_stuck_is_target]: the first of these alone implies
      the third, for any configurations. *)

From Stdlib Require Import NArith List Relations.
From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool eqtype seq.
From Wasm Require Import datatypes operations opsem properties.
From Determinism Require Import Fragment.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Det.

Context `{ho: host}.

Notation cfg := (host_state * store_record * frame * seq administrative_instruction)%type.

(** ** The statements *)

(** 1. Step determinism on the fragment. *)
Definition reduce_det_fragment : Prop :=
  forall hs s f es hs1 s1 f1 es1 hs2 s2 f2 es2,
    cfg_ok s es ->
    reduce hs s f es hs1 s1 f1 es1 ->
    reduce hs s f es hs2 s2 f2 es2 ->
    (hs1, s1, f1, es1) = (hs2, s2, f2, es2).

(** The fragment is closed under steps, up to trapping. *)
Definition fragment_step_preserved : Prop :=
  forall hs s f es hs' s' f' es',
    cfg_ok s es ->
    reduce hs s f es hs' s' f' es' ->
    s'.(s_funcs) = s.(s_funcs) /\ (es_ok es' \/ trapped es').

(** Once trapped, always trapped (for any store, no fragment needed). *)
Definition trapped_step_preserved : Prop :=
  forall hs s f es hs' s' f' es',
    trapped es ->
    reduce hs s f es hs' s' f' es' ->
    trapped es'.

(** ** Values are irreducible (proved) *)

Lemma const_list_lfill_hole k (lh : lholed k) es :
  const_list (lfill lh es) -> const_list es.
Proof.
  case: lh => [vs es'|k' vs n es' lh es''] /=.
  - by rewrite !const_list_cat => /andP [_ /andP [H _]].
  - by rewrite const_list_cat /= andbF.
Qed.

Lemma const_list_v_to_e_cat_last vs e :
  const_list (v_to_e_list vs ++ [:: e]) -> is_const e.
Proof. by rewrite const_list_cat /= andbT => /andP [_]. Qed.

Lemma reduce_simple_not_const es es' : reduce_simple es es' -> const_list es -> False.
Proof.
  case => //=; intros;
    repeat match goal with
           | H : lfill _ _ = _ |- _ => subst
           end;
    try (match goal with
         | H : is_true (const_list (lfill _ _)) |- _ =>
             apply const_list_lfill_hole in H; by []
         end);
    try (match goal with
         | H : is_true (_ && _) |- _ => by rewrite !andbF in H
         end);
    try by [].
Qed.

Lemma const_irreducible_gen hs s f es hs' s' f' es' :
  reduce hs s f es hs' s' f' es' -> const_list es -> False.
Proof.
  elim => {hs s f es hs' s' f' es'} //=; intros;
    try (subst; by apply: reduce_simple_not_const; eauto);
    repeat match goal with
           | H : ?x = v_to_e_list _ |- _ => subst x
           | H : lfill _ _ = _ |- _ => subst
           end;
    try (match goal with
         | H : is_true (const_list (_ ++ [:: _])) |- _ =>
             rewrite const_list_cat /= ?andbF in H; by []
         end);
    try (match goal with
         | H : is_true (const_list (lfill _ _)) |- _ =>
             apply const_list_lfill_hole in H; by eauto
         end);
    try (match goal with
         | H : is_true (_ && _) |- _ => by rewrite !andbF in H
         end);
    try by [].
Qed.

Lemma const_irreducible hs s f vs hs' s' f' es' :
  reduce hs s f (v_to_e_list vs) hs' s' f' es' -> False.
Proof. move => H. apply: (const_irreducible_gen H). exact: v_to_e_const. Qed.

(** ** The corollary for [reduce_trans], from the three statements *)

Section FromStatements.

Hypothesis Hdet : reduce_det_fragment.
Hypothesis Hpres : fragment_step_preserved.
Hypothesis Htrap : trapped_step_preserved.

Definition cfg_ok_c (c : cfg) : bool := let '(_, s, _, es) := c in cfg_ok s es.
Definition trapped_c (c : cfg) : Prop := let '(_, _, _, es) := c in trapped es.
Definition result_c (c : cfg) (vs : seq value) : Prop :=
  let '(_, _, _, es) := c in es = v_to_e_list vs.

Lemma rt_rt1n (c c' : cfg) :
  reduce_trans c c' -> clos_refl_trans_1n _ reduce_tuple c c'.
Proof. exact: clos_rt_rt1n. Qed.

Lemma rt1n_rt (c c' : cfg) :
  clos_refl_trans_1n _ reduce_tuple c c' -> reduce_trans c c'.
Proof. exact: clos_rt1n_rt. Qed.

Lemma result_irreducible (c c' : cfg) vs : result_c c vs -> ~ reduce_tuple c c'.
Proof.
  case: c => [[[hs s] f] es]; case: c' => [[[hs' s'] f'] es'] /= ->.
  exact: const_irreducible.
Qed.

Lemma trapped_stays (c c' : cfg) :
  trapped_c c -> reduce_trans c c' -> trapped_c c'.
Proof.
  move => Ht /rt_rt1n H. elim: H Ht => [//|x y z Hxy _ IH] Hx.
  apply: IH. move: x y Hxy Hx => [[[? ?] ?] ?] [[[? ?] ?] ?].
  rewrite /reduce_tuple /trapped_c => H1 H2. exact: (Htrap H2 H1).
Qed.

Lemma trapped_never_result (c c' : cfg) vs :
  trapped_c c -> reduce_trans c c' -> result_c c' vs -> False.
Proof.
  move => Ht Hr. move: (trapped_stays Ht Hr).
  case: c' {Hr} => [[[? ?] ?] ?] /= Ht' Heq. rewrite Heq in Ht'.
  move: (trapped_not_const Ht'). by rewrite v_to_e_const.
Qed.

(** One step from a fragment configuration that reaches the result [D]
    lands in a fragment configuration that still reaches [D]. *)
Lemma step_towards_result (c c1 D : cfg) vs :
  cfg_ok_c c -> reduce_trans c D -> result_c D vs -> reduce_tuple c c1 ->
  cfg_ok_c c1 /\ reduce_trans c1 D.
Proof.
  move => Hok /rt_rt1n HD HR Hc1.
  case: HD HR Hc1 Hok => [|mid D' Hd Hrest] HR Hc1 Hok.
  - by case: (result_irreducible HR Hc1).
  - move: c c1 mid Hd Hc1 Hok Hrest => [[[hs s] f] es] [[[hs1 s1] f1] es1] [[[hd sd] fd] esd] /=
      Hd Hc1 Hok Hrest.
    have E := Hdet Hok Hd Hc1. case: E => ? ? ? ?; subst.
    case: (Hpres Hok Hc1) => Hf [Hes|Ht].
    + split; last exact: rt1n_rt.
      move: Hok; rewrite /cfg_ok /funcs_ok Hf => /andP [-> _]. by rewrite Hes.
    + exfalso. apply: (trapped_never_result (c := (hs1, s1, f1, es1)) _ _ HR) => //.
      exact: rt1n_rt.
Qed.

(** Every configuration reachable from [c] still reaches the result. *)
Theorem unique_outcome (c D c' : cfg) vs :
  cfg_ok_c c -> reduce_trans c D -> result_c D vs ->
  reduce_trans c c' -> cfg_ok_c c' /\ reduce_trans c' D.
Proof.
  move => Hok HD HR /rt_rt1n H.
  elim: H Hok HD => [x|x y z Hxy _ IH] Hok HD; first by [].
  case: (step_towards_result Hok HD HR Hxy) => Hy HyD. exact: IH.
Qed.

(** No infinite reduction sequence starts at [c]. *)
Theorem no_infinite_run (c D : cfg) vs :
  cfg_ok_c c -> reduce_trans c D -> result_c D vs ->
  forall run : nat -> cfg, run 0 = c ->
    (forall n, reduce_tuple (run n) (run n.+1)) -> False.
Proof.
  move => Hok HD HR run H0 Hrun.
  move: (rt_rt1n HD) => H1.
  elim: H1 run H0 Hrun Hok HD HR => [x|x y z Hxy Hyz IH] run H0 Hrun Hok HD HR.
  - move: (Hrun 0). rewrite H0. exact: (result_irreducible HR).
  - have Hr0 := Hrun 0. rewrite H0 in Hr0.
    case: (step_towards_result Hok HD HR Hr0) => Hok1 HD1.
    (* determinism: the run's second configuration is [y] *)
    have Ey : run 1 = y.
    { clear IH Hok1 HD1 HD H0.
      move: x (run 1) y Hxy Hr0 Hok {Hyz} => [[[? ?] ?] ?] [[[? ?] ?] ?] [[[? ?] ?] ?] /=
        Hxy Hr0 Hok.
      by case: (Hdet Hok Hr0 Hxy) => -> -> -> ->. }
    apply: (IH (fun n => run n.+1)); rewrite /= ?Ey //; by rewrite -Ey.
Qed.

(** Every reachable configuration that cannot step is the result. *)
Theorem maximal_run_ends_in_result (c D c' : cfg) vs :
  cfg_ok_c c -> reduce_trans c D -> result_c D vs ->
  reduce_trans c c' -> (forall c'', ~ reduce_tuple c' c'') -> c' = D.
Proof.
  move => Hok HD HR Hc' Hstuck.
  case: (unique_outcome Hok HD HR Hc') => _ /rt_rt1n H.
  case: H Hstuck => [//|y z Hy _] Hstuck. by case: (Hstuck _ Hy).
Qed.

End FromStatements.

(** The bundle a client uses: given the three statements, a fragment
    configuration that reaches a list of values has that as its only
    outcome. *)
Definition deterministic_outcome (c D : cfg) : Prop :=
  (forall c', reduce_trans c c' -> reduce_trans c' D) /\
  (forall run : nat -> cfg, run 0 = c -> (forall n, reduce_tuple (run n) (run n.+1)) -> False) /\
  (forall c', reduce_trans c c' -> (forall c'', ~ reduce_tuple c' c'') -> c' = D).

(** The first conjunct of [deterministic_outcome] alone already gives
    the third, for any configurations (no fragment needed): if every
    configuration reachable from [c] can still reach [D], then every
    reachable configuration that cannot reduce is [D]. *)
Lemma still_reaches_stuck_is_target (c D : cfg) :
  (forall c', reduce_trans c c' -> reduce_trans c' D) ->
  forall c', reduce_trans c c' -> (forall c'', ~ reduce_tuple c' c'') -> c' = D.
Proof.
  move => Hall c' Hc' Hstuck.
  move: (rt_rt1n (Hall c' Hc')) => H.
  case: H Hstuck => [//|y z Hy _] Hstuck. by case: (Hstuck _ Hy).
Qed.

Theorem deterministic_outcome_if :
  reduce_det_fragment -> fragment_step_preserved -> trapped_step_preserved ->
  forall hs s f es hs' s' f' vs,
    cfg_ok s es ->
    reduce_trans (hs, s, f, es) (hs', s', f', v_to_e_list vs) ->
    deterministic_outcome (hs, s, f, es) (hs', s', f', v_to_e_list vs).
Proof.
  move => Hdet Hpres Htrap hs s f es hs' s' f' vs Hok HD.
  have HR : result_c (hs', s', f', v_to_e_list vs) vs by [].
  split; [|split].
  - move => c' Hc'. by case: (unique_outcome Hdet Hpres Htrap (c := (hs, s, f, es)) Hok HD HR Hc').
  - exact: (no_infinite_run Hdet Hpres Htrap (c := (hs, s, f, es)) Hok HD HR).
  - move => c' Hc' Hs.
    exact: (@maximal_run_ends_in_result Hdet Hpres Htrap (hs, s, f, es) _ c' vs Hok HD HR Hc' Hs).
Qed.

End Det.
