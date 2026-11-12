(** * Focus.v: first decomposition lemma towards [reduce_det_fragment].

    Exports (PROVED):
    - [split_last_nc]: list algebra: if [Y] is all values, the first
      non-value of [Y ++ [x]] is [x] and nothing follows it.
    - [reduce_focus_first_gen]: a step from [vs ++ e :: rest], where [e]
      is the first non-value instruction and is not [AI_trap], leaves
      [rest] untouched: the result is [es0' ++ rest] for a step
      [vs ++ [e] -> es0'] with the same store, frame and host state.
      (Holds for every configuration; no fragment needed.)

    So determinism reduces to steps of lists [values ++ [e]]
    (HeadStep.v, Det.v). *)

From Stdlib Require Import NArith List.
From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool eqtype seq.
From Wasm Require Import datatypes operations opsem properties contexts.
From Determinism Require Import Fragment ReduceDet Trapped.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Focus.

Context `{ho: host}.

(** If the first non-value of [Y ++ [x]] is at position [size vs], with
    [Y] all values, then nothing follows it. *)
Lemma split_last_nc Y x vs e rest :
  const_list Y -> is_const e = false ->
  Y ++ [:: x] = v_to_e_list vs ++ e :: rest -> e = x /\ rest = [::].
Proof.
  elim: Y vs => [|y Y IH] [|v vs] //= HY He.
  - by case => -> ->.
  - case => _ Ex. by case: vs Ex.
  - move => [Ey _]. move: HY. by rewrite /const_list /= Ey He.
  - move: HY. rewrite /const_list /= => /andP [_ HY] E. case: E => _ E. exact: (IH vs HY He E).
Qed.


Ltac cl_tac := by rewrite /const_list /= ?is_const_v_to_e ?is_const_vref.

Ltac focus_with Y x He HX :=
  let E1 := fresh "E" in let E2 := fresh "E" in
  destruct (@split_last_nc Y x _ _ _ ltac:(cl_tac) He HX) as [E1 E2].

Ltac focus_base :=
  match goal with
  | HX : ?Y ++ [:: ?x] = v_to_e_list _ ++ _ :: _, He : is_const _ = false |- _ =>
      let E1 := fresh "E" in let E2 := fresh "E" in
      destruct (@split_last_nc Y x _ _ _ ltac:(first [assumption | apply: v_to_e_const]) He HX) as [E1 E2]
  | HX : [:: ?x] = v_to_e_list _ ++ _ :: _, He : is_const _ = false |- _ => focus_with (@nil administrative_instruction) x He HX
  | HX : [:: ?a; ?x] = v_to_e_list _ ++ _ :: _, He : is_const _ = false |- _ => focus_with [:: a] x He HX
  | HX : [:: ?a; ?b; ?x] = v_to_e_list _ ++ _ :: _, He : is_const _ = false |- _ => focus_with [:: a; b] x He HX
  | HX : [:: ?a; ?b; ?c; ?x] = v_to_e_list _ ++ _ :: _, He : is_const _ = false |- _ => focus_with [:: a; b; c] x He HX
  end.

Lemma lfill0_trap_first k (lh : lholed k) : k = 0 -> first_nc (lfill lh [:: AI_trap]) = Some AI_trap.
Proof. case: lh => [vs es|? ? ? ? ? ?] //= _. by rewrite first_nc_vs. Qed.

Lemma first_nc_split vs e rest : is_const e = false -> first_nc (v_to_e_list vs ++ e :: rest) = Some e.
Proof. move => He. by rewrite first_nc_vs /= He. Qed.

Lemma reduce_focus_first_gen hs s f X hs' s' f' X' :
  reduce hs s f X hs' s' f' X' ->
  forall vs e rest, is_const e = false -> e <> AI_trap ->
  X = v_to_e_list vs ++ e :: rest ->
  exists es0', X' = es0' ++ rest /\ reduce hs s f (v_to_e_list vs ++ [:: e]) hs' s' f' es0'.
Proof.
  elim => {hs s f X hs' s' f' X'}.
  1: { move => e e' s f hs Hs vs e0 rest He Ht HX.
       case: Hs HX => //; intros.
       all: try (focus_base; subst; eexists; rewrite cats0; split; first reflexivity;
             match goal with HX : _ = v_to_e_list _ ++ [:: _] |- _ => rewrite -HX end;
             by apply: r_simple; econstructor; eauto).
       (* rs_trap: the first non-value would be the trap *)
       all: exfalso; subst; match goal with
                     | HX : lfill ?lh _ = _ ++ _ :: _, He : is_const ?e = false, Ht : ?e <> AI_trap |- _ =>
                         move: (lfill0_trap_first lh erefl); rewrite HX first_nc_split // => - [E]; by apply: Ht
                     end. }
  all: intros.
  all: try (subst; focus_base; subst; eexists; rewrite cats0; split; first reflexivity;
             match goal with HX : _ = v_to_e_list _ ++ [:: _] |- _ => rewrite -HX end;
             by econstructor; eauto).
  (* r_label *)
  match goal with
  | Hred : reduce _ _ _ ?es0 _ _ _ ?es0', IH : forall _ _ _, _ -> _ -> ?es0 = _ -> _,
    HX0 : ?L = v_to_e_list _ ++ _ :: _, He0 : is_const _ = false, Ht0 : _ <> AI_trap |- _ =>
      rename IH into IHr; rename HX0 into HX; rename He0 into He; rename Ht0 into Ht
  end.
  match goal with
  | Hred : reduce _ _ _ ?es0 _ _ _ ?es0', HX : lfill ?lh ?es0 = _ |- _ =>
      have Hnc : const_list es0 = false by case Hc: (const_list es0) => //; case: (const_irreducible_gen Hred Hc)
  end.
  match goal with H : lfill _ _ = les' |- _ => subst les' end.
  match goal with H : lfill _ _ = les |- _ => subst les end.
  move: HX Hnc. case: lh => [vs' es''|k' vs' n c lh' es''] /= HX Hnc.
  - case: (first_nc_not_const Hnc) => e1 /first_nc_some [He1 [vs1 [r1 Ees0]]].
    rewrite Ees0 -catA /= catA v_to_e_cat in HX.
    case: (v_to_e_split_eq (e1 := e1) (e2 := e) (ltac:(by rewrite He1)) (ltac:(by rewrite He)) HX) => Evs [Ee Erest]. subst.
    case: (IHr vs1 e r1 He Ht erefl) => es1 [Ees0' Hr1]. subst.
    exists (v_to_e_list vs' ++ es1). split; first by rewrite !catA.
    rewrite -v_to_e_cat -catA.
    apply: (r_label (lh := LH_base vs' [::])); first exact: Hr1.
    + by rewrite /= cats0.
    + by rewrite /= cats0.
  - have Hl : is_const (AI_label n c (lfill lh' es)) = false by [].
    case: (v_to_e_split_eq (e1 := AI_label n c (lfill lh' es)) (e2 := e) (ltac:(by rewrite Hl)) (ltac:(by rewrite He)) HX) => Evs [Ee Erest]. subst.
    exists (v_to_e_list vs ++ [:: AI_label n c (lfill lh' es')]). split; first by rewrite -catA.
    apply: (r_label (lh := LH_rec vs n c lh' [::])); first exact: H.
    + by rewrite /= ?cats0.
    + by rewrite /= ?cats0.
Qed.

End Focus.
