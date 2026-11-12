(** * Trapped.v: once a configuration is [trapped], it stays trapped.

    Exports:
    - [first_nc es]: the first non-value instruction of [es], if any.
    - [trapped_head e]: [e] is [AI_trap], or a label / frame whose body is
      [trapped].
    - [trapped_iff]: [trapped es <-> exists e, first_nc es = Some e /\
      trapped_head e].
    - [trapped_lfill], [trapped_lfill_inv]: [trapped] commutes with
      filling an evaluation context (for a non-value hole content).
    - [trapped_step_preserved_proved : trapped_step_preserved] (PROVED,
      for every store, frame and host state; no fragment needed). *)

From Stdlib Require Import NArith List.
From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool eqtype seq.
From Wasm Require Import datatypes operations opsem properties.
From Determinism Require Import Fragment ReduceDet.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Trapped.

Context `{ho: host}.

Fixpoint first_nc (es : seq administrative_instruction) : option administrative_instruction :=
  match es with
  | [::] => None
  | e :: es' => if is_const e then first_nc es' else Some e
  end.

Definition trapped_head (e : administrative_instruction) : Prop :=
  match e with
  | AI_trap => True
  | AI_label _ _ LI => trapped LI
  | AI_frame _ _ es => trapped es
  | _ => False
  end.

Lemma is_const_v_to_e v : is_const (v_to_e v) = true.
Proof. by rewrite /is_const v2e2v. Qed.

Lemma first_nc_v v es : first_nc (v_to_e v :: es) = first_nc es.
Proof. by rewrite /= is_const_v_to_e. Qed.

Lemma first_nc_vs vs es : first_nc (v_to_e_list vs ++ es) = first_nc es.
Proof. elim: vs => [//|v vs IH] /=. by rewrite is_const_v_to_e. Qed.

Lemma first_nc_const_cat vs es : const_list vs -> first_nc (vs ++ es) = first_nc es.
Proof.
  elim: vs => [//|v vs IH] /=. rewrite /const_list /= => /andP [-> H]. exact: IH.
Qed.

Lemma first_nc_cat_some es rest e : first_nc es = Some e -> first_nc (es ++ rest) = Some e.
Proof. elim: es => [//|x es IH] /=. by case: (is_const x) => //. Qed.

Lemma first_nc_none es : first_nc es = None -> const_list es.
Proof.
  elim: es => [//|x es IH] /=. case Hx: (is_const x) => H //.
  move: (IH H). by rewrite /const_list /=.
Qed.

Lemma first_nc_some es e : first_nc es = Some e ->
  is_const e = false /\ exists vs rest, es = v_to_e_list vs ++ e :: rest.
Proof.
  elim: es => [//|x es IH] /=. case Hx: (is_const x).
  - move => /IH [He [vs [rest ->]]]. split => //.
    move: Hx; rewrite /is_const. case Hv: (e_to_v_opt x) => [v|//] _.
    exists (v :: vs), rest. rewrite /=.
    suff -> : x = v_to_e v by [].
    by case: x Hv => //= [[] //= ? [<-] | ? [<-] | ? [<-]].
  - case => <-. split => //. by exists [::], es.
Qed.

Lemma first_nc_not_const es : const_list es = false -> exists e, first_nc es = Some e.
Proof.
  case H: (first_nc es) => [e|]; first by exists e.
  by rewrite (first_nc_none H).
Qed.

Lemma trapped_iff es : trapped es <-> exists e, first_nc es = Some e /\ trapped_head e.
Proof.
  split.
  - case => [vs rest|vs n cont es0 rest H|vs n f es0 rest H];
      rewrite first_nc_vs /=; by eexists; split.
  - move => [e [/first_nc_some [_ [vs [rest ->]]] Hh]].
    case: e Hh => //= *; by constructor.
Qed.

Lemma trapped_lfill k (lh : lholed k) es : trapped es -> trapped (lfill lh es).
Proof.
  elim: lh => [vs es'|k' vs n es' lh IH es''] /= Ht.
  - move/trapped_iff: Ht => [e [He Hh]]. apply/trapped_iff. exists e.
    by rewrite first_nc_vs (first_nc_cat_some _ He).
  - apply/trapped_iff. rewrite first_nc_vs /=. eexists; split; first by [].
    exact: IH.
Qed.

Lemma trapped_lfill_inv k (lh : lholed k) es :
  const_list es = false -> trapped (lfill lh es) -> trapped es.
Proof.
  move => Hnc. case: (first_nc_not_const Hnc) => e He.
  elim: lh => [vs es'|k' vs n es' lh IH es''] /=.
  - move/trapped_iff => [e' [He' Hh]]. apply/trapped_iff. exists e'.
    move: He'. rewrite first_nc_vs (first_nc_cat_some _ He) => - [Ee]. subst. by split.
  - move/trapped_iff => [e' [He' Hh]]. move: He'. rewrite first_nc_vs /= => - [Ee].
    rewrite -Ee /= in Hh. exact: IH.
Qed.

(** Lists whose first non-value instruction is a given non-trapped
    instruction are not trapped. *)
Lemma not_trapped_first es e : first_nc es = Some e -> ~ trapped_head e -> ~ trapped es.
Proof. move => He Hh /trapped_iff [e' [He' Hh']]. rewrite He in He'. case: He' => Ee. by subst. Qed.

Lemma lfill_vs_e_not_trapped k (lh : lholed k) vs e :
  const_list vs -> is_const e = false -> ~ trapped_head e ->
  ~ trapped (lfill lh (vs ++ [:: e])).
Proof.
  move => Hvs He Hh /trapped_lfill_inv H.
  have Hnc : const_list (vs ++ [:: e]) = false by rewrite const_list_cat Hvs /= He.
  move: (H Hnc). apply: (not_trapped_first (e := e)); last exact: Hh.
  by rewrite first_nc_const_cat //= He.
Qed.

Lemma first_nc_const es : const_list es -> first_nc es = None.
Proof.
  elim: es => [//|x es IH] /=. rewrite /const_list /= => /andP [-> H]. exact: IH.
Qed.

(** [trapped [e]] for a single label or frame is [trapped] of its body. *)
Lemma trapped_single e : trapped [:: e] -> trapped_head e.
Proof.
  move/trapped_iff => [e' [He Hh]]. move: He => /=.
  case Hc: (is_const e) => // - [Ee]. by subst.
Qed.

Lemma is_const_vref r : is_const (vref_to_e r) = true.
Proof. by case: r. Qed.

Ltac not_trapped H :=
  move/trapped_iff: H => [? []];
  rewrite ?first_nc_vs ?first_nc_v ?first_nc_const_cat /= ?is_const_vref /=;
  try (case => <-); by [].

Ltac trapped_cases :=
  subst;
  try (match goal with H : trapped _ |- _ => not_trapped H end);
  try (match goal with H : trapped [:: _] |- _ => move/trapped_single: H => /= H end);
  try (match goal with H : trapped ?l, H' : is_true (const_list ?l) |- _ =>
         by move/trapped_iff: H => [? []]; rewrite first_nc_const end);
  try (match goal with H : trapped (lfill _ _) |- _ =>
         by exfalso; apply: (lfill_vs_e_not_trapped _ _ _ H) end).

Theorem trapped_step_preserved_proved : trapped_step_preserved.
Proof.
  move => hs s f es hs' s' f' es' Ht Hred.
  elim: Hred Ht => {hs s f es hs' s' f' es'}.
  (* r_simple *)
  1: { move => e e' s f hs Hs. case: Hs => //; intros;
         try by (apply/trapped_iff; exists AI_trap).
       all: trapped_cases. }
  all: intros; trapped_cases.
  all: try by (apply/trapped_iff; exists AI_trap).
  (* r_label: the hole content is not a value list, so it is trapped *)
  - match goal with
    | Hred : reduce _ _ _ ?es _ _ _ _, IH : trapped ?es -> _, H : trapped (lfill _ ?es) |- _ =>
        apply: trapped_lfill; apply: IH; apply: (trapped_lfill_inv _ H);
        case Hc: (const_list es) => //; exfalso; exact: (const_irreducible_gen Hred Hc)
    end.
  (* r_frame *)
  - apply/trapped_iff. eexists; split; first by [].
    match goal with IH : trapped ?es -> _, H : trapped ?es |- _ => exact: IH H end.
Qed.



End Trapped.
