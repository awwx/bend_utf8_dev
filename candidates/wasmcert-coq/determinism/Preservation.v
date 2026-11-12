(** * Preservation.v: a step from a fragment configuration stays in the
    fragment or traps, and never changes the function closures.

    Exports:
    - [ai_ok_v_to_e], [es_ok_const]: values are in the fragment.
    - [lfill_es_ok_replace]: replacing the hole content of a fragment
      context by a fragment list gives a fragment list.
    - [funcs_ok_lookup]: in a [funcs_ok] store, every closure is [func_ok].
    - [smem_store_funcs], [smem_store_packed_funcs], [supdate_glob_funcs]:
      the store updates the fragment can do leave [s_funcs] unchanged.
    - [fragment_step_preserved_proved : fragment_step_preserved] (PROVED). *)

From Stdlib Require Import NArith List.
From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool eqtype seq.
From Wasm Require Import datatypes operations opsem properties.
From Determinism Require Import Fragment ReduceDet Trapped.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Preservation.

Context `{ho: host}.

Lemma ai_ok_v_to_e v : ai_ok (v_to_e v).
Proof. by case: v => [?|?|[?|?|?]]. Qed.

Lemma ai_ok_vref r : ai_ok (vref_to_e r).
Proof. by case: r. Qed.

Lemma es_ok_const es : const_list es -> es_ok es.
Proof.
  elim: es => [//|e es IH]. rewrite /const_list /= => /andP [He Hes].
  move: (IH Hes). rewrite /es_ok /= => ->. rewrite andbT.
  move: He; rewrite /is_const.
  by case: e => //= [[] //] *.
Qed.

Lemma lfill_es_ok_replace k (lh : lholed k) es es' :
  es_ok (lfill lh es) -> es_ok es' -> es_ok (lfill lh es').
Proof.
  elim: lh => [vs es0|k' vs n es0 lh IH es1] /=.
  - rewrite !es_ok_cat => /andP [-> /andP [_ ->]] ->. by [].
  - rewrite !es_ok_cat !es_ok_cons /= => /andP [-> /andP [/andP [-> H] ->]] Hes'.
    by move: (IH H Hes'); rewrite /es_ok => ->.
Qed.

Lemma funcs_ok_lookup s a cl :
  funcs_ok s -> lookup_N s.(s_funcs) a = Some cl -> func_ok cl.
Proof.
  rewrite /funcs_ok /lookup_N => Hall Hn.
  move: (List.nth_error_In _ _ Hn) => Hin.
  exact: (proj1 (List.forallb_forall _ _) Hall _ Hin).
Qed.

Lemma smem_store_funcs s inst n off v t s' :
  smem_store s inst n off v t = Some s' -> s'.(s_funcs) = s.(s_funcs).
Proof.
  rewrite /smem_store.
  case: (lookup_N _ _) => // ?; case: (lookup_N _ _) => // ?; case: (store _ _ _ _ _) => // ?.
  by case => <-.
Qed.

Lemma smem_store_packed_funcs s inst n off v tp s' :
  smem_store_packed s inst n off v tp = Some s' -> s'.(s_funcs) = s.(s_funcs).
Proof.
  rewrite /smem_store_packed.
  case: (lookup_N _ _) => // ?; case: (lookup_N _ _) => // ?; case: (store_packed _ _ _ _ _) => // ?.
  by case => <-.
Qed.

Lemma supdate_glob_funcs s inst j v s' :
  supdate_glob s inst j v = Some s' -> s'.(s_funcs) = s.(s_funcs).
Proof.
  rewrite /supdate_glob /supdate_glob_s.
  case: (sglob_ind _ _ _) => //= k. case: (lookup_N _ _) => //= ?. by case => <-.
Qed.

Lemma es_ok_label n c LI : es_ok [:: AI_label n c LI] = es_ok c && es_ok LI.
Proof. by rewrite /es_ok /= andbT. Qed.

Lemma es_ok_frame n f es : es_ok [:: AI_frame n f es] = es_ok es.
Proof. by rewrite /es_ok /= andbT. Qed.

(** One case-closing tactic: unfold the fragment test of the left-hand
    side, and either refute it or show the right-hand side is in the
    fragment. *)
Ltac frag_cases :=
  subst;
  repeat match goal with
         | H : is_true (cfg_ok _ _) |- _ =>
             let H1 := fresh "Hfuncs" in let H2 := fresh "Hes" in
             move/andP: H => [H1 H2];
             rewrite ?es_ok_cat ?es_ok_cons /= ?ai_ok_v_to_e ?ai_ok_vref /= in H2
         end;
  repeat match goal with
         | H : is_true (_ && _) |- _ =>
             let H1 := fresh "Ha" in let H2 := fresh "Hb" in
             move/andP: H => [H1 H2]
         end;
  try by [];
  try (split; first by []);
  try (by right; apply/trapped_iff; exists AI_trap);
  try (left; rewrite ?es_ok_cat ?es_ok_cons ?es_ok_to_e_list /= ?ai_ok_v_to_e ?ai_ok_vref
              ?es_ok_v_to_e /= ?andbT; by [] || by apply: es_ok_const).

Ltac frag_finish :=
  try (match goal with
       | Hf : is_true (funcs_ok ?s), Hl : lookup_N (s_funcs ?s) _ = Some _ |- _ =>
           move: (funcs_ok_lookup Hf Hl) => /= Hcl
       end);
  try by [];
  try (match goal with
       | H : supdate_glob _ _ _ _ = Some _ |- _ => rewrite (supdate_glob_funcs H)
       | H : smem_store _ _ _ _ _ _ = Some _ |- _ => rewrite (smem_store_funcs H)
       | H : smem_store_packed _ _ _ _ _ _ = Some _ |- _ => rewrite (smem_store_packed_funcs H)
       end; by split; [|left]);
  try (left; rewrite ?es_ok_frame ?es_ok_label ?es_ok_cat ?es_ok_to_e_list /=;
       repeat (apply/andP; split); by [] || by apply: es_ok_const).

Theorem fragment_step_preserved_proved : fragment_step_preserved.
Proof.
  move => hs s f es hs' s' f' es' Hok Hred.
  elim: Hred Hok => {hs s f es hs' s' f' es'}.
  1: { move => e e' s f hs Hs. case: Hs => //; intros; frag_cases; frag_finish. }
  all: intros; frag_cases; frag_finish.
  (* r_invoke_native: the body comes from a fragment closure *)
  - left. rewrite !andbT. match goal with Hcl : is_true (forallb bi_ok ?es) |- _ =>
      by move: (es_ok_to_e_list es); rewrite /es_ok Hcl end.
  (* r_label *)
  - match goal with
    | IH : is_true (cfg_ok ?s ?es) -> _, Hf : is_true (funcs_ok ?s), Hes : is_true (es_ok (lfill ?lh ?es)) |- _ =>
        have [Hf' [Hok'|Ht]] := IH (introT andP (conj Hf (lfill_es_ok Hes)));
        split => //; [left; exact: (lfill_es_ok_replace Hes Hok') | right; exact: trapped_lfill]
    end.
  (* r_frame *)
  - match goal with
    | IH : is_true (cfg_ok ?s ?es) -> _, Hf : is_true (funcs_ok ?s), Hes : is_true (forallb ai_ok ?es) |- _ =>
        have [Hf' [Hok'|Ht]] := IH (introT andP (conj Hf Hes));
        split => //; [left; by rewrite es_ok_frame | right; apply/trapped_iff; eexists; by split]
    end.
Qed.

End Preservation.
