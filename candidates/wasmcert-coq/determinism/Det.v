(** * Det.v: [reduce] is deterministic on the fragment.

    Exports:
    - [cat_suffix_eq], [set_nth_irrelevant]: list facts.
    - [lfill_nl_unique]: a context filled with values followed by a
      non-label instruction ([br], [return]) determines the depth, the
      instruction and (given its length) the value list.
    - [br_stuck], [return_stuck]: such filled contexts do not step when the
      branch does not target a label inside them / for [return] always.
    - [head_step_det]: two [head_step]s of the same [ves ++ [e]] agree,
      given determinism for the body of [e] (label or frame).
    - [reduce_det_fragment_proved : reduce_det_fragment]. *)

From Stdlib Require Import NArith ZArith List Lia.
From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool eqtype seq.
From Wasm Require Import datatypes operations opsem properties contexts.
From Determinism Require Import Fragment ReduceDet Trapped Preservation Focus HeadStep.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Det.

Context `{ho: host}.

Notation ais := (seq administrative_instruction).

Lemma cat_suffix_eq (A : Type) (a b a' b' : seq A) :
  size b = size b' -> a ++ b = a' ++ b' -> a = a' /\ b = b'.
Proof.
  move => Hs H.
  have Ha : size a = size a' by move: (f_equal size H); rewrite !size_cat Hs => /addIn.
  move: (f_equal (take (size a)) H) (f_equal (drop (size a)) H).
  rewrite take_size_cat // drop_size_cat // Ha take_size_cat // drop_size_cat //.
Qed.

Lemma set_nth_irrelevant (A : Type) (x y : A) s i v :
  i < size s -> set_nth x s i v = set_nth y s i v.
Proof. elim: s i => [//|a s IH] [|i] //= Hi. by rewrite IH. Qed.

Lemma head_step_of hs s f ves e hs' s' f' X' :
  reduce hs s f (ves ++ [:: e]) hs' s' f' X' ->
  funcs_ok s -> const_list ves -> is_const e = false -> ai_ok e ->
  head_step hs s f ves e hs' s' f' X'.
Proof. move => Hr Hf Hv He Hok. exact: head_step_complete. Qed.

Lemma basic_not_label b : forall n c LI, AI_basic b <> AI_label n c LI.
Proof. by []. Qed.

Lemma not_const_label n c LI : is_const (AI_label n c LI) = false.
Proof. by []. Qed.

Lemma lfill_nl_unique k1 (lh1 : lholed k1) k2 (lh2 : lholed k2) vs1 vs2 x1 x2 :
  const_list vs1 -> const_list vs2 -> is_const x1 = false -> is_const x2 = false ->
  (forall n c LI, x1 <> AI_label n c LI) -> (forall n c LI, x2 <> AI_label n c LI) ->
  lfill lh1 (vs1 ++ [:: x1]) = lfill lh2 (vs2 ++ [:: x2]) ->
  k1 = k2 /\ x1 = x2 /\ (size vs1 = size vs2 -> vs1 = vs2).
Proof.
  move => Hv1 Hv2 Hx1 Hx2 Hl1 Hl2.
  case: (const_es_exists Hv1) => w1 ->. case: (const_es_exists Hv2) => w2 ->.
  have Nx1 : ~ is_const x1 by rewrite Hx1.
  have Nx2 : ~ is_const x2 by rewrite Hx2.
  have Nl : forall n c LI, ~ is_const (AI_label n c LI) by [].
  elim: lh1 k2 lh2 => [u1 r1|k1' u1 n1 c1 lh1 IH r1] k2 [u2 r2|k2' u2 n2 c2 lh2 r2] /= H.
  - rewrite -!catA /= !catA !v_to_e_cat in H.
    case: (v_to_e_split_eq Nx1 Nx2 H) => Eu [Ex _]. do 2 (split => //).
    rewrite !size_map => Hs. by case: (cat_suffix_eq Hs Eu) => _ ->.
  - rewrite -!catA /= !catA !v_to_e_cat in H.
    case: (v_to_e_split_eq Nx1 (Nl _ _ _) H) => _ [Ex _]. by case: (Hl1 _ _ _ Ex).
  - rewrite -!catA /= !catA !v_to_e_cat in H.
    case: (v_to_e_split_eq (Nl _ _ _) Nx2 H) => _ [Ex _]. by case: (Hl2 _ _ _ (esym Ex)).
  - case: (v_to_e_split_eq (Nl _ _ _) (Nl _ _ _) H) => _ [[_ _ Ein] _].
    case: (IH _ _ Ein) => -> [-> Hs]. by split.
Qed.

Lemma lfill_nl_unique_eq k1 (lh1 : lholed k1) k2 (lh2 : lholed k2) vs1 vs2 x1 x2 :
  lfill lh1 (vs1 ++ [:: x1]) = lfill lh2 (vs2 ++ [:: x2]) ->
  const_list vs1 -> const_list vs2 -> is_const x1 = false -> is_const x2 = false ->
  (forall n c LI, x1 <> AI_label n c LI) -> (forall n c LI, x2 <> AI_label n c LI) ->
  k1 = k2 /\ x1 = x2 /\ (size vs1 = size vs2 -> vs1 = vs2).
Proof. move => H *. exact: lfill_nl_unique H. Qed.

(** Splitting [lfill (LH_base ..)] around the first non-value. *)
Lemma lfill_base_split u (vs : ais) x r :
  const_list vs -> exists w, v_to_e_list u ++ (vs ++ [:: x]) ++ r = v_to_e_list w ++ x :: r.
Proof.
  move => Hv. case: (const_es_exists Hv) => w ->. exists (u ++ w).
  by rewrite -v_to_e_cat -!catA.
Qed.

Lemma br_stuck hs s f k (lh : lholed k) vs j hs' s' f' X :
  funcs_ok s -> const_list vs -> k <= j ->
  es_ok (lfill lh (vs ++ [:: AI_basic (BI_br (N.of_nat j))])) ->
  reduce hs s f (lfill lh (vs ++ [:: AI_basic (BI_br (N.of_nat j))])) hs' s' f' X -> False.
Proof.
  move => Hf Hv.
  elim: lh hs' s' f' X => [u r|k' u n c lh IH r] hs' s' f' X /= Hk Hok Hr.
  - case: (lfill_base_split u (AI_basic (BI_br (N.of_nat j))) r Hv) => w Ew.
    rewrite Ew in Hr.
    case: (reduce_focus_first_gen Hr (vs := w) (e := AI_basic (BI_br (N.of_nat j))) (rest := r) erefl _ erefl)
      => // X0 [_ Hr0].
    move: (head_step_of Hr0 Hf (v_to_e_const _) erefl erefl) => Hh.
    inversion Hh.
  - case: (reduce_focus_first_gen Hr (vs := u) (e := AI_label n c (lfill lh (vs ++ [:: AI_basic (BI_br (N.of_nat j))])))
             (rest := r) erefl _ erefl) => // X0 [_ Hr0].
    have Hokl : ai_ok (AI_label n c (lfill lh (vs ++ [:: AI_basic (BI_br (N.of_nat j))]))).
    { move: Hok. by rewrite es_ok_cat es_ok_cons => /andP [_ /andP [-> _]]. }
    move: (head_step_of Hr0 Hf (v_to_e_const _) erefl Hokl) => Hh.
    inversion Hh; subst.
    + match goal with H : is_true (const_list (lfill _ _)) |- _ => move/const_list_lfill_hole: H end.
      by rewrite const_list_cat Hv /=.
    + match goal with H : lfill ?lh0 (?vs0 ++ _) = lfill lh _, Hc : is_true (const_list ?vs0) |- _ =>
        case: (lfill_nl_unique_eq H Hc Hv erefl erefl (@basic_not_label _) (@basic_not_label _)) => Ek [Ex _] end.
      case: Ex => /Nat2N.inj Eij. subst. by rewrite ltnn in Hk.
    + eapply IH; [exact: (ltnW Hk) | by move: Hokl => /= /andP [_ H]; exact: H | eassumption].
Qed.

Lemma return_stuck hs s f k (lh : lholed k) vs hs' s' f' X :
  funcs_ok s -> const_list vs ->
  es_ok (lfill lh (vs ++ [:: AI_basic BI_return])) ->
  reduce hs s f (lfill lh (vs ++ [:: AI_basic BI_return])) hs' s' f' X -> False.
Proof.
  move => Hf Hv.
  elim: lh hs' s' f' X => [u r|k' u n c lh IH r] hs' s' f' X /= Hok Hr.
  - case: (lfill_base_split u (AI_basic BI_return) r Hv) => w Ew.
    rewrite Ew in Hr.
    case: (reduce_focus_first_gen Hr (vs := w) (e := AI_basic BI_return) (rest := r) erefl _ erefl)
      => // X0 [_ Hr0].
    move: (head_step_of Hr0 Hf (v_to_e_const _) erefl erefl) => Hh.
    inversion Hh.
  - case: (reduce_focus_first_gen Hr (vs := u) (e := AI_label n c (lfill lh (vs ++ [:: AI_basic BI_return])))
             (rest := r) erefl _ erefl) => // X0 [_ Hr0].
    have Hokl : ai_ok (AI_label n c (lfill lh (vs ++ [:: AI_basic BI_return]))).
    { move: Hok. by rewrite es_ok_cat es_ok_cons => /andP [_ /andP [-> _]]. }
    move: (head_step_of Hr0 Hf (v_to_e_const _) erefl Hokl) => Hh.
    inversion Hh; subst.
    + match goal with H : is_true (const_list (lfill _ _)) |- _ => move/const_list_lfill_hole: H end.
      by rewrite const_list_cat Hv /=.
    + match goal with H : lfill ?lh0 (?vs0 ++ _) = lfill lh _, Hc : is_true (const_list ?vs0) |- _ =>
        case: (lfill_nl_unique_eq H Hc Hv erefl erefl (@basic_not_label _) (@basic_not_label _)) => Ek [Ex _] end.
      by [].
    + eapply IH; [by move: Hokl => /= /andP [_ H]; exact: H | eassumption].
Qed.

Definition det_at hs s f (es : ais) : Prop :=
  forall hs1 s1 f1 es1 hs2 s2 f2 es2,
    reduce hs s f es hs1 s1 f1 es1 -> reduce hs s f es hs2 s2 f2 es2 ->
    (hs1, s1, f1, es1) = (hs2, s2, f2, es2).

Ltac det_simpl :=
  repeat match goal with
  | H : ?a ++ [:: _] = ?a' ++ [:: _] |- _ =>
      apply cat_suffix_eq in H; [ case: H => ? H; try injection H; intros; subst | by [] ]
  | H : ?a ++ [:: _; _] = ?a' ++ [:: _; _] |- _ =>
      apply cat_suffix_eq in H; [ case: H => ? H; try injection H; intros; subst | by [] ]
  | H : ?a ++ [:: _; _; _] = ?a' ++ [:: _; _; _] |- _ =>
      apply cat_suffix_eq in H; [ case: H => ? H; try injection H; intros; subst | by [] ]
  | H : Some _ = Some _ |- _ => injection H; intros; subst
  | H : v_to_e _ = v_to_e _ |- _ => apply ve_inj in H; subst
  | H1 : ?x = Some _, H2 : ?x = Some _ |- _ => rewrite H1 in H2
  | H1 : ?x = Some _, H2 : ?x = None |- _ => rewrite H1 in H2; discriminate
  | H1 : ?x = ?y, H2 : ?x <> ?y |- _ => by case: (H2 H1)
  end.

Lemma head_step_det hs s f ves e hs1 s1 f1 X1 hs2 s2 f2 X2 :
  funcs_ok s -> ai_ok e ->
  (forall n c LI, e = AI_label n c LI -> det_at hs s f LI) ->
  (forall n f0 es0, e = AI_frame n f0 es0 -> det_at hs s f0 es0) ->
  head_step hs s f ves e hs1 s1 f1 X1 -> head_step hs s f ves e hs2 s2 f2 X2 ->
  (hs1, s1, f1, X1) = (hs2, s2, f2, X2).
Proof.
  move => Hf Hok Hl Hfr H1 H2.
  case: H1 Hok Hl Hfr H2 => *;
    match goal with H : head_step _ _ _ _ _ _ _ _ _ |- _ => inversion H; subst end;
    det_simpl; try by [].
  (* br_table: in range and out of range are exclusive *)
  all: try (exfalso; lia).
  (* block, loop, invoke: the number of consumed values is fixed *)
  all: try (match goal with H : ?a ++ ?b = ?a' ++ ?b' |- _ =>
              apply cat_suffix_eq in H;
              [ case: H => ? H; subst; try (apply v_to_e_inj in H; subst); det_simpl; by []
              | rewrite ?size_map -?length_is_size; lia ]
            end).
  (* a value list does not step *)
  all: try (match goal with Hc : is_true (const_list ?L), Hr : reduce _ _ _ ?L _ _ _ _ |- _ =>
              case: (const_irreducible_gen Hr Hc) end).
  (* a context filled with a branch / return is not a value list *)
  all: try (match goal with Hc : is_true (const_list (lfill _ (?vs ++ _))), Hv : is_true (const_list ?vs) |- _ =>
              move/const_list_lfill_hole: Hc; by rewrite const_list_cat Hv end).
  (* a context filled with a branch to its own depth / a return does not step *)
  all: try (match goal with
            | Hr : reduce _ _ _ (lfill ?lh (?vs ++ [:: AI_basic (BI_br (N.of_nat _))])) _ _ _ _,
              Hv : is_true (const_list ?vs), Hok : is_true (ai_ok (AI_label _ _ _)) |- _ =>
                exfalso; apply: (br_stuck Hf Hv (leqnn _) _ Hr); by move: Hok => /= /andP [_ H]
            | Hr : reduce _ _ _ (lfill ?lh (?vs ++ [:: AI_basic BI_return])) _ _ _ _,
              Hv : is_true (const_list ?vs), Hok : is_true (ai_ok (AI_frame _ _ _)) |- _ =>
                exfalso; apply: (return_stuck Hf Hv _ Hr); by move: Hok => /= H
            end).
  (* two branches / returns: same values *)
  all: try (match goal with
            | H : lfill _ (?vs0 ++ [:: ?x0]) = lfill _ (?vs ++ [:: ?x]),
              Hv0 : is_true (const_list ?vs0), Hv : is_true (const_list ?vs) |- _ =>
                case: (lfill_nl_unique_eq H Hv0 Hv erefl erefl (@basic_not_label _) (@basic_not_label _))
                  => _ [_ Hs]; rewrite Hs // -!length_is_size; by congruence
            end).
  (* steps inside a label or frame body: induction hypothesis *)
  all: try (match goal with
            | Hl : forall n c LI, AI_label _ _ _ = _ -> det_at _ _ _ _,
              H1 : reduce _ _ _ ?L _ _ _ _, H2 : reduce _ _ _ ?L _ _ _ _ |- _ =>
                case: (Hl _ _ _ erefl _ _ _ _ _ _ _ _ H1 H2) => *; by subst
            | Hl : forall n f0 es0, AI_frame _ _ _ = _ -> det_at _ _ _ _,
              H1 : reduce _ _ _ ?L _ _ _ _, H2 : reduce _ _ _ ?L _ _ _ _ |- _ =>
                case: (Hl _ _ _ erefl _ _ _ _ _ _ _ _ H1 H2) => *; by subst
            end).
  (* local.set: the new frame is determined (the default of set_nth is irrelevant in range) *)
  all: match goal with
       | H1 : f_inst ?f1 = f_inst ?f, H2 : f_inst ?f2 = f_inst ?f,
         L1 : f_locs ?f1 = set_nth _ _ _ _, L2 : f_locs ?f2 = set_nth _ _ _ _,
         Hi : (N.to_nat _ < length _)%coq_nat |- _ =>
           have E : f1 = f2;
           [ destruct f1, f2; simpl in *; subst; f_equal; apply: set_nth_irrelevant;
             by rewrite -length_is_size; apply/ltP
           | by rewrite E ]
       | H1 : f_inst ?f1 = f_inst ?f, H2 : f_inst ?f2 = f_inst ?f,
         L1 : f_locs ?f1 = set_nth _ _ _ _, L2 : f_locs ?f2 = set_nth _ _ _ _,
         Hi : is_true (N.to_nat _ < length _) |- _ =>
           have E : f1 = f2;
           [ destruct f1, f2; simpl in *; subst; f_equal; apply: set_nth_irrelevant;
             by rewrite -length_is_size
           | by rewrite E ]
       end.
Qed.

(** ** Assembly, by induction on the nesting size of the instruction list *)

Fixpoint ai_size (e : administrative_instruction) : nat :=
  match e with
  | AI_label _ _ LI => (fix go l := match l with [::] => 0 | x :: l' => ai_size x + go l' end) LI + 1
  | AI_frame _ _ es => (fix go l := match l with [::] => 0 | x :: l' => ai_size x + go l' end) es + 1
  | _ => 1
  end.

Definition es_size (l : ais) : nat := sumn (map ai_size l).

Lemma ai_size_label n c LI : ai_size (AI_label n c LI) = es_size LI + 1.
Proof. rewrite /= /es_size. congr (_ + 1). by elim: LI => //= x l ->. Qed.

Lemma ai_size_frame n f0 es : ai_size (AI_frame n f0 es) = es_size es + 1.
Proof. rewrite /= /es_size. congr (_ + 1). by elim: es => //= x l ->. Qed.

Lemma es_size_split vs e rest : ai_size e <= es_size (v_to_e_list vs ++ e :: rest).
Proof. by rewrite /es_size map_cat sumn_cat /= addnCA leq_addr. Qed.

Theorem reduce_det_fragment_proved : reduce_det_fragment.
Proof.
  suff H : forall m hs s f es, es_size es < m -> cfg_ok s es -> det_at hs s f es.
  { move => hs s f es hs1 s1 f1 es1 hs2 s2 f2 es2 Hok H1 H2.
    exact: (H (es_size es).+1 hs s f es (ltnSn _) Hok _ _ _ _ _ _ _ _ H1 H2). }
  elim => [|m IH] hs s f es Hsz Hok //.
  move => hs1 s1 f1 X1 hs2 s2 f2 X2 H1 H2.
  have Hnc : const_list es = false.
  { case Hc: (const_list es) => //. case: (const_irreducible_gen H1 Hc). }
  case: (first_nc_not_const Hnc) => e /first_nc_some [He [vs [rest Ees]]]. subst es.
  move: (Hok) => /andP [Hf Hes].
  have Hoke : ai_ok e by move: Hes; rewrite es_ok_cat es_ok_v_to_e es_ok_cons => /andP [_ /andP [-> _]].
  have Ht : e <> AI_trap by move => E; rewrite E in Hoke.
  case: (reduce_focus_first_gen H1 He Ht erefl) => Y1 [-> Hr1].
  case: (reduce_focus_first_gen H2 He Ht erefl) => Y2 [-> Hr2].
  have Hh1 := head_step_of Hr1 Hf (v_to_e_const _) He Hoke.
  have Hh2 := head_step_of Hr2 Hf (v_to_e_const _) He Hoke.
  have Hlt : ai_size e <= m by move: (es_size_split vs e rest) Hsz => /leq_ltn_trans H /H; rewrite ltnS.
  have E : (hs1, s1, f1, Y1) = (hs2, s2, f2, Y2).
  { apply: (head_step_det Hf Hoke _ _ Hh1 Hh2).
    - move => n c LI E. subst e. apply: IH.
      + by move: Hlt; rewrite ai_size_label addn1.
      + by rewrite /cfg_ok Hf; move: Hoke => /= /andP [_ H].
    - move => n f0 es0 E. subst e. apply: IH.
      + by move: Hlt; rewrite ai_size_frame addn1.
      + by rewrite /cfg_ok Hf. }
  by case: E => -> -> -> ->.
Qed.

End Det.
