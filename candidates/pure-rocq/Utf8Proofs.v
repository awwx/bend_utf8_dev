(* Utf8Proofs.v: proofs of the laws of Utf8Laws.v and of RefDecoder_correct.

   Exported for downstream use (see also Utf8Ref.v for the definitions
   RefDecoder, step, step_empty, State, vp, vs, seq_value, seq_cp, bN,
   seq_len, lo2, hi2, is_cont, second_ok):

   - <law>_proved : <law>   for each spec-internal law of Utf8Laws.v
   - RefDecoder_correct : Decoder_correct RefDecoder
   - encodes_iff : encodes s cp <-> vs s = true /\ cp = seq_cp s
   - valid_sequence_iff : is_valid_sequence s <-> vs s = true
   - valid_sequence_prefix_iff : is_valid_sequence_prefix s <-> vp s = true
   - seq_cp_value : vs s = true -> U32_to_N (seq_cp s) = seq_value s
   - seq_value_scalar : vs s = true -> seq_value s <= 0x10FFFF /\ not surrogate
   - run, run_app, ref_decode_buffer_run, step_inv, Inv (state invariant)
   - step_output_ok : every code point output by step is a scalar or U+FFFD
   - byte-range equations: see section "Range lemmas" at the end. *)

From Stdlib Require Import List NArith Arith Bool Lia.
From Stdlib Require Strings.Byte Strings.Ascii.
Import Corelib.Init.Byte ListNotations.
From Utf8 Require Import Utf8Laws Utf8Ref Utf8Check.

Local Open Scope N_scope.

(** * Bit-level laws *)

Theorem bit8_value_sum_proved : bit8_value_sum.
Proof. intros [] [] [] [] [] [] [] []; reflexivity. Qed.

Theorem bit8_value_word_proved : bit8_value_word.
Proof. intros [] [] [] [] [] [] [] []; reflexivity. Qed.

Theorem u32_byte4_bits_proved : u32_byte4_bits.
Proof. unfold u32_byte4_bits; intros; reflexivity. Qed.

Theorem is_surrogate_code_point_examples_proved : is_surrogate_code_point_examples.
Proof. vm_compute. repeat split. Qed.

(** * U32 round trip *)

Lemma tb0 b x : N.testbit (N.b2n b + 2 * x) 0 = b.
Proof.
  destruct b; simpl N.b2n;
    [rewrite N.add_comm; apply N.testbit_odd_0|rewrite N.add_0_l; apply N.testbit_even_0].
Qed.

Lemma tbS b x p : N.testbit (N.b2n b + 2 * x) (N.pos p) = N.testbit x (Pos.pred_N p).
Proof.
  rewrite <- (N.succ_pos_pred p) at 1.
  destruct b; simpl N.b2n;
    [rewrite N.add_comm; apply N.testbit_odd_succ|rewrite N.add_0_l; apply N.testbit_even_succ]; lia.
Qed.

Lemma tb_last b : N.testbit (N.b2n b) 0 = b.
Proof. destruct b; reflexivity. Qed.

(* ~8 s: 528 rewrites. *)
Lemma U32_of_to x : U32_of_N (U32_to_N x) = x.
Proof.
  destruct x; unfold U32_to_N, U32_of_N.
  repeat (first [rewrite tb0 | rewrite tbS]; cbv [Pos.pred_N Pos.pred_double]).
  rewrite !tb_last. reflexivity.
Qed.

Lemma U32_to_N_inj x y : U32_to_N x = U32_to_N y -> x = y.
Proof. intros H; rewrite <- (U32_of_to x), <- (U32_of_to y), H; reflexivity. Qed.

Lemma scalar_bounds cp :
  is_unicode_scalar cp = true -> U32_to_N cp <= 0x10FFFF /\ is_surr_N (U32_to_N cp) = false.
Proof.
  unfold is_unicode_scalar, is_surrogate_code_point, U32_is_ge, U32_is_le.
  assert (E1 : U32_to_N (U32_of_N 0) = 0) by reflexivity.
  assert (E2 : U32_to_N (U32_of_N 0x10FFFF) = 0x10FFFF) by reflexivity.
  assert (E3 : U32_to_N (U32_of_N 0xD800) = 0xD800) by reflexivity.
  assert (E4 : U32_to_N (U32_of_N 0xDFFF) = 0xDFFF) by reflexivity.
  rewrite E1, E2, E3, E4. unfold is_surr_N.
  intros H; repeat rewrite andb_true_iff in H. destruct H as [[_ H1] H2].
  apply N.leb_le in H1. split; auto. apply negb_true_iff in H2.
  rewrite <- H2; f_equal.
Qed.

(** * Valid sequences: central characterization *)

Lemma vs_vp s : vs s = true -> vp s = true.
Proof. unfold vs; intros H; apply andb_true_iff in H; tauto. Qed.

Lemma vs_nil : vs [] = false.
Proof. reflexivity. Qed.

Lemma encodes_vs s cp : encodes s cp -> vs s = true /\ cp = seq_cp s.
Proof.
  intros [Hsc Hen]. destruct (scalar_bounds _ Hsc) as [Hb Hs].
  rewrite <- (U32_of_to cp) in Hen.
  destruct (checkA _ Hb Hs) as (_ & He & Hv & Hval & _).
  rewrite He in Hen; injection Hen as <-. split; auto.
  unfold seq_cp; rewrite Hval; symmetry; apply U32_of_to.
Qed.

Lemma vs_fB s : vs s = true ->
  scalarN (seq_value s) = true /\ enc_N (seq_value s) = s.
Proof.
  intros H. pose proof (checkB s (vs_vp s H)) as HB. unfold fB in HB.
  rewrite H in HB; cbn [implb negb andb] in HB. apply andb_true_iff in HB as [HB _].
  apply andb_true_iff in HB as [H1 H2]. split; auto. apply bytes_eqb_eq; auto.
Qed.

Lemma seq_value_scalar s : vs s = true ->
  seq_value s <= 0x10FFFF /\ ~ (0xD800 <= seq_value s <= 0xDFFF).
Proof.
  intros H; destruct (vs_fB s H) as [H1 _]. unfold scalarN, is_surr_N in H1.
  apply andb_true_iff in H1 as [H1 H2]. apply N.leb_le in H1. split; auto.
  apply negb_true_iff in H2. intros [A B].
  apply N.leb_le in A; apply N.leb_le in B. rewrite A, B in H2; discriminate.
Qed.

Lemma vs_encodes s : vs s = true -> encodes s (seq_cp s).
Proof.
  intros H; destruct (vs_fB s H) as [H1 H2].
  unfold scalarN in H1; apply andb_true_iff in H1 as [H1 H3].
  apply N.leb_le in H1; apply negb_true_iff in H3.
  destruct (checkA _ H1 H3) as (Hs & He & _).
  split; unfold seq_cp; auto. rewrite He, H2; reflexivity.
Qed.

Lemma seq_cp_value s : vs s = true -> U32_to_N (seq_cp s) = seq_value s.
Proof.
  intros H; destruct (vs_fB s H) as [H1 _].
  unfold scalarN in H1; apply andb_true_iff in H1 as [H1 H3].
  apply N.leb_le in H1; apply negb_true_iff in H3.
  destruct (checkA _ H1 H3) as (_ & _ & _ & _ & E); exact E.
Qed.

Theorem encodes_iff s cp : encodes s cp <-> vs s = true /\ cp = seq_cp s.
Proof.
  split; [apply encodes_vs|]. intros [H ->]; apply vs_encodes; auto.
Qed.

Theorem valid_sequence_iff s : is_valid_sequence s <-> vs s = true.
Proof.
  split; [intros [cp H]; apply (encodes_vs _ _ H)|].
  intros H; exists (seq_cp s); apply vs_encodes; auto.
Qed.

Lemma pending_completion s : vp s = true -> vs s = false ->
  vs (s ++ completion s) = true /\ seq_value (s ++ completion s) <> 0xFFFD.
Proof.
  intros H1 H2. pose proof (checkB s H1) as HB. unfold fB in HB.
  rewrite H2 in HB; cbn [implb negb andb] in HB.
  apply andb_true_iff in HB as [A B]. split; auto.
  apply negb_true_iff in B. intros E; rewrite E in B; discriminate.
Qed.

Theorem valid_sequence_prefix_iff s : is_valid_sequence_prefix s <-> vp s = true.
Proof.
  split.
  - destruct s as [|b1 m]; simpl; [tauto|]. intros [rest H].
    apply valid_sequence_iff, vs_vp in H. apply (vp_app (b1 :: m) rest H). discriminate.
  - intros H. destruct s as [|b1 m]; [discriminate|]. unfold is_valid_sequence_prefix.
    destruct (vs (b1 :: m)) eqn:E.
    + exists []; rewrite app_nil_r; apply valid_sequence_iff; auto.
    + exists (completion (b1 :: m)); apply valid_sequence_iff, pending_completion; auto.
Qed.

Lemma vs_prefix_free s t : vs s = true -> vs (s ++ t) = true -> t = [].
Proof.
  destruct s as [|b1 m]; [discriminate|]. unfold vs.
  intros H1 H2. apply andb_true_iff in H1 as [_ H1]. apply andb_true_iff in H2 as [_ H2].
  cbn [app length] in H1, H2. apply Nat.eqb_eq in H1, H2. rewrite length_app in H2.
  destruct t; auto. cbn [length] in *. lia.
Qed.

Lemma pending_no_valid_prefix st : vp st = true -> vs st = false ->
  forall seq l, st = seq ++ l -> vs seq = true -> False.
Proof.
  intros H1 H2 seq l E Hv. destruct (pending_completion st H1 H2) as [Hc _].
  rewrite E, <- app_assoc in Hc. pose proof (vs_prefix_free _ _ Hv Hc) as Z.
  apply app_eq_nil in Z as [-> _]. rewrite app_nil_r in E; subst; congruence.
Qed.

(** * The laws about valid sequences and subparts *)

Theorem begins_with_scalar_unique_proved : begins_with_scalar_unique.
Proof.
  intros bytes cp1 r1 cp2 r2 [s1 [E1 A1]] [s2 [E2 A2]].
  apply encodes_vs in E1 as [V1 ->]; apply encodes_vs in E2 as [V2 ->].
  rewrite <- A2 in A1. apply app_eq_app in A1 as [l [[-> B]|[-> B]]].
  - rewrite (vs_prefix_free _ _ V2 V1) in *. rewrite app_nil_r; auto.
  - rewrite (vs_prefix_free _ _ V1 V2) in *. rewrite app_nil_r; auto.
Qed.

Theorem not_valid_sequence_prefix_extended_proved : not_valid_sequence_prefix_extended.
Proof.
  intros b1 more extra H1 H2. apply H1.
  apply valid_sequence_prefix_iff in H2; apply valid_sequence_prefix_iff.
  apply (vp_app _ _ H2). discriminate.
Qed.

Lemma ms_le b1 more s1 s2 l :
  maximal_subpart b1 more s1 -> maximal_subpart b1 more s2 -> s1 = s2 ++ l -> l = [].
Proof.
  intros [[x1 P1] [V1 _]] [_ [V2 L2]] E. destruct l as [|c e]; auto. exfalso.
  apply (L2 c e). { exists x1; rewrite <- E; exact P1. }
  rewrite <- E. destruct V1 as [V1|V1]; auto. subst s1.
  destruct s2 as [|y s2]; [destruct V2 as [V2|V2]; [exfalso; exact V2|discriminate]|].
  simpl in E; injection E as _ E. destruct s2; discriminate.
Qed.

Theorem maximal_subpart_unique_proved : maximal_subpart_unique.
Proof.
  intros b1 more s1 s2 M1 M2.
  pose proof M1 as [[x1 P1] _]. pose proof M2 as [[x2 P2] _].
  rewrite <- P2 in P1. apply app_eq_app in P1 as [l [[E _]|[E _]]].
  - pose proof (ms_le _ _ _ _ _ M1 M2 E) as Z; subst l. rewrite app_nil_r in E; auto.
  - pose proof (ms_le _ _ _ _ _ M2 M1 E) as Z; subst l. rewrite app_nil_r in E; auto.
Qed.

(** * Relational facts about decodes_first, by case of the step machine *)

Lemma df_valid s rest : vs s = true -> decodes_first (s ++ rest) (Some (seq_cp s, rest)).
Proof.
  intros H. destruct s as [|b1 m]; [discriminate|]. cbn [app decodes_first].
  left. exists (seq_cp (b1 :: m)), rest. split; auto.
  exists (b1 :: m); split; auto. apply vs_encodes; auto.
Qed.

Lemma bws_vs bytes cp rest :
  begins_with_scalar bytes cp rest -> exists seq, vs seq = true /\ seq ++ rest = bytes.
Proof. intros [seq [E A]]; exists seq; split; auto. apply (encodes_vs _ _ E). Qed.

Lemma df_bad_lead b rest : vp [b] = false -> decodes_first (b :: rest) (Some (FFFD, rest)).
Proof.
  intros Hb. cbn [decodes_first]. right. split.
  - intros cp r H. apply bws_vs in H as [[|c sq] [Hv A]]; [discriminate|].
    injection A as -> _. apply vs_vp in Hv.
    rewrite (vp_app [b] sq Hv ltac:(discriminate)) in Hb; discriminate.
  - exists [b], rest. split; [|split; reflexivity].
    split; [exists rest; reflexivity|]. split; [right; reflexivity|].
    intros c extra _ Hvp. apply valid_sequence_prefix_iff in Hvp.
    rewrite (vp_app [b] _ Hvp ltac:(discriminate)) in Hb; discriminate.
Qed.

Lemma df_replaced b1 more sp rest :
  no_valid_sequence (b1 :: more) -> maximal_subpart b1 more sp -> sp ++ rest = b1 :: more ->
  decodes_first (b1 :: more) (Some (FFFD, rest)).
Proof. intros H1 H2 H3. right. split; auto. exists sp, rest; auto. Qed.

Lemma df_stuck st b rest : vp st = true -> vs st = false -> vp (st ++ [b]) = false ->
  decodes_first (st ++ b :: rest) (Some (FFFD, b :: rest)).
Proof.
  intros H1 H2 H3.
  assert (Hne : forall x, st ++ x <> []) by (intros x; destruct st; discriminate).
  assert (NV : no_valid_sequence (st ++ b :: rest)).
  { intros cp r H. apply bws_vs in H as [seq [Hv A]].
    apply app_eq_app in A as [l [[E B]|[E B]]].
    - destruct l as [|x l'].
      + rewrite app_nil_r in E; subst seq; congruence.
      + injection B as -> _. subst seq. apply vs_vp in Hv.
        replace (st ++ x :: l') with ((st ++ [x]) ++ l') in Hv by (rewrite <- app_assoc; reflexivity).
        rewrite (vp_app _ _ Hv (Hne _)) in H3; discriminate.
    - apply (pending_no_valid_prefix st H1 H2 seq l E Hv). }
  assert (ML : maximal_subpart_longer_not_valid_prefix st (st ++ b :: rest)).
  { intros c extra [r' Hr'] Hvp.
    rewrite <- app_assoc in Hr'. apply app_inv_head in Hr'. injection Hr' as -> _.
    apply valid_sequence_prefix_iff in Hvp.
    replace (st ++ b :: extra) with ((st ++ [b]) ++ extra) in Hvp by (rewrite <- app_assoc; reflexivity).
    rewrite (vp_app _ _ Hvp (Hne _)) in H3; discriminate. }
  destruct st as [|c0 st0]; [discriminate|].
  apply df_replaced with (sp := c0 :: st0); [exact NV| |reflexivity].
  split; [exists (b :: rest); reflexivity|].
  split; [left; apply valid_sequence_prefix_iff; auto|exact ML].
Qed.

Lemma df_pending_end st : vp st = true -> vs st = false ->
  decodes_first st (Some (FFFD, [])).
Proof.
  intros H1 H2.
  assert (NV : no_valid_sequence st).
  { intros cp r H. apply bws_vs in H as [seq [Hv A]].
    apply (pending_no_valid_prefix st H1 H2 seq r (eq_sym A) Hv). }
  assert (ML : maximal_subpart_longer_not_valid_prefix st st).
  { intros c extra [r' Hr'] _.
    apply (f_equal (@length byte)) in Hr'. rewrite !length_app in Hr'. cbn [length] in Hr'. lia. }
  destruct st as [|c0 st0]; [discriminate|].
  apply df_replaced with (sp := c0 :: st0); [exact NV| |apply app_nil_r].
  split; [exists []; apply app_nil_r|].
  split; [left; apply valid_sequence_prefix_iff; auto|exact ML].
Qed.

Theorem decodes_first_unique_proved : decodes_first_unique.
Proof.
  intros [|b1 m] r1 r2; cbn [decodes_first]; [intros -> ->; reflexivity|].
  intros [[cp1 [rs1 [B1 ->]]]|[N1 [sp1 [rs1 [M1 [A1 ->]]]]]]
         [[cp2 [rs2 [B2 ->]]]|[N2 [sp2 [rs2 [M2 [A2 ->]]]]]].
  - destruct (begins_with_scalar_unique_proved _ _ _ _ _ B1 B2) as [-> ->]; auto.
  - exfalso; apply (N2 _ _ B1).
  - exfalso; apply (N1 _ _ B2).
  - rewrite (maximal_subpart_unique_proved _ _ _ _ M1 M2) in A1.
    rewrite <- A2 in A1. apply app_inv_head in A1; subst; auto.
Qed.

Theorem decodes_first_empty_proved : decodes_first_empty.
Proof. intros r H; exact H. Qed.

Theorem decodes_first_nonempty_proved : decodes_first_nonempty.
Proof.
  intros b1 m r [[cp [rs [_ ->]]]|[_ [sp [rs [_ [_ ->]]]]]]; reflexivity.
Qed.

(** * The step machine *)

Definition Inv (st : State) : Prop := st = [] \/ (vp st = true /\ vs st = false).

Fixpoint run (st : State) (bytes : list byte) : State * Text :=
  match bytes with
  | [] => (st, [])
  | b :: r => let '(s1, o1) := step st b in let '(s2, o2) := run s1 r in (s2, o1 ++ o2)
  end.

Lemma fold_run bytes st out :
  fold_left step_acc bytes (st, out) = (fst (run st bytes), out ++ snd (run st bytes)).
Proof.
  revert st out; induction bytes as [|b r IH]; intros st out; simpl.
  - rewrite app_nil_r; reflexivity.
  - destruct (step st b) as [s1 o1]. rewrite IH. destruct (run s1 r) as [s2 o2]; simpl.
    rewrite app_assoc; reflexivity.
Qed.

Lemma ref_decode_buffer_run st bytes : ref_decode_buffer st bytes = run st bytes.
Proof. unfold ref_decode_buffer; rewrite fold_run; destruct (run st bytes); reflexivity. Qed.

Lemma run_app st x y :
  run st (x ++ y) = let '(s1, o1) := run st x in let '(s2, o2) := run s1 y in (s2, o1 ++ o2).
Proof.
  revert st; induction x as [|b r IH]; intros st; simpl.
  - destruct (run st y); reflexivity.
  - destruct (step st b) as [s1 o1]. rewrite IH. destruct (run s1 r) as [s2 o2].
    destruct (run s2 y) as [s3 o3]. rewrite app_assoc; reflexivity.
Qed.

Lemma step_empty_inv b : Inv (fst (step_empty b)).
Proof.
  unfold step_empty, Inv. destruct (vp [b]) eqn:E1; [destruct (vs [b]) eqn:E2|]; simpl; auto.
Qed.

Lemma step_inv st b : Inv st -> Inv (fst (step st b)).
Proof.
  intros _. destruct st as [|c st0]; [apply step_empty_inv|]. unfold step.
  destruct (vp ((c :: st0) ++ [b])) eqn:E1; [destruct (vs ((c :: st0) ++ [b])) eqn:E2|].
  - left; reflexivity.
  - right; auto.
  - pose proof (step_empty_inv b). destruct (step_empty b); auto.
Qed.

Lemma run_inv st bytes : Inv st -> Inv (fst (run st bytes)).
Proof.
  revert st; induction bytes as [|b r IH]; intros st H; simpl; auto.
  pose proof (step_inv st b H) as H1. destruct (step st b) as [s1 o1].
  specialize (IH s1 H1). destruct (run s1 r); auto.
Qed.

Lemma decodes_cons bytes cp r t :
  decodes_first bytes (Some (cp, r)) -> decodes r t -> decodes bytes (cp :: t).
Proof. intros H1 H2; exists r; split; auto. Qed.

Lemma step_empty_dec b rest t :
  decodes (fst (step_empty b) ++ rest) t -> decodes (b :: rest) (snd (step_empty b) ++ t).
Proof.
  unfold step_empty. destruct (vp [b]) eqn:E1; [destruct (vs [b]) eqn:E2|]; cbn [fst snd app]; intros H.
  - apply decodes_cons with rest; auto. apply (df_valid [b] rest E2).
  - exact H.
  - apply decodes_cons with rest; auto. apply df_bad_lead; auto.
Qed.

Lemma step_dec st b rest t : Inv st ->
  decodes (fst (step st b) ++ rest) t -> decodes (st ++ b :: rest) (snd (step st b) ++ t).
Proof.
  intros [->|[H1 H2]]; [apply step_empty_dec|].
  destruct st as [|c st0] eqn:Est; [discriminate|]. rewrite <- Est in *.
  assert (Hs : step st b = if vp (st ++ [b]) then if vs (st ++ [b]) then ([], [seq_cp (st ++ [b])])
             else (st ++ [b], []) else let '(st', o) := step_empty b in (st', FFFD :: o))
    by (rewrite Est; reflexivity).
  rewrite Hs. replace (st ++ b :: rest) with ((st ++ [b]) ++ rest) by (rewrite <- app_assoc; reflexivity).
  destruct (vp (st ++ [b])) eqn:E1; [destruct (vs (st ++ [b])) eqn:E2|]; cbn [fst snd app]; intros H.
  - apply decodes_cons with rest; auto. apply df_valid; auto.
  - exact H.
  - pose proof (step_empty_dec b rest t) as Hd. destruct (step_empty b) as [s1 o1]; cbn [fst snd app] in *.
    rewrite <- app_assoc. apply decodes_cons with (b :: rest); auto.
    apply df_stuck; auto.
Qed.

Lemma run_dec st bytes rest t : Inv st ->
  decodes (fst (run st bytes) ++ rest) t -> decodes (st ++ bytes ++ rest) (snd (run st bytes) ++ t).
Proof.
  revert st t; induction bytes as [|b r IH]; intros st t Hi; simpl; auto.
  pose proof (step_inv st b Hi) as Hi1. pose proof (step_dec st b (r ++ rest)) as Hs.
  destruct (step st b) as [s1 o1]. specialize (IH s1). destruct (run s1 r) as [s2 o2]; simpl in *.
  intros H. rewrite <- app_assoc. apply Hs; auto.
Qed.

Lemma done_dec st : Inv st -> decodes st (ref_done st).
Proof.
  intros [->|[H1 H2]]; [reflexivity|].
  destruct st as [|c st0] eqn:Est; [discriminate|]. rewrite <- Est in *.
  replace (ref_done st) with [FFFD] by (rewrite Est; reflexivity).
  apply decodes_cons with []; [apply df_pending_end; auto|reflexivity].
Qed.

Lemma ref_decode_run bytes :
  ref_decode bytes = snd (run [] bytes) ++ ref_done (fst (run [] bytes)).
Proof. unfold ref_decode; rewrite ref_decode_buffer_run; destruct (run [] bytes); reflexivity. Qed.

Theorem ref_decode_ok bytes : decodes bytes (ref_decode bytes).
Proof.
  rewrite ref_decode_run. pose proof (run_dec [] bytes [] (ref_done (fst (run [] bytes)))) as H.
  rewrite !app_nil_r in H. cbn [app] in H. apply H; [left; reflexivity|].
  apply done_dec, run_inv; left; reflexivity.
Qed.

(** * Laws about decodes_first and decodes *)

Theorem decodes_first_exists_proved : decodes_first_exists.
Proof.
  intros bytes. pose proof (ref_decode_ok bytes) as H. unfold decodes in H.
  destruct (ref_decode bytes) as [|cp t]; simpl in H; [eauto|].
  destruct H as [r [H _]]; eauto.
Qed.

Theorem maximal_subpart_exists_proved : maximal_subpart_exists.
Proof.
  intros b1 more Hn. destruct (decodes_first_exists_proved (b1 :: more)) as [r H].
  destruct H as [[cp [rs [B _]]]|[_ [sp [rs [M _]]]]]; [exfalso; apply (Hn _ _ B)|eauto].
Qed.

Theorem decodes_exists_proved : decodes_exists.
Proof. intros bytes; exists (ref_decode bytes); apply ref_decode_ok. Qed.

Theorem decodes_unique_proved : decodes_unique.
Proof.
  unfold decodes. intros bytes t1; revert bytes; induction t1 as [|c1 t1 IH];
    intros bytes [|c2 t2]; simpl.
  - auto.
  - intros H [r [H2 _]]. pose proof (decodes_first_unique_proved _ _ _ H H2); discriminate.
  - intros [r [H1 _]] H. pose proof (decodes_first_unique_proved _ _ _ H H1); discriminate.
  - intros [r1 [H1 G1]] [r2 [H2 G2]].
    pose proof (decodes_first_unique_proved _ _ _ H1 H2) as E; injection E as -> ->.
    f_equal; eauto.
Qed.

Theorem decodes_examples_proved : decodes_examples.
Proof.
  repeat split;
  match goal with
  | |- decodes ?l ?T => replace T with (ref_decode l) by (vm_compute; reflexivity);
                        apply ref_decode_ok
  end.
Qed.

(** * Streaming laws for RefDecoder *)

Lemma feed_run buffers st :
  feed RefDecoder buffers st = run st (concat buffers).
Proof.
  revert st; induction buffers as [|buf rest IH]; intros st; [reflexivity|].
  simpl concat. rewrite run_app. simpl feed. unfold feed_then.
  change (decode_buffer RefDecoder st buf) with (ref_decode_buffer st buf).
  rewrite ref_decode_buffer_run. destruct (run st buf) as [s1 o1].
  unfold feed_prepend. rewrite IH. destruct (run s1 (concat rest)); reflexivity.
Qed.

Lemma decoded_run buffers :
  decoded RefDecoder buffers = snd (run [] (concat buffers)) ++ ref_done (fst (run [] (concat buffers))).
Proof. unfold decoded; rewrite feed_run; change (decode_start_state RefDecoder) with (@nil byte); destruct (run [] (concat buffers)); reflexivity. Qed.

Lemma decoded_so_far_run buffers :
  decoded_so_far RefDecoder buffers = snd (run [] (concat buffers)).
Proof. unfold decoded_so_far; rewrite feed_run; change (decode_start_state RefDecoder) with (@nil byte); destruct (run [] (concat buffers)); reflexivity. Qed.

Theorem RefDecoder_decodes : utf8_decodes RefDecoder.
Proof.
  intros buffers. rewrite decoded_run. rewrite <- ref_decode_run. apply ref_decode_ok.
Qed.

Theorem RefDecoder_safe : utf8_decode_buffer_safe RefDecoder.
Proof.
  intros buffers rest full H. rewrite decoded_so_far_run.
  set (bytes := concat buffers) in *.
  pose proof (run_inv [] bytes (or_introl eq_refl)) as Hi.
  set (st' := fst (run [] bytes)) in *.
  destruct (decodes_exists_proved (st' ++ rest)) as [t Ht].
  pose proof (run_dec [] bytes rest t (or_introl eq_refl) Ht) as H2. simpl in H2.
  rewrite (decodes_unique_proved _ _ _ H H2). exists t; reflexivity.
Qed.

Lemma U32_eq_dec (x y : U32) : {x = y} + {x <> y}.
Proof. decide equality; apply bool_dec. Qed.

Theorem RefDecoder_prompt : utf8_decode_buffer_prompt RefDecoder.
Proof.
  intros buffers c. rewrite decoded_so_far_run.
  set (bytes := concat buffers).
  pose proof (run_inv [] bytes (or_introl eq_refl)) as Hi.
  set (st' := fst (run [] bytes)) in *. set (o := snd (run [] bytes)).
  assert (Hr : forall rest t, decodes (st' ++ rest) t -> decodes (bytes ++ rest) (o ++ t))
    by (intros rest t Ht; exact (run_dec [] bytes rest t (or_introl eq_refl) Ht)).
  destruct Hi as [Hst|[H1 H2]].
  - exists [], o. split.
    + pose proof (Hr [] [] ltac:(rewrite Hst; reflexivity)) as G.
      rewrite (app_nil_r o) in G; exact G.
    + intros [m Hm]. apply (f_equal (@length U32)) in Hm. rewrite !length_app in Hm.
      simpl in Hm; lia.
  - destruct (U32_eq_dec c FFFD) as [->|Hc].
    + destruct (pending_completion st' H1 H2) as [Hv Hne].
      exists (completion st'), (o ++ [seq_cp (st' ++ completion st')]). split.
      * apply Hr. apply decodes_cons with []; [|reflexivity].
        pose proof (df_valid _ [] Hv) as G; rewrite app_nil_r in G; exact G.
      * intros [m Hm]. rewrite <- app_assoc in Hm. apply app_inv_head in Hm.
        apply (f_equal (hd FFFD)) in Hm. cbn [hd app] in Hm.
        apply Hne. rewrite <- (seq_cp_value _ Hv), <- Hm. reflexivity.
    + exists [], (o ++ [FFFD]). split.
      * apply Hr. rewrite app_nil_r. apply decodes_cons with []; [apply df_pending_end; auto|reflexivity].
      * intros [m Hm]. rewrite <- app_assoc in Hm. apply app_inv_head in Hm.
        apply (f_equal (hd c)) in Hm. cbn [hd app] in Hm. auto.
Qed.

Theorem RefDecoder_correct : Decoder_correct RefDecoder.
Proof. split; [apply RefDecoder_decodes|split; [apply RefDecoder_safe|apply RefDecoder_prompt]]. Qed.

(** * Downstream lemmas: outputs, ranges, step equations *)

(* What a code point output by the decoder satisfies. *)
Definition output_ok (cp : U32) : Prop :=
  cp = FFFD \/
  (is_unicode_scalar cp = true /\ U32_to_N cp <= 0x10FFFF /\
   ~ (0xD800 <= U32_to_N cp <= 0xDFFF)).

Lemma FFFD_value : U32_to_N FFFD = 0xFFFD.
Proof. reflexivity. Qed.

Lemma seq_cp_ok s : vs s = true -> output_ok (seq_cp s).
Proof.
  intros H. right. rewrite (seq_cp_value s H). split; [apply (vs_encodes s H)|].
  apply seq_value_scalar; auto.
Qed.

Lemma step_empty_output_ok b : Forall output_ok (snd (step_empty b)).
Proof.
  unfold step_empty. destruct (vp [b]); [destruct (vs [b]) eqn:E|]; cbn [snd].
  - constructor; [apply seq_cp_ok; auto|constructor].
  - constructor.
  - constructor; [left; reflexivity|constructor].
Qed.

Theorem step_output_ok st b : Forall output_ok (snd (step st b)).
Proof.
  destruct st as [|c st0]; [apply step_empty_output_ok|]. unfold step.
  destruct (vp ((c :: st0) ++ [b])); [destruct (vs ((c :: st0) ++ [b])) eqn:E|].
  - constructor; [apply seq_cp_ok; auto|constructor].
  - constructor.
  - pose proof (step_empty_output_ok b) as H. destruct (step_empty b) as [s1 o1].
    cbn [snd] in *. constructor; auto. left; reflexivity.
Qed.

Theorem ref_done_output_ok st : Forall output_ok (ref_done st).
Proof. destruct st; cbn; constructor; [left; reflexivity|constructor]. Qed.

(* Pending state length: at most 3 bytes. *)
Lemma Inv_len st : Inv st -> (length st <= 3)%nat.
Proof.
  intros [->|[H1 H2]]; [simpl; lia|].
  destruct st as [|b1 r]; [discriminate|].
  pose proof (vp_len_lead _ _ H1) as L. pose proof (seq_len_le4 (bN b1)).
  unfold vs in H2. rewrite H1 in H2. cbn [andb] in H2. apply Nat.eqb_neq in H2. lia.
Qed.

(* Lead-byte table. *)
Lemma seq_len_cases n :
  (n <= 0x7F /\ seq_len n = 1%nat) \/
  (0xC2 <= n <= 0xDF /\ seq_len n = 2%nat) \/
  (0xE0 <= n <= 0xEF /\ seq_len n = 3%nat) \/
  (0xF0 <= n <= 0xF4 /\ seq_len n = 4%nat) \/
  (((0x80 <= n <= 0xC1) \/ 0xF5 <= n) /\ seq_len n = 0%nat).
Proof.
  unfold seq_len.
  destruct (N.leb_spec n 0x7F); [left; auto|].
  destruct (N.leb_spec 0xC2 n), (N.leb_spec n 0xDF); cbn [andb];
    try (right; left; split; [lia|reflexivity]);
  destruct (N.leb_spec 0xE0 n), (N.leb_spec n 0xEF); cbn [andb];
    try (right; right; left; split; [lia|reflexivity]);
  destruct (N.leb_spec 0xF0 n), (N.leb_spec n 0xF4); cbn [andb];
    try (right; right; right; left; split; [lia|reflexivity]);
  right; right; right; right; split; auto; lia.
Qed.

Lemma vp_one b : vp [b] = (Nat.ltb 0 (seq_len (bN b))).
Proof.
  unfold vp. cbn [length]. destruct (seq_len (bN b)) as [|[|k]]; reflexivity.
Qed.

Lemma vp_one_iff b : vp [b] = true <-> bN b <= 0x7F \/ 0xC2 <= bN b <= 0xF4.
Proof.
  rewrite vp_one, Nat.ltb_lt. destruct (seq_len_cases (bN b)) as [[A ->]|[[A ->]|[[A ->]|[[A ->]|[A ->]]]]];
    split; intros; try lia.
Qed.

Lemma vs_one_iff b : vs [b] = true <-> bN b <= 0x7F.
Proof.
  unfold vs. rewrite vp_one. cbn [length].
  destruct (seq_len_cases (bN b)) as [[A ->]|[[A ->]|[[A ->]|[[A ->]|[A ->]]]]];
    cbn; split; intros; try lia; try discriminate; auto.
Qed.

Lemma vp_cons2 b1 b2 r :
  vp (b1 :: b2 :: r) = true <->
  (2 + length r <= seq_len (bN b1))%nat /\
  lo2 (bN b1) <= bN b2 <= hi2 (bN b1) /\
  Forall (fun b => 0x80 <= bN b <= 0xBF) r.
Proof.
  unfold vp, second_ok, is_cont. cbn [length].
  rewrite !andb_true_iff, Nat.ltb_lt, Nat.leb_le, !N.leb_le, forallb_forall, Forall_forall.
  split.
  - intros [[A B] [[C D] E]]. split; [lia|split; [lia|]]. intros x Hx.
    specialize (E x Hx). apply andb_true_iff in E as [E1 E2]. apply N.leb_le in E1, E2; lia.
  - intros [A [B C]]. split; [lia|split; [lia|]]. intros x Hx.
    specialize (C x Hx). apply andb_true_iff; split; apply N.leb_le; lia.
Qed.

Lemma vs_vp_len s : vs s = true <-> vp s = true /\
  match s with [] => False | b1 :: _ => length s = seq_len (bN b1) end.
Proof.
  unfold vs. destruct s as [|b1 r]; [cbn; split; [discriminate|tauto]|].
  rewrite andb_true_iff, Nat.eqb_eq; tauto.
Qed.

(* Arithmetic value of the decoded code point (for shifts and masks). *)
Lemma seq_cp_value1 b1 : vs [b1] = true -> U32_to_N (seq_cp [b1]) = bN b1.
Proof. intros H; rewrite seq_cp_value; auto. Qed.
Lemma seq_cp_value2 b1 b2 : vs [b1; b2] = true ->
  U32_to_N (seq_cp [b1; b2]) = (bN b1 mod 32) * 64 + bN b2 mod 64.
Proof. intros H; rewrite seq_cp_value; auto. Qed.
Lemma seq_cp_value3 b1 b2 b3 : vs [b1; b2; b3] = true ->
  U32_to_N (seq_cp [b1; b2; b3]) = ((bN b1 mod 16) * 64 + bN b2 mod 64) * 64 + bN b3 mod 64.
Proof. intros H; rewrite seq_cp_value; auto. Qed.
Lemma seq_cp_value4 b1 b2 b3 b4 : vs [b1; b2; b3; b4] = true ->
  U32_to_N (seq_cp [b1; b2; b3; b4]) =
  (((bN b1 mod 8) * 64 + bN b2 mod 64) * 64 + bN b3 mod 64) * 64 + bN b4 mod 64.
Proof. intros H; rewrite seq_cp_value; auto. Qed.

(* Step equations, by case. *)
Lemma step_empty_ascii b : bN b <= 0x7F -> step [] b = ([], [seq_cp [b]]).
Proof.
  intros H. assert (V : vs [b] = true) by (apply vs_one_iff; auto).
  cbn [step]. unfold step_empty. rewrite (vs_vp _ V), V. reflexivity.
Qed.

Lemma step_empty_lead b : 0xC2 <= bN b <= 0xF4 -> step [] b = ([b], []).
Proof.
  intros H. assert (V : vp [b] = true) by (apply vp_one_iff; auto).
  assert (W : vs [b] = false) by (destruct (vs [b]) eqn:E; auto; apply vs_one_iff in E; lia).
  cbn [step]. unfold step_empty. rewrite V, W. reflexivity.
Qed.

Lemma step_empty_bad b : (0x80 <= bN b <= 0xC1 \/ 0xF5 <= bN b) -> step [] b = ([], [FFFD]).
Proof.
  intros H. assert (V : vp [b] = false)
    by (destruct (vp [b]) eqn:E; auto; apply vp_one_iff in E; lia).
  cbn [step]. unfold step_empty. rewrite V. reflexivity.
Qed.

Lemma step_pending st b : st <> [] ->
  step st b =
  if vp (st ++ [b]) then (if vs (st ++ [b]) then ([], [seq_cp (st ++ [b])]) else (st ++ [b], []))
  else let '(st', o) := step_empty b in (st', FFFD :: o).
Proof. destruct st; [congruence|reflexivity]. Qed.
