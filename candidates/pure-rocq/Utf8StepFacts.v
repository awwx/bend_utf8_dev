(* Utf8StepFacts.v: RefDecoder's step function case by case, the byte ranges
   a pending state allows next, and how much UTF-16 output decoding can
   produce.  Pure (no Wasm); no axioms.  Used by implementations that are
   proved to refine RefDecoder (../wasmcert-coq/decoder).

   Exports:
   - Step equations for a non-empty pending state st and next byte b
     (complementing step_empty_ascii/_lead/_bad and step_pending of
     Utf8Proofs.v):
       step_reject   : vp (st ++ [b]) = false -> step st b = (fst (step [] b), FFFD :: snd (step [] b))
       step_extend   : vp = true, vs = false  -> step st b = (st ++ [b], [])
       step_complete : vs (st ++ [b]) = true   -> step st b = ([], [seq_cp (st ++ [b])])
   - Pending states (Inv (b1 :: r)):
       pending_lead : 0xC2 <= bN b1 <= 0xF4 and length (b1 :: r) < seq_len (bN b1)
       lo_next n b1, hi_next n b1 : the allowed range of the next byte after
         n pending bytes with lead b1 (lo2/hi2 after the lead, else 80..BF)
       pending_vp : vp (b1 :: r ++ [b]) = true <-> lo_next .. <= bN b <= hi_next ..
       pending_vs : (given vp) vs (b1 :: r ++ [b]) = true <-> length (b1 :: r) + 1 = seq_len (bN b1)
   - seq_cp_bound : vs s = true -> U32_to_N (seq_cp s) < 0x110000
   - ref_decode_buffer_snoc : decoding pre ++ [b] is decoding pre, then one step
   - Output size in UTF-16 code units (the count behind the decoder's
     output-area bound):
       cp_units cp     : 1 if U32_to_N cp < 0x10000, else 2 (a surrogate pair)
       text_units t    : sum of cp_units over t; text_units_app
       pending_units st: 0 if st = [], else 1 (pending bytes can later turn
                         into at most one more unit than the bytes still to come)
       step_units_bound    : text_units (snd (step st b)) + pending_units st'
                             <= 1 + pending_units st
       decode_units_bound  : for ref_decode_buffer st bs = (st', t),
                             text_units t + pending_units st' <= length bs + pending_units st
       ref_done_units_bound: text_units (ref_done st) <= 1 *)

From Stdlib Require Import List NArith Arith Bool Lia.
From Stdlib Require Strings.Byte.
Import ListNotations.
From Utf8 Require Import Utf8Laws Utf8Ref Utf8Proofs.

Local Open Scope N_scope.

(** * Step equations for a pending state *)

Lemma step_reject st b : st <> [] -> vp (st ++ [b]) = false ->
  step st b = (fst (step [] b), FFFD :: snd (step [] b)).
Proof.
  intros Hne Hvp. rewrite (step_pending _ _ Hne), Hvp. cbn [step].
  destruct (step_empty b); reflexivity.
Qed.

Lemma step_extend st b : st <> [] -> vp (st ++ [b]) = true -> vs (st ++ [b]) = false ->
  step st b = (st ++ [b], []).
Proof. intros Hne Hvp Hvs. rewrite (step_pending _ _ Hne), Hvp, Hvs. reflexivity. Qed.

Lemma step_complete st b : st <> [] -> vs (st ++ [b]) = true ->
  step st b = ([], [seq_cp (st ++ [b])]).
Proof. intros Hne Hvs. rewrite (step_pending _ _ Hne), (vs_vp _ Hvs), Hvs. reflexivity. Qed.

(** * Pending states: lead byte and the allowed next byte *)

Lemma pending_lead b1 r : Inv (b1 :: r) ->
  0xC2 <= bN b1 <= 0xF4 /\ (length (b1 :: r) < seq_len (bN b1))%nat.
Proof.
  intros [H|[Hvp Hvs]]; [discriminate|].
  pose proof (vp_len_lead _ _ Hvp) as Hle.
  assert (Hne : length (b1 :: r) <> seq_len (bN b1)).
  { intros E. assert (vs (b1 :: r) = true) by (apply vs_vp_len; split; assumption).
    congruence. }
  assert (Hlt : (length (b1 :: r) < seq_len (bN b1))%nat) by lia.
  split; [|exact Hlt].
  destruct (seq_len_cases (bN b1)) as [[A E]|[[A E]|[[A E]|[[A E]|[A E]]]]];
    rewrite E in Hlt; cbn [length] in Hlt; lia.
Qed.

Definition lo_next (n : nat) (b1 : Byte.byte) : N := if Nat.eqb n 1 then lo2 (bN b1) else 0x80.
Definition hi_next (n : nat) (b1 : Byte.byte) : N := if Nat.eqb n 1 then hi2 (bN b1) else 0xBF.

Lemma pending_vp b1 r b : Inv (b1 :: r) ->
  vp ((b1 :: r) ++ [b]) = true <->
  lo_next (length (b1 :: r)) b1 <= bN b <= hi_next (length (b1 :: r)) b1.
Proof.
  intros HI. destruct (pending_lead _ _ HI) as [_ Hlt].
  destruct HI as [H|[Hvp _]]; [discriminate|].
  unfold lo_next, hi_next.
  destruct r as [|b2 r]; cbn [app length Nat.eqb] in *.
  - rewrite vp_cons2. cbn [length]. split; [tauto|].
    intros H. split; [lia|split; [exact H|constructor]].
  - rewrite vp_cons2, Forall_app, length_app. apply vp_cons2 in Hvp.
    destruct Hvp as [_ [H2 H3]]. cbn [length]. split.
    + intros [_ [_ [_ H]]]. inversion H as [|? ? Hb]; exact Hb.
    + intros H. split; [lia|]. split; [exact H2|]. split; [exact H3|]. constructor; [exact H|constructor].
Qed.

Lemma pending_vs b1 r b : Inv (b1 :: r) -> vp ((b1 :: r) ++ [b]) = true ->
  vs ((b1 :: r) ++ [b]) = true <-> (length (b1 :: r) + 1 = seq_len (bN b1))%nat.
Proof.
  intros _ Hvp. rewrite vs_vp_len. cbn [app length]. rewrite length_app. cbn [length].
  split; [intros [_ H]; lia | intros H; split; [exact Hvp|lia]].
Qed.

Lemma seq_cp_bound s : vs s = true -> U32_to_N (seq_cp s) < 0x110000.
Proof.
  intros H. rewrite seq_cp_value by exact H.
  destruct (seq_value_scalar s H) as [H1 _]. lia.
Qed.

Lemma ref_decode_buffer_snoc st0 pre b :
  ref_decode_buffer st0 (pre ++ [b]) =
  let '(st, t) := ref_decode_buffer st0 pre in
  (fst (step st b), t ++ snd (step st b)).
Proof.
  unfold ref_decode_buffer. rewrite fold_left_app. cbn [fold_left].
  destruct (fold_left step_acc pre (st0, [])) as [st t]. cbn [step_acc].
  destruct (step st b); reflexivity.
Qed.

(** * Output size in UTF-16 code units *)

Definition cp_units (cp : U32) : nat := if U32_to_N cp <? 0x10000 then 1 else 2.

Fixpoint text_units (t : Text) : nat :=
  match t with [] => 0%nat | cp :: t' => (cp_units cp + text_units t')%nat end.

Definition pending_units (st : State) : nat := match st with [] => 0 | _ => 1 end.

Lemma text_units_app t1 t2 : text_units (t1 ++ t2) = (text_units t1 + text_units t2)%nat.
Proof. induction t1 as [|u t1 IH]; cbn; [reflexivity|]. rewrite IH. lia. Qed.

Lemma cp_units_le2 cp : (cp_units cp <= 2)%nat.
Proof. unfold cp_units. destruct (_ <? _); lia. Qed.

Lemma FFFD_units1 : cp_units FFFD = 1%nat.
Proof. unfold cp_units. rewrite FFFD_value. reflexivity. Qed.

Lemma step_empty_units_bound b :
  (text_units (snd (step [] b)) + pending_units (fst (step [] b)) <= 1)%nat.
Proof.
  destruct (N.le_gt_cases (bN b) 0x7F) as [H1|H1].
  - rewrite (step_empty_ascii b H1). cbn [fst snd text_units pending_units].
    assert (V : vs [b] = true) by (apply vs_one_iff; exact H1).
    unfold cp_units. rewrite (seq_cp_value1 b V).
    replace (bN b <? 0x10000) with true by (symmetry; apply N.ltb_lt; lia). lia.
  - destruct (N.le_gt_cases 0xC2 (bN b)) as [H2|H2];
      [destruct (N.le_gt_cases (bN b) 0xF4) as [H3|H3]|].
    + rewrite (step_empty_lead b ltac:(lia)). cbn. lia.
    + rewrite (step_empty_bad b ltac:(lia)). cbn [fst snd text_units pending_units].
      rewrite FFFD_units1. lia.
    + rewrite (step_empty_bad b ltac:(lia)). cbn [fst snd text_units pending_units].
      rewrite FFFD_units1. lia.
Qed.

Lemma step_units_bound st b :
  (text_units (snd (step st b)) + pending_units (fst (step st b)) <= 1 + pending_units st)%nat.
Proof.
  destruct st as [|b1 r].
  - pose proof (step_empty_units_bound b). cbn [pending_units]. lia.
  - rewrite (step_pending (b1 :: r) b ltac:(discriminate)).
    destruct (vp ((b1 :: r) ++ [b])); [destruct (vs ((b1 :: r) ++ [b]))|].
    + cbn [fst snd text_units pending_units].
      pose proof (cp_units_le2 (seq_cp ((b1 :: r) ++ [b]))). lia.
    + cbn. lia.
    + pose proof (step_empty_units_bound b) as H. change (step [] b) with (step_empty b) in H.
      destruct (step_empty b) as [st' o]. cbn [fst snd] in H |- *.
      cbn [text_units pending_units].
      rewrite FFFD_units1. lia.
Qed.

(* Over a whole buffer, with a general accumulator (for the induction). *)
Lemma fold_units_bound bs st t :
  let '(st', t') := fold_left step_acc bs (st, t) in
  (text_units t' + pending_units st' <= text_units t + length bs + pending_units st)%nat.
Proof.
  revert st t. induction bs as [|b bs IH]; intros st t.
  - cbn. lia.
  - cbn [fold_left].
    assert (A : step_acc (st, t) b = (fst (step st b), t ++ snd (step st b)))
      by (unfold step_acc; destruct (step st b); reflexivity).
    rewrite A. pose proof (step_units_bound st b) as Hs.
    specialize (IH (fst (step st b)) (t ++ snd (step st b))).
    destruct (fold_left step_acc bs _) as [st' t'].
    rewrite text_units_app in IH. cbn [length]. lia.
Qed.

Theorem decode_units_bound st bs :
  let '(st', t) := ref_decode_buffer st bs in
  (text_units t + pending_units st' <= length bs + pending_units st)%nat.
Proof. exact (fold_units_bound bs st []). Qed.

Lemma ref_done_units_bound st : (text_units (ref_done st) <= 1)%nat.
Proof. destruct st; cbn [ref_done text_units]; [lia|]. rewrite FFFD_units1. lia. Qed.
