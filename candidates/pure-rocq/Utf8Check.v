(* Utf8Check.v: the exhaustive computations (vm_compute) that connect the
   bit-level spec (U32 / encoding) with the N-range table of Utf8Ref.v.

   checkA: every Unicode scalar n (n <= 0x10FFFF, not a surrogate):
           encoding (U32_of_N n) = Some (enc_N n), vs (enc_N n),
           seq_value (enc_N n) = n, is_unicode_scalar (U32_of_N n),
           U32_to_N (U32_of_N n) = n.
   checkB: every valid sequence prefix s (vp s):
           if vs s: seq_value s is a scalar and enc_N (seq_value s) = s;
           otherwise s ++ completion s is a valid sequence whose value is
           not 0xFFFD. *)

From Stdlib Require Import List NArith Arith Bool Lia.
From Stdlib Require Strings.Byte.
Import Corelib.Init.Byte ListNotations.
From Utf8 Require Import Utf8Laws Utf8Ref.

Local Open Scope N_scope.

Definition byte_of (n : N) : byte :=
  match Byte.of_N n with Some b => b | None => x00 end.

Lemma byte_of_bN b : byte_of (bN b) = b.
Proof. unfold byte_of, bN. now rewrite Byte.of_to_N. Qed.

Definition enc_N (n : N) : list byte :=
  if n <? 0x80 then [byte_of n]
  else if n <? 0x800 then [byte_of (0xC0 + n / 64); byte_of (0x80 + n mod 64)]
  else if n <? 0x10000 then
    [byte_of (0xE0 + n / 4096); byte_of (0x80 + (n / 64) mod 64); byte_of (0x80 + n mod 64)]
  else
    [byte_of (0xF0 + n / 262144); byte_of (0x80 + (n / 4096) mod 64);
     byte_of (0x80 + (n / 64) mod 64); byte_of (0x80 + n mod 64)].

Fixpoint bytes_eqb (l1 l2 : list byte) : bool :=
  match l1, l2 with
  | [], [] => true
  | a :: r1, b :: r2 => Byte.eqb a b && bytes_eqb r1 r2
  | _, _ => false
  end.

Lemma bytes_eqb_eq l1 l2 : bytes_eqb l1 l2 = true -> l1 = l2.
Proof.
  revert l2; induction l1 as [|a r IH]; destruct l2 as [|b r2]; simpl; try discriminate; auto.
  intros H; apply andb_true_iff in H as [H1 H2].
  apply Byte.byte_dec_bl in H1; subst; f_equal; auto.
Qed.

Definition opt_eqb (o : option (list byte)) (l : list byte) : bool :=
  match o with Some l' => bytes_eqb l' l | None => false end.

Lemma opt_eqb_eq o l : opt_eqb o l = true -> o = Some l.
Proof. destruct o; simpl; try discriminate. intros H; now rewrite (bytes_eqb_eq _ _ H). Qed.

Definition is_surr_N (n : N) : bool := (0xD800 <=? n) && (n <=? 0xDFFF).
Definition scalarN (n : N) : bool := (n <=? 0x10FFFF) && negb (is_surr_N n).

Definition fA (n : N) : bool :=
  if is_surr_N n then true else
  let cp := U32_of_N n in
  let e := enc_N n in
  is_unicode_scalar cp && opt_eqb (encoding cp) e && vs e
  && (seq_value e =? n) && (U32_to_N cp =? n).

(* ---- iteration over N ranges ---- *)

Fixpoint all_from (f : N -> bool) (k : nat) (n : N) : bool :=
  match k with O => true | S k' => if f n then all_from f k' (N.succ n) else false end.

Lemma all_from_ok f k n :
  all_from f k n = true -> forall m, n <= m -> m < n + N.of_nat k -> f m = true.
Proof.
  revert n; induction k as [|k IH]; simpl; intros n H m H1 H2; [lia|].
  destruct (f n) eqn:E; [|discriminate].
  destruct (N.eq_dec m n) as [->|Hne]; auto.
  apply (IH (N.succ n)); auto; lia.
Qed.

Definition all2 (f : N -> bool) (hi : nat) : bool :=
  all_from (fun h => all_from (fun l => f (h * 1024 + l)) 1024 0) hi 0.

Lemma all2_ok f hi : all2 f hi = true -> forall m, m < N.of_nat hi * 1024 -> f m = true.
Proof.
  unfold all2; intros H m Hm.
  assert (Hd := N.div_mod m 1024 ltac:(lia)).
  assert (Hl := N.mod_lt m 1024 ltac:(lia)).
  assert (Hh : m / 1024 < N.of_nat hi) by (apply N.Div0.div_lt_upper_bound; lia).
  assert (E : N.of_nat 1024 = 1024) by reflexivity.
  assert (A1 : 0 <= m / 1024) by apply N.le_0_l. assert (A2 : m / 1024 < 0 + N.of_nat hi) by (rewrite N.add_0_l; exact Hh).
  pose proof (all_from_ok _ _ _ H (m / 1024) A1 A2) as H2; cbv beta in H2.
  assert (A3 : 0 <= m mod 1024) by apply N.le_0_l. assert (A4 : m mod 1024 < 0 + N.of_nat 1024) by (rewrite E, N.add_0_l; exact Hl).
  pose proof (all_from_ok _ _ _ H2 (m mod 1024) A3 A4) as H3.
  cbv beta in H3. rewrite N.mul_comm in Hd. rewrite Hd. exact H3.
Qed.

Lemma checkA_comp : all2 fA 1088 = true.
Proof. vm_compute. reflexivity. Qed.

Lemma checkA n : n <= 0x10FFFF -> is_surr_N n = false ->
  let cp := U32_of_N n in
  is_unicode_scalar cp = true /\ encoding cp = Some (enc_N n) /\ vs (enc_N n) = true /\
  seq_value (enc_N n) = n /\ U32_to_N cp = n.
Proof.
  intros Hn Hs.
  assert (E : N.of_nat 1088 = 1088) by reflexivity.
  pose proof (all2_ok _ _ checkA_comp n ltac:(rewrite E; lia)) as H.
  unfold fA in H; rewrite Hs in H.
  apply andb_true_iff in H as [H H4]. apply andb_true_iff in H as [H H3].
  apply andb_true_iff in H as [H H2]. apply andb_true_iff in H as [H H1].
  repeat split; auto using opt_eqb_eq; apply N.eqb_eq; auto.
Qed.

(* ---- all bytes, and enumeration of valid prefixes ---- *)

Definition all_bytes_def : list byte := map (fun k => byte_of (N.of_nat k)) (seq 0 256).
(* Precomputed, so that the enumeration does not rebuild it. *)
Definition all_bytes : list byte := Eval vm_compute in all_bytes_def.
Lemma all_bytes_eq : all_bytes = all_bytes_def.
Proof. vm_compute; reflexivity. Qed.

Lemma in_all_bytes b : In b all_bytes.
Proof.
  rewrite all_bytes_eq; unfold all_bytes_def; apply in_map_iff; exists (N.to_nat (bN b)); split.
  - rewrite N2Nat.id; apply byte_of_bN.
  - apply in_seq; pose proof (Byte.to_N_bounded b); unfold bN; lia.
Qed.

Lemma vp_app s t : vp (s ++ t) = true -> s <> [] -> vp s = true.
Proof.
  destruct s as [|b1 r]; [congruence|]; intros H _.
  change ((b1 :: r) ++ t) with (b1 :: (r ++ t)) in H.
  unfold vp in *.
  apply andb_true_iff in H as [H H3]. apply andb_true_iff in H as [H1 H2].
  apply andb_true_iff; split; [apply andb_true_iff; split; auto|].
  - apply Nat.leb_le in H2; apply Nat.leb_le. simpl in *. rewrite length_app in H2. lia.
  - destruct r as [|b2 r]; auto. simpl in H3. apply andb_true_iff in H3 as [H3 H4].
    rewrite forallb_app in H4. apply andb_true_iff in H4 as [H4 _]. rewrite H3, H4; reflexivity.
Qed.

Lemma seq_len_le4 n : (seq_len n <= 4)%nat.
Proof.
  unfold seq_len; repeat match goal with |- context [if ?c then _ else _] => destruct c end; lia.
Qed.

Lemma vp_len s : vp s = true -> (length s <= 4)%nat.
Proof.
  destruct s as [|b1 r]; [discriminate|]. unfold vp.
  intros H; apply andb_true_iff in H as [H _]; apply andb_true_iff in H as [_ H].
  apply Nat.leb_le in H. pose proof (seq_len_le4 (bN b1)). lia.
Qed.

(* NB: implb / orb are functions, hence strict in the VM; use `if` so the
   enumeration is pruned (an implb version evaluates all 256^4 lists). *)
Definition check_all (P : list byte -> bool) : bool :=
  forallb (fun b1 => if vp [b1] then P [b1] && (if Nat.leb (seq_len (bN b1)) 1 then true else
   forallb (fun b2 => if vp [b1; b2] then P [b1; b2] && (if Nat.leb (seq_len (bN b1)) 2 then true else
    forallb (fun b3 => if vp [b1; b2; b3] then P [b1; b2; b3] && (if Nat.leb (seq_len (bN b1)) 3 then true else
     forallb (fun b4 => if vp [b1; b2; b3; b4] then P [b1; b2; b3; b4] else true)
      all_bytes) else true) all_bytes) else true) all_bytes) else true) all_bytes.

Lemma vp1 b1 r : vp (b1 :: r) = true -> vp [b1] = true.
Proof. intros H; apply (vp_app [b1] r H); discriminate. Qed.
Lemma vp2 b1 b2 r : vp (b1 :: b2 :: r) = true -> vp [b1; b2] = true.
Proof. intros H; apply (vp_app [b1; b2] r H); discriminate. Qed.
Lemma vp3 b1 b2 b3 r : vp (b1 :: b2 :: b3 :: r) = true -> vp [b1; b2; b3] = true.
Proof. intros H; apply (vp_app [b1; b2; b3] r H); discriminate. Qed.

Lemma vp_len_lead b1 r : vp (b1 :: r) = true -> (length (b1 :: r) <= seq_len (bN b1))%nat.
Proof.
  unfold vp. intros H; apply andb_true_iff in H as [H _]; apply andb_true_iff in H as [_ H].
  apply Nat.leb_le in H; exact H.
Qed.

Lemma orb_left_false (a c : bool) : a = false -> (if a then true else c) = true -> c = true.
Proof. intros ->; auto. Qed.

Lemma check_all_ok P : check_all P = true -> forall s, vp s = true -> P s = true.
Proof.
  intros H s Hs. pose proof (vp_len s Hs) as Hl.
  unfold check_all in H.
  assert (F : forall (f : byte -> bool) b, forallb f all_bytes = true -> f b = true)
    by (intros f b Hf; rewrite forallb_forall in Hf; apply Hf, in_all_bytes).
  assert (I : forall a c : bool, (if a then c else true) = true -> a = true -> c = true)
    by (intros [] []; simpl; auto).
  destruct s as [|b1 [|b2 [|b3 [|b4 [|b5 r]]]]]; [discriminate| | | | |simpl in Hl; lia];
  pose proof (F _ b1 H) as H1; cbv beta in H1;
  pose proof (I _ _ H1 ltac:(eapply vp1; exact Hs)) as G1;
  apply andb_true_iff in G1 as [P1 G1]; try exact P1;
  (apply orb_left_false in G1; [|apply Nat.leb_gt; pose proof (vp_len_lead _ _ Hs) as L; cbn [length] in L; lia]);
  pose proof (F _ b2 G1) as H2; cbv beta in H2;
  pose proof (I _ _ H2 ltac:(eapply vp2; exact Hs)) as G2;
  apply andb_true_iff in G2 as [P2 G2]; try exact P2;
  (apply orb_left_false in G2; [|apply Nat.leb_gt; pose proof (vp_len_lead _ _ Hs) as L; cbn [length] in L; lia]);
  pose proof (F _ b3 G2) as H3; cbv beta in H3;
  pose proof (I _ _ H3 ltac:(eapply vp3; exact Hs)) as G3;
  apply andb_true_iff in G3 as [P3 G3]; try exact P3;
  (apply orb_left_false in G3; [|apply Nat.leb_gt; pose proof (vp_len_lead _ _ Hs) as L; cbn [length] in L; lia]);
  pose proof (F _ b4 G3) as H4; cbv beta in H4;
  exact (I _ _ H4 Hs).
Qed.

(* Bytes that complete a valid sequence prefix to a valid sequence. *)
Definition completion (s : list byte) : list byte :=
  match s with
  | [] => []
  | [b1] => match seq_len (bN b1) with
            | 2%nat => [x80]
            | 3%nat => [byte_of (lo2 (bN b1)); x80]
            | 4%nat => [byte_of (lo2 (bN b1)); x80; x80]
            | _ => []
            end
  | b1 :: _ => repeat x80 (seq_len (bN b1) - length s)
  end.

Definition fB (s : list byte) : bool :=
  implb (vs s) (scalarN (seq_value s) && bytes_eqb (enc_N (seq_value s)) s) &&
  implb (negb (vs s))
    (vs (s ++ completion s) && negb (seq_value (s ++ completion s) =? 0xFFFD)).

Lemma checkB_comp : check_all fB = true.
Proof. vm_compute. reflexivity. Qed.

Lemma checkB s : vp s = true -> fB s = true.
Proof. apply check_all_ok, checkB_comp. Qed.
