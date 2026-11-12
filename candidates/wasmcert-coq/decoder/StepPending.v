(** * StepPending.v: step_spec, part 2: non-empty pending state, the cases
    "the byte does not continue the sequence" (U+FFFD, then the byte is
    reprocessed from the empty state) and "the byte extends it".

    Decoder-specific.

    Exports:
    - Packed state: [enc_cases], [enc_count] (state >> 24 = number of
      pending bytes), [enc_first] (state & 255 = first byte).
    - Code pieces: [pframe], [extend_code], [complete_code], [ok_code],
      [reject_code], [pending_code_eq] (pending_code split into them),
      [ok_locals], [wrapQ].
    - Wasm paths: [step_code_pending] (load, count, branch to the pending
      code), [range_code_ok] (the lo/hi range of the next byte, via
      Utf8StepFacts.lo_next / hi_next), [pending_split], [len_code_ok],
      [extend_arith] (packing one more byte into the state).
    - [step_case_reject], [step_case_extend]: the whole two cases.
    The range facts (pending_lead / pending_vp / pending_vs) and step
    equations (step_reject / step_extend) are in the pure layer,
    ../../pure-rocq/Utf8StepFacts.v. *)

From Stdlib Require Import ZArith NArith List Lia.
From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool eqtype seq.
From Wasm Require Import datatypes operations opsem properties.
From Utf8 Require Import Utf8Laws Utf8Ref Utf8Proofs Utf8StepFacts.
From SymExec Require Import I32 Steps Control Wp Mem WpMem.
From Decoder Require Import Module Instance Boundary Repr Exports OutBound Decode StepEmpty.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section StepPending.

Context `{ho: host}.
Variable hs : host_state.

(** ** i32 operations on small values *)

(** i32.and of two comparison results is their conjunction. *)

(** ** The packed state *)

Lemma enc_cases st : Inv st ->
  st = [::] \/ (exists b1, st = [:: b1]) \/ (exists b1 b2, st = [:: b1; b2]) \/
  (exists b1 b2 b3, st = [:: b1; b2; b3]).
Proof.
  move => HI. have := Inv_len _ HI.
  case: st HI => [|b1 [|b2 [|b3 [|b4 r]]]] _ /= H; try lia.
  - by left.
  - by right; left; exists b1.
  - by right; right; left; exists b1, b2.
  - by right; right; right; exists b1, b2, b3.
Qed.

Lemma enc_count st : Inv st -> (enc st / 2 ^ 24 = Z.of_nat (length st))%Z.
Proof.
  move => HI.
  case: (enc_cases HI) => [->|[[b1 ->]|[[b1 [b2 ->]]|[b1 [b2 [b3 ->]]]]]] //=;
    try have := bZ_range b1; try have := bZ_range b2; try have := bZ_range b3;
    move => *; Z.div_mod_to_equations; lia.
Qed.

Lemma enc_first b1 r : Inv (b1 :: r) -> (enc (b1 :: r) mod 2 ^ 8 = bZ b1)%Z.
Proof.
  move => HI. have := Inv_len _ HI. have := bZ_range b1.
  case: r HI => [|b2 [|b3 [|b4 r]]] _ /=; try have := bZ_range b2; try have := bZ_range b3;
    move => *; try lia; Z.div_mod_to_equations; lia.
Qed.

(** The locals of [decode] while [pending_code] runs. *)
Definition pframe (l : list value) : frame := Build_frame l inst0.

Lemma step_code_pending st b s1 m1 wb L i o j0 j1 j2 j3 j4 j5 j6 Q :
  Inv st -> st <> [::] -> nth_error s1.(s_mems) 0 = Some m1 ->
  mem_lookup (N.of_nat i) m1.(meminst_data) = Some wb -> byte_as_mem b wb ->
  (Z.of_nat i < Wasm_int.Int32.modulus)%Z ->
  wp hs s1 (pframe [:: vZ (enc st); vZ L; vZ (Z.of_nat i); vZ o; vZ (bZ b); vZ (Z.of_nat (length st)); j2; j3; j4; j5; j6])
     [::] pending_code (fun s2 f2 stk2 => stk2 = [::] /\ wp hs s2 f2 [::] [::] Q) ->
  wp hs s1 (frame_of st L i o [:: j0; j1; j2; j3; j4; j5; j6]) [::] step_code Q.
Proof.
  move => HI Hne Hm Hl Hb Him H.
  rewrite /step_code /frame_of /lg /ls /i32c /i_shr /bin /if_ /BTn.
  wp_step.
  apply: (wp_load8 (m1 := m1) (wb := wb)) => //.
  rewrite Hb -/(bZ b).
  wp_step. wp_step. wp_step. wp_step.
  rewrite (@shru_val (enc st) 24 (small_enc st) ltac:(lia)).
  rewrite (enc_count HI).
  repeat wp_step.
  apply: wp_if => Hc.
  - exfalso. apply: Hne. move: Hc.
    have Hl3 := Inv_len _ HI.
    rewrite /app_testop_i /= /Wasm_int.Int32.eq unsigned_small; first by rewrite modulus_val; lia.
    case: Coqlib.zeq => //. by case: st {H HI Hl3}.
  - exact: H.
Qed.

(** [range_code]: lo, hi (locals 8, 9) := the allowed range of the next byte. *)
Lemma range_code_ok s1 (n : nat) b1 l0 l1 l2 l3 l4 l7 l8 l9 l10 :
  (1 <= n)%coq_nat -> (n <= 3)%coq_nat ->
  wp hs s1 (pframe [:: l0; l1; l2; l3; l4; vZ (Z.of_nat n); vZ (bZ b1); l7; l8; l9; l10]) [::] range_code
    (fun s2 f2 stk2 => s2 = s1 /\ stk2 = [::] /\
       f2 = pframe [:: l0; l1; l2; l3; l4; vZ (Z.of_nat n); vZ (bZ b1); l7;
                      vZ (Z.of_N (lo_next n b1)); vZ (Z.of_N (hi_next n b1)); l10]).
Proof.
  move => Hn Hn3. have Hb1 := bN_bZ b1. have HbN := bN_lt b1.
  rewrite /range_code /pframe /lg /ls /i32c /i_eq /rel /if_ /BTn.
  repeat wp_step. rewrite eq_val; try small_tac.
  wp_if_bool.
  - have Hn1 : n = 1%coq_nat by lia.
    subst n. rewrite /lo_next /hi_next /=.
    repeat wp_step. rewrite eq_val; try small_tac.
    wp_if_bool; repeat wp_step; split => //; repeat wp_step;
    rewrite eq_val; try small_tac;
    wp_if_bool; repeat wp_step; split => //; repeat wp_step;
    rewrite eq_val; try small_tac;
    wp_if_bool; repeat wp_step; split => //; repeat wp_step;
    rewrite eq_val; try small_tac;
    wp_if_bool; repeat wp_step; split => //; repeat wp_step;
    split => //; repeat wp_step; (split; first by []); (split; first by []);
    rewrite /lo2 /hi2;
    repeat (case: N.eqb_spec => ?); try (exfalso; lia); reflexivity.
  - have Hn1 : Nat.eqb n 1 = false by apply/Nat.eqb_neq; lia.
    rewrite /lo_next /hi_next Hn1.
    repeat wp_step. split => //. repeat wp_step. split => //.
Qed.

(** ** pending_code: the range test, then complete/extend ([ok_code]) or reject *)

Definition extend_code :=
  [:: lg 0; lg 4; lg 5; i32c 3; i_shl; i_shl; i_or; i32c 0x1000000; i_add; ls 0].
Definition complete_code := cp_code ++ emit_cp ++ [:: i32c 0; ls 0].
Definition ok_code :=
  len_code ++ [:: lg 5; i32c 1; i_add; lg 10; i_eq; if_ complete_code extend_code].
Definition reject_code := emit_fffd ++ [:: i32c 0; ls 0] ++ empty_code.

Lemma pending_code_eq : pending_code =
  [:: lg 0; i32c 0xFF; i_and; ls 6] ++ range_code ++
  [:: lg 4; lg 8; i_geu; lg 4; lg 9; i_leu; i_and; if_ ok_code reject_code].
Proof. by []. Qed.

(** The locals after the range test: b1 in 6, lo/hi in 8/9. *)
Definition ok_locals (st : State) b1 b l1 l2 l3 j3 j6 :=
  [:: vZ (enc st); l1; l2; l3; vZ (bZ b); vZ (Z.of_nat (length st)); vZ (bZ b1); j3;
      vZ (Z.of_N (lo_next (length st) b1)); vZ (Z.of_N (hi_next (length st) b1)); j6].

Definition wrapQ Q := fun s2 f2 (stk2 : seq value) => stk2 = [::] /\ wp hs s2 f2 [::] [::] Q.

Lemma pending_split s1 b1 r b l1 l2 l3 j2 j3 j4 j5 j6 Q :
  Inv (b1 :: r) ->
  (vp (app (b1 :: r) [:: b]) = true ->
     wp hs s1 (pframe (ok_locals (b1 :: r) b1 b l1 l2 l3 j3 j6)) [::] ok_code (wrapQ Q)) ->
  (vp (app (b1 :: r) [:: b]) = false ->
     wp hs s1 (pframe (ok_locals (b1 :: r) b1 b l1 l2 l3 j3 j6)) [::] reject_code (wrapQ Q)) ->
  wp hs s1 (pframe [:: vZ (enc (b1 :: r)); l1; l2; l3; vZ (bZ b); vZ (Z.of_nat (length (b1 :: r))); j2; j3; j4; j5; j6])
     [::] pending_code Q.
Proof.
  move => HI Hok Hrej.
  set st := b1 :: r. set n := length st.
  have Hn1 : (1 <= n)%coq_nat by rewrite /n /st /=; lia.
  have Hn3 : (n <= 3)%coq_nat by exact: Inv_len.
  have E : Wasm_int.int_and i32m (Wasm_int.Int32.repr (enc st)) (Wasm_int.Int32.repr 255) =
           Wasm_int.Int32.repr (bZ b1).
  { rewrite -(enc_first HI). exact: (@and_val (enc st) 8 (small_enc st) ltac:(lia)). }
  rewrite pending_code_eq /pframe /lg /ls /i32c /i_and /bin.
  apply: wp_app.
  wp_step. wp_step. wp_step. rewrite E. wp_step. wp_step.
  apply: wp_app. apply: wp_mono; last by apply: (range_code_ok s1 (n := n) b1).
  move => s2 f2 stk2 [-> [-> ->]].
  have Hlo : (lo_next n b1 < 256)%num.
  { rewrite /lo_next /lo2. case: Nat.eqb => //. repeat case: N.eqb => //. }
  have Hhi : (hi_next n b1 < 256)%num.
  { rewrite /hi_next /hi2. case: Nat.eqb => //. repeat case: N.eqb => //. }
  rewrite /pframe /i_geu /i_leu /rel /if_ /BTn.
  repeat wp_step.
  have Hb := bZ_range b. have Hm := modulus_val.
  rewrite geu_val; try lia.
  rewrite leu_val; try lia.
  rewrite and_bool.
  have Hv := pending_vp _ _ b HI.
  apply: wp_if => Hc.
  - apply: Hok. apply/Hv. move: (wasm_bool_nz Hc) => /andP [/Z.leb_le H1 /Z.leb_le H2].
    rewrite bN_bZ /n /st in H1 H2. lia.
  - apply: Hrej. have Hf := wasm_bool_z Hc.
    case E2: (vp (app st [:: b])) => //. move: E2 => /Hv [H1 H2].
    rewrite /n /st bN_bZ in Hf.
    have Ht : ((Z.of_N (lo_next (length (b1 :: r)) b1) <=? Z.of_N (bN b)) &&
               (Z.of_N (bN b) <=? Z.of_N (hi_next (length (b1 :: r)) b1)))%Z = true
      by apply/andP; split; apply/Z.leb_le; lia.
    by rewrite Hf in Ht.
Qed.

(** ** Case: the byte does not continue the pending prefix (U+FFFD, then
    the byte is reprocessed from the empty state) *)

Lemma step_case_reject b1 r b : Inv (b1 :: r) -> vp (app (b1 :: r) [:: b]) = false -> step_case hs (b1 :: r) b.
Proof.
  move => HI Hvp s1 m1 wb L i o junk Hm _ Hj Hl Hb Ho Hlen Hom Him.
  have {}Hlen : (Z.to_N o + 4 <= operations.mem_length m1)%num by move: Hlen; cbn [pend]; lia.
  case: junk Hj => [|j0 [|j1 [|j2 [|j3 [|j4 [|j5 [|j6 [|j7 junk]]]]]]]] // _.
  have Hmod := modulus_val.
  have Es := step_reject (b1 :: r) b ltac:(discriminate) Hvp.
  apply: (step_code_pending (m1 := m1) (wb := wb) (b := b)) => //.
  apply: pending_split => //; first by rewrite Hvp.
  move => _. rewrite /reject_code /pframe.
  apply: wp_app. apply: (@emit_fffd_ok _ _ _ hs _ m1) => //; try lia.
  move => m2 Hw1.
  apply: wp_app.
  rewrite /i32c /ls. wp_step. wp_step. apply: wp_nil.
  have Hm2 : nth_error (s_mems (upd_mem0 s1 m2)) 0 = Some m2 by apply: upd_mem0_nth Hm.
  have Hlen2 : (operations.mem_length m1 = operations.mem_length m2)%num by case: Hw1 => _ [-> _].
  apply: (@empty_code_ok _ _ _ hs _ m2) => //; try lia.
  move => m3 Hw2. split => //. apply: wp_nil. split => //. apply: wp_nil.
  rewrite Es. split => //.
  exists m3, [:: vZ (bZ b); vZ (Z.of_nat (length (b1 :: r))); vZ (bZ b1); j3;
              vZ (Z.of_N (lo_next (length (b1 :: r)) b1)); vZ (Z.of_N (hi_next (length (b1 :: r)) b1)); j6].
  have Hu : utf16le (FFFD :: snd (step [::] b)) = utf16le [:: FFFD] ++ utf16le (snd (step [::] b)).
  { by rewrite -utf16le_cat. }
  have Hl2 : (length (utf16le (snd (step [::] b))) <= 2)%coq_nat.
  { case: (step_empty_cases b) => [[-> ->]|[[-> ->]|[-> ->]]]; cbn; lia. }
  rewrite /= in Hl2.
  rewrite Hu FFFD_units.
  split; first by rewrite upd_mem0_twice.
  split.
  { have Eo : (o + 2 + Z.of_nat (length (utf16le (snd (step [::] b)))) =
               o + Z.of_nat (length ([:: 0xFD; 0xFF]%num ++ utf16le (snd (step [::] b)))))%Z
      by cbn [cat length]; lia.
    rewrite /frame_of -Eo. reflexivity. }
  split; first by [].
  split; last by cbn; lia.
  apply: wr_writes; first by cbn; lia.
  rewrite FFFD_units in Hw1.
  apply: (wr_app Hw1).
  have -> : (Z.to_N o + N.of_nat (length [:: 0xFD; 0xFF]%num))%num = Z.to_N (o + 2) by cbn; lia.
  exact Hw2.
Qed.

(** ** len_code: L (local 10) := seq_len b1, for a lead byte b1 *)

Lemma len_code_ok s1 b1 l0 l1 l2 l3 l4 l5 l7 l8 l9 l10 :
  (0xC2 <= bN b1 <= 0xF4)%num ->
  wp hs s1 (pframe [:: l0; l1; l2; l3; l4; l5; vZ (bZ b1); l7; l8; l9; l10]) [::] len_code
    (fun s2 f2 stk2 => s2 = s1 /\ stk2 = [::] /\
       f2 = pframe [:: l0; l1; l2; l3; l4; l5; vZ (bZ b1); l7; l8; l9; vZ (Z.of_nat (seq_len (bN b1)))]).
Proof.
  move => Hl. have Hb1 := bN_bZ b1. have HbN := bN_lt b1. have Hm := modulus_val.
  rewrite /len_code /pframe /lg /ls /i32c /i_ltu /rel /if_ /BTn.
  repeat wp_step. rewrite ltu_val; try lia.
  wp_if_bool; repeat wp_step; split => //; repeat wp_step;
    rewrite ltu_val; try lia;
    wp_if_bool; repeat wp_step; split => //; repeat wp_step; (split; first by []); (split; first by []);
    case: (seq_len_cases (bN b1)) => [[A ->]|[[A ->]|[[A ->]|[[A ->]|[A ->]]]]]; try (exfalso; lia); reflexivity.
Qed.

(** ** Case: the byte extends the pending prefix (no output) *)

(** The packed state after appending byte b (st has 1 or 2 bytes). *)
Lemma extend_arith b1 r b : Inv (b1 :: r) -> (length (b1 :: r) <= 2)%coq_nat ->
  Wasm_int.int_add i32m
    (Wasm_int.int_or i32m (Wasm_int.Int32.repr (enc (b1 :: r)))
       (Wasm_int.int_shl i32m (Wasm_int.Int32.repr (bZ b))
          (Wasm_int.int_shl i32m (Wasm_int.Int32.repr (Z.of_nat (length (b1 :: r)))) (Wasm_int.Int32.repr 3))))
    (Wasm_int.Int32.repr 16777216)
  = Wasm_int.Int32.repr (enc (app (b1 :: r) [:: b])).
Proof.
  move => HI Hn. have Hm := modulus_val.
  have Hb := bZ_range b. have Hb1 := bZ_range b1.
  have P8 : (2 ^ 8 = 256)%Z by []. have P16 : (2 ^ 16 = 65536)%Z by [].
  have P24 : (2 ^ 24 = 16777216)%Z by [].
  have S1 : small (Z.of_nat (length (b1 :: r))) by apply small_const; lia.
  rewrite (@shl_val (Z.of_nat (length (b1 :: r))) 3 S1 ltac:(lia)).
  have K : (0 <= Z.of_nat (length (b1 :: r)) * 2 ^ 3 < 32)%Z by cbn [length] in Hn |- *; lia.
  rewrite (@shl_val (bZ b) (Z.of_nat (length (b1 :: r)) * 2 ^ 3) (small_byte b) K).
  change (Wasm_int.Int32.iadd
    (Wasm_int.Int32.or (Wasm_int.Int32.repr (enc (b1 :: r)))
       (Wasm_int.Int32.repr (bZ b * 2 ^ (Z.of_nat (length (b1 :: r)) * 2 ^ 3))))
    (Wasm_int.Int32.repr 16777216) = Wasm_int.Int32.repr (enc (app (b1 :: r) [:: b]))).
  clear S1 K. case: r HI Hn => [|b2 [|b3 r]] HI Hn; cbn [length] in Hn; try lia.
  - have E : enc [:: b1] = (bZ b1 + 1 * 2 ^ 24)%Z by [].
    have -> : (Z.of_nat (length [:: b1]) * 2 ^ 3 = 8)%Z by [].
    rewrite E i32_or_repr; rewrite ?P8 ?P24; try lia.
    rewrite (lor_pack (x := bZ b1) (k := 8)); rewrite ?P8 ?P24; try lia.
    rewrite i32_iadd_repr. f_equal. cbn [app enc]. rewrite ?P8 ?P24. lia.
  - have Hb2 := bZ_range b2.
    have E : enc [:: b1; b2] = (bZ b1 + bZ b2 * 256 + 2 * 2 ^ 24)%Z by [].
    have -> : (Z.of_nat (length [:: b1; b2]) * 2 ^ 3 = 16)%Z by [].
    rewrite E i32_or_repr; rewrite ?P16 ?P24; try lia.
    rewrite (lor_pack (x := bZ b1 + bZ b2 * 256) (k := 16)); rewrite ?P16 ?P24; try lia.
    rewrite i32_iadd_repr. f_equal. cbn [app enc]. rewrite ?P16 ?P24. lia.
Qed.

Lemma step_case_extend b1 r b : Inv (b1 :: r) ->
  vp (app (b1 :: r) [:: b]) = true -> vs (app (b1 :: r) [:: b]) = false -> step_case hs (b1 :: r) b.
Proof.
  move => HI Hvp Hvs s1 m1 wb L i o junk Hm _ Hj Hl Hb Ho Hlen Hom Him.
  have {}Hlen : (Z.to_N o + 4 <= operations.mem_length m1)%num by move: Hlen; cbn [pend]; lia.
  case: junk Hj => [|j0 [|j1 [|j2 [|j3 [|j4 [|j5 [|j6 [|j7 junk]]]]]]]] // _.
  have Hmod := modulus_val.
  have Es := step_extend (b1 :: r) b ltac:(discriminate) Hvp Hvs.
  have [Hlead Hlt] := pending_lead _ _ HI.
  have Hne : (length (b1 :: r) + 1 <> seq_len (bN b1))%coq_nat.
  { move => E. have : vs (app (b1 :: r) [:: b]) = true by apply/pending_vs. by rewrite Hvs. }
  have H4 := seq_len_le4 (bN b1).
  have Hn2 : (length (b1 :: r) <= 2)%coq_nat by lia.
  apply: (step_code_pending (m1 := m1) (wb := wb) (b := b)) => //.
  apply: pending_split => //; last by rewrite Hvp.
  move => _. rewrite /ok_code /ok_locals.
  apply: wp_app. apply: wp_mono; last by apply: len_code_ok.
  move => s2 f2 stk2 [-> [-> ->]].
  rewrite /pframe /lg /i32c /i_add /i_eq /bin /rel /if_ /BTn.
  repeat wp_step.
  rewrite iadd_val eq_val; try (apply small_const; lia).
  wp_if_bool; first by exfalso; lia.
  rewrite /extend_code /lg /ls /i32c /i_shl /i_or /i_add /bin.
  repeat wp_step.
  rewrite (extend_arith b HI Hn2).
  repeat wp_step. split => //. apply: wp_nil. split => //. apply: wp_nil. split => //. apply: wp_nil.
  rewrite Es. split => //.
  exists m1, [:: vZ (bZ b); vZ (Z.of_nat (length (b1 :: r))); vZ (bZ b1); j3;
              vZ (Z.of_N (lo_next (length (b1 :: r)) b1)); vZ (Z.of_N (hi_next (length (b1 :: r)) b1));
              vZ (Z.of_nat (seq_len (bN b1)))].
  split; first by rewrite (upd_mem0_same Hm).
  split; first by rewrite /frame_of /= Z.add_0_r.
  split; first by [].
  split; last by cbn; lia.
  apply: wr_writes; first by cbn; lia.
  exact: wr_nil.
Qed.

End StepPending.
