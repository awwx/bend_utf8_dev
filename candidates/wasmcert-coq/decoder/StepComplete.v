(** * StepComplete.v: step_spec, part 3: the byte completes the pending
    sequence, so a code point is computed from the bytes and written.

    Decoder-specific.

    Exports:
    - [utf16le_cp]: the output bytes of a code point below 0x110000
      (one unit below 0x10000, else a surrogate pair).
    - [emit_cp_ok]: emit_cp writes exactly those bytes.
    - [cp_code_ok2], [cp_code_ok3], [cp_code_ok4]: cp_code computes the
      code point of a two-, three-, four-byte sequence (local 7 :=
      seq_value), by shifts, masks and ors (../symexec/I32.v).
    - [step_case_complete]: the whole case, for any length, given that
      cp_code computes the sequence's value (hypothesis); and its
      instances [step_case_complete2], [step_case_complete3],
      [step_case_complete4] (with cp_code_ok2/3/4).
    The code-point value comes from the pure layer's sealed interface of
    seq_cp (seq_cp_value, seq_cp_bound; seq_cp is Opaque there, see the end
    of ../../pure-rocq/Utf8Proofs.v). *)

From Stdlib Require Import ZArith NArith List Lia.
From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool eqtype seq.
From Wasm Require Import datatypes operations opsem properties.
From Utf8 Require Import Utf8Laws Utf8Ref Utf8Proofs Utf8StepFacts.
From SymExec Require Import I32 Steps Control Wp Mem WpMem.
From Decoder Require Import Module Instance Boundary Repr Exports OutBound Decode StepEmpty StepPending.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section StepComplete.

Context `{ho: host}.
Variable hs : host_state.

(** UTF-16 code units of a scalar value c, as 16-bit values. *)
Lemma utf16le_cp u : (U32_to_N u < 0x110000)%num ->
  let c := U32_to_N u in
  utf16le [:: u] =
  if (c <? 0x10000)%num then [:: (c mod 256)%num; (c / 256)%num]
  else let h := (0xD800 + (c - 0x10000) / 0x400)%num in
       let l := (0xDC00 + (c - 0x10000) mod 0x400)%num in
       [:: (h mod 256)%num; (h / 256)%num; (l mod 256)%num; (l / 256)%num].
Proof.
  move => Hc c. rewrite /utf16le /utf16_units -/c. cbn [flat_map].
  by case: (c <? 0x10000)%num.
Qed.

Lemma emit_cp_ok s1 m1 (l0 l1 l2 l4 l5 l6 : value) (o : Z) u rest Q :
  nth_error s1.(s_mems) 0 = Some m1 ->
  (0 <= o)%Z -> (o + 4 < Wasm_int.Int32.modulus)%Z ->
  (Z.to_N o + 4 <= operations.mem_length m1)%num ->
  (U32_to_N u < 0x110000)%num ->
  (forall m2, wr m1 m2 (Z.to_N o) (utf16le [:: u]) ->
     Q (upd_mem0 s1 m2)
       (Build_frame (l0 :: l1 :: l2 :: vZ (o + Z.of_nat (length (utf16le [:: u]))) :: l4 :: l5 :: l6 ::
                     vZ (Z.of_N (U32_to_N u)) :: rest) inst0) [::]) ->
  wp hs s1 (Build_frame (l0 :: l1 :: l2 :: vZ o :: l4 :: l5 :: l6 :: vZ (Z.of_N (U32_to_N u)) :: rest) inst0)
     [::] emit_cp Q.
Proof.
  move => Hm Ho Hom Hl Hc HQ.
  have Hmod := modulus_val.
  rewrite (utf16le_cp Hc) in HQ.
  set c := U32_to_N u in HQ Hc *.
  unfold_code. rewrite /vZ. repeat wp_step.
  rewrite ltu_val; try lia.
  apply: wp_if => Hif.
  - have Hlt : (c < 0x10000)%num.
    { move: (wasm_bool_nz Hif) => /Z.ltb_lt. lia. }
    have Eb : (c <? 0x10000)%num = true by apply N.ltb_lt. rewrite Eb in HQ.
    repeat wp_step.
    apply: (wp_store16_o (m1 := m1)) => //; try lia.
    move => m2 Hw. repeat wp_step. split => //. apply wp_nil.
    rewrite /= i32_iadd_repr. apply HQ. by rewrite N.add_0_r in Hw.
  - have Hge : (0x10000 <= c)%num.
    { move: (wasm_bool_z Hif) => /Z.ltb_ge. lia. }
    have Eb : (c <? 0x10000)%num = false by apply N.ltb_ge. rewrite Eb in HQ.
    set h := (0xD800 + (c - 0x10000) / 0x400)%num in HQ.
    set l := (0xDC00 + (c - 0x10000) mod 0x400)%num in HQ.
    have Hsc : small (Z.of_N c) by rewrite /small; lia.
    have Eh : Wasm_int.int_add i32m (Wasm_int.int_shr_u i32m (Wasm_int.Int32.repr (Z.of_N c)) (Wasm_int.Int32.repr 10))
                (Wasm_int.Int32.repr 55232) = Wasm_int.Int32.repr (Z.of_N h).
    { rewrite (@shru_val (Z.of_N c) 10 Hsc ltac:(lia)).
      rewrite iadd_val. f_equal. rewrite /h. have -> : (2 ^ 10 = 1024)%Z by [].
      zify; Z.div_mod_to_equations; lia. }
    have El : Wasm_int.int_or i32m (Wasm_int.int_and i32m (Wasm_int.Int32.repr (Z.of_N c)) (Wasm_int.Int32.repr 1023))
                (Wasm_int.Int32.repr 56320) = Wasm_int.Int32.repr (Z.of_N l).
    { have E1 := @and_val (Z.of_N c) 10 Hsc ltac:(lia).
      have E1023 : (2 ^ 10 - 1 = 1023)%Z by []. rewrite E1023 in E1. rewrite E1.
      have Hmb : (0 <= Z.of_N c mod 2 ^ 10 < 2 ^ 10)%Z by apply Z.mod_pos_bound.
      change (Wasm_int.Int32.or (Wasm_int.Int32.repr (Z.of_N c mod 2 ^ 10)) (Wasm_int.Int32.repr 56320) =
              Wasm_int.Int32.repr (Z.of_N l)).
      have P10 : (2 ^ 10 = 1024)%Z by [].
      rewrite i32_or_repr; try lia.
      have -> : (56320 = 55 * 2 ^ 10)%Z by [].
      rewrite Z_lor_disjoint; try lia.
      f_equal. rewrite /l. have -> : (2 ^ 10 = 1024)%Z by [].
      have Em : (c mod 1024 = (c - 0x10000) mod 0x400)%num.
      { have Ec : c = ((c - 0x10000) + 64 * 0x400)%num by lia.
        rewrite {1}Ec. by rewrite N.Div0.mod_add. }
      rewrite N2Z.inj_add -Em N2Z.inj_mod. lia. }
    have Hh : (h < 65536)%num.
    { have : ((c - 0x10000) / 0x400 < 1024)%num by apply N.Div0.div_lt_upper_bound; lia.
      rewrite /h. lia. }
    have Hl16 : (l < 65536)%num.
    { have : ((c - 0x10000) mod 0x400 < 0x400)%num by apply N.mod_lt.
      rewrite /l. lia. }
    repeat wp_step. rewrite Eh.
    apply: (wp_store16_o (m1 := m1)) => //; try lia.
    move => m2 Hw1. repeat wp_step. rewrite El.
    have Hm2 : nth_error (s_mems (upd_mem0 s1 m2)) 0 = Some m2 by apply: upd_mem0_nth Hm.
    have Hlen2 : (operations.mem_length m2 = operations.mem_length m1)%num by case: Hw1 => _ [-> _].
    apply: (wp_store16_o (m1 := m2)) => //; try lia.
    move => m3 Hw2. repeat wp_step. split => //. apply wp_nil.
    rewrite /= i32_iadd_repr upd_mem0_twice. apply HQ.
    rewrite N.add_0_r in Hw1.
    exact: (wr_app Hw1 Hw2).
Qed.

(** ** The code point computed by cp_code, by sequence length *)

(** cp_code for a two-byte sequence b1 b (L = 2 in local 10). *)
Lemma cp_code_ok2 s1 b1 b l0 l1 l2 l3 l5 l7 l8 l9 :
  wp hs s1 (pframe [:: l0; l1; l2; l3; vZ (bZ b); l5; vZ (bZ b1); l7; l8; l9; vZ 2]) [::] cp_code
    (fun s2 f2 stk2 => s2 = s1 /\ stk2 = [::] /\
       f2 = pframe [:: l0; l1; l2; l3; vZ (bZ b); l5; vZ (bZ b1); vZ (Z.of_N (seq_value [:: b1; b]));
                      l8; l9; vZ 2]).
Proof.
  have Hb := bZ_range b. have Hb1 := bZ_range b1. have Hm := modulus_val.
  rewrite /cp_code /pframe /lg /ls /i32c /i_and /i_or /i_shl /i_eq /bin /rel /if_ /BTn.
  repeat wp_step. rewrite eq_val; try small_tac.
  wp_if_bool; last by exfalso; lia.
  repeat wp_step. split => //. repeat wp_step. split => //. split => //.
  rewrite (@mask_val (bZ b) 63 6); try small_tac; try done.
  rewrite (@mask_val (bZ b1) 31 5); try small_tac; try done.
  have M5 := @mod_bound (bZ b1) 5 ltac:(lia).
  have M6 := @mod_bound (bZ b) 6 ltac:(lia).
  have P5 : (2 ^ 5 = 32)%Z by []. have P6 : (2 ^ 6 = 64)%Z by [].
  rewrite (@shl_val (bZ b1 mod 2 ^ 5) 6); try (apply small_const; lia); try lia.
  rewrite or_val; try (apply small_const; lia).
  rewrite Z_lor_disjoint; try lia.
  have Ex : (bZ b mod 2 ^ 6 + bZ b1 mod 2 ^ 5 * 2 ^ 6 = Z.of_N (seq_value [:: b1; b]))%Z.
  { rewrite /seq_value N2Z.inj_add N2Z.inj_mul !N2Z.inj_mod -!bN_bZ P5 P6. lia. }
  by rewrite Ex.
Qed.

(** cp_code for a three-byte sequence b1 b2 b (L = 3; b2 from st >> 8). *)
Lemma cp_code_ok3 s1 b1 b2 b l1 l2 l3 l5 l7 l8 l9 :
  wp hs s1 (pframe [:: vZ (enc [:: b1; b2]); l1; l2; l3; vZ (bZ b); l5; vZ (bZ b1); l7; l8; l9; vZ 3]) [::] cp_code
    (fun s2 f2 stk2 => s2 = s1 /\ stk2 = [::] /\
       f2 = pframe [:: vZ (enc [:: b1; b2]); l1; l2; l3; vZ (bZ b); l5; vZ (bZ b1);
                      vZ (Z.of_N (seq_value [:: b1; b2; b])); l8; l9; vZ 3]).
Proof.
  have Hb := bZ_range b. have Hb1 := bZ_range b1. have Hb2 := bZ_range b2. have Hm := modulus_val.
  have P4 : (2 ^ 4 = 16)%Z by []. have P6 : (2 ^ 6 = 64)%Z by []. have P8 : (2 ^ 8 = 256)%Z by [].
  have P12 : (2 ^ 12 = 4096)%Z by [].
  rewrite /cp_code /low6_of_st /pframe /lg /ls /i32c /i_and /i_or /i_shl /i_shr /i_eq /bin /rel /if_ /BTn. cbv [app].
  repeat wp_step. rewrite eq_val; try small_tac.
  wp_if_bool; first by exfalso; lia.
  repeat wp_step. rewrite eq_val; try small_tac.
  wp_if_bool; last by exfalso; lia.
  repeat (wp_step || (split; [reflexivity|])).
  idtac.
  have Henc : enc [:: b1; b2] = (bZ b1 + bZ b2 * 256 + 2 * 16777216)%Z by [].
  rewrite (@mask_val (bZ b) 63 6); try small_tac; try done.
  rewrite (@mask_val (bZ b1) 15 4); try small_tac; try done.
  rewrite (@shru_val (enc [:: b1; b2]) 8 (small_enc _) ltac:(lia)).
  have Hq : small (enc [:: b1; b2] / 2 ^ 8) by rewrite /small Henc P8; Z.div_mod_to_equations; lia.
  rewrite (@mask_val (enc [:: b1; b2] / 2 ^ 8) 63 6 Hq); try done; try lia.
  have E2 : (enc [:: b1; b2] / 2 ^ 8 mod 2 ^ 6 = bZ b2 mod 2 ^ 6)%Z.
  { rewrite Henc P8 P6. Z.div_mod_to_equations. lia. }
  rewrite E2.
  have M4 := @mod_bound (bZ b1) 4 ltac:(lia).
  have M6 := @mod_bound (bZ b) 6 ltac:(lia).
  have M6' := @mod_bound (bZ b2) 6 ltac:(lia).
  rewrite (@shl_val (bZ b1 mod 2 ^ 4) 12); try (apply small_const; lia); try lia.
  rewrite (@shl_val (bZ b2 mod 2 ^ 6) 6); try (apply small_const; lia); try lia.
  have M6x : (0 <= bZ b mod 2 ^ 6 < 2 ^ 12)%Z by lia.
  rewrite or_val; try (apply small_const; lia).
  rewrite (Z_lor_disjoint (ltac:(lia) : (0 <= 12)%Z) M6x (ltac:(lia) : (0 <= bZ b1 mod 2 ^ 4)%Z)).
  rewrite or_val; try (apply small_const; lia).
  rewrite -(Z_lor_disjoint (ltac:(lia) : (0 <= 12)%Z) M6x (ltac:(lia) : (0 <= bZ b1 mod 2 ^ 4)%Z)).
  rewrite lor_swap.
  rewrite (Z_lor_disjoint (ltac:(lia) : (0 <= 6)%Z) M6 (ltac:(lia) : (0 <= bZ b2 mod 2 ^ 6)%Z)).
  have Hy : (0 <= bZ b mod 2 ^ 6 + bZ b2 mod 2 ^ 6 * 2 ^ 6 < 2 ^ 12)%Z by lia.
  rewrite (Z_lor_disjoint (ltac:(lia) : (0 <= 12)%Z) Hy (ltac:(lia) : (0 <= bZ b1 mod 2 ^ 4)%Z)).
  have Ex : (bZ b mod 2 ^ 6 + bZ b2 mod 2 ^ 6 * 2 ^ 6 + bZ b1 mod 2 ^ 4 * 2 ^ 12 =
             Z.of_N (seq_value [:: b1; b2; b]))%Z.
  { rewrite /seq_value ?N2Z.inj_add ?N2Z.inj_mul ?N2Z.inj_add ?N2Z.inj_mul !N2Z.inj_mod -!bN_bZ P4 P6 P12. cbn [Z.of_N]. lia. }
  by rewrite Ex.
Qed.

(** cp_code for a four-byte sequence b1 b2 b3 b (L = 4). *)
(** Or-ing a bit field c << j into a + (h << k), where a < 2^j and the field
    fits below bit k: plain addition. *)

Lemma cp_code_ok4 s1 b1 b2 b3 b l1 l2 l3 l5 l7 l8 l9 :
  wp hs s1 (pframe [:: vZ (enc [:: b1; b2; b3]); l1; l2; l3; vZ (bZ b); l5; vZ (bZ b1); l7; l8; l9; vZ 4]) [::] cp_code
    (fun s2 f2 stk2 => s2 = s1 /\ stk2 = [::] /\
       f2 = pframe [:: vZ (enc [:: b1; b2; b3]); l1; l2; l3; vZ (bZ b); l5; vZ (bZ b1);
                      vZ (Z.of_N (seq_value [:: b1; b2; b3; b])); l8; l9; vZ 4]).
Proof.
  have Hb := bZ_range b. have Hb1 := bZ_range b1. have Hb2 := bZ_range b2. have Hb3 := bZ_range b3.
  have Hm := modulus_val.
  have P3 : (2 ^ 3 = 8)%Z by []. have P6 : (2 ^ 6 = 64)%Z by []. have P8 : (2 ^ 8 = 256)%Z by [].
  have P12 : (2 ^ 12 = 4096)%Z by []. have P16 : (2 ^ 16 = 65536)%Z by [].
  have P18 : (2 ^ 18 = 262144)%Z by [].
  rewrite /cp_code /low6_of_st /pframe /lg /ls /i32c /i_and /i_or /i_shl /i_shr /i_eq /bin /rel /if_ /BTn. cbv [app].
  repeat wp_step. rewrite eq_val; try small_tac.
  wp_if_bool; first by exfalso; lia.
  repeat wp_step. rewrite eq_val; try small_tac.
  wp_if_bool; first by exfalso; lia.
  repeat (wp_step || (split; [reflexivity|])).
  have Henc : enc [:: b1; b2; b3] = (bZ b1 + bZ b2 * 256 + bZ b3 * 65536 + 3 * 16777216)%Z by [].
  rewrite (@mask_val (bZ b) 63 6); try small_tac; try done.
  rewrite (@mask_val (bZ b1) 7 3); try small_tac; try done.
  rewrite (@shru_val (enc [:: b1; b2; b3]) 8 (small_enc _) ltac:(lia)).
  rewrite (@shru_val (enc [:: b1; b2; b3]) 16 (small_enc _) ltac:(lia)).
  have Hq8 : small (enc [:: b1; b2; b3] / 2 ^ 8) by rewrite /small Henc P8; Z.div_mod_to_equations; lia.
  have Hq16 : small (enc [:: b1; b2; b3] / 2 ^ 16) by rewrite /small Henc P16; Z.div_mod_to_equations; lia.
  rewrite (@mask_val (enc [:: b1; b2; b3] / 2 ^ 8) 63 6 Hq8); try done; try lia.
  rewrite (@mask_val (enc [:: b1; b2; b3] / 2 ^ 16) 63 6 Hq16); try done; try lia.
  have E2 : (enc [:: b1; b2; b3] / 2 ^ 8 mod 2 ^ 6 = bZ b2 mod 2 ^ 6)%Z.
  { rewrite Henc P8 P6. Z.div_mod_to_equations. lia. }
  have E3 : (enc [:: b1; b2; b3] / 2 ^ 16 mod 2 ^ 6 = bZ b3 mod 2 ^ 6)%Z.
  { rewrite Henc P16 P6. Z.div_mod_to_equations. lia. }
  rewrite E2 E3.
  have M3 := @mod_bound (bZ b1) 3 ltac:(lia).
  have M6 := @mod_bound (bZ b) 6 ltac:(lia).
  have M6b := @mod_bound (bZ b2) 6 ltac:(lia).
  have M6c := @mod_bound (bZ b3) 6 ltac:(lia).
  rewrite (@shl_val (bZ b1 mod 2 ^ 3) 18); try (apply small_const; lia); try lia.
  rewrite (@shl_val (bZ b2 mod 2 ^ 6) 12); try (apply small_const; lia); try lia.
  rewrite (@shl_val (bZ b3 mod 2 ^ 6) 6); try (apply small_const; lia); try lia.
  set A := (bZ b mod 2 ^ 6)%Z. set B := (bZ b1 mod 2 ^ 3)%Z.
  set C := (bZ b2 mod 2 ^ 6)%Z. set D := (bZ b3 mod 2 ^ 6)%Z.
  (* A | B<<18 *)
  have HA18 : (0 <= A < 2 ^ 18)%Z by lia.
  rewrite or_val; try (apply small_const; lia).
  rewrite (Z_lor_disjoint (ltac:(lia) : (0 <= 18)%Z) HA18 (ltac:(lia) : (0 <= B)%Z)).
  (* | C<<12 *)
  rewrite or_val; try (apply small_const; lia).
  have HA12 : (0 <= A < 2 ^ 12)%Z by lia.
  rewrite (@lor_mid A C B 12 18); try lia.
  (* | D<<6 *)
  rewrite or_val; try (apply small_const; lia).
  have -> : (A + C * 2 ^ 12 + B * 2 ^ 18 = A + (C + B * 2 ^ 6) * 2 ^ 12)%Z by rewrite P6 P12 P18; lia.
  rewrite (@lor_mid A D (C + B * 2 ^ 6) 6 12); try lia.
  have Ex : (A + D * 2 ^ 6 + (C + B * 2 ^ 6) * 2 ^ 12 = Z.of_N (seq_value [:: b1; b2; b3; b]))%Z.
  { rewrite /A /B /C /D /seq_value ?N2Z.inj_add ?N2Z.inj_mul ?N2Z.inj_add ?N2Z.inj_mul ?N2Z.inj_add ?N2Z.inj_mul
      !N2Z.inj_mod -!bN_bZ P3 P6 P12. cbn [Z.of_N]. lia. }
  by rewrite Ex.
Qed.

(** ** Case: the byte completes the pending sequence (any length)

    The proof is the same for every length: the module checks the range of
    b and the count, computes the code point with cp_code (the only part
    that depends on the length: hypothesis [Hcp], from cp_code_ok2/3/4),
    writes it with emit_cp and resets the state to 0. *)

Lemma step_case_complete b1 r b :
  Inv (b1 :: r) -> vs (app (b1 :: r) [:: b]) = true ->
  (forall s1 l1 l2 l3 l5 l7 l8 l9,
     wp hs s1 (pframe [:: vZ (enc (b1 :: r)); l1; l2; l3; vZ (bZ b); l5; vZ (bZ b1); l7; l8; l9;
                          vZ (Z.of_nat (length (b1 :: r) + 1))]) [::] cp_code
       (fun s2 f2 stk2 => s2 = s1 /\ stk2 = [::] /\
          f2 = pframe [:: vZ (enc (b1 :: r)); l1; l2; l3; vZ (bZ b); l5; vZ (bZ b1);
                         vZ (Z.of_N (seq_value (app (b1 :: r) [:: b]))); l8; l9;
                         vZ (Z.of_nat (length (b1 :: r) + 1))])) ->
  step_case hs (b1 :: r) b.
Proof.
  move => HI Hvs Hcp s1 m1 wb L i o junk Hm _ Hj Hl Hb Ho Hlen Hom Him.
  have {}Hlen : (Z.to_N o + 4 <= operations.mem_length m1)%num by move: Hlen; cbn [pend]; lia.
  case: junk Hj => [|j0 [|j1 [|j2 [|j3 [|j4 [|j5 [|j6 [|j7 junk]]]]]]]] // _.
  have Hmod := modulus_val.
  have H3 := Inv_len _ HI.
  have Hvp : vp (app (b1 :: r) [:: b]) = true by apply: vs_vp.
  have Es := step_complete (b1 :: r) b ltac:(discriminate) Hvs.
  have [Hlead Hlt] := pending_lead _ _ HI.
  have HL : (length (b1 :: r) + 1 = seq_len (bN b1))%coq_nat by apply: (proj1 (pending_vs _ _ b HI Hvp)).
  have Hbnd := seq_cp_bound _ Hvs.
  apply: (step_code_pending (m1 := m1) (wb := wb) (b := b)) => //.
  apply: pending_split => //; last by rewrite Hvp.
  move => _. rewrite /ok_code /ok_locals.
  apply: wp_app. apply: wp_mono; last by apply: len_code_ok.
  move => s2 f2 stk2 [-> [-> ->]].
  rewrite -HL.
  rewrite /pframe /lg /i32c /i_add /i_eq /bin /rel /if_ /BTn.
  repeat wp_step.
  rewrite iadd_val eq_val; try (apply small_const; cbn [length] in *; lia).
  wp_if_bool; last by exfalso; match goal with H : (_ =? _)%Z = false |- _ => move/Z.eqb_neq: H; lia end.
  rewrite /complete_code.
  apply: wp_app. apply: wp_mono; last by apply: Hcp.
  move => s3 f3 stk3 [-> [-> ->]].
  apply: wp_app.
  rewrite /pframe -(seq_cp_value _ Hvs).
  refine (emit_cp_ok (m1 := m1) (u := seq_cp (app (b1 :: r) [:: b])) (l0 := vZ (enc (b1 :: r))) _ _ _ _ _ _);
    [exact Hm|lia|lia|lia|exact Hbnd|].
  move => m2 Hw.
  rewrite /i32c /ls. repeat wp_step. split => //. apply: wp_nil. split => //. apply: wp_nil.
  split => //. apply: wp_nil.
  rewrite Es. split => //.
  exists m2, [:: vZ (bZ b); vZ (Z.of_nat (length (b1 :: r))); vZ (bZ b1);
              vZ (Z.of_N (U32_to_N (seq_cp (app (b1 :: r) [:: b]))));
              vZ (Z.of_N (lo_next (length (b1 :: r)) b1)); vZ (Z.of_N (hi_next (length (b1 :: r)) b1));
              vZ (Z.of_nat (length (b1 :: r) + 1))].
  do 3 (split; first by []).
  have H4 := utf16le_one_len (seq_cp (app (b1 :: r) [:: b])).
  split; last by [].
  exact: wr_writes.
Qed.

Lemma step_case_complete2 b1 b : Inv [:: b1] -> vs [:: b1; b] = true -> step_case hs [:: b1] b.
Proof. move => HI Hvs. apply: step_case_complete HI Hvs _ => *. exact: cp_code_ok2. Qed.

Lemma step_case_complete3 b1 b2 b : Inv [:: b1; b2] -> vs [:: b1; b2; b] = true -> step_case hs [:: b1; b2] b.
Proof. move => HI Hvs. apply: step_case_complete HI Hvs _ => *. exact: cp_code_ok3. Qed.

Lemma step_case_complete4 b1 b2 b3 b : Inv [:: b1; b2; b3] -> vs [:: b1; b2; b3; b] = true ->
  step_case hs [:: b1; b2; b3] b.
Proof. move => HI Hvs. apply: step_case_complete HI Hvs _ => *. exact: cp_code_ok4. Qed.

End StepComplete.
