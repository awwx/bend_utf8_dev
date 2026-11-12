(** * Decode.v: the [decode] export: the loop, memory framing and output
    accumulation, proved CONDITIONALLY on [step_spec] (one iteration of
    [step_code] refines RefDecoder's [step]), which is stated here as a
    [Definition ... : Prop] and taken as an explicit premise
    (StepSpec.v proves it; Theorems.v combines the two).

    Decoder-specific.

    Exports:
    - [vZ] (an i32 value), [frame_of] (the locals of decode for a state,
      length, index, output address), [writes] (the bytes written by one
      step), [step_spec].
    - [utf16le_cat] (utf16le over ssreflect's cat), [mem_holds_app],
      [mem_holds_same], [wp_exec], [upd_mem0_nth], [upd_mem0_twice].
    - Section Decode (premise [step_spec], a store like the instantiated
      one, an input buffer in memory): loop invariant [inv], [post],
      [loop_body_ok] (one iteration), [decode_loop], and
      [decode_correct]: the call returns the new state and output length,
      and the output bytes are at OUT. *)

From Stdlib Require Import ZArith NArith List Lia.
From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool eqtype seq.
From Wasm Require Import datatypes operations opsem properties.
From Utf8 Require Import Utf8Laws Utf8Ref Utf8Proofs Utf8StepFacts.
From SymExec Require Import I32 Steps Control Wp Mem WpMem.
From Decoder Require Import Module Instance Boundary Repr Exports OutBound.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Decode.

Context `{ho: host}.
Variable hs : host_state.

Definition vZ (z : Z) : value := VAL_num (VAL_int32 (Wasm_int.Int32.repr z)).

(** Locals of [decode] in the loop: st, len, i, o, and 7 scratch locals. *)
Definition frame_of (st : State) (L : Z) (i : nat) (o : Z) (junk : list value) : frame :=
  Build_frame (vZ (enc st) :: vZ L :: vZ (Z.of_nat i) :: vZ o :: junk) inst0.

(** Bytes [ns] written by one step at [o], and the rest of memory unchanged. *)
Definition writes (m1 m2 : meminst) (o : N) (ns : list N) : Prop :=
  m2.(meminst_type) = m1.(meminst_type) /\
  operations.mem_length m2 = operations.mem_length m1 /\
  mem_holds m2 o ns /\
  forall q, (q < o \/ o + N.of_nat (length ns) <= q)%num ->
    mem_lookup q m2.(meminst_data) = mem_lookup q m1.(meminst_data).

(** THE PER-BYTE LEMMA (proved as StepSpec.step_spec_proved): one run of
    [step_code] on byte [b] (at address [i]) in state [st] produces
    RefDecoder's [step st b]: the new state, and the UTF-16LE bytes of its
    output at [o], changing nothing else.  Memory room needed at [o]: 2
    bytes from the empty state (at most one unit is written), 4 bytes
    when bytes are pending (U+FFFD plus a unit, or a surrogate pair). *)
Definition step_spec : Prop :=
  forall (s1 : store_record) (m1 : meminst) (st : State) (b : Byte.byte) (wb : bytes.byte)
         (L : Z) (i : nat) (o : Z) (junk : list value),
    nth_error s1.(s_mems) 0 = Some m1 ->
    Inv st -> length junk = 7 ->
    mem_lookup (N.of_nat i) m1.(meminst_data) = Some wb -> byte_as_mem b wb ->
    (0 <= o)%Z -> (Z.to_N o + 2 + N.of_nat (pend st) <= operations.mem_length m1)%num ->
    (o + 4 < Wasm_int.Int32.modulus)%Z -> (Z.of_nat i < Wasm_int.Int32.modulus)%Z ->
    wp hs s1 (frame_of st L i o junk) [::] step_code
      (fun s2 f2 stk2 =>
         stk2 = [::] /\
         exists m2 junk',
           s2 = upd_mem0 s1 m2 /\
           f2 = frame_of (fst (step st b)) L i (o + Z.of_nat (length (utf16le (snd (step st b))))) junk' /\
           length junk' = 7 /\
           writes m1 m2 (Z.to_N o) (utf16le (snd (step st b))) /\
           (length (utf16le (snd (step st b))) <= 4)%coq_nat).

(** ** Pure helpers *)

(* [utf16le_app] (OutBound.v) is stated with List.app; under ssreflect's
   seq, [++] is [cat], which [rewrite] does not identify with app. *)
Lemma utf16le_cat t1 t2 : utf16le (t1 ++ t2) = utf16le t1 ++ utf16le t2.
Proof. exact: utf16le_app. Qed.

Lemma mem_holds_app m p ns1 ns2 :
  mem_holds m p ns1 -> mem_holds m (p + N.of_nat (length ns1))%num ns2 ->
  mem_holds m p (ns1 ++ ns2).
Proof.
  move => H1 H2 i n.
  case: (Nat.lt_ge_cases i (length ns1)) => Hi.
  - rewrite nth_error_app1 //. by apply H1.
  - rewrite nth_error_app2 // => Hn.
    case: (H2 _ _ Hn) => wb [Hl Hu]. exists wb; split => //.
    rewrite -Hl. f_equal. lia.
Qed.

Lemma mem_holds_same m1 m2 p ns :
  (forall q, (p <= q < p + N.of_nat (length ns))%num ->
     mem_lookup q m2.(meminst_data) = mem_lookup q m1.(meminst_data)) ->
  mem_holds m1 p ns -> mem_holds m2 p ns.
Proof.
  move => Hs H i n Hn. case: (H _ _ Hn) => wb [Hl Hu]. exists wb; split => //.
  rewrite Hs //. have := nth_error_Some ns i. rewrite Hn => [[Hlt _]].
  have := Hlt ltac:(discriminate). lia.
Qed.

Lemma wp_exec s1 f1 stk bes S F K :
  wp hs s1 f1 stk bes (fun s2 f2 stk2 => s2 = S /\ f2 = F /\ stk2 = K) ->
  exec hs s1 f1 stk bes S F K.
Proof. move => [s2 [f2 [stk2 [H [E1 [E2 E3]]]]]]; by subst. Qed.

(** ** The loop *)

Hypothesis Hstep : step_spec.

Variable s : store_record.
Variable m : meminst.
Hypothesis Hfuncs : s.(s_funcs) = s0.(s_funcs).
Hypothesis Hmem : nth_error s.(s_mems) 0 = Some m.
Hypothesis Hlen : (mem_bytes_needed <= operations.mem_length m)%num.

Variable st0 : State.
Variable bs : list Byte.byte.
Hypothesis HI0 : Inv st0.
Hypothesis Hbs : (length bs <= IN_max)%coq_nat.
Hypothesis Hin : mem_holds m IN_addr (byte_values bs).

Definition lenZ : Z := Z.of_nat (length bs).

Definition inv (n : nat) (s' : store_record) (f : frame) : Prop :=
  exists pre rest m' junk st t,
    bs = pre ++ rest /\ n = length rest /\
    ref_decode_buffer st0 pre = (st, t) /\ Inv st /\
    s' = upd_mem0 s m' /\
    f = frame_of st lenZ (length pre) (OUT + Z.of_nat (length (utf16le t))) junk /\
    length junk = 7 /\
    mem_frame m m' OUT_addr (out_area (length bs)) /\
    mem_holds m' OUT_addr (utf16le t) /\
    (* output so far, plus the credit of pending bytes (OutBound.pend) *)
    (Nat.add (length (utf16le t)) (pend st) <= Nat.add (Nat.mul 2 (length pre)) (pend st0))%coq_nat.

Definition post (s' : store_record) (f : frame) : Prop :=
  exists m' junk st t,
    ref_decode_buffer st0 bs = (st, t) /\ Inv st /\
    s' = upd_mem0 s m' /\
    f = frame_of st lenZ (length bs) (OUT + Z.of_nat (length (utf16le t))) junk /\
    mem_frame m m' OUT_addr (out_area (length bs)) /\
    mem_holds m' OUT_addr (utf16le t).

Lemma loop_split :
  loop_body = (([:: lg 2; lg 1; i_geu] ++ [:: BI_br_if 1%num]) ++ (step_code ++ [:: lg 2; i32c 1; i_add; ls 2])) ++ [:: BI_br 0%num].
Proof. by []. Qed.

Lemma bs_bound : (Z.of_nat (length bs) <= 65536)%Z.
Proof.
  have H := Hbs. apply Nat2Z.inj_le in H.
  have E : Z.of_nat IN_max = 65536%Z by vm_compute.
  by rewrite E in H.
Qed.

Lemma A_ok s1 st i o junk :
  (Z.of_nat i < lenZ)%Z ->
  wp hs s1 (frame_of st lenZ i o junk) [::] ([:: lg 2; lg 1; i_geu] ++ [:: BI_br_if 1%num])
    (fun s2 f2 stk2 => s2 = s1 /\ f2 = frame_of st lenZ i o junk /\ stk2 = [::]).
Proof.
  move => Hi.
  have Hbs65 := bs_bound.
  unfold_code. rewrite /frame_of.
  have Hl : (0 <= lenZ <= 65536)%Z by rewrite /lenZ; lia.
  repeat wp_step. rewrite geu_val; try (rewrite modulus_val; lia).
  have -> : (lenZ <=? Z.of_nat i)%Z = false by apply Z.leb_gt; lia.
  eapply wp_cons; first by apply exec_br_if_false.
  by apply wp_nil.
Qed.

Lemma B_ok s1 st i o junk :
  wp hs s1 (frame_of st lenZ i o junk) [::] [:: lg 2; i32c 1; i_add; ls 2]
    (fun s2 f2 stk2 => s2 = s1 /\ f2 = frame_of st lenZ (i + 1) o junk /\ stk2 = [::]).
Proof.
  unfold_code. rewrite /frame_of.
  repeat wp_step. split => //. split => //.
  by rewrite /= /vZ i32_iadd_repr Nat2Z.inj_add.
Qed.

Lemma upd_mem0_nth s1 m1 m2 : nth_error s1.(s_mems) 0 = Some m1 ->
  nth_error (upd_mem0 s1 m2).(s_mems) 0 = Some m2.
Proof. by case: s1 => fs ts [|x ms] gs es ds. Qed.

Lemma upd_mem0_twice s1 m1 m2 : upd_mem0 (upd_mem0 s1 m1) m2 = upd_mem0 s1 m2.
Proof. by case: s1 => fs ts [|x ms] gs es ds. Qed.

Lemma loop_body_ok n s1 f1 : inv n s1 f1 ->
  (exists n' s2 f2, (n' < n)%coq_nat /\ exec_br hs s1 f1 [::] loop_body s2 f2 0%num /\ inv n' s2 f2) \/
  (exists s2 f2, exec_br hs s1 f1 [::] loop_body s2 f2 1%num /\ post s2 f2).
Proof.
  move => [pre [rest [m1 [junk [st [t [Hbs' [Hn [Hdec [HI [Hs1 [Hf1 [Hj [Hfr [Hho Hlt]]]]]]]]]]]]]]].
  have Hpre : (length pre <= length bs)%coq_nat by rewrite Hbs' length_app; lia.
  have Hbs65 := bs_bound.
  have Hlen_pre : (0 <= Z.of_nat (length pre) < Wasm_int.Int32.modulus)%Z by rewrite modulus_val; lia.
  have Hlen_bs : (0 <= lenZ < Wasm_int.Int32.modulus)%Z by rewrite /lenZ modulus_val; lia.
  rewrite loop_split.
  case: rest Hbs' Hn => [|b rest'] Hbs' Hn.
  - (* exit *)
    right. exists s1, f1. split.
    + apply: exec_br_prefix. apply: exec_br_prefix. apply: exec_then_br; last by apply exec_br_if_true; apply wasm_bool_true_nz.
      apply: wp_exec. subst f1. unfold_code. rewrite /frame_of.
      repeat wp_step. rewrite geu_val //.
      have -> : (lenZ <=? Z.of_nat (length pre))%Z = true by rewrite /lenZ Hbs' cats0; apply Z.leb_le; lia.
      by [].
    + have Ep : pre = bs by rewrite Hbs' cats0.
      subst pre. exists m1, junk, st, t. by do 5 (split; first by []).
  - (* one more byte *)
    left.
    have Hnth : nth_error (byte_values bs) (length pre) = Some (Byte.to_N b).
    { rewrite /byte_values Hbs'. apply map_nth_error. rewrite nth_error_app2 // Nat.sub_diag. by []. }
    case: (Hin Hnth) => wb [Hwb Hu].
    move: Hfr => [Hty [Hlen1 Hout]].
    have Hwb1 : mem_lookup (N.of_nat (length pre)) m1.(meminst_data) = Some wb.
    { have Hq : (N.of_nat (length pre) < OUT_addr \/ (OUT_addr + out_area (length bs) <= N.of_nat (length pre)))%num.
      { left. rewrite OUT_addr_val. have : (length pre < length bs)%coq_nat by rewrite Hbs' length_app /=; lia.
        lia. }
      rewrite (Hout _ Hq).
      have E : (IN_addr + N.of_nat (length pre) = N.of_nat (length pre))%num by rewrite /IN_addr /IN; lia.
      by rewrite E in Hwb. }
    have Hm1 : nth_error (s_mems s1) 0 = Some m1 by rewrite Hs1; apply: upd_mem0_nth Hmem.
    have HL := Hlen. rewrite mem_bytes_needed_val in HL.
    have Hlt' : (length pre < length bs)%coq_nat by rewrite Hbs' length_app /=; lia.
    set o := (OUT + Z.of_nat (length (utf16le t)))%Z.
    have Ho0 : (0 <= o)%Z by rewrite /o /OUT; lia.
    have Eo : Z.to_N o = (65536 + N.of_nat (length (utf16le t)))%num.
    { rewrite /o /OUT. apply N2Z.inj. rewrite Z2N.id; lia. }
    have Hp0 := pend_le2 st0.
    (* room for this step: o + 2 + pend st <= OUT + 2 * |bs| + 2 = mem_bytes_needed *)
    have Ho4 : (Z.to_N o + 2 + N.of_nat (pend st) <= operations.mem_length m1)%num.
    { rewrite Hlen1 Eo. have Hz1 : (Z.of_nat (length pre) < 65536)%Z by clear - Hlt' Hbs65; lia.
      apply: (N.le_trans _ 196610%num); last by exact HL.
      have Hnb : (Z.of_nat (length (utf16le t)) + Z.of_nat (pend st) <= 131072)%Z by clear - Hlt Hz1 Hp0; lia.
      clear - Hnb. lia. }
    have Hom : (o + 4 < Wasm_int.Int32.modulus)%Z by rewrite modulus_val /o /OUT; lia.
    have Him : (Z.of_nat (length pre) < Wasm_int.Int32.modulus)%Z by rewrite modulus_val; lia.
    have W0 := Hstep. rewrite /step_spec in W0.
    have W := W0 s1 m1 st b wb lenZ (length pre) o junk Hm1 HI Hj Hwb1 Hu Ho0 Ho4 Hom Him.
    clear W0.
    have W2 : wp hs s1 f1 [::]
        (([:: lg 2; lg 1; i_geu] ++ [:: BI_br_if 1%num]) ++ (step_code ++ [:: lg 2; i32c 1; i_add; ls 2]))
        (fun s2 f2 stk2 => stk2 = [::] /\ inv (length rest') s2 f2).
    { subst f1. apply wp_app.
      eapply wp_mono; last by apply: A_ok; rewrite /lenZ; clear - Hlt'; lia.
      move => s2 f2 stk2 [E1 [E2 E3]].
      subst s2 f2 stk2. apply wp_app.
      eapply wp_mono; last by exact W.
      move => s3 f3 stk3 [E3 [m2 [junk' [Hs3 [Hf3 [Hj' [Hw Hle4]]]]]]].
      subst f3 stk3.
      eapply wp_mono; last by apply: B_ok.
      move => s4 f4 stk4 [E4 [E5 E6]]. subst s4 f4 stk4.
      split => //.
      move: Hw => [Hty2 [Hlen2 [Hho2 Hout2]]].
      have Hsb := step_out_bound st b.
      have Hzp : (Z.of_nat (length pre) + 1 <= Z.of_nat (length bs))%Z by clear - Hlt'; lia.
      have Hz4 : (Z.of_nat (length (utf16le (snd (step st b)))) <= 4)%Z by clear - Hle4; lia.
      exists (pre ++ [:: b]), rest', m2, junk', (fst (step st b)), (t ++ snd (step st b)).
      split; first by rewrite Hbs' -catA.
      split; first by [].
      split; first by rewrite ref_decode_buffer_snoc Hdec.
      split; first by apply step_inv.
      split; first by rewrite Hs3 Hs1 upd_mem0_twice.
      split.
      { rewrite utf16le_app.
        have -> : (OUT + Z.of_nat (length (utf16le t ++ utf16le (snd (step st b)))))%Z =
                  (o + Z.of_nat (length (utf16le (snd (step st b)))))%Z
          by rewrite length_app Nat2Z.inj_add /o; clear; lia.
        have -> : length (pre ++ [:: b]) = (length pre + 1)%coq_nat by rewrite length_app.
        by []. }
      split; first by [].
      split.
      { split; first by rewrite Hty2.
        split; first by rewrite Hlen2.
        move => q Hq.
        have Hq2 : (q < Z.to_N o \/ Z.to_N o + N.of_nat (length (utf16le (snd (step st b)))) <= q)%num.
        { rewrite Eo. move: Hq. rewrite OUT_addr_val /out_area. clear - Hsb Hlt Hp0 Hzp. lia. }
        rewrite (Hout2 _ Hq2). by apply Hout. }
      split.
      { rewrite utf16le_app. apply: mem_holds_app.
        - apply: (mem_holds_same (m1 := m1)) => //.
          move => q Hq. apply Hout2. left. rewrite Eo. move: Hq. rewrite OUT_addr_val. clear. lia.
        - have -> : (OUT_addr + N.of_nat (length (utf16le t)))%num = Z.to_N o
            by rewrite OUT_addr_val Eo.
          exact Hho2. }
      rewrite utf16le_app !length_app. cbn [length]. clear - Hlt Hsb. lia. }
    case: W2 => s2 [f2 [stk2 [Hex [E Hinv]]]]. subst stk2.
    exists (length rest'), s2, f2. split; first by rewrite Hn /=; lia.
    split => //. apply: exec_then_br; first exact Hex. apply exec_br_br.
Qed.

Definition junk0 : list value := [:: vZ 0; vZ 0; vZ 0; vZ 0; vZ 0; vZ 0; vZ 0].

Lemma decode_loop :
  exists s' f', exec hs (upd_mem0 s m) (frame_of st0 lenZ 0 (OUT + Z.of_nat 0) junk0) [::]
                  [:: BI_block BT_none [:: BI_loop BT_none loop_body]] s' f' [::] /\ post s' f'.
Proof.
  apply: (block_loop_rule (P := inv)); first by move => n1 s1 f1 H; apply: loop_body_ok.
  exists [::], bs, m, junk0, st0, [::].
  split; first by []. split; first by []. split; first by [].
  split; first by []. split; first by []. split; first by []. split; first by [].
  split; first by split; [by [] | split; [by [] | by []]].
  split; first by move => [|i] n. by [].
Qed.

Lemma decode_correct :
  exists st t m',
    ref_decode_buffer st0 bs = (st, t) /\ Inv st /\
    mem_frame m m' OUT_addr (out_area (length bs)) /\ mem_holds m' OUT_addr (utf16le t) /\
    call_returns hs s 1%num [:: i32v (Wasm_int.Int32.repr (enc st0)); i32_of_nat (length bs)]
      (store_with_mem s 0%num m')
      [:: i32v (Wasm_int.Int32.repr (enc st)); i32_of_nat (length (utf16le t))].
Proof.
  case: decode_loop => s' [f' [Hex [m' [junk [st [t [Hdec [HI [Hs' [Hf' [Hfr Hho]]]]]]]]]]].
  exists st, t, m'. do 4 (split; first by []).
  rewrite store_with_mem0.
  apply: (call_of_wp (ts1 := [:: T32; T32]) (ts2 := [:: T32; T32]) (x := 1%num) (ts := repeat T32 9)
            (body := decode_body) (defs := [:: vZ 0; vZ 0; vZ 0; vZ 0; vZ 0; vZ 0; vZ 0; vZ 0; vZ 0])) => //.
  - by rewrite Hfuncs.
  - rewrite /decode_body. cbv [i32c ls lg i_sub bin BTn].
    eapply wp_cons; first by apply exec_const.
    eapply wp_cons; first by apply exec_local_set.
    rewrite (upd_mem0_same Hmem) in Hex.
    eapply wp_cons; first by exact Hex.
    rewrite Hf' Hs' /frame_of.
    repeat wp_step.
    split; first by [].
    change (Wasm_int.int_sub i32m) with Wasm_int.Int32.isub.
    rewrite i32_isub_repr Z.add_simpl_l. reflexivity.
Qed.

End Decode.
