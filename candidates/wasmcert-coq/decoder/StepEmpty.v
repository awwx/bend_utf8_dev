(** * StepEmpty.v: step_spec, part 1: the empty-state case, the per-case
    statement [step_case], and the pieces shared with the pending cases.

    Decoder-specific (uses the module's code from Module.v).

    Exports:
    - Tactics (top level): [small_tac], [wp_if_bool] (used by
      StepPending.v and StepComplete.v).
    - Memory writes: [wr m1 m2 a ns] (m2 is m1 with exactly the bytes ns
      written at a: same type and length, ns at a, nothing else changed),
      [wr_nil], [wr_app], [wr_writes] (to Decode.writes), [store16_wr],
      [lookup_mem0], [wp_store16_o], [wp_load8].
    - [utf16le_ascii]: the output bytes of an ASCII code point.
    - Wasm paths: [emit_fffd_ok], [empty_code_ok] (all three paths of
      empty_code: ASCII / lead byte / invalid byte, with RefDecoder's
      [step [] b] as the result), [step_empty_cases].
    - [step_case st b]: step_spec for one state and byte;
      [step_spec_of_cases]; [step_case_empty] (the empty-state case).
    Arithmetic is from ../symexec/I32.v, packed-state facts from Repr.v,
    step equations from ../../pure-rocq/Utf8StepFacts.v. *)

From Stdlib Require Import ZArith NArith List Lia.
From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool eqtype seq.
From Wasm Require Import datatypes operations opsem properties.
From Utf8 Require Import Utf8Laws Utf8Ref Utf8Proofs Utf8StepFacts.
From SymExec Require Import I32 Steps Control Wp Mem WpMem.
From Decoder Require Import Module Instance Boundary Repr Exports OutBound Decode.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Tactics shared by the step_spec case files (top level, so that
    StepPending.v and StepComplete.v get them by importing this file):
    [small_tac] proves [small x] for bytes, packed states and constants;
    [wp_if_bool] splits on an [if] whose condition is a comparison result. *)
Ltac small_tac := solve [apply small_byte | apply small_enc | apply small_const; lia | rewrite /small modulus_val; lia].
Ltac wp_if_bool :=
  apply: wp_if; [move=> /wasm_bool_nz ? | move=> /wasm_bool_z ?].

Section StepEmpty.

Context `{ho: host}.
Variable hs : host_state.

(** ** i32 arithmetic on small values *)

(** Bitwise or of a value below 2^k with a multiple of 2^k is addition. *)

(** ** Memory: exactly the bytes [ns] written at [a] *)

Definition wr (m1 m2 : meminst) (a : N) (ns : list N) : Prop :=
  m2.(meminst_type) = m1.(meminst_type) /\
  operations.mem_length m2 = operations.mem_length m1 /\
  mem_holds m2 a ns /\
  forall q, (q < a \/ a + N.of_nat (length ns) <= q)%num ->
    mem_lookup q m2.(meminst_data) = mem_lookup q m1.(meminst_data).

Lemma wr_nil m a : wr m m a [::].
Proof. split; [by []|split; [by []|split; [by move => [|i] n|by []]]]. Qed.

Lemma wr_app m1 m2 m3 a ns1 ns2 :
  wr m1 m2 a ns1 -> wr m2 m3 (a + N.of_nat (length ns1))%num ns2 -> wr m1 m3 a (ns1 ++ ns2).
Proof.
  move => [T1 [L1 [H1 O1]]] [T2 [L2 [H2 O2]]].
  split; first by rewrite T2. split; first by rewrite L2.
  split.
  - apply: mem_holds_app => //.
    apply: (mem_holds_same (m1 := m2)) => // q Hq. apply O2. lia.
  - move => q Hq. rewrite length_app Nat2N.inj_add in Hq.
    rewrite (O2 q ltac:(lia)). apply O1. lia.
Qed.

Lemma wr_writes m1 m2 o ns : (length ns <= 4)%coq_nat -> wr m1 m2 o ns -> writes m1 m2 o ns.
Proof.
  move => _ [T [L [H O]]]. by split.
Qed.

(** One 16-bit store of a code unit [u] writes its two little-endian bytes. *)
Lemma store16_wr m1 m2 a u : (u < 65536)%num ->
  store16_post m1 m2 a (Wasm_int.Int32.repr (Z.of_N u)) -> wr m1 m2 a [:: (u mod 256)%num; (u / 256)%num].
Proof.
  move => Hu [T [L [H0 [H1 O]]]].
  have Hz : Wasm_int.Int32.unsigned (Wasm_int.Int32.repr (Z.of_N u)) = Z.of_N u
    by apply unsigned_small; rewrite modulus_val; lia.
  rewrite Hz in H0 H1.
  split => //. split => //. split.
  - move => [|[|i]] n; cbn [nth_error]; last by case: i.
    + move => [<-]. eexists; split; first by rewrite N.add_0_r; exact H0.
      rewrite /lo_byte Integers.Byte.unsigned_repr_eq N2Z.inj_mod. by [].
    + move => [<-]. eexists; split; first by exact H1.
      have Hd : (0 <= Z.of_N u / 256 < 256)%Z
        by split; [apply Z.div_pos|apply Z.div_lt_upper_bound]; lia.
      rewrite /hi_byte byte_unsigned_repr // N2Z.inj_div. by [].
  - move => q Hq. apply O. cbn [length] in Hq. lia.
Qed.

(** Setting the pending count: [x | k << 24] = [x + k * 2^24] for x < 2^24. *)

(** ** The 16-bit store at the output position [o] (local 3) *)

Lemma lookup_mem0 (s1 : store_record) m1 : nth_error s1.(s_mems) 0 = Some m1 ->
  lookup_N s1.(s_mems) 0%num = Some m1.
Proof. by []. Qed.

Lemma wp_store16_o s1 m1 f stk o off u rest Q :
  f.(f_inst) = inst0 -> nth_error s1.(s_mems) 0 = Some m1 ->
  (0 <= o)%Z -> (o < Wasm_int.Int32.modulus)%Z ->
  (Z.to_N o + off + 2 <= operations.mem_length m1)%num -> (u < 65536)%num ->
  (forall m2, wr m1 m2 (Z.to_N o + off)%num [:: (u mod 256)%num; (u / 256)%num] ->
     wp hs (upd_mem0 s1 m2) f stk rest Q) ->
  wp hs s1 f (VAL_num (VAL_int32 (Wasm_int.Int32.repr (Z.of_N u))) :: VAL_num (VAL_int32 (Wasm_int.Int32.repr o)) :: stk)
    (BI_store T_i32 (Some Tp_i16) {| memarg_offset := off; memarg_align := 0%num |} :: rest) Q.
Proof.
  move => Hi Hm Ho Hom Hl Hu HQ.
  have Hk : Wasm_int.N_of_uint i32m (Wasm_int.Int32.repr o) = Z.to_N o.
  { change (Z.to_N (Wasm_int.Int32.unsigned (Wasm_int.Int32.repr o)) = Z.to_N o). by rewrite unsigned_small. }
  apply: (wp_store16 (m := m1)); first by rewrite Hi.
  - exact: lookup_mem0.
  - by rewrite Hk.
  - move => m2 Hp. apply HQ. apply: store16_wr => //. by rewrite -Hk.
Qed.

(** ** Code units of the outputs of [step] *)

Lemma utf16le_ascii b : (bN b <= 0x7F)%num ->
  utf16le [:: seq_cp [:: b]] = [:: (bN b mod 256)%num; (bN b / 256)%num].
Proof.
  move => H. rewrite /utf16le /utf16_units. cbn [flat_map].
  have V : vs [:: b] = true by apply vs_one_iff. rewrite (seq_cp_value1 _ V).
  have -> : (bN b <? 0x10000)%num = true by apply N.ltb_lt; lia.
  by [].
Qed.

(** ** Wasm paths *)

(** Close the [stk = [::] /\ wp _ _ _ [::] _] wrappers that [wp_if] leaves. *)
Ltac wp_close := repeat (apply wp_nil || (split; [reflexivity|])).

Lemma emit_fffd_ok s1 m1 (l0 l1 l2 : value) (o : Z) junk Q :
  nth_error s1.(s_mems) 0 = Some m1 ->
  (0 <= o)%Z -> (o < Wasm_int.Int32.modulus)%Z ->
  (Z.to_N o + 2 <= operations.mem_length m1)%num ->
  (forall m2, wr m1 m2 (Z.to_N o) (utf16le [:: FFFD]) ->
     Q (upd_mem0 s1 m2) (Build_frame (l0 :: l1 :: l2 :: vZ (o + 2) :: junk) inst0) [::]) ->
  wp hs s1 (Build_frame (l0 :: l1 :: l2 :: vZ o :: junk) inst0) [::] emit_fffd Q.
Proof.
  move => Hm Ho Hom Hl HQ.
  unfold_code. repeat wp_step.
  change (Wasm_int.Int32.repr 65533) with (Wasm_int.Int32.repr (Z.of_N 65533)).
  apply: (wp_store16_o (m1 := m1)) => //; try lia.
  move => m2 Hw. repeat wp_step.
  rewrite /= i32_iadd_repr. apply HQ.
  rewrite FFFD_units. move: Hw. by rewrite N.add_0_r.
Qed.

(** The three outcomes of [step [] b], as needed for output lengths. *)
Lemma step_empty_cases b :
  (step [::] b = ([::], [:: seq_cp [:: b]]) /\ utf16le [:: seq_cp [:: b]] = [:: (bN b mod 256)%num; (bN b / 256)%num]) \/
  (step [::] b = ([:: b], [::]) /\ utf16le [::] = [::]) \/
  (step [::] b = ([::], [:: FFFD]) /\ utf16le [:: FFFD] = [:: 0xFD; 0xFF]%num).
Proof.
  have HbN := bN_lt b.
  case: (N.le_gt_cases (bN b) 0x7F) => H1.
  - left. split; [by apply step_empty_ascii | by apply utf16le_ascii].
  - right. case: (N.le_gt_cases 0xC2 (bN b)) => H2; [case: (N.le_gt_cases (bN b) 0xF4) => H3|].
    + left. split => //. apply step_empty_lead. lia.
    + right. split; [apply step_empty_bad; lia | exact FFFD_units].
    + right. split; [apply step_empty_bad; lia | exact FFFD_units].
Qed.

Lemma enc_nil : enc [::] = 0%Z.
Proof. by []. Qed.

(** RefDecoder's [step [] b], computed by [empty_code] (st = 0 in local 0,
    b in local 4).  The three paths: ASCII (write b), lead byte (st := b |
    1 << 24), invalid byte (write U+FFFD). *)
Lemma empty_code_ok s1 m1 (l1 l2 : value) (o : Z) b junk Q :
  nth_error s1.(s_mems) 0 = Some m1 ->
  (0 <= o)%Z -> (o < Wasm_int.Int32.modulus)%Z ->
  (Z.to_N o + 2 <= operations.mem_length m1)%num ->
  (forall m2, wr m1 m2 (Z.to_N o) (utf16le (snd (step [::] b))) ->
     Q (upd_mem0 s1 m2)
       (Build_frame (vZ (enc (fst (step [::] b))) :: l1 :: l2 ::
                     vZ (o + Z.of_nat (length (utf16le (snd (step [::] b))))) :: vZ (bZ b) :: junk) inst0) [::]) ->
  wp hs s1 (Build_frame (vZ 0 :: l1 :: l2 :: vZ o :: vZ (bZ b) :: junk) inst0) [::] empty_code Q.
Proof.
  move => Hm Ho Hom Hl HQ.
  have Hb := bZ_range b. have HbN := bN_lt b.
  have Hmod := modulus_val.
  unfold_code. rewrite /vZ. repeat wp_step.
  apply: wp_if => Hc.
  - (* ASCII *)
    have Ha : (bZ b < 128)%Z.
    { move: (wasm_bool_nz Hc). rewrite ltu_val; lia. }
    have Es : step [::] b = ([::], [:: seq_cp [:: b]]) by apply step_empty_ascii; rewrite bN_bZ in Ha; lia.
    have Hu : utf16le [:: seq_cp [:: b]] = [:: (bN b mod 256)%num; (bN b / 256)%num]
      by apply utf16le_ascii; rewrite bN_bZ in Ha; lia.
    rewrite Es Hu in HQ.
    repeat wp_step. rewrite bN_bZ.
    apply: (wp_store16_o (m1 := m1)) => //; try lia.
    move => m2 Hw. repeat wp_step. wp_close.
    rewrite /= i32_iadd_repr -bN_bZ. apply HQ. by rewrite N.add_0_r in Hw.
  - have Ha : (128 <= bZ b)%Z.
    { move: (wasm_bool_z Hc). rewrite ltu_val; lia. }
    repeat wp_step.
    have Ex : Wasm_int.int_sub i32m (Wasm_int.Int32.repr (bZ b)) (Wasm_int.Int32.repr 194) =
      Wasm_int.Int32.repr (bZ b - 194)%Z := i32_isub_repr _ _.
    rewrite Ex.
    (* (b - 0xC2) as unsigned: below 0x32 iff b in C2..F4 *)
    have Hsub : Wasm_int.Int32.repr (bZ b - 194)%Z =
      Wasm_int.Int32.repr (if (194 <=? bZ b)%Z then bZ b - 194 else bZ b - 194 + Wasm_int.Int32.modulus)%Z.
    { case: Z.leb_spec => H //. apply Wasm_int.Int32.eqm_samerepr. exists (-1)%Z. lia. }
    rewrite Hsub.
    apply: wp_if => Hc2.
    + (* lead byte *)
      have Hl2 : (194 <= bZ b <= 244)%Z.
      { move: (wasm_bool_nz Hc2). case: Z.leb_spec => H; rewrite leu_val; lia. }
      have Es : step [::] b = ([:: b], [::]) by apply step_empty_lead; rewrite bN_bZ in Hl2; lia.
      rewrite Es /= in HQ.
      have Eo := @or_count (bZ b) 1 ltac:(lia) ltac:(lia).
      rewrite Z.mul_1_l in Eo.
      repeat wp_step. rewrite Eo. wp_close.
      rewrite Z.add_0_r in HQ.
      rewrite -(upd_mem0_same Hm). apply HQ. exact: wr_nil.
    + (* invalid byte *)
      have Hl2 : (128 <= bZ b <= 193 \/ 245 <= bZ b)%Z.
      { move: (wasm_bool_z Hc2). case: Z.leb_spec => H; rewrite leu_val; lia. }
      have Es : step [::] b = ([::], [:: FFFD]) by apply step_empty_bad; rewrite bN_bZ in Hl2; lia.
      rewrite Es in HQ.
      apply: (emit_fffd_ok (m1 := m1)) => // m2 Hw. wp_close.
      rewrite FFFD_units in HQ Hw. by apply HQ.
Qed.

(** ** Reading the input byte (i32.load8_u at i) *)

Lemma wp_load8 s1 m1 f stk i wb rest Q :
  f.(f_inst) = inst0 -> nth_error s1.(s_mems) 0 = Some m1 ->
  (Z.of_nat i < Wasm_int.Int32.modulus)%Z ->
  mem_lookup (N.of_nat i) m1.(meminst_data) = Some wb ->
  wp hs s1 f (VAL_num (VAL_int32 (Wasm_int.Int32.repr (Integers.Byte.unsigned wb))) :: stk) rest Q ->
  wp hs s1 f (VAL_num (VAL_int32 (Wasm_int.Int32.repr (Z.of_nat i))) :: stk) (load8 :: rest) Q.
Proof.
  move => Hi Hm Hlt Hl HQ.
  have Hk : Wasm_int.N_of_uint i32m (Wasm_int.Int32.repr (Z.of_nat i)) = N.of_nat i.
  { change (Z.to_N (Wasm_int.Int32.unsigned (Wasm_int.Int32.repr (Z.of_nat i))) = N.of_nat i).
    rewrite unsigned_small; lia. }
  have Hin : (N.of_nat i < operations.mem_length m1)%num.
  { case: (N.lt_ge_cases (N.of_nat i) (operations.mem_length m1)) => // H.
    have Hx : mem_lookup (N.of_nat i) (meminst_data m1) = None
      by apply mem_lookup_oob; rewrite /operations.mem_length in H; lia.
    by rewrite Hl in Hx. }
  apply: wp_cons HQ.
  have Hsm : smem s1 (f_inst f) = Some m1 by rewrite /smem Hi.
  have Hlp : load_packed SX_U m1 (Wasm_int.N_of_uint i32m (Wasm_int.Int32.repr (Z.of_nat i))) 0%num 1%num 4%num
             = Some [:: wb; #00; #00; #00].
  { rewrite /load_packed /load Hk.
    have -> : (N.of_nat i + (0 + 1) <=? operations.mem_length m1)%num = true by apply N.leb_le; lia.
    rewrite /read_bytes /= N.add_0_r N.add_0_r Hl. by []. }
  have E := exec_load_packed (t := T_i32) (tp := Tp_i8) (marg := ma 0) hs stk Hsm Hlp.
  have Ev : wasm_deserialise [:: wb; #00; #00; #00] T_i32 = VAL_int32 (Wasm_int.Int32.repr (Integers.Byte.unsigned wb)).
  { Local Transparent Archi.big_endian.
    rewrite /wasm_deserialise /common.Memdata.decode_int /common.Memdata.rev_if_be /Archi.big_endian /=.
    do 2 f_equal. have -> : Integers.Byte.unsigned #00 = 0%Z by []. lia. }
  rewrite Ev in E. exact E.
Qed.

(** ** The empty-state case of [step_spec] *)

(** [step_spec], for one given state [st] and byte [b]. *)
Definition step_case (st : State) (b : Byte.byte) : Prop :=
  forall (s1 : store_record) (m1 : meminst) (wb : bytes.byte)
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

Lemma step_spec_of_cases : (forall st b, step_case st b) -> step_spec hs.
Proof. move => H s1 m1 st b wb L i o junk. exact: H. Qed.

Lemma step_case_empty b : step_case [::] b.
Proof.
  move => s1 m1 wb L i o junk Hm HI Hj Hl Hb Ho Hlen Hom Him.
  case: junk Hj => [|j0 [|j1 [|j2 [|j3 [|j4 [|j5 [|j6 [|j7 junk]]]]]]]] //= _.
  have Hmod := modulus_val.
  rewrite /step_code /frame_of /lg /ls /i32c /i_shr /bin /if_ /BTn.
  wp_step.
  apply: (wp_load8 (m1 := m1) (wb := wb)) => //.
  rewrite Hb -/(bZ b).
  repeat wp_step.
  apply: wp_if => Hc; last by exfalso; move: Hc; vm_compute; congruence.
  apply: (empty_code_ok (m1 := m1)) => //; try lia.
  move => m2 Hw. wp_close.
  exists m2, [:: vZ (bZ b); vZ 0; j2; j3; j4; j5; j6].
  have Hl4 : (length (utf16le (snd (step [::] b))) <= 2)%coq_nat.
  { case: (step_empty_cases b) => [[-> ->]|[[-> ->]|[-> ->]]]; cbn; lia. }
  have E0 : Wasm_int.int_shr_u i32m (Wasm_int.Int32.repr (enc [::])) (Wasm_int.Int32.repr 24) =
            Wasm_int.Int32.repr 0 by vm_compute.
  have Hl4' : (length (utf16le (snd (step_empty b))) <= 2)%coq_nat := Hl4.
  rewrite E0. split; first by []. split; first by []. split; first by []. split; last lia.
  apply: wr_writes => //. lia.
Qed.

End StepEmpty.
