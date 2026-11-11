(** WORK IN PROGRESS, NOT PART OF THE BUILD: first sub-block of step_spec.
    Compile from the parent directory:
      rocq c -Q . Decoder -Q ../../pure-rocq Utf8 wip/StepWIP.v *)
From Stdlib Require Import ZArith NArith List Lia.
From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool eqtype seq.
From Wasm Require Import datatypes operations opsem properties.
From Utf8 Require Import Utf8Laws Utf8Ref Utf8Proofs.
From Decoder Require Import Module Steps Control Wp Mem WpMem Instance Boundary Repr Exports Decode.

Section W.
Context `{ho: host}.
Variable hs : host_state.

(** emit_fffd: writes FD FF at o, o += 2. *)
Lemma emit_fffd_ok s1 m1 (l0 l1 l2 : value) (o : Z) junk :
  nth_error s1.(s_mems) 0 = Some m1 ->
  (0 <= o)%Z -> (o + 4 < Wasm_int.Int32.modulus)%Z ->
  (Z.to_N o + 2 <= operations.mem_length m1)%num ->
  exists m2,
    store16_post m1 m2 (Z.to_N o) (Wasm_int.Int32.repr 0xFFFD) /\
    wp hs s1 (Build_frame (l0 :: l1 :: l2 :: vZ o :: junk) inst0) [::] emit_fffd
      (fun s2 f2 stk2 => s2 = upd_mem0 s1 m2 /\
         f2 = Build_frame (l0 :: l1 :: l2 :: vZ (o + 2) :: junk) inst0 /\ stk2 = [::]).
Proof.
  move => Hm Ho Hom Hl.
  have Hk : Wasm_int.N_of_uint i32m (Wasm_int.Int32.repr o) = Z.to_N o.
  { change (Z.to_N (Wasm_int.Int32.unsigned (Wasm_int.Int32.repr o)) = Z.to_N o). rewrite unsigned_small //. lia. }
  have Hb : (N.add (N.add (Wasm_int.N_of_uint i32m (Wasm_int.Int32.repr o)) 0) 2 <=
             operations.mem_length m1)%num by rewrite Hk N.add_0_r.
  case: (store16_spec (Wasm_int.Int32.repr 0xFFFD) Hb) => m2 [Hst Hpost].
  exists m2. split.
  { rewrite -[Z.to_N o]N.add_0_r -Hk. exact Hpost. }
  unfold_code. repeat wp_step.
  apply: (wp_store16_eq (m := m1) (m' := m2)) => //.
  repeat wp_step. split => //. split => //.
  by rewrite /vZ /= i32_iadd_repr.
Qed.


Lemma wasm_bool_nz b : wasm_bool b <> Wasm_int.int_zero i32m -> b = true.
Proof. by case: b. Qed.
Lemma wasm_bool_z b : wasm_bool b = Wasm_int.int_zero i32m -> b = false.
Proof. by case: b. Qed.

Lemma ltu_val a b : (0 <= a < Wasm_int.Int32.modulus)%Z -> (0 <= b < Wasm_int.Int32.modulus)%Z ->
  app_relop (Relop_i (ROI_lt SX_U)) (VAL_int32 (Wasm_int.Int32.repr a)) (VAL_int32 (Wasm_int.Int32.repr b))
  = (a <? b)%Z.
Proof.
  move => Ha Hb. rewrite /app_relop /= /Wasm_int.Int32.ltu !unsigned_small //.
  case: Coqlib.zlt => H; case: Z.ltb_spec => H' //=; lia.
Qed.

(** The ASCII path of empty_code (one of its three paths). *)
Lemma empty_ascii_ok s1 m1 (l0 l1 l2 : value) (o bz : Z) junk :
  nth_error s1.(s_mems) 0 = Some m1 ->
  (0 <= o)%Z -> (o + 4 < Wasm_int.Int32.modulus)%Z ->
  (Z.to_N o + 2 <= operations.mem_length m1)%num ->
  (0 <= bz < 128)%Z ->
  exists m2,
    store16_post m1 m2 (Z.to_N o) (Wasm_int.Int32.repr bz) /\
    wp hs s1 (Build_frame (l0 :: l1 :: l2 :: vZ o :: vZ bz :: junk) inst0) [::] empty_code
      (fun s2 f2 stk2 => stk2 = [::] /\ s2 = upd_mem0 s1 m2 /\
         f2 = Build_frame (l0 :: l1 :: l2 :: vZ (o + 2) :: vZ bz :: junk) inst0).
Proof.
  move => Hm Ho Hom Hl Hb.
  have Hk : Wasm_int.N_of_uint i32m (Wasm_int.Int32.repr o) = Z.to_N o.
  { change (Z.to_N (Wasm_int.Int32.unsigned (Wasm_int.Int32.repr o)) = Z.to_N o). rewrite unsigned_small //. lia. }
  have Hb2 : (N.add (N.add (Wasm_int.N_of_uint i32m (Wasm_int.Int32.repr o)) 0) 2 <=
             operations.mem_length m1)%num by rewrite Hk N.add_0_r.
  case: (store16_spec (Wasm_int.Int32.repr bz) Hb2) => m2 [Hst Hpost].
  exists m2. split.
  { rewrite -[Z.to_N o]N.add_0_r -Hk. exact Hpost. }
  unfold_code. rewrite /vZ. repeat wp_step.
  apply: wp_if => Hc; last first.
  { exfalso. move: (wasm_bool_z _ Hc). rewrite ltu_val; try (rewrite modulus_val; lia).
    move/Z.ltb_ge. lia. }
  repeat wp_step.
  apply: (wp_store16_eq (m := m1) (m' := m2)) => //.
  repeat wp_step. split => //.
  repeat wp_step. split => //. split => //.
  by rewrite /= i32_iadd_repr.
Qed.

Lemma leu_val a b : (0 <= a < Wasm_int.Int32.modulus)%Z -> (0 <= b < Wasm_int.Int32.modulus)%Z ->
  app_relop (Relop_i (ROI_le SX_U)) (VAL_int32 (Wasm_int.Int32.repr a)) (VAL_int32 (Wasm_int.Int32.repr b))
  = (a <=? b)%Z.
Proof.
  move => Ha Hb. rewrite /app_relop /= /Wasm_int.Int32.ltu !unsigned_small //.
  case: Coqlib.zlt => H; case: Z.leb_spec => H' //=; lia.
Qed.

Lemma or_lead_check :
  List.forallb (fun n => Z.eqb (Z.lor (Z.of_nat n) 16777216) (Z.of_nat n + 16777216)) (List.seq 0 256) = true.
Proof. by vm_compute. Qed.

Lemma or_lead a : (0 <= a < 256)%Z ->
  Wasm_int.Int32.or (Wasm_int.Int32.repr a) (Wasm_int.Int32.repr 16777216) =
  Wasm_int.Int32.repr (a + 16777216).
Proof.
  move => Ha. rewrite /Wasm_int.Int32.or !unsigned_small; try (rewrite modulus_val; lia).
  f_equal.
  have Hin : List.In (Z.to_nat a) (List.seq 0 256) by apply List.in_seq; lia.
  have H := proj1 (List.forallb_forall _ _) or_lead_check _ Hin.
  have Ea : Z.of_nat (Z.to_nat a) = a by apply Z2Nat.id; lia.
  rewrite Ea in H. by apply/Z.eqb_eq.
Qed.

(** The lead-byte path of empty_code.  UNFINISHED (Admitted; WIP file only). *)
Lemma empty_lead_ok s1 (l0 l1 l2 : value) (o bz : Z) junk :
  (194 <= bz <= 244)%Z ->
  wp hs s1 (Build_frame (l0 :: l1 :: l2 :: vZ o :: vZ bz :: junk) inst0) [::] empty_code
    (fun s2 f2 stk2 => stk2 = [::] /\ s2 = s1 /\
       f2 = Build_frame (vZ (bz + 16777216) :: l1 :: l2 :: vZ o :: vZ bz :: junk) inst0).
Proof.
  move => Hb.
  unfold_code. rewrite /vZ. repeat wp_step.
  apply: wp_if => Hc.
  { exfalso. move: (wasm_bool_nz _ Hc). rewrite ltu_val; try (rewrite modulus_val; lia).
    move/Z.ltb_lt. lia. }
  repeat wp_step.
  have Ex : Wasm_int.int_sub i32m (Wasm_int.Int32.repr bz) (Wasm_int.Int32.repr 194) = Wasm_int.Int32.repr (bz - 194) := i32_isub_repr _ _. rewrite Ex.
  apply: wp_if => Hc2; last first.
  { exfalso. move: (wasm_bool_z _ Hc2). rewrite leu_val; try (rewrite modulus_val; lia).
    move/Z.leb_gt. lia. }
  repeat wp_step. split; first by [].
  have Eo : Wasm_int.int_or i32m (Wasm_int.Int32.repr bz) (Wasm_int.Int32.repr 16777216) =
            Wasm_int.Int32.repr (bz + 16777216) by apply: or_lead; lia.
  rewrite Eo /=.
  (* UNFINISHED: the final frame equality (`split` fails on the remaining goal with
     "Unable to find an instance for the variable x"; not investigated). *)
  admit.
Admitted.

End W.
