(** * Correctness of the [count_non_ascii] export (a loop over linear memory). *)

From Stdlib Require Import ZArith NArith Lia.
From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool eqtype seq.
From compcert Require Import Integers.
From Wasm Require Import operations opsem properties memory.
From Spike Require Import Spec Module Steps Instance.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Correct.

Context `{ho: host}.

Local Notation vi32 z := (VAL_num (VAL_int32 (Wasm_int.Int32.repr z))).

(** [bytes_at m p bs]: the bytes [bs] are stored in memory [m] starting
    at address [p]. *)
Fixpoint bytes_at (m : meminst) (p : N) (bs : list byte) : Prop :=
  match bs with
  | [::] => True
  | b :: rest => mem_lookup p m.(meminst_data) = Some b /\ bytes_at m (N.add p 1) rest
  end.

(** ** Arithmetic facts about i32 *)

Lemma i32_unsigned_repr z : (0 <= z < Wasm_int.Int32.modulus)%Z -> Wasm_int.Int32.unsigned (Wasm_int.Int32.repr z) = z.
Proof.
  move => H; apply Wasm_int.Int32.unsigned_repr.
  rewrite /Wasm_int.Int32.max_unsigned; lia.
Qed.

Lemma i32_add_repr a b : Wasm_int.Int32.add (Wasm_int.Int32.repr a) (Wasm_int.Int32.repr b) = Wasm_int.Int32.repr (a + b).
Proof.
  rewrite /Wasm_int.Int32.add; apply Wasm_int.Int32.eqm_samerepr, Wasm_int.Int32.eqm_add; apply Wasm_int.Int32.eqm_sym, Wasm_int.Int32.eqm_unsigned_repr.
Qed.

Lemma i32_sub_repr a b : Wasm_int.Int32.sub (Wasm_int.Int32.repr a) (Wasm_int.Int32.repr b) = Wasm_int.Int32.repr (a - b).
Proof.
  rewrite /Wasm_int.Int32.sub; apply Wasm_int.Int32.eqm_samerepr, Wasm_int.Int32.eqm_sub; apply Wasm_int.Int32.eqm_sym, Wasm_int.Int32.eqm_unsigned_repr.
Qed.

Lemma wasm_bool_repr b : wasm_bool b = Wasm_int.Int32.repr (if b then 1%Z else 0%Z).
Proof. by case: b. Qed.

(** One loaded byte, zero-extended, compared with 0x80. *)
Lemma load_byte_value b :
  wasm_deserialise (sign_extend_bytes SX_U 4 [:: b]) T_i32 = VAL_int32 (Wasm_int.Int32.repr (Byte.unsigned b)).
Proof.
  rewrite /wasm_deserialise /sign_extend_bytes /=.
  do 2 f_equal.
  rewrite /common.Memdata.decode_int /common.Memdata.rev_if_be.
  Local Transparent Archi.big_endian.
  rewrite /Archi.big_endian /=.
  have -> : Byte.unsigned #00 = 0%Z by [].
  lia.
Qed.

Lemma ge_0x80 b :
  wasm_bool (~~ Wasm_int.Int32.ltu (Wasm_int.Int32.repr (Byte.unsigned b)) (Wasm_int.Int32.repr 128))
  = Wasm_int.Int32.repr (if is_non_ascii b then 1%Z else 0%Z).
Proof.
  have R := Byte.unsigned_range b.
  have Hm : Byte.modulus = 256%Z by [].
  have HM : Wasm_int.Int32.modulus = 4294967296%Z by [].
  rewrite /Wasm_int.Int32.ltu /is_non_ascii !i32_unsigned_repr; try lia.
  case: Coqlib.zlt => H; case: Z.leb_spec => H' //=; lia.
Qed.

Lemma eqz_nonzero n : (0 < n < Wasm_int.Int32.modulus)%Z ->
  wasm_bool (app_testop_i i32m TO_eqz (Wasm_int.Int32.repr n)) = Wasm_int.int_zero i32m.
Proof.
  move => H.
  have Hu : Wasm_int.Int32.unsigned (Wasm_int.Int32.repr n) = n by apply i32_unsigned_repr; lia.
  rewrite /= /Wasm_int.Int32.eq Hu Wasm_int.Int32.unsigned_zero.
  by case: Coqlib.zeq => //; lia.
Qed.

(** ** The loop *)

Definition frame_of (p : Wasm_int.Int32.int) (n acc : nat) : frame :=
  Build_frame [:: VAL_num (VAL_int32 p); vi32 (Z.of_nat n); vi32 (Z.of_nat acc)] inst0.

Variable hs : host_state.
Variable s : store_record.
Variable m : meminst.
Hypothesis Hmem : smem s inst0 = Some m.
Variable total : nat.   (* = count_non_ascii of the whole input *)

(** Loop invariant: [rest] are the bytes still to be read at [p], the
    accumulator plus the count of [rest] is the total. *)
Definition inv (n : nat) (s' : store_record) (f : frame) : Prop :=
  s' = s /\ exists p rest acc,
    n = size rest /\
    (Wasm_int.Int32.unsigned p + Z.of_nat (size rest) <= Wasm_int.Int32.modulus)%Z /\
    (Z.of_nat (size rest) < Wasm_int.Int32.modulus)%Z /\
    bytes_at m (Z.to_N (Wasm_int.Int32.unsigned p)) rest /\
    (acc + count_non_ascii rest)%nat = total /\
    f = frame_of p (size rest) acc.

Definition post (s' : store_record) (f : frame) : Prop :=
  s' = s /\ exists p, f = frame_of p 0 total.

Lemma exec_nil_eq2 s1 f1 f2 stk1 stk2 :
  f1 = f2 -> stk1 = stk2 -> exec hs s1 f1 stk1 [::] s1 f2 stk2.
Proof. by move => -> ->; apply exec_nil. Qed.

Lemma lookup_in_bounds p b : mem_lookup p m.(meminst_data) = Some b ->
  N.le (N.add p 1) (operations.mem_length m).
Proof.
  move => H.
  case: (N.le_gt_cases (p + 1) (operations.mem_length m)) => // Hgt.
  rewrite mem_lookup_oob in H => //.
  rewrite /operations.mem_length in Hgt. lia.
Qed.

Lemma count_loop_iteration n s' f :
  inv n s' f ->
  (exists n' s'' f', (n' < n)%coq_nat /\ exec_br hs s' f [::] count_loop_body s'' f' (0 : N) /\ inv n' s'' f') \/
  (exists s'' f', exec_br hs s' f [::] count_loop_body s'' f' (1 : N) /\ post s'' f').
Proof.
  move => [-> [p [rest [acc [-> [Hbound [Hsize [Hbytes [Hacc ->]]]]]]]]].
  case: rest Hbound Hbytes Hacc Hsize => [| b rest] Hbound Hbytes Hacc Hsize.
  - (* exit *)
    right. exists s, (frame_of p 0 acc); split.
    + have -> : count_loop_body = count_exit_test ++ (count_step ++ [:: BI_br (0 : N)]) by [].
      apply exec_br_prefix.
      eapply exec_then_br with (b1 := [:: BI_local_get (1 : N); BI_testop T_i32 TO_eqz]).
      * eapply exec_cons; first by apply exec_local_get.
        eapply exec_cons; first by apply exec_testop_i32.
        by apply exec_nil.
      * by apply exec_br_if_true.
    + split => //. exists p. by rewrite /= addn0 in Hacc; rewrite Hacc.
  - (* one more byte *)
    left.
    case: Hbytes => [Hb Hrest].
    set k := Z.to_N (Wasm_int.Int32.unsigned p) in Hb Hrest.
    have Hin := lookup_in_bounds Hb.
    have Hp1 : (Wasm_int.Int32.unsigned p + 1 < Wasm_int.Int32.modulus)%Z \/ rest = [::].
    { destruct rest as [|? ?]; [by right | left; rewrite /= in Hbound; lia]. }
    set acc' := (acc + (if is_non_ascii b then 1 else 0))%nat.
    set p' := Wasm_int.Int32.add p (Wasm_int.Int32.repr 1).
    exists (size rest), s, (frame_of p' (size rest) acc').
    split; first by rewrite /=; lia.
    split.
    + have -> : count_loop_body = (count_exit_test ++ count_step) ++ [:: BI_br (0 : N)] by [].
      apply exec_then_br with (s1 := s) (f1 := frame_of p' (size rest) acc') (stk1 := [::]);
        last by apply exec_br_br.
      eapply exec_app with (b1 := count_exit_test).
      { eapply exec_cons; first by apply exec_local_get.
        eapply exec_cons; first by apply exec_testop_i32.
        have Hpos : (0 < Z.of_nat (size (b :: rest)) < Wasm_int.Int32.modulus)%Z
          by rewrite /= in Hsize *; lia.
        rewrite (eqz_nonzero Hpos).
        eapply exec_cons; first by apply exec_br_if_false.
        by apply exec_nil. }
      rewrite /count_step.
      eapply exec_cons; first by apply exec_local_get.
      eapply exec_cons; first by apply exec_local_get.
      eapply exec_cons.
      { apply exec_load_packed with (m := m) (bs := sign_extend_bytes SX_U 4 [:: b]) => //.
        have Hk : Wasm_int.N_of_uint i32m p = k by [].
        rewrite /load_packed /load Hk /=.
        case: N.leb_spec => Hle; last lia.
        have Hr : read_bytes m (k + 0) 1 = Some [:: b].
        { rewrite /read_bytes /= !N.add_0_r Hb //. }
        by rewrite Hr. }
      rewrite load_byte_value.
      eapply exec_cons; first by apply exec_const.
      eapply exec_cons; first by apply exec_relop.
      eapply exec_cons; first by apply exec_binop.
      eapply exec_cons; first by apply exec_local_set.
      eapply exec_cons; first by apply exec_local_get.
      eapply exec_cons; first by apply exec_const.
      eapply exec_cons; first by apply exec_binop.
      eapply exec_cons; first by apply exec_local_set.
      eapply exec_cons; first by apply exec_local_get.
      eapply exec_cons; first by apply exec_const.
      eapply exec_cons; first by apply exec_binop.
      eapply exec_cons; first by apply exec_local_set.
      apply exec_nil_eq2 => //.
      rewrite /frame_of /= /p' /Wasm_int.Int32.iadd /Wasm_int.Int32.isub ge_0x80 !i32_add_repr i32_sub_repr.
      have E1 : (Z.pos (Pos.of_succ_nat (size rest)) - 1 = Z.of_nat (size rest))%Z by lia.
      have E2 : (Z.of_nat acc + (if is_non_ascii b then 1 else 0) = Z.of_nat acc')%Z
        by rewrite /acc' /addn /addn_rec; case: (is_non_ascii b); lia.
      by rewrite E1 E2.
    + split => //.
      have Hpu : (Wasm_int.Int32.unsigned p + 1 < Wasm_int.Int32.modulus)%Z ->
                 Wasm_int.Int32.unsigned p' = (Wasm_int.Int32.unsigned p + 1)%Z.
      { move => H. rewrite /p' /Wasm_int.Int32.add.
        have -> : Wasm_int.Int32.unsigned (Wasm_int.Int32.repr 1) = 1%Z by [].
        apply i32_unsigned_repr. have := Wasm_int.Int32.unsigned_range p. lia. }
      have Rp := Wasm_int.Int32.unsigned_range p.
      have Rp' := Wasm_int.Int32.unsigned_range p'.
      exists p', rest, acc'.
      split; first by [].
      split.
      { case: Hp1 => [H|->]; last by move: Rp'; rewrite /=; lia.
        rewrite Hpu //. rewrite /= in Hbound. lia. }
      split; first by rewrite /= in Hsize; lia.
      split.
      { case: Hp1 => [H|->] //.
        rewrite Hpu //.
        have -> : Z.to_N (Wasm_int.Int32.unsigned p + 1) = N.add k 1 by rewrite /k; lia.
        exact Hrest. }
      split; last by [].
      rewrite /acc' -Hacc /= /addn /addn_rec. lia.
Qed.

(** ** The function body and the export *)

Lemma count_body_correct ptr bs :
  bytes_at m (Z.to_N (Wasm_int.Int32.unsigned ptr)) bs ->
  (Wasm_int.Int32.unsigned ptr + Z.of_nat (size bs) <= Wasm_int.Int32.modulus)%Z ->
  (Z.of_nat (size bs) < Wasm_int.Int32.modulus)%Z ->
  total = count_non_ascii bs ->
  exists f',
    exec hs s (Build_frame [:: VAL_num (VAL_int32 ptr); vi32 (Z.of_nat (size bs)); vi32 0] inst0)
      [::] count_body s f' [:: vi32 (Z.of_nat total)].
Proof.
  move => Hbytes Hbound Hsz Htotal.
  have HP : inv (size bs) s (frame_of ptr (size bs) 0).
  { split => //. exists ptr, bs, 0%nat.
    by do 5 (split => //); rewrite Htotal. }
  have [s' [f' [Hloop [Hs [p Hf]]]]] :=
    @block_loop_rule _ _ _ hs count_loop_body inv post count_loop_iteration (size bs) s _ [::] HP.
  subst s' f'.
  exists (frame_of p 0 total).
  have -> : count_body = BI_block BT_none [:: BI_loop BT_none count_loop_body] :: [:: BI_local_get 2] by [].
  eapply exec_cons; first by apply Hloop.
  eapply exec_cons; first by apply exec_local_get.
  by apply exec_nil.
Qed.

End Correct.

(** Invocation on ANY store in which function address 1 holds the
    module's second closure and the module's memory is [m], with the
    input bytes [bs] stored at [ptr]. *)
Theorem count_non_ascii_invoke `{ho: host} hs s f0 m (ptr len : i32) bs :
  lookup_N s.(s_funcs) 1 = Some count_closure ->
  smem s inst0 = Some m ->
  bytes_at m (Z.to_N (Wasm_int.Int32.unsigned ptr)) bs ->
  Z.of_nat (size bs) = Wasm_int.Int32.unsigned len ->
  (Wasm_int.Int32.unsigned ptr + Wasm_int.Int32.unsigned len <= Wasm_int.Int32.modulus)%Z ->
  reduce_trans
    (hs, s, f0, [:: AI_basic (BI_const_num (VAL_int32 ptr));
                   AI_basic (BI_const_num (VAL_int32 len)); AI_invoke (1 : N)])
    (hs, s, f0, [:: AI_basic (BI_const_num
                     (VAL_int32 (Wasm_int.Int32.repr (Z.of_nat (count_non_ascii bs)))))]).
Proof.
  move => Hcl Hmem Hbytes Hlen Hbound.
  have Hlen' : len = Wasm_int.Int32.repr (Z.of_nat (size bs))
    by rewrite Hlen Wasm_int.Int32.repr_unsigned.
  have Hsz : (Z.of_nat (size bs) < Wasm_int.Int32.modulus)%Z
    by rewrite Hlen; have := Wasm_int.Int32.unsigned_range len; lia.
  have [f' Hbody] := @count_body_correct _ _ _ hs s m Hmem _ ptr bs Hbytes
                       ltac:(rewrite Hlen; lia) Hsz erefl.
  rewrite Hlen'.
  eapply invoke_rule with
    (args := [:: VAL_num (VAL_int32 ptr); VAL_num (VAL_int32 (Wasm_int.Int32.repr (Z.of_nat (size bs))))])
    (res := [:: VAL_num (VAL_int32 (Wasm_int.Int32.repr (Z.of_nat (count_non_ascii bs))))])
    (defs := [:: VAL_num (VAL_int32 (Wasm_int.Int32.repr 0))]);
    [ exact Hcl | done | done | done | ].
  exact Hbody.
Qed.
