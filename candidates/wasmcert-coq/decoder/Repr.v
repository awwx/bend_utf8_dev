(** * The state representation: RefDecoder's pending-byte list packed in
    an i32 (b1 | b2 << 8 | b3 << 16 | n << 24). *)

From Stdlib Require Import ZArith NArith List Lia.
From Stdlib Require Strings.Byte.
From Wasm Require Import numerics.
From Utf8 Require Import Utf8Laws Utf8Ref Utf8Proofs.
From SymExec Require Import I32.
Import ListNotations.

Definition bZ (b : Byte.byte) : Z := Z.of_N (Byte.to_N b).

Definition enc (st : list Byte.byte) : Z :=
  match st with
  | [] => 0
  | [b1] => bZ b1 + 1 * 16777216
  | [b1; b2] => bZ b1 + bZ b2 * 256 + 2 * 16777216
  | [b1; b2; b3] => bZ b1 + bZ b2 * 256 + bZ b3 * 65536 + 3 * 16777216
  | _ => 0
  end%Z.

Definition Rst (st : State) (v : Wasm_int.Int32.int) : Prop :=
  Inv st /\ v = Wasm_int.Int32.repr (enc st).

Lemma bZ_range b : (0 <= bZ b < 256)%Z.
Proof. unfold bZ. destruct b; vm_compute; split; congruence. Qed.

Lemma enc_range st : (0 <= enc st < 67108864)%Z.
Proof.
  destruct st as [|b1 [|b2 [|b3 [|b4 r]]]]; cbn [enc];
    try pose proof (bZ_range b1); try pose proof (bZ_range b2); try pose proof (bZ_range b3); lia.
Qed.

Lemma enc_zero st : Inv st -> (enc st = 0 <-> st = [])%Z.
Proof.
  intros HI. pose proof (Inv_len st HI).
  destruct st as [|b1 [|b2 [|b3 [|b4 r]]]]; cbn [enc length] in *;
    try pose proof (bZ_range b1); try pose proof (bZ_range b2); try pose proof (bZ_range b3);
    split; intros; try discriminate; try lia; try reflexivity.
Qed.

Lemma bN_bZ b : bZ b = Z.of_N (bN b).
Proof. reflexivity. Qed.

Lemma bN_lt b : (bN b < 256)%N.
Proof. pose proof (bZ_range b). unfold bZ in H. unfold bN. lia. Qed.

Lemma small_byte b : small (bZ b).
Proof. pose proof (bZ_range b). unfold small. rewrite modulus_val. lia. Qed.

Lemma small_enc st : small (enc st).
Proof. pose proof (enc_range st). unfold small. rewrite modulus_val. lia. Qed.
