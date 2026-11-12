(** * OutBound.v: facts about [utf16le] (Boundary.v's output encoding) and
    how many output bytes RefDecoder can produce.

    Pure (no Wasm semantics).  The counting itself is in the pure layer
    (../../pure-rocq/Utf8StepFacts.v: [text_units], [pending_units],
    [step_units_bound], [decode_units_bound]); this file only converts
    UTF-16 code units to bytes ([utf16le_length]: 2 bytes per unit).

    Exports:
    - [pend st]: 0 if no bytes are pending, else 2 (the byte "credit" that
      pending bytes carry: they can later turn into at most one extra
      UTF-16 unit, a U+FFFD or the second unit of a surrogate pair);
      [pend_le2], [pend_units] (pend = 2 * pending_units).
    - [utf16le_app], [utf16le_one_length], [utf16le_length], [utf16le_one_len] (one code point is
      at most 4 bytes).
    - [step_out_bound]: one byte gives |utf16le out| + pend st' <= 2 + pend st.
    - [decode_out_bound]: any input [bs] gives
        |utf16le out| + pend st' <= 2 * |bs| + pend st  (<= 2 * |bs| + 2);
      [decode_out_area]: the same against Boundary.v's [out_area].
    - [ref_done_out_bound]: [ref_done] gives at most 2 output bytes. *)

From Stdlib Require Import List NArith Lia.
From Stdlib Require Strings.Byte.
From Utf8 Require Import Utf8Laws Utf8Ref Utf8Proofs Utf8StepFacts.
From Decoder Require Import Boundary.
Import ListNotations.

Definition pend (st : State) : nat := match st with [] => 0 | _ => 2 end.

Lemma pend_le2 st : (pend st <= 2)%nat.
Proof. destruct st; cbn; lia. Qed.

Lemma pend_units st : pend st = (2 * pending_units st)%nat.
Proof. destruct st; reflexivity. Qed.

Lemma utf16le_app t1 t2 : utf16le (t1 ++ t2) = utf16le t1 ++ utf16le t2.
Proof. unfold utf16le. rewrite !flat_map_app. reflexivity. Qed.

Lemma utf16le_one_length u : length (utf16le [u]) = (2 * cp_units u)%nat.
Proof.
  unfold utf16le, utf16_units, cp_units. cbn [flat_map]. rewrite app_nil_r.
  destruct (_ <? _)%N; reflexivity.
Qed.

Lemma utf16le_length t : length (utf16le t) = (2 * text_units t)%nat.
Proof.
  induction t as [|u t IH]; [reflexivity|].
  change (u :: t) with ([u] ++ t).
  rewrite utf16le_app, length_app, IH, utf16le_one_length. cbn [app text_units]. lia.
Qed.

Lemma utf16le_one_len u : (length (utf16le [u]) <= 4)%nat.
Proof. rewrite utf16le_length. cbn [text_units]. pose proof (cp_units_le2 u). lia. Qed.

Lemma step_out_bound st b :
  (length (utf16le (snd (step st b))) + pend (fst (step st b)) <= 2 + pend st)%nat.
Proof. rewrite utf16le_length, !pend_units. pose proof (step_units_bound st b). lia. Qed.

Theorem decode_out_bound st bs :
  let '(st', t) := ref_decode_buffer st bs in
  (length (utf16le t) + pend st' <= 2 * length bs + pend st)%nat.
Proof.
  pose proof (decode_units_bound st bs) as H.
  destruct (ref_decode_buffer st bs) as [st' t].
  rewrite utf16le_length, !pend_units. lia.
Qed.

(** The form used by the boundary statement: at most 2 bytes per input
    byte, plus 2 ([out_area] in Boundary.v). *)
Corollary decode_out_area st bs :
  (N.of_nat (length (utf16le (snd (ref_decode_buffer st bs)))) <= out_area (length bs))%N.
Proof.
  pose proof (decode_out_bound st bs) as H. pose proof (pend_le2 st).
  destruct (ref_decode_buffer st bs) as [st' t]. cbn [snd]. unfold out_area. lia.
Qed.

Lemma ref_done_out_bound st : (N.of_nat (length (utf16le (ref_done st))) <= out_area 0)%N.
Proof.
  rewrite utf16le_length. pose proof (ref_done_units_bound st). unfold out_area. lia.
Qed.
