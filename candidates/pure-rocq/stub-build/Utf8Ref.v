(* Utf8Ref.v: the reference streaming decoder RefDecoder (definitions only).

   Everything here is stated over N byte values (Byte.to_N), following the
   Unicode "well-formed UTF-8 byte sequences" table (Table 3-7):

     lead      second    third   fourth
     00..7F
     C2..DF    80..BF
     E0        A0..BF    80..BF
     E1..EC    80..BF    80..BF
     ED        80..9F    80..BF
     EE..EF    80..BF    80..BF
     F0        90..BF    80..BF  80..BF
     F1..F3    80..BF    80..BF  80..BF
     F4        80..8F    80..BF  80..BF

   State of the decoder: the list of pending bytes (a valid sequence
   prefix that is not yet a whole valid sequence; length 0..3).
   KEEP THESE DEFINITIONS STABLE: a downstream refinement proof uses them. *)

From Stdlib Require Import List NArith Bool.
From Stdlib Require Strings.Byte.
Import Corelib.Init.Byte.
Import ListNotations.
From Utf8 Require Import Utf8Laws.

Local Open Scope N_scope.

Definition bN (b : byte) : N := Byte.to_N b.

(* Expected sequence length from the lead byte value; 0 = not a lead. *)
Definition seq_len (b1 : N) : nat :=
  if b1 <=? 0x7F then 1%nat
  else if (0xC2 <=? b1) && (b1 <=? 0xDF) then 2%nat
  else if (0xE0 <=? b1) && (b1 <=? 0xEF) then 3%nat
  else if (0xF0 <=? b1) && (b1 <=? 0xF4) then 4%nat
  else 0%nat.

(* Range of the second byte, given the lead byte value. *)
Definition lo2 (b1 : N) : N :=
  if b1 =? 0xE0 then 0xA0 else if b1 =? 0xF0 then 0x90 else 0x80.
Definition hi2 (b1 : N) : N :=
  if b1 =? 0xED then 0x9F else if b1 =? 0xF4 then 0x8F else 0xBF.

Definition is_cont (b : byte) : bool := (0x80 <=? bN b) && (bN b <=? 0xBF).

Definition second_ok (b1 b2 : byte) : bool :=
  (lo2 (bN b1) <=? bN b2) && (bN b2 <=? hi2 (bN b1)).

(* Decision procedure for valid sequence prefixes. *)
Definition vp (s : list byte) : bool :=
  match s with
  | [] => false
  | b1 :: r =>
      Nat.ltb 0 (seq_len (bN b1)) && Nat.leb (length s) (seq_len (bN b1)) &&
      match r with
      | [] => true
      | b2 :: r' => second_ok b1 b2 && forallb is_cont r'
      end
  end.

(* Decision procedure for valid sequences. *)
Definition vs (s : list byte) : bool :=
  vp s && match s with
          | [] => false
          | b1 :: _ => Nat.eqb (length s) (seq_len (bN b1))
          end.

(* The code point value of a sequence (meaningful when `vs s = true`):
   the usual combination of the low bits. *)
Definition seq_value (s : list byte) : N :=
  match s with
  | [b1] => bN b1
  | [b1; b2] => (bN b1 mod 32) * 64 + bN b2 mod 64
  | [b1; b2; b3] => ((bN b1 mod 16) * 64 + bN b2 mod 64) * 64 + bN b3 mod 64
  | [b1; b2; b3; b4] =>
      (((bN b1 mod 8) * 64 + bN b2 mod 64) * 64 + bN b3 mod 64) * 64 + bN b4 mod 64
  | _ => 0
  end.

Definition seq_cp (s : list byte) : U32 := U32_of_N (seq_value s).

Definition FFFD : U32 := replacement_char.

(* ---- The per-byte step function ---- *)

Definition State : Type := list byte.

Definition step_empty (b : byte) : State * Text :=
  if vp [b] then
    if vs [b] then ([], [seq_cp [b]]) else ([b], [])
  else ([], [FFFD]).

Definition step (st : State) (b : byte) : State * Text :=
  match st with
  | [] => step_empty b
  | _ =>
      let s := st ++ [b] in
      if vp s then
        if vs s then ([], [seq_cp s]) else (s, [])
      else
        let '(st', o) := step_empty b in (st', FFFD :: o)
  end.

Definition step_acc (acc : State * Text) (b : byte) : State * Text :=
  let '(st, out) := acc in
  let '(st', o) := step st b in (st', out ++ o).

Definition ref_decode_buffer (st : State) (buf : list byte) : State * Text :=
  fold_left step_acc buf (st, []).

Definition ref_done (st : State) : Text :=
  match st with [] => [] | _ => [FFFD] end.

Definition RefDecoder : Decoder := {|
  DecodeState := State;
  decode_start_state := [];
  decode_buffer := ref_decode_buffer;
  decode_done := ref_done
|}.

(* Whole-buffer decoding by the machine. *)
Definition ref_decode (bytes : list byte) : Text :=
  let '(st, out) := ref_decode_buffer [] bytes in out ++ ref_done st.
