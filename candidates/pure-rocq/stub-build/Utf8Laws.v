(* Utf8Laws.v: a Rocq translation of LAWS.bend, the specification of
   UTF-8 decoding with U+FFFD replacement of maximal subparts, and of a
   streaming decoder.

   This file holds definitions and statements only.  Each Bend `law`
   becomes a `Definition <name> : Prop := ...` stating the law; proofs
   live elsewhere (as LAWS.bend vs PROOF.bend).

   Translation conventions (TRANSLATION.txt has the full record):

   - A Bend name `f.g` becomes `f_g`.  The one clash this causes, the
     def `decodes_first.nonempty` vs the law `decodes_first_nonempty`, is
     resolved by naming the def `decodes_first_nonempty_case`.
   - Bend's `Type`-valued propositions become `Prop`: `Exists` is
     `exists`, `Or` is `\/`, `&` (between propositions) is `/\`,
     `-> Empty` is `-> False`, and `{a == b : T}` is `a = b`.  A Bend
     `law` with `for x: T` premises becomes a `forall`.
   - Bytes are the standard library's `byte` (Corelib's `Init.Byte`)
     instead of U32 values with a separate 0..255 range proof, so
     LAWS.bend's `all_bytes`, `utf8_decode_buffer_all_bytes`,
     `all_buffers_bytes` and its helpers, and the erased `valid`
     arguments are absent.
   - Code points are `U32` below: 32 booleans, least significant bit
     first, the same representation as Bend's `U32{Word(32n)}`.
   - Text (Bend's `String`, a list of `Chr{U32}`) is `Text`, a list of
     code points with no scalar-value restriction.
   - The streaming laws are stated over an abstract `Decoder` instead
     of the implementation module `UTF8`. *)

From Stdlib Require Import List NArith Bool.
From Stdlib Require Strings.Byte Strings.Ascii.
Import Corelib.Init.Byte.
Import ListNotations.

Local Open Scope N_scope.


(** * Counterparts of the Bend Base definitions that LAWS.bend uses *)

(* Bend's `U32` is `U32{Word(32n)}`, and a `Word` stores its least
   significant bit first: `b0` below is bit 0 and `b31` is bit 31. *)

Inductive U32 : Set :=
  U32_bits (b0 b1 b2 b3 b4 b5 b6 b7
            b8 b9 b10 b11 b12 b13 b14 b15
            b16 b17 b18 b19 b20 b21 b22 b23
            b24 b25 b26 b27 b28 b29 b30 b31 : bool).

(* The value of a U32 as a binary number: bit `i` has weight 2^i.
   (Base's `U32.to_nat`, with `N` for `Nat`.) *)

Definition U32_to_N (x : U32) : N :=
  match x with
  | U32_bits b0 b1 b2 b3 b4 b5 b6 b7
             b8 b9 b10 b11 b12 b13 b14 b15
             b16 b17 b18 b19 b20 b21 b22 b23
             b24 b25 b26 b27 b28 b29 b30 b31 =>
      N.b2n b0 + 2 * (N.b2n b1 + 2 * (N.b2n b2 + 2 * (N.b2n b3 +
      2 * (N.b2n b4 + 2 * (N.b2n b5 + 2 * (N.b2n b6 + 2 * (N.b2n b7 +
      2 * (N.b2n b8 + 2 * (N.b2n b9 + 2 * (N.b2n b10 + 2 * (N.b2n b11 +
      2 * (N.b2n b12 + 2 * (N.b2n b13 + 2 * (N.b2n b14 + 2 * (N.b2n b15 +
      2 * (N.b2n b16 + 2 * (N.b2n b17 + 2 * (N.b2n b18 + 2 * (N.b2n b19 +
      2 * (N.b2n b20 + 2 * (N.b2n b21 + 2 * (N.b2n b22 + 2 * (N.b2n b23 +
      2 * (N.b2n b24 + 2 * (N.b2n b25 + 2 * (N.b2n b26 + 2 * (N.b2n b27 +
      2 * (N.b2n b28 + 2 * (N.b2n b29 + 2 * (N.b2n b30 + 2 * (N.b2n b31
      )))))))))))))))))))))))))))))))
  end.

(* The U32 whose bits are the low 32 bits of `n`, i.e. `n` modulo
   2^32.  This stands for Bend's U32 numeric literals and for
   `Char.to_u32('\u{...}')` of a character literal; every value it is
   applied to in this file is below 2^32. *)

Definition U32_of_N (n : N) : U32 :=
  U32_bits
    (N.testbit n 0) (N.testbit n 1) (N.testbit n 2) (N.testbit n 3)
    (N.testbit n 4) (N.testbit n 5) (N.testbit n 6) (N.testbit n 7)
    (N.testbit n 8) (N.testbit n 9) (N.testbit n 10) (N.testbit n 11)
    (N.testbit n 12) (N.testbit n 13) (N.testbit n 14) (N.testbit n 15)
    (N.testbit n 16) (N.testbit n 17) (N.testbit n 18) (N.testbit n 19)
    (N.testbit n 20) (N.testbit n 21) (N.testbit n 22) (N.testbit n 23)
    (N.testbit n 24) (N.testbit n 25) (N.testbit n 26) (N.testbit n 27)
    (N.testbit n 28) (N.testbit n 29) (N.testbit n 30) (N.testbit n 31).

(* Unsigned comparisons of U32 values (Base's `U32.is_le` and
   `U32.is_ge`). *)

Definition U32_is_le (a b : U32) : bool := N.leb (U32_to_N a) (U32_to_N b).

Definition U32_is_ge (a b : U32) : bool := N.leb (U32_to_N b) (U32_to_N a).

(* Base's `Maybe.is_some`. *)

Definition Maybe_is_some {A : Type} (m : option A) : bool :=
  match m with
  | None => false
  | Some _ => true
  end.

(* Bend's `String` is a list of `Chr{U32}`: a list of code points, with
   no restriction to Unicode scalar values.  `Text` is that list.
   Bend's string `++` is list `++`. *)

Definition Text : Type := list U32.


(** ** Bits to bytes helper *)

(* Type alias for a tuple of eight bools. *)

Definition Bit8 : Type :=
  bool * bool * bool * bool * bool * bool * bool * bool.

(* Given a tuple of eight bools, return the byte whose value is the
   binary integer, most significant bit first.  (`Byte.of_bits` takes
   its bits least significant first.) *)

Definition bit8_value (bit8 : Bit8) : byte :=
  let '(b7, b6, b5, b4, b3, b2, b1, b0) := bit8 in
  Byte.of_bits (b0, (b1, (b2, (b3, (b4, (b5, (b6, b7))))))).

(* Given 8 booleans used as bits, most significant bit first, convert
   to its byte value 0..255. *)

Definition bit8_value_sum : Prop :=
  forall b7 b6 b5 b4 b3 b2 b1 b0 : bool,
    Byte.to_N (bit8_value (b7, b6, b5, b4, b3, b2, b1, b0)) =
      N.b2n b7 * 128 +
      N.b2n b6 * 64 +
      N.b2n b5 * 32 +
      N.b2n b4 * 16 +
      N.b2n b3 * 8 +
      N.b2n b2 * 4 +
      N.b2n b1 * 2 +
      N.b2n b0 * 1.

(* Provide an independent check of `bit8_value`: convert the booleans
   to a list of bits, then to an N, and then to a byte. *)

Definition bit8_value_word : Prop :=
  forall b7 b6 b5 b4 b3 b2 b1 b0 : bool,
    (* The list stores its least significant bit first, as
       `Ascii.N_of_digits` reads it. *)
    let word := [b0; b1; b2; b3; b4; b5; b6; b7] in
    Some (bit8_value (b7, b6, b5, b4, b3, b2, b1, b0)) =
      Byte.of_N (Ascii.N_of_digits word).


(** ** U32 to four bytes helper *)

(* Bits are grouped into bytes, most significant byte and bit first. *)

Definition Byte4 : Type := Bit8 * Bit8 * Bit8 * Bit8.

(* Split a U32 into its four bytes, most significant byte first, each
   as eight bools, most significant bit first. *)

Definition u32_byte4 (value : U32) : Byte4 :=
  match value with
  | U32_bits b0 b1 b2 b3 b4 b5 b6 b7
             b8 b9 b10 b11 b12 b13 b14 b15
             b16 b17 b18 b19 b20 b21 b22 b23
             b24 b25 b26 b27 b28 b29 b30 b31 =>
      ((b31, b30, b29, b28, b27, b26, b25, b24),
       (b23, b22, b21, b20, b19, b18, b17, b16),
       (b15, b14, b13, b12, b11, b10, b9, b8),
       (b7, b6, b5, b4, b3, b2, b1, b0))
  end.

(* Bit 31 is the first bool of the first byte, and bit 0 the last bool
   of the last byte. *)

Definition u32_byte4_bits : Prop :=
  forall b31 b30 b29 b28 b27 b26 b25 b24
         b23 b22 b21 b20 b19 b18 b17 b16
         b15 b14 b13 b12 b11 b10 b9 b8
         b7 b6 b5 b4 b3 b2 b1 b0 : bool,
    u32_byte4 (U32_bits b0 b1 b2 b3 b4 b5 b6 b7
                        b8 b9 b10 b11 b12 b13 b14 b15
                        b16 b17 b18 b19 b20 b21 b22 b23
                        b24 b25 b26 b27 b28 b29 b30 b31) =
      ((b31, b30, b29, b28, b27, b26, b25, b24),
       (b23, b22, b21, b20, b19, b18, b17, b16),
       (b15, b14, b13, b12, b11, b10, b9, b8),
       (b7, b6, b5, b4, b3, b2, b1, b0)).


(** * UTF-8 encoding specification *)

(** ** Surrogate code points *)

(* Surrogate code points are U+D800..U+DFFF. *)

Definition is_surrogate_code_point (cp : U32) : bool :=
  U32_is_ge cp (U32_of_N 0xD800) &&
  U32_is_le cp (U32_of_N 0xDFFF).

Definition is_surrogate_code_point_examples : Prop :=
  is_surrogate_code_point (U32_of_N 0x0000) = false /\
  is_surrogate_code_point (U32_of_N 0xD7FF) = false /\
  is_surrogate_code_point (U32_of_N 0xD800) = true /\
  is_surrogate_code_point (U32_of_N 0xDC00) = true /\
  is_surrogate_code_point (U32_of_N 0xDFFF) = true /\
  is_surrogate_code_point (U32_of_N 0xE000) = false.


(** ** Unicode scalars *)

(* A Unicode scalar is any code point from U+0000 to U+10FFFF excluding
   surrogate code points. *)

Definition is_unicode_scalar (cp : U32) : bool :=
  U32_is_ge cp (U32_of_N 0x000000) &&
  U32_is_le cp (U32_of_N 0x10FFFF) &&
  negb (is_surrogate_code_point cp).


(** ** Byte shapes *)

(* By a "byte shape" we mean a series of bytes that has the correct bit
   pattern for a UTF-8 encoding.  This includes invalid UTF-8 encodings
   such as overlong encodings, encodings of surrogate code points, and
   encodings of code point values above U+10FFFF. *)

(* UTF-8 one-byte shape

   00000000 00000000 00000000 0yyyzzzz -> 0yyyzzzz

   Returns Some byte if the shape matches, or None if the shape doesn't
   match. *)

Definition one_byte_shape_bits (bits : Byte4) : option byte :=
  match bits with
  | ((false, false, false, false, false, false, false, false),
     (false, false, false, false, false, false, false, false),
     (false, false, false, false, false, false, false, false),
     (false, y1, y2, y3, z1, z2, z3, z4)) =>
      Some (bit8_value (false, y1, y2, y3, z1, z2, z3, z4))
  | _ =>
      None
  end.

Definition one_byte_shape (cp : U32) : option byte :=
  one_byte_shape_bits (u32_byte4 cp).

(* UTF-8 two-byte shape

   00000000 00000000 00000xxx yyyyzzzz -> 110xxxyy 10yyzzzz

   Returns the two bytes if the shape matches, or None if the shape
   doesn't match.

   Capacity includes overlong encodings of 0..127; shortest-form
   validity is separate. *)

Definition two_byte_shape_bits (bits : Byte4) : option (byte * byte) :=
  match bits with
  | ((false, false, false, false, false, false, false, false),
     (false, false, false, false, false, false, false, false),
     (false, false, false, false, false, x1, x2, x3),
     (y1, y2, y3, y4, z1, z2, z3, z4)) =>
      Some (bit8_value (true, true, false, x1, x2, x3, y1, y2),
            bit8_value (true, false, y3, y4, z1, z2, z3, z4))
  | _ =>
      None
  end.

Definition two_byte_shape (cp : U32) : option (byte * byte) :=
  two_byte_shape_bits (u32_byte4 cp).

(* UTF-8 three-byte shape

   00000000 00000000 wwwwxxxx yyyyzzzz -> 1110wwww 10xxxxyy 10yyzzzz

   Returns the three bytes if the shape matches, or None if the shape
   doesn't match.

   Capacity includes overlong encodings of 0..2047 and encodings of
   surrogate code points; validity is separate. *)

Definition three_byte_shape_bits (bits : Byte4) : option (byte * byte * byte) :=
  match bits with
  | ((false, false, false, false, false, false, false, false),
     (false, false, false, false, false, false, false, false),
     (w1, w2, w3, w4, x1, x2, x3, x4),
     (y1, y2, y3, y4, z1, z2, z3, z4)) =>
      Some (bit8_value (true, true, true, false, w1, w2, w3, w4),
            bit8_value (true, false, x1, x2, x3, x4, y1, y2),
            bit8_value (true, false, y3, y4, z1, z2, z3, z4))
  | _ =>
      None
  end.

Definition three_byte_shape (cp : U32) : option (byte * byte * byte) :=
  three_byte_shape_bits (u32_byte4 cp).

(* UTF-8 four-byte shape

   00000000 000uvvvv wwwwxxxx yyyyzzzz -> 11110uvv 10vvwwww 10xxxxyy 10yyzzzz

   Returns the four bytes if the shape matches, or None if the shape
   doesn't match.

   Capacity includes overlong encodings of 0..65535 and encodings of
   code point values above U+10FFFF; validity is separate. *)

Definition four_byte_shape_bits (bits : Byte4) : option (byte * byte * byte * byte) :=
  match bits with
  | ((false, false, false, false, false, false, false, false),
     (false, false, false, u, v1, v2, v3, v4),
     (w1, w2, w3, w4, x1, x2, x3, x4),
     (y1, y2, y3, y4, z1, z2, z3, z4)) =>
      Some (bit8_value (true, true, true, true, false, u, v1, v2),
            bit8_value (true, false, v3, v4, w1, w2, w3, w4),
            bit8_value (true, false, x1, x2, x3, x4, y1, y2),
            bit8_value (true, false, y3, y4, z1, z2, z3, z4))
  | _ =>
      None
  end.

Definition four_byte_shape (cp : U32) : option (byte * byte * byte * byte) :=
  four_byte_shape_bits (u32_byte4 cp).


(** ** Encoding *)

(* The UTF-8 encoding of `cp` is its shortest byte shape: one byte when
   `cp` has a one-byte shape, otherwise two, three or four.  (A longer
   encoding of a code point that has a shorter shape would be overlong.)
   Code points above U+1FFFFF have no encoding. *)

Definition encoding_four (shape : option (byte * byte * byte * byte)) : option (list byte) :=
  match shape with
  | None =>
      None
  | Some (b1, b2, b3, b4) =>
      Some [b1; b2; b3; b4]
  end.

Definition encoding_three (cp : U32) (shape : option (byte * byte * byte)) : option (list byte) :=
  match shape with
  | None =>
      encoding_four (four_byte_shape cp)
  | Some (b1, b2, b3) =>
      Some [b1; b2; b3]
  end.

Definition encoding_two (cp : U32) (shape : option (byte * byte)) : option (list byte) :=
  match shape with
  | None =>
      encoding_three cp (three_byte_shape cp)
  | Some (b1, b2) =>
      Some [b1; b2]
  end.

Definition encoding_if (cp : U32) (one : option byte) : option (list byte) :=
  match one with
  | Some b1 =>
      Some [b1]
  | None =>
      encoding_two cp (two_byte_shape cp)
  end.

Definition encoding (cp : U32) : option (list byte) :=
  encoding_if cp (one_byte_shape cp).

(* `seq` is the UTF-8 encoding of the Unicode scalar `cp`. *)

Definition encodes (seq : list byte) (cp : U32) : Prop :=
  is_unicode_scalar cp = true /\
  encoding cp = Some seq.


(** ** Valid sequences *)

(* A "valid sequence" is a sequence of bytes that is the UTF-8 encoding
   of a Unicode scalar.  Since the encoding of a code point is its
   shortest byte shape, an overlong encoding is not a valid sequence;
   nor is the encoding of a surrogate code point or of a value above
   U+10FFFF, since neither is a Unicode scalar. *)

Definition is_valid_sequence (seq : list byte) : Prop :=
  exists cp : U32, encodes seq cp.


(** ** A valid sequence at the front of a buffer *)

(* `bytes` begins with a valid sequence that encodes `cp`, and `rest` is
   the bytes after it. *)

Definition begins_with_scalar (bytes : list byte) (cp : U32) (rest : list byte) : Prop :=
  exists seq : list byte,
    encodes seq cp /\
    seq ++ rest = bytes.

(* `bytes` does not begin with a valid sequence. *)

Definition no_valid_sequence (bytes : list byte) : Prop :=
  forall (cp : U32) (rest : list byte), begins_with_scalar bytes cp rest -> False.

(* No valid sequence is a proper prefix of another, so a buffer begins
   with at most one valid sequence: the scalar and the bytes after it
   are unique. *)

Definition begins_with_scalar_unique : Prop :=
  forall (bytes : list byte)
         (cp1 : U32) (rest1 : list byte)
         (cp2 : U32) (rest2 : list byte),
    begins_with_scalar bytes cp1 rest1 ->
    begins_with_scalar bytes cp2 rest2 ->
    cp1 = cp2 /\ rest1 = rest2.


(** ** Valid sequence prefix *)

(* A "valid sequence prefix" is one or more bytes that begin a valid
   sequence (or could begin a valid sequence): there exists zero or
   more bytes which when added to them make a valid sequence.

   The empty list is not a valid sequence prefix; a valid sequence is
   also a valid sequence prefix.

   Later we may find out that the actual input doesn't describe a valid
   sequence, so this says that if we've only seen these bytes so far,
   they *could* be the start of a legal encoding (including being
   themselves a complete valid sequence). *)

Definition is_valid_sequence_prefix (seq : list byte) : Prop :=
  match seq with
  | [] =>
      False
  | b1 :: more =>
      exists rest : list byte,
        is_valid_sequence ((b1 :: more) ++ rest)
  end.

(* While a non-valid sequence can sometimes become a valid sequence by
   adding more bytes (i.e. to complete the sequence), a non-empty
   sequence of bytes that is not a valid sequence *prefix* cannot
   become a valid prefix by adding more bytes.

   That is, a non-empty prefix which is not a valid sequence prefix
   stays as an invalid prefix no matter what bytes might be added to
   it. *)

Definition not_valid_sequence_prefix_extended : Prop :=
  forall (b1 : byte) (more extra : list byte),
    (is_valid_sequence_prefix (b1 :: more) -> False) ->
    is_valid_sequence_prefix ((b1 :: more) ++ extra) -> False.


(** ** Byte prefix *)

(* We define a "prefix" to mean that the buffer begins with the bytes
   of the prefix. *)

Definition is_prefix (prefix bytes : list byte) : Prop :=
  exists rest : list byte,
    prefix ++ rest = bytes.


(** ** Maximal subparts *)

(* Where the bytes being decoded do not begin with a valid sequence,
   the "maximal subpart" at their front is the run of bytes replaced by
   one U+FFFD.  The Unicode Standard (§3.9) defines it as the longest
   prefix that is either a valid sequence prefix or a single byte.

   So it is either:

   * the first byte alone, when it is not a valid sequence prefix (by
     `not_valid_sequence_prefix_extended`, no longer prefix is one
     either); or,

   * when the first byte is a valid sequence prefix, the longest run of
     bytes at the front that is also a valid sequence prefix.

   In the second case the prefix stops short of a whole sequence:
   either the input ends after it, or the next byte cannot extend it. *)

(* Consider an example where we have input bytes F0 9F 98 41.

   First we see F0.  By itself it is not a valid sequence, but it
   is a valid sequence prefix, so we can't tell yet whether the input
   begins with a valid sequence or not.

   The same holds when we see F0 9F and then F0 9F 98: each is a valid
   sequence prefix (F0 9F 98 80 would be U+1F600), but not yet a whole
   sequence.

   The next byte, 41, cannot continue F0 9F 98, so only when we see the
   41 do we know that the input does not begin with a valid sequence.

   And yet because we don't know how the bad bytes came about, it's
   possible that the 41 is valid input in its own right.  Thus Unicode
   defines the "maximal subpart" to be *only* the longest valid sequence
   prefix (when the first byte is a valid sequence prefix), not
   including the byte that showed the prefix could not be completed.
   The next byte, 41 in our example, is decoded fresh.

   This means that the result of our example is U+FFFD followed by "A"
   (41). *)

(* `longer_not_valid_prefix` is a relation that states that if
   `subpart` is a prefix of `bytes`, adding one or more of the following
   bytes from `bytes` to the subpart will not produce a valid sequence
   prefix.

   By itself this relation doesn't say anything about whether `subpart`
   itself is a valid prefix, only that no longer prefix of `bytes` is a
   valid prefix. *)

Definition maximal_subpart_longer_not_valid_prefix (subpart bytes : list byte) : Prop :=
  forall (c : byte) (extra : list byte),
    is_prefix (subpart ++ c :: extra) bytes ->
    is_valid_sequence_prefix (subpart ++ c :: extra) -> False.

(* `subpart` is the maximal subpart at the front of the non-empty bytes
   `b1 :: more`: a prefix of them that is either a valid sequence prefix
   or the first byte alone, such that no longer prefix is a valid
   sequence prefix.  Meant for bytes that do not begin with a valid
   sequence. *)

Definition maximal_subpart (b1 : byte) (more : list byte)
  (subpart : list byte) : Prop :=
  is_prefix subpart (b1 :: more) /\
  (is_valid_sequence_prefix subpart \/ subpart = [b1]) /\
  maximal_subpart_longer_not_valid_prefix subpart (b1 :: more).

(* Now we check our definition of "maximal subpart".

   Given a non-empty buffer that doesn't begin with a valid sequence, a
   maximal subpart both exists and is unique. *)

Definition maximal_subpart_exists : Prop :=
  forall (b1 : byte) (more : list byte),
    no_valid_sequence (b1 :: more) ->
    exists subpart : list byte, maximal_subpart b1 more subpart.

Definition maximal_subpart_unique : Prop :=
  forall (b1 : byte) (more : list byte) (s1 s2 : list byte),
    maximal_subpart b1 more s1 ->
    maximal_subpart b1 more s2 ->
    s1 = s2.


(** * Decoding a complete buffer. *)

(* We start by specifying how a complete buffer is decoded, and later
   we'll require that stream decoding must have the same result. *)


(** ** Unicode replacement character *)

(* Ill-formed input is replaced as the Unicode Standard recommends (§3.9,
   "U+FFFD Substitution of Maximal Subparts"): each maximal subpart, the
   longest run of bytes that is a valid sequence prefix or else a single
   byte, becomes one U+FFFD. *)

Definition code_point_to_string (cp : U32) : Text :=
  [cp].

(* U+FFFD REPLACEMENT CHARACTER. *)

Definition replacement_char : U32 :=
  U32_of_N 0xFFFD.

(* U+FFFD REPLACEMENT CHARACTER, as a one-character text. *)

Definition replacement_char_string : Text :=
  code_point_to_string replacement_char.


(** ** Decoding the first code point of a complete buffer *)

(* These relations are on complete buffers: an incomplete sequence at
   the end of the buffer results in a replacement character. *)

(* For use with a non-empty buffer (the first byte `b1` and the
   remaining bytes `more`) that doesn't begin with a valid sequence,
   `decodes_first_replaced` is a relation which states that, for some
   `subpart` and `rest`:

   * `subpart` is the maximal subpart at the front of the buffer;

   * the buffer is `subpart` followed by `rest`; and

   * `result` is the Unicode replacement character and `rest`. *)

Definition decodes_first_replaced (b1 : byte) (more : list byte)
  (result : option (U32 * list byte)) : Prop :=
  exists (subpart : list byte) (rest : list byte),
    maximal_subpart b1 more subpart /\
    subpart ++ rest = b1 :: more /\
    result = Some (replacement_char, rest).

(* `bytes` begins with a valid sequence, and `result` is the scalar that
   it encodes and the bytes after it. *)

Definition decodes_first_scalar (bytes : list byte)
  (result : option (U32 * list byte)) : Prop :=
  exists (cp : U32) (rest : list byte),
    begins_with_scalar bytes cp rest /\
    result = Some (cp, rest).

(* Decoding the first code point of the non-empty buffer `b1 :: more`
   gives `result`: the scalar of the valid sequence at the front of the
   buffer and the bytes after it, or, when the buffer doesn't begin with
   a valid sequence, the replaced result.

   (This is LAWS.bend's `decodes_first.nonempty`; the name
   `decodes_first_nonempty` belongs to the law below.) *)

Definition decodes_first_nonempty_case (b1 : byte) (more : list byte)
  (result : option (U32 * list byte)) : Prop :=
  decodes_first_scalar (b1 :: more) result \/
  (no_valid_sequence (b1 :: more) /\ decodes_first_replaced b1 more result).

(* Decoding the first code point of the complete buffer `bytes` gives
   `result`: None if `bytes` is empty, otherwise the code point and the
   bytes that follow it. *)

Definition decodes_first (bytes : list byte)
  (result : option (U32 * list byte)) : Prop :=
  match bytes with
  | [] =>
      result = None
  | b1 :: more =>
      decodes_first_nonempty_case b1 more result
  end.

(* Now we add some checks for our definition. *)

(* We check that for any buffer, decodes_first implies that a result
   exists. (That is, we haven't created a definition for which there is
   some buffer that no `result` value at all satisfies the definition.)
   The result itself can be None or Some, we just require that there is
   one. *)

Definition decodes_first_exists : Prop :=
  forall bytes : list byte,
    exists result : option (U32 * list byte), decodes_first bytes result.

(* We also check for uniqueness: for any buffer, there is only one
   `result` value which satisfies our definition. *)

Definition decodes_first_unique : Prop :=
  forall (bytes : list byte) (r1 r2 : option (U32 * list byte)),
    decodes_first bytes r1 ->
    decodes_first bytes r2 ->
    r1 = r2.

(* Check that decoding the first code point of an empty buffer gives
   None.  This is trivial given our decodes_first definition above, but
   we include for completeness. *)

Definition decodes_first_empty : Prop :=
  forall result : option (U32 * list byte),
    decodes_first [] result ->
    result = None.

(* Check that decoding the first code point of any non-empty buffer
   always gives Some. *)

Definition decodes_first_nonempty : Prop :=
  forall (b1 : byte) (more : list byte) (result : option (U32 * list byte)),
    decodes_first (b1 :: more) result ->
    Maybe_is_some result = true.

(* Decoding the complete buffer `bytes` gives the text `text`: empty if
   there is nothing to decode, otherwise the code point that
   `decodes_first` gives followed by the text from decoding the bytes
   after it.

   The recursion is on `text`, which shrinks at each step, so `text`
   comes first in `decodes_go`. *)

Fixpoint decodes_go (text : Text) (bytes : list byte) : Prop :=
  match text with
  | [] =>
      decodes_first bytes None
  | cp :: more =>
      exists rest : list byte,
        decodes_first bytes (Some (cp, rest)) /\ decodes_go more rest
  end.

Definition decodes (bytes : list byte) (text : Text) : Prop :=
  decodes_go text bytes.

(* Every buffer decodes to some text. *)

Definition decodes_exists : Prop :=
  forall bytes : list byte,
    exists text : Text, decodes bytes text.

(* A buffer decodes to only one text. *)

Definition decodes_unique : Prop :=
  forall (bytes : list byte) (t1 t2 : Text),
    decodes bytes t1 ->
    decodes bytes t2 ->
    t1 = t2.

(* Bytes are written as the standard library's byte constructors, in
   hex: x41 = 65 "A", x42 = 66 "B", x48 = 72 "H", x80 = 128, x82 = 130,
   x90 = 144, x98 = 152, x9f = 159, xa0 = 160, xa9 = 169, xac = 172,
   xc0 = 192, xc2 = 194, xe0 = 224, xe2 = 226, xed = 237, xf0 = 240,
   xf4 = 244, xff = 255.

   Text literals are written as lists of code points: "A" is
   [U32_of_N 65], "B" is [U32_of_N 66] and "H" is [U32_of_N 72]. *)

Definition decodes_examples : Prop :=
  (* Nothing to decode. *)
  decodes [] [] /\
  (* One-byte sequences. *)
  decodes [x41; x42] [U32_of_N 65; U32_of_N 66] /\
  (* A two-byte sequence: C2 A9 is U+00A9. *)
  decodes [xc2; xa9] (code_point_to_string (U32_of_N 169)) /\
  (* A lead byte followed by a byte that cannot continue it: the lead
     byte is replaced, and "A" decodes afresh. *)
  decodes [xc2; x41] (replacement_char_string ++ [U32_of_N 65]) /\
  (* C0 is not a valid sequence prefix (it would be overlong), nor is
     a lone continuation byte: each is replaced separately. *)
  decodes [xc0; x80] (replacement_char_string ++ replacement_char_string) /\
  (* A sequence left unfinished at the end of the buffer is replaced. *)
  decodes [xc2] replacement_char_string /\
  (* The second C2 cannot continue the first; it then begins C2 A9. *)
  decodes [xc2; xc2; xa9] (replacement_char_string ++ code_point_to_string (U32_of_N 169)) /\
  (* Valid sequences around a byte that never appears in UTF-8. *)
  decodes [x48; xc2; xa9; xff]
    ([U32_of_N 72] ++ code_point_to_string (U32_of_N 169) ++ replacement_char_string) /\
  (* A three-byte sequence: E2 82 AC is U+20AC. *)
  decodes [xe2; x82; xac] (code_point_to_string (U32_of_N 8364)) /\
  (* A four-byte sequence: F0 9F 98 80 is U+1F600. *)
  decodes [xf0; x9f; x98; x80] (code_point_to_string (U32_of_N 128512)) /\
  (* The two bytes of an unfinished three-byte sequence are one maximal
     subpart, so they give one replacement character. *)
  decodes [xe2; x82] replacement_char_string /\
  (* The same subpart when the next byte cannot continue it. *)
  decodes [xe2; x82; x41] (replacement_char_string ++ [U32_of_N 65]) /\
  (* Three bytes of an unfinished four-byte sequence are also one
     maximal subpart. *)
  decodes [xf0; x9f; x98] replacement_char_string /\
  (* The same subpart when the next byte cannot continue it. *)
  decodes [xf0; x9f; x98; x41] (replacement_char_string ++ [U32_of_N 65]) /\
  (* E0 80 would be overlong: E0 must be followed by A0..BF. *)
  decodes [xe0; x80; x80]
    (replacement_char_string ++ replacement_char_string ++ replacement_char_string) /\
  (* ED A0 would begin a surrogate: ED must be followed by 80..9F. *)
  decodes [xed; xa0; x80]
    (replacement_char_string ++ replacement_char_string ++ replacement_char_string) /\
  (* F4 90 would exceed U+10FFFF: F4 must be followed by 80..8F. *)
  decodes [xf4; x90; x80; x80]
    (replacement_char_string ++ replacement_char_string ++
     replacement_char_string ++ replacement_char_string).


(** * Stream decoding *)

(* LAWS.bend states these laws about the implementation module `UTF8`.
   Here they are stated about any `Decoder`, a record of the same four
   things:

   `decode_start_state D` is the decoder state before any input.

   `decode_buffer D state buffer` takes the next buffer of bytes and
   returns the new state and the text that is now fully resolved.

   `decode_done D state` returns the text that ends the input.

   The state type, `DecodeState D`, is the implementation's choice: the
   laws below only describe the text that comes out. *)

Record Decoder : Type := {
  DecodeState : Type;
  decode_start_state : DecodeState;
  decode_buffer : DecodeState -> list byte -> DecodeState * Text;
  decode_done : DecodeState -> Text
}.

(* We'll show that regardless of how the input is split into buffers,
   the result of the stream decoding (all of the text returned by
   `decode_buffer` and `decode_done`, concatenated together) satisfies
   our specification for decoding a complete input (all the buffers
   concatenated together). *)

(* We'll also show that each call to `decode_buffer` returns all of the
   text that *can* be returned based on the input buffers seen so far.
   (Otherwise, for example, an implementation could keep all the input
   buffers in the state and then deliver the entire decoded text from
   the call to `decode_done`.) *)

(* LAWS.bend's section "all_bytes" (`all_bytes` and the law
   `utf8_decode_buffer_all_bytes`) has no counterpart: buffers here are
   lists of `byte`, so every element is a byte value. *)


(** ** Running the decoder *)

(* We define a function `decoded`:

   `decoded D (buffers : list (list byte)) : Text`

   It takes a list of buffers, where each buffer is a list of bytes.
   It returns the output text, the concatenation of the text returned
   by the calls to `decode_buffer` and the final call to
   `decode_done`. *)

(* To keep track of our state running the decoder, we use a pair of the
   decoder state that we need to pass to the decoder functions and the
   concatenated text returned so far. *)

Definition feed_prepend (D : Decoder) (text : Text) (result : DecodeState D * Text) :
  DecodeState D * Text :=
  let '(state, more) := result in
  (state, text ++ more).

Definition feed_then (D : Decoder) (result : DecodeState D * Text)
  (rest : DecodeState D -> DecodeState D * Text) :
  DecodeState D * Text :=
  let '(state, text) := result in
  feed_prepend D text (rest state).

(* Give `buffers` to `decode_buffer` in order, starting from `state`,
   and join the text that the calls return. *)

Fixpoint feed (D : Decoder) (buffers : list (list byte))
  (state : DecodeState D) : DecodeState D * Text :=
  match buffers with
  | [] =>
      (state, [])
  | buffer :: rest =>
      feed_then D (decode_buffer D state buffer)
        (fun s => feed D rest s)
  end.

(* The text returned for `buffers`, without calling `decode_done`. *)

Definition decoded_so_far_text (D : Decoder) (fed : DecodeState D * Text) : Text :=
  let '(state, text) := fed in
  text.

Definition decoded_so_far (D : Decoder) (buffers : list (list byte)) : Text :=
  decoded_so_far_text D (feed D buffers (decode_start_state D)).

(* The text returned for `buffers`, including calling `decode_done`. *)

Definition decoded_text (D : Decoder) (fed : DecodeState D * Text) : Text :=
  let '(state, text) := fed in
  text ++ decode_done D state.

Definition decoded (D : Decoder) (buffers : list (list byte)) : Text :=
  decoded_text D (feed D buffers (decode_start_state D)).


(** ** Running the decoder satisfies `decodes` *)

(* In whatever way the input is split into buffers, giving them in
   order to `decode_buffer` and then calling `decode_done` gives what
   their concatenation decodes to. *)

Definition utf8_decodes (D : Decoder) : Prop :=
  forall buffers : list (list byte),
    decodes (concat buffers) (decoded D buffers).

(* `prefix` is a prefix of `text`. *)

Definition is_text_prefix (prefix text : Text) : Prop :=
  exists more : Text, prefix ++ more = text.

(* After each buffer, the decoder has returned the longest text that
   every continuation of the input agrees on.  This has two halves. *)

(* Safe: whatever bytes follow, the whole input decodes to text that
   begins with the text returned so far.  Later bytes cannot change
   anything already returned. *)

Definition utf8_decode_buffer_safe (D : Decoder) : Prop :=
  forall (buffers : list (list byte)) (rest : list byte) (full : Text),
    decodes (concat buffers ++ rest) full ->
    is_text_prefix (decoded_so_far D buffers) full.

(* Prompt: nothing is held back.  No longer text is safe: for any code
   point `c`, some bytes could follow for which the whole input does not
   decode to text beginning with the text returned so far followed by
   `c`. *)

Definition utf8_decode_buffer_prompt (D : Decoder) : Prop :=
  forall (buffers : list (list byte)) (c : U32),
    exists rest : list byte,
      exists full : Text,
        decodes (concat buffers ++ rest) full /\
        (is_text_prefix (decoded_so_far D buffers ++ code_point_to_string c) full -> False).


(** ** All the streaming laws together *)

(* Not in LAWS.bend: the conjunction of the three laws on the decoder,
   for convenience. *)

Definition Decoder_correct (D : Decoder) : Prop :=
  utf8_decodes D /\
  utf8_decode_buffer_safe D /\
  utf8_decode_buffer_prompt D.
