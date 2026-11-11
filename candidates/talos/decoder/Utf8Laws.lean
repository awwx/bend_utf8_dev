-- Lean 4 translation of /root/bend/utf8/LAWS.bend (core Lean only).
--
-- This file is the specification only: each Bend `law` is a `def` of
-- type `Prop` stating the law, with no proof.  The proofs live
-- elsewhere.
--
-- Translation conventions (see TRANSLATION.txt for the full record):
--
-- * A byte is a `UInt8`.  LAWS.bend uses `U32` values with a separate
--   proof that they are 0..255; with `UInt8` that proof is not needed,
--   so `all_bytes` and everything that uses it are dropped.
--
-- * A code point is a `UInt32`, a 32-bit value like Bend's `U32`, with
--   no restriction to Unicode scalar values.
--
-- * Text (Bend's `String`, a list of `Chr{U32}`) is `Text`, a list of
--   code points.  Lean's `String` and `Char` are not used.
--
-- * Bend's `Type`-valued propositions become `Prop`: `Exists` is `∃`,
--   `Or` is `∨`, `&` is `∧`, `-> Empty` is `¬`, and `{a == b : T}` is
--   `a = b`.
--
-- * The streaming laws are about an abstract `Decoder` rather than the
--   Bend implementation `UTF8.*`.

-- Bend's `String`: a list of code points.
abbrev Text : Type := List UInt32

-- ## Bits to bytes helper

-- Type alias for a tuple of eight bools.
abbrev Bit8 : Type :=
  Bool × Bool × Bool × Bool × Bool × Bool × Bool × Bool

-- Given a tuple of eight bools, return the byte value of the binary
-- integer, most significant bit first.
--
-- `BitVec.ofBoolListLE` takes its bits least significant bit first.
def bit8_value (bit8 : Bit8) : UInt8 :=
  match bit8 with
  | (b7, b6, b5, b4, b3, b2, b1, b0) =>
    UInt8.ofBitVec (BitVec.ofBoolListLE [b0, b1, b2, b3, b4, b5, b6, b7])

-- Given 8 booleans used as bits, most significant bit first, convert
-- to its byte value 0..255.

def bit8_value_sum : Prop :=
  ∀ (b7 b6 b5 b4 b3 b2 b1 b0 : Bool),
    bit8_value (b7, b6, b5, b4, b3, b2, b1, b0) =
      (b7.toUInt8 * 128 +
       b6.toUInt8 * 64 +
       b5.toUInt8 * 32 +
       b4.toUInt8 * 16 +
       b3.toUInt8 * 8 +
       b2.toUInt8 * 4 +
       b1.toUInt8 * 2 +
       b0.toUInt8 * 1 : UInt8)

-- Provide an independent check of `bit8_value`: convert the booleans
-- to a `BitVec 8`, then to a Nat, and then to a byte.

def bit8_value_word : Prop :=
  ∀ (b7 b6 b5 b4 b3 b2 b1 b0 : Bool),
    -- `BitVec.ofBoolListLE` takes the least significant bit first.
    let word : BitVec 8 := BitVec.ofBoolListLE [b0, b1, b2, b3, b4, b5, b6, b7]
    bit8_value (b7, b6, b5, b4, b3, b2, b1, b0) =
      UInt8.ofNat word.toNat


-- ## U32 to four bytes helper

-- Bits are grouped into bytes, most significant byte and bit first.
abbrev Byte4 : Type :=
  Bit8 × Bit8 × Bit8 × Bit8

-- Split a UInt32 into its four bytes, most significant byte first, each
-- as eight bools, most significant bit first.
--
-- `getLsbD i` is bit `i`, counting from the least significant bit 0.
def u32_byte4 (value : UInt32) : Byte4 :=
  let w := value.toBitVec
  ((w.getLsbD 31, w.getLsbD 30, w.getLsbD 29, w.getLsbD 28,
    w.getLsbD 27, w.getLsbD 26, w.getLsbD 25, w.getLsbD 24),
   (w.getLsbD 23, w.getLsbD 22, w.getLsbD 21, w.getLsbD 20,
    w.getLsbD 19, w.getLsbD 18, w.getLsbD 17, w.getLsbD 16),
   (w.getLsbD 15, w.getLsbD 14, w.getLsbD 13, w.getLsbD 12,
    w.getLsbD 11, w.getLsbD 10, w.getLsbD 9, w.getLsbD 8),
   (w.getLsbD 7, w.getLsbD 6, w.getLsbD 5, w.getLsbD 4,
    w.getLsbD 3, w.getLsbD 2, w.getLsbD 1, w.getLsbD 0))

-- Bit 31 is the first bool of the first byte, and bit 0 the last bool
-- of the last byte.
--
-- The UInt32 is built from its 32 bits, least significant bit first.

def u32_byte4_bits : Prop :=
  ∀ (b31 b30 b29 b28 b27 b26 b25 b24
     b23 b22 b21 b20 b19 b18 b17 b16
     b15 b14 b13 b12 b11 b10 b9 b8
     b7 b6 b5 b4 b3 b2 b1 b0 : Bool),
    u32_byte4 (UInt32.ofBitVec (BitVec.ofBoolListLE
      [b0, b1, b2, b3, b4, b5, b6, b7,
       b8, b9, b10, b11, b12, b13, b14, b15,
       b16, b17, b18, b19, b20, b21, b22, b23,
       b24, b25, b26, b27, b28, b29, b30, b31])) =
      ((b31, b30, b29, b28, b27, b26, b25, b24),
       (b23, b22, b21, b20, b19, b18, b17, b16),
       (b15, b14, b13, b12, b11, b10, b9, b8),
       (b7, b6, b5, b4, b3, b2, b1, b0))


-- ### UTF-8 encoding specification

-- ## Surrogate code points

-- Surrogate code points are U+D800..U+DFFF.

def is_surrogate_code_point (cp : UInt32) : Bool :=
  decide (cp ≥ 0xD800) &&
  decide (cp ≤ 0xDFFF)

def is_surrogate_code_point_examples : Prop :=
  is_surrogate_code_point 0x0000 = false ∧
  is_surrogate_code_point 0xD7FF = false ∧
  is_surrogate_code_point 0xD800 = true ∧
  is_surrogate_code_point 0xDC00 = true ∧
  is_surrogate_code_point 0xDFFF = true ∧
  is_surrogate_code_point 0xE000 = false


-- ## Unicode scalars

-- A Unicode scalar is any code point from U+0000 to U+10FFFF excluding
-- surrogate code points.

def is_unicode_scalar (cp : UInt32) : Bool :=
  decide (cp ≥ 0x000000) &&
  decide (cp ≤ 0x10FFFF) &&
  !(is_surrogate_code_point cp)


-- ## Byte shapes

-- By a "byte shape" we mean a series of bytes that has the correct bit
-- pattern for a UTF-8 encoding.  This includes invalid UTF-8 encodings
-- such as overlong encodings, encodings of surrogate code points, and
-- encodings of code point values above U+10FFFF.

-- UTF-8 one-byte shape
--
-- 00000000 00000000 00000000 0yyyzzzz -> 0yyyzzzz
--
-- Returns some byte if the shape matches, or none if the shape doesn't
-- match.

def one_byte_shape.bits (bits : Byte4) : Option UInt8 :=
  match bits with
  | ((false, false, false, false, false, false, false, false),
     (false, false, false, false, false, false, false, false),
     (false, false, false, false, false, false, false, false),
     (false, y1, y2, y3, z1, z2, z3, z4)) =>
    some (bit8_value (false, y1, y2, y3, z1, z2, z3, z4))
  | _ =>
    none

def one_byte_shape (cp : UInt32) : Option UInt8 :=
  one_byte_shape.bits (u32_byte4 cp)

-- UTF-8 two-byte shape
--
-- 00000000 00000000 00000xxx yyyyzzzz -> 110xxxyy 10yyzzzz
--
-- Returns the two bytes if the shape matches, or none if the shape
-- doesn't match.
--
-- Capacity includes overlong encodings of 0..127; shortest-form
-- validity is separate.

def two_byte_shape.bits (bits : Byte4) : Option (UInt8 × UInt8) :=
  match bits with
  | ((false, false, false, false, false, false, false, false),
     (false, false, false, false, false, false, false, false),
     (false, false, false, false, false, x1, x2, x3),
     (y1, y2, y3, y4, z1, z2, z3, z4)) =>
    some (bit8_value (true, true, false, x1, x2, x3, y1, y2),
          bit8_value (true, false, y3, y4, z1, z2, z3, z4))
  | _ =>
    none

def two_byte_shape (cp : UInt32) : Option (UInt8 × UInt8) :=
  two_byte_shape.bits (u32_byte4 cp)

-- UTF-8 three-byte shape
--
-- 00000000 00000000 wwwwxxxx yyyyzzzz -> 1110wwww 10xxxxyy 10yyzzzz
--
-- Returns the three bytes if the shape matches, or none if the shape
-- doesn't match.
--
-- Capacity includes overlong encodings of 0..2047 and encodings of
-- surrogate code points; validity is separate.

def three_byte_shape.bits (bits : Byte4) : Option (UInt8 × UInt8 × UInt8) :=
  match bits with
  | ((false, false, false, false, false, false, false, false),
     (false, false, false, false, false, false, false, false),
     (w1, w2, w3, w4, x1, x2, x3, x4),
     (y1, y2, y3, y4, z1, z2, z3, z4)) =>
    some (bit8_value (true, true, true, false, w1, w2, w3, w4),
          bit8_value (true, false, x1, x2, x3, x4, y1, y2),
          bit8_value (true, false, y3, y4, z1, z2, z3, z4))
  | _ =>
    none

def three_byte_shape (cp : UInt32) : Option (UInt8 × UInt8 × UInt8) :=
  three_byte_shape.bits (u32_byte4 cp)

-- UTF-8 four-byte shape
--
-- 00000000 000uvvvv wwwwxxxx yyyyzzzz -> 11110uvv 10vvwwww 10xxxxyy 10yyzzzz
--
-- Returns the four bytes if the shape matches, or none if the shape
-- doesn't match.
--
-- Capacity includes overlong encodings of 0..65535 and encodings of
-- code point values above U+10FFFF; validity is separate.

def four_byte_shape.bits (bits : Byte4) : Option (UInt8 × UInt8 × UInt8 × UInt8) :=
  match bits with
  | ((false, false, false, false, false, false, false, false),
     (false, false, false, u, v1, v2, v3, v4),
     (w1, w2, w3, w4, x1, x2, x3, x4),
     (y1, y2, y3, y4, z1, z2, z3, z4)) =>
    some (bit8_value (true, true, true, true, false, u, v1, v2),
          bit8_value (true, false, v3, v4, w1, w2, w3, w4),
          bit8_value (true, false, x1, x2, x3, x4, y1, y2),
          bit8_value (true, false, y3, y4, z1, z2, z3, z4))
  | _ =>
    none

def four_byte_shape (cp : UInt32) : Option (UInt8 × UInt8 × UInt8 × UInt8) :=
  four_byte_shape.bits (u32_byte4 cp)


-- ## Encoding

-- The UTF-8 encoding of `cp` is its shortest byte shape: one byte when
-- `cp` has a one-byte shape, otherwise two, three or four.  (A longer
-- encoding of a code point that has a shorter shape would be overlong.)
-- Code points above U+1FFFFF have no encoding.

def encoding.four (shape : Option (UInt8 × UInt8 × UInt8 × UInt8)) : Option (List UInt8) :=
  match shape with
  | none =>
    none
  | some (b1, b2, b3, b4) =>
    some [b1, b2, b3, b4]

def encoding.three (cp : UInt32) (shape : Option (UInt8 × UInt8 × UInt8)) : Option (List UInt8) :=
  match shape with
  | none =>
    encoding.four (four_byte_shape cp)
  | some (b1, b2, b3) =>
    some [b1, b2, b3]

def encoding.two (cp : UInt32) (shape : Option (UInt8 × UInt8)) : Option (List UInt8) :=
  match shape with
  | none =>
    encoding.three cp (three_byte_shape cp)
  | some (b1, b2) =>
    some [b1, b2]

def encoding.«if» (cp : UInt32) (one : Option UInt8) : Option (List UInt8) :=
  match one with
  | some b1 =>
    some [b1]
  | none =>
    encoding.two cp (two_byte_shape cp)

def encoding (cp : UInt32) : Option (List UInt8) :=
  encoding.«if» cp (one_byte_shape cp)

-- `seq` is the UTF-8 encoding of the Unicode scalar `cp`.

def encodes (seq : List UInt8) (cp : UInt32) : Prop :=
  is_unicode_scalar cp = true ∧
  encoding cp = some seq


-- ## Valid sequences

-- A "valid sequence" is a sequence of bytes that is the UTF-8 encoding
-- of a Unicode scalar.  Since the encoding of a code point is its
-- shortest byte shape, an overlong encoding is not a valid sequence;
-- nor is the encoding of a surrogate code point or of a value above
-- U+10FFFF, since neither is a Unicode scalar.

def is_valid_sequence (seq : List UInt8) : Prop :=
  ∃ cp : UInt32, encodes seq cp


-- ## A valid sequence at the front of a buffer

-- `bytes` begins with a valid sequence that encodes `cp`, and `rest` is
-- the bytes after it.

def begins_with_scalar (bytes : List UInt8) (cp : UInt32) (rest : List UInt8) : Prop :=
  ∃ seq : List UInt8,
    encodes seq cp ∧
    seq ++ rest = bytes

-- `bytes` does not begin with a valid sequence.

def no_valid_sequence (bytes : List UInt8) : Prop :=
  ∀ (cp : UInt32) (rest : List UInt8), ¬ begins_with_scalar bytes cp rest

-- No valid sequence is a proper prefix of another, so a buffer begins
-- with at most one valid sequence: the scalar and the bytes after it
-- are unique.

def begins_with_scalar_unique : Prop :=
  ∀ (bytes : List UInt8)
    (cp1 : UInt32) (rest1 : List UInt8)
    (cp2 : UInt32) (rest2 : List UInt8),
    begins_with_scalar bytes cp1 rest1 →
    begins_with_scalar bytes cp2 rest2 →
    cp1 = cp2 ∧ rest1 = rest2


-- ## Valid sequence prefix

-- A "valid sequence prefix" is one or more bytes that begin a valid
-- sequence (or could begin a valid sequence): there exists zero or
-- more bytes which when added to them make a valid sequence.
--
-- The empty list is not a valid sequence prefix; a valid sequence is
-- also a valid sequence prefix.
--
-- Later we may find out that the actual input doesn't describe a valid
-- sequence, so this says that if we've only seen these bytes so far,
-- they *could* be the start of a legal encoding (including being
-- themselves a complete valid sequence).

def is_valid_sequence_prefix : List UInt8 → Prop
  | [] =>
    False
  | b1 :: more =>
    ∃ rest : List UInt8,
      is_valid_sequence ((b1 :: more) ++ rest)

-- While a non-valid sequence can sometimes become a valid sequence by
-- adding more bytes (i.e. to complete the sequence), a non-empty
-- sequence of bytes that is not a valid sequence *prefix* cannot
-- become a valid prefix by adding more bytes.
--
-- That is, a non-empty prefix which is not a valid sequence prefix
-- stays as an invalid prefix no matter what bytes might be added to
-- it.

def not_valid_sequence_prefix_extended : Prop :=
  ∀ (b1 : UInt8) (more extra : List UInt8),
    ¬ is_valid_sequence_prefix (b1 :: more) →
    ¬ is_valid_sequence_prefix ((b1 :: more) ++ extra)


-- ## Byte prefix

-- We define a "prefix" to mean that the buffer begins with the bytes
-- of the prefix.

def is_prefix (pre : List UInt8) (bytes : List UInt8) : Prop :=
  ∃ rest : List UInt8,
    pre ++ rest = bytes


-- ## Maximal subparts

-- Where the bytes being decoded do not begin with a valid sequence,
-- the "maximal subpart" at their front is the run of bytes replaced by
-- one U+FFFD.  The Unicode Standard (§3.9) defines it as the longest
-- prefix that is either a valid sequence prefix or a single byte.
--
-- So it is either:
--
-- * the first byte alone, when it is not a valid sequence prefix (by
--   `not_valid_sequence_prefix_extended`, no longer prefix is one
--   either); or,
--
-- * when the first byte is a valid sequence prefix, the longest run of
--   bytes at the front that is also a valid sequence prefix.
--
-- In the second case the prefix stops short of a whole sequence:
-- either the input ends after it, or the next byte cannot extend it.

-- Consider an example where we have input bytes F0 9F 98 41.
--
-- First we see F0.  By itself it is not a valid sequence, but it
-- is a valid sequence prefix, so we can't tell yet whether the input
-- begins with a valid sequence or not.
--
-- The same holds when we see F0 9F and then F0 9F 98: each is a valid
-- sequence prefix (F0 9F 98 80 would be U+1F600), but not yet a whole
-- sequence.
--
-- The next byte, 41, cannot continue F0 9F 98, so only when we see the
-- 41 do we know that the input does not begin with a valid sequence.
--
-- And yet because we don't know how the bad bytes came about, it's
-- possible that the 41 is valid input in its own right.  Thus Unicode
-- defines the "maximal subpart" to be *only* the longest valid sequence
-- prefix (when the first byte is a valid sequence prefix), not
-- including the byte that showed the prefix could not be completed.
-- The next byte, 41 in our example, is decoded fresh.
--
-- This means that the result of our example is U+FFFD followed by "A"
-- (41).

-- `longer_not_valid_prefix` is a relation that states that if
-- `subpart` is a prefix of `bytes`, adding one or more of the following
-- bytes from `bytes` to the subpart will not produce a valid sequence
-- prefix.
--
-- By itself this relation doesn't say anything about whether `subpart`
-- itself is a valid prefix, only that no longer prefix of `bytes` is a
-- valid prefix.

def maximal_subpart.longer_not_valid_prefix (subpart : List UInt8) (bytes : List UInt8) : Prop :=
  ∀ (c : UInt8) (extra : List UInt8),
    is_prefix (subpart ++ c :: extra) bytes →
    ¬ is_valid_sequence_prefix (subpart ++ c :: extra)

-- `subpart` is the maximal subpart at the front of the non-empty bytes
-- `b1 :: more`: a prefix of them that is either a valid sequence prefix
-- or the first byte alone, such that no longer prefix is a valid
-- sequence prefix.  Meant for bytes that do not begin with a valid
-- sequence.

def maximal_subpart (b1 : UInt8) (more : List UInt8)
    (subpart : List UInt8) : Prop :=
  is_prefix subpart (b1 :: more) ∧
  (is_valid_sequence_prefix subpart ∨ subpart = [b1]) ∧
  maximal_subpart.longer_not_valid_prefix subpart (b1 :: more)

-- Now we check our definition of "maximal subpart".
--
-- Given a non-empty buffer that doesn't begin with a valid sequence, a
-- maximal subpart both exists and is unique.

def maximal_subpart_exists : Prop :=
  ∀ (b1 : UInt8) (more : List UInt8),
    no_valid_sequence (b1 :: more) →
    ∃ subpart : List UInt8, maximal_subpart b1 more subpart

def maximal_subpart_unique : Prop :=
  ∀ (b1 : UInt8) (more : List UInt8) (s1 s2 : List UInt8),
    maximal_subpart b1 more s1 →
    maximal_subpart b1 more s2 →
    s1 = s2


-- ### Decoding a complete buffer.

-- We start by specifying how a complete buffer is decoded, and later
-- we'll require that stream decoding must have the same result.


-- ## Unicode replacement character

-- Ill-formed input is replaced as the Unicode Standard recommends (§3.9,
-- "U+FFFD Substitution of Maximal Subparts"): each maximal subpart, the
-- longest run of bytes that is a valid sequence prefix or else a single
-- byte, becomes one U+FFFD.

def code_point_to_string (cp : UInt32) : Text :=
  [cp]

-- U+FFFD REPLACEMENT CHARACTER.

def replacement_char : UInt32 :=
  0xFFFD

-- U+FFFD REPLACEMENT CHARACTER, as a one-character text.

def replacement_char_string : Text :=
  code_point_to_string replacement_char


-- ## Decoding the first code point of a complete buffer

-- These relations are on complete buffers: an incomplete sequence at
-- the end of the buffer results in a replacement character.

-- For use with a non-empty buffer (the first byte `b1` and the
-- remaining bytes `more`) that doesn't begin with a valid sequence,
-- `decodes_first.replaced` is a relation which states that, for some
-- `subpart` and `rest`:
--
-- * `subpart` is the maximal subpart at the front of the buffer;
--
-- * the buffer is `subpart` followed by `rest`; and
--
-- * `result` is the Unicode replacement character and `rest`.

def decodes_first.replaced (b1 : UInt8) (more : List UInt8)
    (result : Option (UInt32 × List UInt8)) : Prop :=
  ∃ subpart : List UInt8, ∃ rest : List UInt8,
    maximal_subpart b1 more subpart ∧
    subpart ++ rest = b1 :: more ∧
    result = some (replacement_char, rest)

-- `bytes` begins with a valid sequence, and `result` is the scalar that
-- it encodes and the bytes after it.

def decodes_first.scalar (bytes : List UInt8)
    (result : Option (UInt32 × List UInt8)) : Prop :=
  ∃ cp : UInt32, ∃ rest : List UInt8,
    begins_with_scalar bytes cp rest ∧
    result = some (cp, rest)

-- Decoding the first code point of the non-empty buffer `b1 :: more`
-- gives `result`: the scalar of the valid sequence at the front of the
-- buffer and the bytes after it, or, when the buffer doesn't begin with
-- a valid sequence, the replaced result.

def decodes_first.nonempty (b1 : UInt8) (more : List UInt8)
    (result : Option (UInt32 × List UInt8)) : Prop :=
  decodes_first.scalar (b1 :: more) result ∨
    (no_valid_sequence (b1 :: more) ∧ decodes_first.replaced b1 more result)

-- Decoding the first code point of the complete buffer `bytes` gives
-- `result`: none if `bytes` is empty, otherwise the code point and the
-- bytes that follow it.

def decodes_first : List UInt8 → Option (UInt32 × List UInt8) → Prop
  | [], result =>
    result = none
  | b1 :: more, result =>
    decodes_first.nonempty b1 more result

-- Now we add some checks for our definition.

-- We check that for any buffer, decodes_first implies that a result
-- exists. (That is, we haven't created a definition for which there is
-- some buffer that no `result` value at all satisfies the definition.)
-- The result itself can be none or some, we just require that there is
-- one.

def decodes_first_exists : Prop :=
  ∀ bytes : List UInt8,
    ∃ result : Option (UInt32 × List UInt8), decodes_first bytes result

-- We also check for uniqueness: for any buffer, there is only one
-- `result` value which satisfies our definition.

def decodes_first_unique : Prop :=
  ∀ (bytes : List UInt8) (r1 r2 : Option (UInt32 × List UInt8)),
    decodes_first bytes r1 →
    decodes_first bytes r2 →
    r1 = r2

-- Check that decoding the first code point of an empty buffer gives
-- none.  This is trivial given our decodes_first def above, but we
-- include for completeness.

def decodes_first_empty : Prop :=
  ∀ result : Option (UInt32 × List UInt8),
    decodes_first [] result →
    result = none

-- Check that decoding the first code point of any non-empty buffer
-- always gives some.

def decodes_first_nonempty : Prop :=
  ∀ (b1 : UInt8) (more : List UInt8) (result : Option (UInt32 × List UInt8)),
    decodes_first (b1 :: more) result →
    result.isSome = true

-- Decoding the complete buffer `bytes` gives the text `text`: empty if
-- there is nothing to decode, otherwise the code point that
-- `decodes_first` gives followed by the text from decoding the bytes
-- after it.
--
-- The recursion is on `text`, which shrinks at each step, so `text`
-- comes first in `decodes.go`.

def decodes.go : Text → List UInt8 → Prop
  | [], bytes =>
    decodes_first bytes none
  | cp :: more, bytes =>
    ∃ rest : List UInt8,
      decodes_first bytes (some (cp, rest)) ∧ decodes.go more rest

def decodes (bytes : List UInt8) (text : Text) : Prop :=
  decodes.go text bytes

-- Every buffer decodes to some text.

def decodes_exists : Prop :=
  ∀ bytes : List UInt8,
    ∃ text : Text, decodes bytes text

-- A buffer decodes to only one text.

def decodes_unique : Prop :=
  ∀ (bytes : List UInt8) (t1 t2 : Text),
    decodes bytes t1 →
    decodes bytes t2 →
    t1 = t2

-- Bytes in hex: 65 = 0x41 "A", 66 = 0x42 "B", 72 = 0x48 "H",
-- 128 = 0x80, 130 = 0x82, 144 = 0x90, 152 = 0x98, 159 = 0x9F,
-- 160 = 0xA0, 169 = 0xA9, 172 = 0xAC, 192 = 0xC0, 194 = 0xC2,
-- 224 = 0xE0, 226 = 0xE2, 237 = 0xED, 240 = 0xF0, 244 = 0xF4,
-- 255 = 0xFF.
--
-- A text literal such as "AB" is written as its list of code points,
-- [65, 66].

def decodes_examples : Prop :=
  -- Nothing to decode.
  decodes [] [] ∧                                            -- ""
  -- One-byte sequences.
  decodes [65, 66] [65, 66] ∧                                -- "AB"
  -- A two-byte sequence: C2 A9 is U+00A9.
  decodes [194, 169] (code_point_to_string 169) ∧
  -- A lead byte followed by a byte that cannot continue it: the lead
  -- byte is replaced, and "A" decodes afresh.
  decodes [194, 65] (replacement_char_string ++ [65]) ∧      -- "A"
  -- C0 is not a valid sequence prefix (it would be overlong), nor is
  -- a lone continuation byte: each is replaced separately.
  decodes [192, 128] (replacement_char_string ++ replacement_char_string) ∧
  -- A sequence left unfinished at the end of the buffer is replaced.
  decodes [194] replacement_char_string ∧
  -- The second C2 cannot continue the first; it then begins C2 A9.
  decodes [194, 194, 169] (replacement_char_string ++ code_point_to_string 169) ∧
  -- Valid sequences around a byte that never appears in UTF-8.
  decodes [72, 194, 169, 255]
    ([72] ++ code_point_to_string 169 ++ replacement_char_string) ∧  -- "H"
  -- A three-byte sequence: E2 82 AC is U+20AC.
  decodes [226, 130, 172] (code_point_to_string 8364) ∧
  -- A four-byte sequence: F0 9F 98 80 is U+1F600.
  decodes [240, 159, 152, 128] (code_point_to_string 128512) ∧
  -- The two bytes of an unfinished three-byte sequence are one maximal
  -- subpart, so they give one replacement character.
  decodes [226, 130] replacement_char_string ∧
  -- The same subpart when the next byte cannot continue it.
  decodes [226, 130, 65] (replacement_char_string ++ [65]) ∧  -- "A"
  -- Three bytes of an unfinished four-byte sequence are also one
  -- maximal subpart.
  decodes [240, 159, 152] replacement_char_string ∧
  -- The same subpart when the next byte cannot continue it.
  decodes [240, 159, 152, 65] (replacement_char_string ++ [65]) ∧  -- "A"
  -- E0 80 would be overlong: E0 must be followed by A0..BF.
  decodes [224, 128, 128]
    (replacement_char_string ++ replacement_char_string ++ replacement_char_string) ∧
  -- ED A0 would begin a surrogate: ED must be followed by 80..9F.
  decodes [237, 160, 128]
    (replacement_char_string ++ replacement_char_string ++ replacement_char_string) ∧
  -- F4 90 would exceed U+10FFFF: F4 must be followed by 80..8F.
  decodes [244, 144, 128, 128]
    (replacement_char_string ++ replacement_char_string ++
     replacement_char_string ++ replacement_char_string)


-- ### Stream decoding

-- A stream decoder `D : Decoder` (in LAWS.bend, the functions of the
-- implementation module `UTF8`):
--
-- `D.start` (`UTF8.decode_start_state()`) is the decoder state before
-- any input.
--
-- `D.decode_buffer state buffer` (`UTF8.decode_buffer`) takes the next
-- buffer of bytes and returns the new state and the text that is now
-- fully resolved.
--
-- `D.decode_done state` (`UTF8.decode_done`) returns the text that ends
-- the input.
--
-- The state type, `D.State` (`UTF8.DecodeState()`), is the
-- implementation's choice: the laws below only describe the text that
-- comes out.

structure Decoder where
  State : Type
  start : State
  decode_buffer : State → List UInt8 → State × Text
  decode_done : State → Text

-- We'll show that regardless of how the input is split into buffers,
-- the result of the stream decoding (all of the text returned by
-- `decode_buffer` and `decode_done`, concatenated together)
-- satisfies our specification for decoding a complete input (all the
-- buffers concatenated together).

-- We'll also show that each call to `decode_buffer` returns all of the
-- text that *can* be returned based on the input buffers seen so far.
-- (Otherwise, for example, an implementation could keep all the input
-- buffers in the state and then deliver the entire decoded text from
-- the call to `decode_done`.)

-- ## all_bytes
--
-- Dropped.  In LAWS.bend, buffers are lists of U32 that are not
-- restricted to 0..255, so `all_bytes` and the law
-- `utf8_decode_buffer_all_bytes` state that restriction.  Here a byte
-- is a `UInt8`, so there is nothing to state.


-- ## Running the decoder

-- We define a function `decoded`:
--
-- `decoded D (buffers : List (List UInt8)) : Text`
--
-- It takes a list of buffers, where each buffer is a list of bytes.  It
-- returns the output text, the concatenation of the text returned by
-- the calls to `decode_buffer` and the final call to `decode_done`.

-- To keep track of our state running the decoder, we use a pair of the
-- decoder state that we need to pass to the decoder functions and the
-- concatenated text returned so far.

def feed.prepend (D : Decoder) (text : Text) (result : D.State × Text) :
    D.State × Text :=
  match result with
  | (state, more) => (state, text ++ more)

def feed.then (D : Decoder) (result : D.State × Text)
    (rest : D.State → D.State × Text) :
    D.State × Text :=
  match result with
  | (state, text) => feed.prepend D text (rest state)

-- Give `buffers` to `D.decode_buffer` in order, starting from `state`,
-- and join the text that the calls return.

def feed (D : Decoder) : List (List UInt8) → D.State → D.State × Text
  | [], state =>
    (state, [])
  | buffer :: rest, state =>
    feed.then D (D.decode_buffer state buffer)
      (fun s => feed D rest s)

-- The text returned for `buffers`, without calling `D.decode_done`.

def decoded_so_far.text (D : Decoder) (fed : D.State × Text) : Text :=
  match fed with
  | (_state, text) => text

def decoded_so_far (D : Decoder) (buffers : List (List UInt8)) : Text :=
  decoded_so_far.text D (feed D buffers D.start)

-- The text returned for `buffers`, including calling `D.decode_done`.

def decoded.text (D : Decoder) (fed : D.State × Text) : Text :=
  match fed with
  | (state, text) => text ++ D.decode_done state

def decoded (D : Decoder) (buffers : List (List UInt8)) : Text :=
  decoded.text D (feed D buffers D.start)


-- ## Running the decoder satisfies `decodes`

-- In whatever way the input is split into buffers, giving them in
-- order to `D.decode_buffer` and then calling `D.decode_done`
-- gives what their concatenation decodes to.
--
-- (`List.flatten` is Bend's `List.concat`: the concatenation of a list
-- of lists.  Lean's `List.concat` is a different function.)

def utf8_decodes (D : Decoder) : Prop :=
  ∀ buffers : List (List UInt8),
    decodes (List.flatten buffers) (decoded D buffers)

-- `pre` is a prefix of `text`.

def is_text_prefix (pre : Text) (text : Text) : Prop :=
  ∃ more : Text, pre ++ more = text

-- After each buffer, the decoder has returned the longest text that
-- every continuation of the input agrees on.  This has two halves.

-- Safe: whatever bytes follow, the whole input decodes to text that
-- begins with the text returned so far.  Later bytes cannot change
-- anything already returned.

def utf8_decode_buffer_safe (D : Decoder) : Prop :=
  ∀ (buffers : List (List UInt8)) (rest : List UInt8) (full : Text),
    decodes (List.flatten buffers ++ rest) full →
    is_text_prefix (decoded_so_far D buffers) full

-- Prompt: nothing is held back.  No longer text is safe: for any code
-- point `c`, some bytes could follow for which the whole input does not
-- decode to text beginning with the text returned so far followed by
-- `c`.

def utf8_decode_buffer_prompt (D : Decoder) : Prop :=
  ∀ (buffers : List (List UInt8)) (c : UInt32),
    ∃ rest : List UInt8,
      ∃ full : Text,
        decodes (List.flatten buffers ++ rest) full ∧
        ¬ is_text_prefix (decoded_so_far D buffers ++ code_point_to_string c) full

-- Not in LAWS.bend: the three streaming laws together, for
-- convenience.

def Decoder.Correct (D : Decoder) : Prop :=
  utf8_decodes D ∧
  utf8_decode_buffer_safe D ∧
  utf8_decode_buffer_prompt D
