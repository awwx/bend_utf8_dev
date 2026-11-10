import Base
import ./defs.bend as Defs
import ./binary.bend as B
import ./utf8.bend as UTF8
import ./func_LAWS.bend as Func

## Bits to bytes helper

# Given a tuple of eight bools, return the U32 value of the binary
# integer, most significant bit first.
def bit8_value(bit8: Defs.Bit8()) -> U32:
  (b7, b6, b5, b4, b3, b2, b1, b0) = bit8
  U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, Word.zero(24n)}}}}}}}}}

# Given 8 booleans used as bits, most significant bit first, convert
# to its U32 value 0..255.  Higher U32 bits are zero.

law bit8_value_sum:
  for +b7: Bool
  for +b6: Bool
  for +b5: Bool
  for +b4: Bool
  for +b3: Bool
  for +b2: Bool
  for +b1: Bool
  for +b0: Bool
  {bit8_value((b7, b6, b5, b4, b3, b2, b1, b0)) ==
    (Bool.to_u32(b7) * 128 +
     Bool.to_u32(b6) * 64 +
     Bool.to_u32(b5) * 32 +
     Bool.to_u32(b4) * 16 +
     Bool.to_u32(b3) * 8 +
     Bool.to_u32(b2) * 4 +
     Bool.to_u32(b1) * 2 +
     Bool.to_u32(b0) * 1 : U32) : U32}

# Provide an independent check of `bit8_value`: convert the booleans
# to a Word(8n), then to a Nat, and then to a U32.

law bit8_value_word:
  for +b7: Bool
  for +b6: Bool
  for +b5: Bool
  for +b4: Bool
  for +b3: Bool
  for +b2: Bool
  for +b1: Bool
  for +b0: Bool
  # Word stores its least significant bit first.
  word = {WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WNil{}}}}}}}}} : Word(8n)}
  {bit8_value((b7, b6, b5, b4, b3, b2, b1, b0)) ==
    U32.from_nat(Word.to_nat(8n, word)) : U32}


### UTF-8 encoding specification

## Surrogate code points

# Surrogate code points are U+D800..U+DFFF.

def is_surrogate_code_point(+cp: U32) -> Bool:
  U32.is_ge(cp, Char.to_u32('\u{D800}')) &&
  U32.is_le(cp, Char.to_u32('\u{DFFF}'))

law is_surrogate_code_point_examples:
  {is_surrogate_code_point(Char.to_u32('\u{0000}')) == False{} : Bool} &
  {is_surrogate_code_point(Char.to_u32('\u{D7FF}')) == False{} : Bool} &
  {is_surrogate_code_point(Char.to_u32('\u{D800}')) == True{} : Bool} &
  {is_surrogate_code_point(Char.to_u32('\u{DC00}')) == True{} : Bool} &
  {is_surrogate_code_point(Char.to_u32('\u{DFFF}')) == True{} : Bool} &
  {is_surrogate_code_point(Char.to_u32('\u{E000}')) == False{} : Bool}


## Unicode scalars

# A Unicode scalar is any code point from U+0000 to U+10FFFF excluding
# surrogate code points.

def is_unicode_scalar(+cp: U32) -> Bool:
  U32.is_ge(cp, Char.to_u32('\u{000000}')) &&
  U32.is_le(cp, Char.to_u32('\u{10FFFF}')) &&
  Bool.not(is_surrogate_code_point(cp))


## Byte shapes

# By a "byte shape" we mean a series of bytes that has the correct bit
# pattern for a UTF-8 encoding.  This includes invalid UTF-8 encodings
# such as overlong encodings, encodings of surrogate code points, and
# encodings of code point values above U+10FFFF.

# UTF-8 one-byte shape
#
# 00000000 00000000 00000000 0yyyzzzz -> 0yyyzzzz
#
# Returns Some U32 representing the byte if the shape matches, or None
# if the shape doesn't match.

def one_byte_shape.bits(bits: Defs.Byte4()) -> Maybe<&2, U32>:
  match bits:
    case ((False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}),
          (False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}),
          (False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}),
          (False{}, y1, y2, y3, z1, z2, z3, z4)):
      Some{bit8_value((False{}, y1, y2, y3, z1, z2, z3, z4))}
    case _:
      None{}

def one_byte_shape(cp: U32) -> Maybe<&2, U32>:
  one_byte_shape.bits(B.u32_byte4(cp))

# UTF-8 two-byte shape
#
# 00000000 00000000 00000xxx yyyyzzzz -> 110xxxyy 10yyzzzz
#
# Returns two U32 representing the two bytes if the shape matches, or
# None if the shape doesn't match.
#
# Capacity includes overlong encodings of 0..127; shortest-form
# validity is separate.

def two_byte_shape.bits(bits: Defs.Byte4()) -> Maybe<&1, U32 & U32>:
  match bits:
    case ((False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}),
          (False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}),
          (False{}, False{}, False{}, False{}, False{}, x1, x2, x3),
          (y1, y2, y3, y4, z1, z2, z3, z4)):
      Some{(bit8_value((True{}, True{}, False{}, x1, x2, x3, y1, y2)),
            bit8_value((True{}, False{}, y3, y4, z1, z2, z3, z4)))}
    case _:
      None{}

def two_byte_shape(cp: U32) -> Maybe<&1, U32 & U32>:
  two_byte_shape.bits(B.u32_byte4(cp))

# UTF-8 three-byte shape
#
# 00000000 00000000 wwwwxxxx yyyyzzzz -> 1110wwww 10xxxxyy 10yyzzzz
#
# Returns three U32 representing the three bytes if the shape matches,
# or None if the shape doesn't match.
#
# Capacity includes overlong encodings of 0..2047 and encodings of
# surrogate code points; validity is separate.

def three_byte_shape.bits(bits: Defs.Byte4()) -> Maybe<&1, U32 & U32 & U32>:
  match bits:
    case ((False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}),
          (False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}),
          (w1, w2, w3, w4, x1, x2, x3, x4),
          (y1, y2, y3, y4, z1, z2, z3, z4)):
      Some{(bit8_value((True{}, True{}, True{}, False{}, w1, w2, w3, w4)),
            bit8_value((True{}, False{}, x1, x2, x3, x4, y1, y2)),
            bit8_value((True{}, False{}, y3, y4, z1, z2, z3, z4)))}
    case _:
      None{}

def three_byte_shape(cp: U32) -> Maybe<&1, U32 & U32 & U32>:
  three_byte_shape.bits(B.u32_byte4(cp))

# UTF-8 four-byte shape
#
# 00000000 000uvvvv wwwwxxxx yyyyzzzz -> 11110uvv 10vvwwww 10xxxxyy 10yyzzzz
#
# Returns four U32 representing the four bytes if the shape matches,
# or None if the shape doesn't match.
#
# Capacity includes overlong encodings of 0..65535 and encodings of
# code point values above U+10FFFF; validity is separate.

def four_byte_shape.bits(bits: Defs.Byte4()) -> Maybe<&1, U32 & U32 & U32 & U32>:
  match bits:
    case ((False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}),
          (False{}, False{}, False{}, u, v1, v2, v3, v4),
          (w1, w2, w3, w4, x1, x2, x3, x4),
          (y1, y2, y3, y4, z1, z2, z3, z4)):
      Some{(bit8_value((True{}, True{}, True{}, True{}, False{}, u, v1, v2)),
            bit8_value((True{}, False{}, v3, v4, w1, w2, w3, w4)),
            bit8_value((True{}, False{}, x1, x2, x3, x4, y1, y2)),
            bit8_value((True{}, False{}, y3, y4, z1, z2, z3, z4)))}
    case _:
      None{}

def four_byte_shape(cp: U32) -> Maybe<&1, U32 & U32 & U32 & U32>:
  four_byte_shape.bits(B.u32_byte4(cp))


## Can encode

# A code point can be encoded as a sequence of bytes iff the shape
# matches.

law utf8_can_encode_as_one_byte:
  for +cp: U32
  {UTF8.can_encode_as_one_byte(cp) == Maybe.is_some(&2, U32, one_byte_shape(cp)) : Bool}

law utf8_can_encode_as_two_bytes:
  for +cp: U32
  {UTF8.can_encode_as_two_bytes(cp) == Maybe.is_some(&1, U32 & U32, two_byte_shape(cp)) : Bool}

law utf8_can_encode_as_three_bytes:
  for +cp: U32
  {UTF8.can_encode_as_three_bytes(cp) == Maybe.is_some(&1, U32 & U32 & U32, three_byte_shape(cp)) : Bool}

law utf8_can_encode_as_four_bytes:
  for +cp: U32
  {UTF8.can_encode_as_four_bytes(cp) == Maybe.is_some(&1, U32 & U32 & U32 & U32, four_byte_shape(cp)) : Bool}


## Encode as

# Given a code point and a supplied proof that the code point *can* be
# encoded as a byte sequence, `encode_as_*` returns those bytes.
# (Supplying the proof means that we don't have to return a Maybe.)

law utf8_encode_as_one_byte:
  for +cp: U32
  for valid: {UTF8.can_encode_as_one_byte(cp) == True{} : Bool}
  {Some{UTF8.encode_as_one_byte(cp, valid)} == one_byte_shape(cp) : Maybe<&2, U32>}

law utf8_encode_as_two_bytes:
  for +cp: U32
  for valid: {UTF8.can_encode_as_two_bytes(cp) == True{} : Bool}
  {Some{UTF8.encode_as_two_bytes(cp, valid)} == two_byte_shape(cp) : Maybe<&1, U32 & U32>}

law utf8_encode_as_three_bytes:
  for +cp: U32
  for valid: {UTF8.can_encode_as_three_bytes(cp) == True{} : Bool}
  {Some{UTF8.encode_as_three_bytes(cp, valid)} == three_byte_shape(cp) : Maybe<&1, U32 & U32 & U32>}

law utf8_encode_as_four_bytes:
  for +cp: U32
  for valid: {UTF8.can_encode_as_four_bytes(cp) == True{} : Bool}
  {Some{UTF8.encode_as_four_bytes(cp, valid)} == four_byte_shape(cp) : Maybe<&1, U32 & U32 & U32 & U32>}


## has_N_byte_shape(bytes) -> Bool

# Return True if the bytes have the byte shape for that number of
# bytes: that is, they are what some code point encodes to.  (At this
# point we're still ignoring overlong encodings.)

law utf8_has_one_byte_shape:
  for +byte: U32
  representation = Exists(U32, cp =>
    {one_byte_shape(cp) == Some{byte} : Maybe<&2, U32>})
  ({UTF8.has_one_byte_shape(byte) == True{} : Bool} -> representation) &
  (representation -> {UTF8.has_one_byte_shape(byte) == True{} : Bool})

law utf8_has_two_byte_shape:
  for +b1: U32
  for +b2: U32
  representation = Exists(U32, cp =>
    {two_byte_shape(cp) == Some{(b1, b2)} : Maybe<&1, U32 & U32>})
  ({UTF8.has_two_byte_shape(b1, b2) == True{} : Bool} -> representation) &
  (representation -> {UTF8.has_two_byte_shape(b1, b2) == True{} : Bool})

law utf8_has_three_byte_shape:
  for +b1: U32
  for +b2: U32
  for +b3: U32
  representation = Exists(U32, cp =>
    {three_byte_shape(cp) == Some{(b1, b2, b3)} : Maybe<&1, U32 & U32 & U32>})
  ({UTF8.has_three_byte_shape(b1, b2, b3) == True{} : Bool} -> representation) &
  (representation -> {UTF8.has_three_byte_shape(b1, b2, b3) == True{} : Bool})

law utf8_has_four_byte_shape:
  for +b1: U32
  for +b2: U32
  for +b3: U32
  for +b4: U32
  representation = Exists(U32, cp =>
    {four_byte_shape(cp) == Some{(b1, b2, b3, b4)} : Maybe<&1, U32 & U32 & U32 & U32>})
  ({UTF8.has_four_byte_shape(b1, b2, b3, b4) == True{} : Bool} -> representation) &
  (representation -> {UTF8.has_four_byte_shape(b1, b2, b3, b4) == True{} : Bool})


## Encoding is bijective

# Each encode_as_N_byte is bijective, and decode_N_byte is exactly its
# inverse.
#
# For a code point which *can be* encoded as the specified number of
# bytes, we can roundtrip `decode(encode(cp)) == cp` and vice versa.

law utf8_one_byte_inverse:
  Func.Bijection(U32, U32,
    cp => UTF8.can_encode_as_one_byte(cp),
    byte => UTF8.has_one_byte_shape(byte),
    cp => valid => UTF8.encode_as_one_byte(cp, valid),
    byte => valid => UTF8.decode_one_byte(byte, valid))

# The bytes of a two-, three- or four-byte encoding.

def two_bytes.first(p: U32 & U32) -> U32:
  (a, b) = p
  a

def two_bytes.second(p: U32 & U32) -> U32:
  (a, b) = p
  b

def three_bytes.first(p: U32 & U32 & U32) -> U32:
  (a, b, c) = p
  a

def three_bytes.second(p: U32 & U32 & U32) -> U32:
  (a, b, c) = p
  b

def three_bytes.third(p: U32 & U32 & U32) -> U32:
  (a, b, c) = p
  c

def four_bytes.first(p: U32 & U32 & U32 & U32) -> U32:
  (a, b, c, d) = p
  a

def four_bytes.second(p: U32 & U32 & U32 & U32) -> U32:
  (a, b, c, d) = p
  b

def four_bytes.third(p: U32 & U32 & U32 & U32) -> U32:
  (a, b, c, d) = p
  c

def four_bytes.fourth(p: U32 & U32 & U32 & U32) -> U32:
  (a, b, c, d) = p
  d

law utf8_two_byte_inverse:
  Func.Bijection(U32, U32 & U32,
    cp => UTF8.can_encode_as_two_bytes(cp),
    p => UTF8.has_two_byte_shape(two_bytes.first(p), two_bytes.second(p)),
    cp => valid => UTF8.encode_as_two_bytes(cp, valid),
    p => valid => UTF8.decode_two_bytes(two_bytes.first(p), two_bytes.second(p), valid))

law utf8_three_byte_inverse:
  Func.Bijection(U32, U32 & U32 & U32,
    cp => UTF8.can_encode_as_three_bytes(cp),
    p => UTF8.has_three_byte_shape(three_bytes.first(p), three_bytes.second(p), three_bytes.third(p)),
    cp => valid => UTF8.encode_as_three_bytes(cp, valid),
    p => valid => UTF8.decode_three_bytes(three_bytes.first(p), three_bytes.second(p), three_bytes.third(p), valid))

law utf8_four_byte_inverse:
  Func.Bijection(U32, U32 & U32 & U32 & U32,
    cp => UTF8.can_encode_as_four_bytes(cp),
    p => UTF8.has_four_byte_shape(four_bytes.first(p), four_bytes.second(p), four_bytes.third(p), four_bytes.fourth(p)),
    cp => valid => UTF8.encode_as_four_bytes(cp, valid),
    p => valid => UTF8.decode_four_bytes(four_bytes.first(p), four_bytes.second(p), four_bytes.third(p), four_bytes.fourth(p), valid))


## Overlong encodings

# In UTF-8, an "overlong" encoding is an encoding which is the correct
# shape for encoding the code point, but a shorter encoding also
# encodes the code point.  These are invalid in UTF-8.

# No one-byte encoding is overlong.

def overlong_one_byte(b1: U32) -> Bool:
  False{}

# A two-byte encoding is overlong if the code point it encodes could
# be encoded as a one byte encoding.

law utf8_overlong_two_bytes:
  for +b1: U32
  for +b2: U32
  for -valid_shape: {UTF8.has_two_byte_shape(b1, b2) == True{} : Bool}
  {UTF8.overlong_two_bytes(b1, b2, valid_shape) ==
    UTF8.can_encode_as_one_byte(UTF8.decode_two_bytes(b1, b2, valid_shape)) : Bool}

# A three-byte encoding is overlong if the code point it encodes could
# be encoded in one or two bytes.

law utf8_overlong_three_bytes:
  for +b1: U32
  for +b2: U32
  for +b3: U32
  for -valid_shape: {UTF8.has_three_byte_shape(b1, b2, b3) == True{} : Bool}
  {UTF8.overlong_three_bytes(b1, b2, b3, valid_shape) ==
    (UTF8.can_encode_as_one_byte(UTF8.decode_three_bytes(b1, b2, b3, valid_shape)) ||
     UTF8.can_encode_as_two_bytes(UTF8.decode_three_bytes(b1, b2, b3, valid_shape))) : Bool}

# A four-byte encoding is overlong if the code point it encodes could
# be encoded in one, two or three bytes.

law utf8_overlong_four_bytes:
  for +b1: U32
  for +b2: U32
  for +b3: U32
  for +b4: U32
  for -valid_shape: {UTF8.has_four_byte_shape(b1, b2, b3, b4) == True{} : Bool}
  {UTF8.overlong_four_bytes(b1, b2, b3, b4, valid_shape) ==
    (UTF8.can_encode_as_one_byte(UTF8.decode_four_bytes(b1, b2, b3, b4, valid_shape)) ||
     UTF8.can_encode_as_two_bytes(UTF8.decode_four_bytes(b1, b2, b3, b4, valid_shape)) ||
     UTF8.can_encode_as_three_bytes(UTF8.decode_four_bytes(b1, b2, b3, b4, valid_shape))) : Bool}


## Valid sequences

# A UTF-8 encoding is valid when:
# * It has the correct byte shape, and
# * It is not overlong, and
# * the code point it encodes is a Unicode scalar (at most U+10FFFF
#   and not a surrogate).
#
# A "valid sequence" is a sequence of bytes which are a valid UTF-8
# encoding.

# Testing the shape first supplies the proof that decoding needs.

def valid_one_byte.if(+byte: U32, shape: Bool,
  -checked: {UTF8.has_one_byte_shape(byte) == shape : Bool}) -> Bool:
  match shape:
    case False{}:
      False{}
    case True{}:
      Bool.not(overlong_one_byte(byte)) &&
      is_unicode_scalar(UTF8.decode_one_byte(byte, checked))

law utf8_valid_one_byte:
  for +byte: U32
  {UTF8.valid_one_byte(byte) == valid_one_byte.if(byte, UTF8.has_one_byte_shape(byte), {==}) : Bool}

def valid_two_bytes.if(+b1: U32, +b2: U32, shape: Bool,
  -checked: {UTF8.has_two_byte_shape(b1, b2) == shape : Bool}) -> Bool:
  match shape:
    case False{}:
      False{}
    case True{}:
      Bool.not(UTF8.overlong_two_bytes(b1, b2, checked)) &&
      is_unicode_scalar(UTF8.decode_two_bytes(b1, b2, checked))

law utf8_valid_two_bytes:
  for +b1: U32
  for +b2: U32
  {UTF8.valid_two_bytes(b1, b2) == valid_two_bytes.if(b1, b2, UTF8.has_two_byte_shape(b1, b2), {==}) : Bool}

def valid_three_bytes.if(+b1: U32, +b2: U32, +b3: U32, shape: Bool,
  -checked: {UTF8.has_three_byte_shape(b1, b2, b3) == shape : Bool}) -> Bool:
  match shape:
    case False{}:
      False{}
    case True{}:
      Bool.not(UTF8.overlong_three_bytes(b1, b2, b3, checked)) &&
      is_unicode_scalar(UTF8.decode_three_bytes(b1, b2, b3, checked))

law utf8_valid_three_bytes:
  for +b1: U32
  for +b2: U32
  for +b3: U32
  {UTF8.valid_three_bytes(b1, b2, b3) == valid_three_bytes.if(b1, b2, b3, UTF8.has_three_byte_shape(b1, b2, b3), {==}) : Bool}

def valid_four_bytes.if(+b1: U32, +b2: U32, +b3: U32, +b4: U32, shape: Bool,
  -checked: {UTF8.has_four_byte_shape(b1, b2, b3, b4) == shape : Bool}) -> Bool:
  match shape:
    case False{}:
      False{}
    case True{}:
      Bool.not(UTF8.overlong_four_bytes(b1, b2, b3, b4, checked)) &&
      is_unicode_scalar(UTF8.decode_four_bytes(b1, b2, b3, b4, checked))

law utf8_valid_four_bytes:
  for +b1: U32
  for +b2: U32
  for +b3: U32
  for +b4: U32
  {UTF8.valid_four_bytes(b1, b2, b3, b4) == valid_four_bytes.if(b1, b2, b3, b4, UTF8.has_four_byte_shape(b1, b2, b3, b4), {==}) : Bool}


## is_valid_sequence

# Returns True when the sequence is exactly a valid sequence.

def is_valid_sequence(seq: List<&2, U32>) -> Bool:
  match seq:
    case +b1 <> Nil{}:
      UTF8.valid_one_byte(b1)
    case +b1 <> +b2 <> Nil{}:
      UTF8.valid_two_bytes(b1, b2)
    case +b1 <> +b2 <> +b3 <> Nil{}:
      UTF8.valid_three_bytes(b1, b2, b3)
    case +b1 <> +b2 <> +b3 <> +b4 <> Nil{}:
      UTF8.valid_four_bytes(b1, b2, b3, b4)
    case _:
      False{}


## Encoding

# The UTF-8 encoding of `cp` is its shortest byte shape: one byte when
# `cp` has a one-byte shape, otherwise two, three or four.  (A longer
# encoding of a code point that has a shorter shape would be overlong.)
# Code points above U+1FFFFF have no encoding.

def encoding.four(shape: Maybe<&1, U32 & U32 & U32 & U32>) -> Maybe<&1, List<&2, U32>>:
  match shape:
    case None{}:
      None{}
    case Some{(b1, b2, b3, b4)}:
      Some{[b1, b2, b3, b4]}

def encoding.three(+cp: U32, shape: Maybe<&1, U32 & U32 & U32>) -> Maybe<&1, List<&2, U32>>:
  match shape:
    case None{}:
      encoding.four(four_byte_shape(cp))
    case Some{(b1, b2, b3)}:
      Some{[b1, b2, b3]}

def encoding.two(+cp: U32, shape: Maybe<&1, U32 & U32>) -> Maybe<&1, List<&2, U32>>:
  match shape:
    case None{}:
      encoding.three(cp, three_byte_shape(cp))
    case Some{(b1, b2)}:
      Some{[b1, b2]}

def encoding.if(+cp: U32, one: Maybe<&2, U32>) -> Maybe<&1, List<&2, U32>>:
  match one:
    case Some{b1}:
      Some{[b1]}
    case None{}:
      encoding.two(cp, two_byte_shape(cp))

def encoding(+cp: U32) -> Maybe<&1, List<&2, U32>>:
  encoding.if(cp, one_byte_shape(cp))

# `seq` is the UTF-8 encoding of the Unicode scalar `cp`.

def encodes(seq: List<&2, U32>, +cp: U32) -> Type:
  {is_unicode_scalar(cp) == True{} : Bool} &
  {encoding(cp) == Some{seq} : Maybe<&1, List<&2, U32>>}

# The valid sequences are exactly the encodings of Unicode scalars.

law valid_sequence_encodes:
  for +seq: List<&2, U32>
  encodes_some = Exists(U32, cp => encodes(seq, cp))
  ({is_valid_sequence(seq) == True{} : Bool} -> encodes_some) &
  (encodes_some -> {is_valid_sequence(seq) == True{} : Bool})


## A valid sequence at the front of a buffer

# `bytes` begins with a valid sequence that encodes `cp`, and `rest` is
# the bytes after it.

def begins_with_scalar(bytes: List<&2, U32>, cp: U32, rest: List<&2, U32>) -> Type:
  Exists(List<&2, U32>, seq =>
    encodes(seq, cp) &
    {List.append(&2, U32, seq, rest) == bytes : List<&2, U32>})

# `bytes` does not begin with a valid sequence.

def no_valid_sequence(bytes: List<&2, U32>) -> Type:
  @cp: U32 -> @rest: List<&2, U32> -> begins_with_scalar(bytes, cp, rest) -> Empty

# No valid sequence is a proper prefix of another, so a buffer begins
# with at most one valid sequence: the scalar and the bytes after it
# are unique.

law begins_with_scalar_unique:
  for +bytes: List<&2, U32>
  for +cp1: U32
  for +rest1: List<&2, U32>
  for +cp2: U32
  for +rest2: List<&2, U32>
  for first: begins_with_scalar(bytes, cp1, rest1)
  for second: begins_with_scalar(bytes, cp2, rest2)
  {cp1 == cp2 : U32} & {rest1 == rest2 : List<&2, U32>}


## Valid sequence prefix

# A "valid sequence prefix" is one or more bytes that begin a valid
# sequence (or could begin a valid sequence): there exists zero or
# more bytes which when added to them make a valid sequence.
#
# The empty list is not a valid sequence prefix; a valid sequence is
# also a valid sequence prefix.
#
# Later we may find out that the actual input doesn't describe a valid
# sequence, so this says that if we've only seen these bytes so far,
# they *could* be the start of a legal encoding (including being
# themselves a complete valid sequence).
#
# `UTF8.is_valid_sequence_prefix(seq)` returns True iff `seq` is a
# valid sequence prefix.

law utf8_is_valid_sequence_prefix:
  for +b1: U32
  for +more: List<&2, U32>
  completion = Exists(List<&2, U32>, rest =>
    {is_valid_sequence(List.append(&2, U32, b1 <> more, rest)) == True{} : Bool})
  ({UTF8.is_valid_sequence_prefix(b1 <> more) == True{} : Bool} -> completion) &
  (completion -> {UTF8.is_valid_sequence_prefix(b1 <> more) == True{} : Bool})

law utf8_empty_not_valid_sequence_prefix:
  {UTF8.is_valid_sequence_prefix(Nil{}) == False{} : Bool}

# While a non-valid sequence can sometimes become a valid sequence by
# adding more bytes (i.e. to complete the sequence), a non-empty
# sequence of bytes that is not a valid sequence *prefix* cannot
# become a valid prefix by adding more bytes.
#
# That is, a non-empty prefix which is not a valid sequence prefix
# stays as an invalid prefix no matter what bytes might be added to
# it.

law not_valid_sequence_prefix_extended:
  for +b1: U32
  for +more: List<&2, U32>
  for +extra: List<&2, U32>
  for invalid: {UTF8.is_valid_sequence_prefix(b1 <> more) == False{} : Bool}
  {UTF8.is_valid_sequence_prefix(List.append(&2, U32, b1 <> more, extra)) == False{} : Bool}


## Byte prefix

# We define a "prefix" to mean that the buffer begins with the bytes
# of the prefix.

def is_prefix(prefix: List<&2, U32>, bytes: List<&2, U32>) -> Type:
  Exists(List<&2, U32>, rest =>
    {List.append(&2, U32, prefix, rest) == bytes : List<&2, U32>})


## Maximal subparts

# Where the bytes being decoded do not begin with a valid sequence,
# the "maximal subpart" at their front is the run of bytes replaced by
# one U+FFFD (Unicode §3.9).  It is either:
#
# * the first byte alone, when it is not a valid sequence prefix; or,
#
# * when the first byte is a valid sequence prefix, the longest run of
#   bytes at the front that is also a valid sequence prefix.
#
# In the second case the prefix stops short of a whole sequence:
# either the input ends after it, or the next byte cannot extend it.

# `longer_not_valid_prefix` is a relation that states that if
# `subpart` is a prefix of `bytes`, adding one or more of the following
# bytes from `bytes` to the subpart will not produce a valid sequence
# prefix.
#
# By itself this relation doesn't say anything about whether `subpart`
# itself is a valid prefix, only that no longer prefix of `bytes` is a
# valid prefix.

def maximal_subpart.longer_not_valid_prefix(subpart: List<&2, U32>, bytes: List<&2, U32>) -> Type:
  @c: U32 -> @extra: List<&2, U32> ->
    is_prefix(List.append(&2, U32, subpart, c <> extra), bytes) ->
    {UTF8.is_valid_sequence_prefix(List.append(&2, U32, subpart, c <> extra)) == False{} : Bool}

# The maximal subpart when the first byte is a valid sequence prefix:
# `subpart` is the longest prefix of `b1 <> more` that is a valid
# sequence prefix.  (Unicode's "initial subsequence of a well-formed
# code unit sequence".)

def maximal_subpart.sequence_prefix(+b1: U32, +more: List<&2, U32>,
  +subpart: List<&2, U32>) -> Type:
  is_prefix(subpart, b1 <> more) &
  {UTF8.is_valid_sequence_prefix(subpart) == True{} : Bool} &
  maximal_subpart.longer_not_valid_prefix(subpart, b1 <> more)

# The maximal subpart when the first byte is not a valid sequence
# prefix: `subpart` is that byte alone.  (Unicode's "subsequence of
# length one".)  Unicode takes the longest subsequence that is either
# a valid sequence prefix or one byte long; here, by
# `not_valid_sequence_prefix_extended`, no longer prefix is a valid
# sequence prefix, so only the one-byte case applies.

def maximal_subpart.single_byte(+b1: U32, +subpart: List<&2, U32>) -> Type:
  {subpart == [b1] : List<&2, U32>}

def maximal_subpart.if(+b1: U32, +more: List<&2, U32>, begins: Bool,
  +subpart: List<&2, U32>) -> Type:
  match begins:
    case True{}:
      maximal_subpart.sequence_prefix(b1, more, subpart)
    case False{}:
      maximal_subpart.single_byte(b1, subpart)

# `subpart` is the maximal subpart at the front of the non-empty bytes
# `b1 <> more`, as the Unicode Standard defines it (§3.9): the longest
# prefix that is a valid sequence prefix, or else the first byte alone.
# Meant for bytes that do not begin with a valid sequence.

def maximal_subpart(+b1: U32, +more: List<&2, U32>,
  +subpart: List<&2, U32>) -> Type:
  maximal_subpart.if(b1, more, UTF8.is_valid_sequence_prefix([b1]), subpart)

# Now we check our definition of "maximal subpart".
#
# Given a non-empty buffer that doesn't begin with a valid sequence, a
# maximal subpart both exists and is unique.

law maximal_subpart_exists:
  for +b1: U32
  for +more: List<&2, U32>
  for invalid: no_valid_sequence(b1 <> more)
  Exists(List<&2, U32>, subpart => maximal_subpart(b1, more, subpart))

law maximal_subpart_unique:
  for +b1: U32
  for +more: List<&2, U32>
  for +s1: List<&2, U32>
  for +s2: List<&2, U32>
  for p1: maximal_subpart(b1, more, s1)
  for p2: maximal_subpart(b1, more, s2)
  {s1 == s2 : List<&2, U32>}


### Decoding a complete buffer.

# We start by specifying how a complete buffer is decoded, and later
# we'll require that stream decoding must have the same result.


## Unicode replacement character

# Ill-formed input is replaced as the Unicode Standard recommends (§3.9,
# "U+FFFD Substitution of Maximal Subparts"): each maximal subpart, the
# longest run of bytes that is a valid sequence prefix or else a single
# byte, becomes one U+FFFD.

def code_point_to_string(cp: U32) -> String:
  SCon{Chr{cp}, SNil{}}

# U+FFFD REPLACEMENT CHARACTER.

def replacement_char() -> U32:
  Char.to_u32('\u{FFFD}')

# U+FFFD REPLACEMENT CHARACTER, as a one-character string.

def replacement_char_string() -> String:
  code_point_to_string(replacement_char())


## Decoding the first code point of a complete buffer

# These relations are on complete buffers: an incomplete sequence at
# the end of the buffer results in a replacement character.

# For use with a non-empty buffer (the first byte `b1` and the
# remaining bytes `more`) that doesn't begin with a valid sequence,
# `decodes_first.replaced` is a relation which states that, for some
# `subpart` and `rest`:
#
# * `subpart` is the maximal subpart at the front of the buffer;
#
# * the buffer is `subpart` followed by `rest`; and
#
# * `result` is the Unicode replacement character and `rest`.

def decodes_first.replaced(+b1: U32, +more: List<&2, U32>,
  result: Maybe<&1, U32 & List<&2, U32>>) -> Type:
  Exists(List<&2, U32>, subpart => Exists(List<&2, U32>, rest =>
    maximal_subpart(b1, more, subpart) &
    {List.append(&2, U32, subpart, rest) == b1 <> more : List<&2, U32>} &
    {result == Some{(replacement_char(), rest)} : Maybe<&1, U32 & List<&2, U32>>}))

# `bytes` begins with a valid sequence, and `result` is the scalar that
# it encodes and the bytes after it.

def decodes_first.scalar(bytes: List<&2, U32>,
  result: Maybe<&1, U32 & List<&2, U32>>) -> Type:
  Exists(U32, cp => Exists(List<&2, U32>, rest =>
    begins_with_scalar(bytes, cp, rest) &
    {result == Some{(cp, rest)} : Maybe<&1, U32 & List<&2, U32>>}))

# Decoding the first code point of the non-empty buffer `b1 <> more`
# gives `result`: the scalar of the valid sequence at the front of the
# buffer and the bytes after it, or, when the buffer doesn't begin with
# a valid sequence, the replaced result.

def decodes_first.nonempty(+b1: U32, +more: List<&2, U32>,
  result: Maybe<&1, U32 & List<&2, U32>>) -> Type:
  Or(decodes_first.scalar(b1 <> more, result),
    no_valid_sequence(b1 <> more) & decodes_first.replaced(b1, more, result))

# Decoding the first code point of the complete buffer `bytes` gives
# `result`: None if `bytes` is empty, otherwise the code point and the
# bytes that follow it.

def decodes_first(bytes: List<&2, U32>,
  result: Maybe<&1, U32 & List<&2, U32>>) -> Type:
  match bytes:
    case Nil{}:
      {result == None{} : Maybe<&1, U32 & List<&2, U32>>}
    case +b1 <> +more:
      decodes_first.nonempty(b1, more, result)

# Now we add some checks for our definition.

# We check that for any buffer, decodes_first implies that a result
# exists. (That is, we haven't created a definition for which there is
# some buffer that no `result` value at all satisfies the definition.)
# The result itself can be None or Some, we just require that there is
# one.

law decodes_first_exists:
  for +bytes: List<&2, U32>
  Exists(Maybe<&1, U32 & List<&2, U32>>, result => decodes_first(bytes, result))

# We also check for uniqueness: for any buffer, there is only one
# `result` value which satisfies our definition.

law decodes_first_unique:
  for +bytes: List<&2, U32>
  for r1: Maybe<&1, U32 & List<&2, U32>>
  for r2: Maybe<&1, U32 & List<&2, U32>>
  for d1: decodes_first(bytes, r1)
  for d2: decodes_first(bytes, r2)
  {r1 == r2 : Maybe<&1, U32 & List<&2, U32>>}

# Check that decoding the first code point of an empty buffer gives
# None.  This is trivial given our decodes_first def above, but we
# include for completeness.

law decodes_first_empty:
  for result: Maybe<&1, U32 & List<&2, U32>>
  for decoded: decodes_first([], result)
  {result == None{} : Maybe<&1, U32 & List<&2, U32>>}

# Check that decoding the first code point of any non-empty buffer
# always gives Some.

law decodes_first_nonempty:
  for +b1: U32
  for +more: List<&2, U32>
  for result: Maybe<&1, U32 & List<&2, U32>>
  for decoded: decodes_first(b1 <> more, result)
  {Maybe.is_some(&1, U32 & List<&2, U32>, result) == True{} : Bool}

# Decoding the complete buffer `bytes` gives the string `text`: empty if
# there is nothing to decode, otherwise the code point that
# `decodes_first` gives followed by the text from decoding the bytes
# after it.
#
# The recursion is on `text`, which shrinks at each step, so `text`
# comes first in `decodes.go`.

def decodes.go(text: String, bytes: List<&2, U32>) -> Type:
  match text:
    case SNil{}:
      decodes_first(bytes, None{})
    case SCon{Chr{cp}, more}:
      Exists(List<&2, U32>, rest =>
        decodes_first(bytes, Some{(cp, rest)}) & decodes.go(more, rest))

def decodes(bytes: List<&2, U32>, text: String) -> Type:
  decodes.go(text, bytes)

# Every buffer decodes to some text.

law decodes_exists:
  for +bytes: List<&2, U32>
  Exists(String, text => decodes(bytes, text))

# A buffer decodes to only one text.

law decodes_unique:
  for +bytes: List<&2, U32>
  for +t1: String
  for +t2: String
  for d1: decodes(bytes, t1)
  for d2: decodes(bytes, t2)
  {t1 == t2 : String}

# Bytes in hex: 65 = 0x41 "A", 66 = 0x42 "B", 72 = 0x48 "H",
# 128 = 0x80, 130 = 0x82, 144 = 0x90, 152 = 0x98, 159 = 0x9F,
# 160 = 0xA0, 169 = 0xA9, 172 = 0xAC, 192 = 0xC0, 194 = 0xC2,
# 224 = 0xE0, 226 = 0xE2, 237 = 0xED, 240 = 0xF0, 244 = 0xF4,
# 255 = 0xFF.

law decodes_examples:
  # Nothing to decode.
  decodes([], "") &
  # One-byte sequences.
  decodes([65, 66], "AB") &
  # A two-byte sequence: C2 A9 is U+00A9.
  decodes([194, 169], code_point_to_string(169)) &
  # A lead byte followed by a byte that cannot continue it: the lead
  # byte is replaced, and "A" decodes afresh.
  decodes([194, 65], replacement_char_string() ++ "A") &
  # C0 is not a valid sequence prefix (it would be overlong), nor is
  # a lone continuation byte: each is replaced separately.
  decodes([192, 128], replacement_char_string() ++ replacement_char_string()) &
  # A sequence left unfinished at the end of the buffer is replaced.
  decodes([194], replacement_char_string()) &
  # The second C2 cannot continue the first; it then begins C2 A9.
  decodes([194, 194, 169], replacement_char_string() ++ code_point_to_string(169)) &
  # Valid sequences around a byte that never appears in UTF-8.
  decodes([72, 194, 169, 255],
    "H" ++ code_point_to_string(169) ++ replacement_char_string()) &
  # A three-byte sequence: E2 82 AC is U+20AC.
  decodes([226, 130, 172], code_point_to_string(8364)) &
  # A four-byte sequence: F0 9F 98 80 is U+1F600.
  decodes([240, 159, 152, 128], code_point_to_string(128512)) &
  # The two bytes of an unfinished three-byte sequence are one maximal
  # subpart, so they give one replacement character.
  decodes([226, 130], replacement_char_string()) &
  # The same subpart when the next byte cannot continue it.
  decodes([226, 130, 65], replacement_char_string() ++ "A") &
  # Three bytes of an unfinished four-byte sequence are also one
  # maximal subpart.
  decodes([240, 159, 152], replacement_char_string()) &
  # E0 80 would be overlong: E0 must be followed by A0..BF.
  decodes([224, 128, 128],
    replacement_char_string() ++ replacement_char_string() ++ replacement_char_string()) &
  # ED A0 would begin a surrogate: ED must be followed by 80..9F.
  decodes([237, 160, 128],
    replacement_char_string() ++ replacement_char_string() ++ replacement_char_string()) &
  # F4 90 would exceed U+10FFFF: F4 must be followed by 80..8F.
  decodes([244, 144, 128, 128],
    replacement_char_string() ++ replacement_char_string() ++
    replacement_char_string() ++ replacement_char_string())


### Stream decoding

# `UTF8.decode_start_state()` is the decoder state before any input.
#
# `UTF8.decode_buffer(state, buffer, valid)` takes the next buffer of
# bytes, with an erased proof `valid` that its values are bytes, and
# returns the new state and the text that is now fully resolved.
#
# `UTF8.decode_done(state)` returns the text that ends the input.
#
# The state type, `UTF8.DecodeState()`, is the implementation's
# choice: the laws below only describe the text that comes out.

# We'll show that regardless of how the input is split into buffers,
# the result of the stream decoding (all of the text returned by
# `UTF8.decode_buffer` and `UTF8.decode_done`, concatenated together)
# satisfies our specification for decoding a complete input (all the
# buffers concatenated together).

# We'll also show that each call to `decode_buffer` returns all of the
# text that *can* be returned based on the input buffers seen so far.
# (Otherwise, for example, an implementation could keep all the input
# buffers in the state and then deliver the entire decoded text from
# the call to `decode_done`.)

## all_bytes

# As of Bend 2.0.40 byte buffers are delivered by base.bend as lists
# of U32, but they are not type restricted to a byte value of 0..255.
# `all_bytes` checks that all the U32 values in a list are 0..255.

def all_bytes(bytes: List<&2, U32>) -> Bool:
  List.all(~&2, ~U32, ~(b => U32.is_le(b, 255)), bytes)

# `UTF8.decode_buffer` requires an erased proof that its buffer passes
# `UTF8.decode_buffer.all_bytes`, which is the same test as `all_bytes`.

law utf8_decode_buffer_all_bytes:
  for +bytes: List<&2, U32>
  {UTF8.decode_buffer.all_bytes(bytes) == all_bytes(bytes) : Bool}


## Running the decoder

# We define a function `decoded`:
#
# `decoded(buffers: List<&2, List<&2, U32>>, -valid: all_buffers_bytes(buffers)) -> String`
#
# It takes a list of buffers, where each buffer is a list of bytes,
# and an erased proof that every buffer holds only byte values.  It
# returns the output text, the concatenation of the text returned by
# the calls to `decode_buffer` and the final call to `decode_done`.

# Every buffer holds only bytes, stated as the proofs that
# `UTF8.decode_buffer` requires.

def all_buffers_bytes(buffers: List<&2, List<&2, U32>>) -> Type:
  match buffers:
    case Nil{}:
      Unit
    case buffer <> rest:
      {UTF8.decode_buffer.all_bytes(buffer) == True{} : Bool} & all_buffers_bytes(rest)

# `feed` can't match on its erased proof, so it takes the proof apart
# with these.

def all_buffers_bytes.head(+buffer: List<&2, U32>, +rest: List<&2, List<&2, U32>>,
  valid: all_buffers_bytes(buffer <> rest)) -> {UTF8.decode_buffer.all_bytes(buffer) == True{} : Bool}:
  (head, tail) = valid
  head

def all_buffers_bytes.tail(+buffer: List<&2, U32>, +rest: List<&2, List<&2, U32>>,
  valid: all_buffers_bytes(buffer <> rest)) -> all_buffers_bytes(rest):
  (head, tail) = valid
  tail

# To keep track of our state running the decoder, we use a pair of the
# decoder state that we need to pass to the decoder functions and the
# concatenated text returned so far.

def feed.prepend(text: String, result: UTF8.DecodeState() & String) ->
  UTF8.DecodeState() & String:
  (state, more) = result
  (state, text ++ more)

def feed.then(result: UTF8.DecodeState() & String,
  rest: UTF8.DecodeState() -> UTF8.DecodeState() & String) ->
  UTF8.DecodeState() & String:
  (state, text) = result
  feed.prepend(text, rest(state))

# Give `buffers` to `UTF8.decode_buffer` in order, starting from `state`,
# and join the text that the calls return.

def feed(+buffers: List<&2, List<&2, U32>>, -valid: all_buffers_bytes(buffers),
  state: UTF8.DecodeState()) -> UTF8.DecodeState() & String:
  match buffers:
    case Nil{}:
      (state, "")
    case +buffer <> +rest:
      feed.then(UTF8.decode_buffer(state, buffer, all_buffers_bytes.head(buffer, rest, valid)),
        s => feed(rest, all_buffers_bytes.tail(buffer, rest, valid), s))

# The text returned for `buffers`, without calling `UTF8.decode_done`.

def decoded_so_far.text(fed: UTF8.DecodeState() & String) -> String:
  (state, text) = fed
  text

def decoded_so_far(+buffers: List<&2, List<&2, U32>>,
  -valid: all_buffers_bytes(buffers)) -> String:
  decoded_so_far.text(feed(buffers, valid, UTF8.decode_start_state()))

# The text returned for `buffers`, including calling `UTF8.decode_done`.

def decoded.text(fed: UTF8.DecodeState() & String) -> String:
  (state, text) = fed
  text ++ UTF8.decode_done(state)

def decoded(+buffers: List<&2, List<&2, U32>>,
  -valid: all_buffers_bytes(buffers)) -> String:
  decoded.text(feed(buffers, valid, UTF8.decode_start_state()))


## Running the decoder satisfies `decodes`

# In whatever way the input is split into buffers, giving them in
# order to `UTF8.decode_buffer` and then calling `UTF8.decode_done`
# gives what their concatenation decodes to.

law utf8_decodes:
  for +buffers: List<&2, List<&2, U32>>
  for -valid: all_buffers_bytes(buffers)
  decodes(List.concat(&2, U32, buffers), decoded(buffers, valid))

# `prefix` is a prefix of `text`.

def is_text_prefix(prefix: String, text: String) -> Type:
  Exists(String, more => {prefix ++ more == text : String})

# After each buffer, the decoder has returned the longest text that
# every continuation of the input agrees on.  This has two halves.

# Safe: whatever bytes follow, the whole input decodes to text that
# begins with the text returned so far.  Later bytes cannot change
# anything already returned.

law utf8_decode_buffer_safe:
  for +buffers: List<&2, List<&2, U32>>
  for -valid: all_buffers_bytes(buffers)
  for +rest: List<&2, U32>
  for +full: String
  for decodes_full: decodes(List.append(&2, U32, List.concat(&2, U32, buffers), rest), full)
  is_text_prefix(decoded_so_far(buffers, valid), full)

# Prompt: nothing is held back.  No longer text is safe: for any code
# point `c`, some bytes could follow for which the whole input does not
# decode to text beginning with the text returned so far followed by
# `c`.

law utf8_decode_buffer_prompt:
  for +buffers: List<&2, List<&2, U32>>
  for -valid: all_buffers_bytes(buffers)
  for +c: U32
  Exists(List<&2, U32>, rest =>
    {all_bytes(rest) == True{} : Bool} &
    Exists(String, full =>
      decodes(List.append(&2, U32, List.concat(&2, U32, buffers), rest), full) &
      (is_text_prefix(decoded_so_far(buffers, valid) ++ code_point_to_string(c), full) -> Empty)))
