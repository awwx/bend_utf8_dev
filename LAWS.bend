import Base
import ./defs.bend as Defs
import ./binary.bend as B
import ./utf8.bend as UTF8
import ./binary_LAWS.bend as BinaryLaws

# UTF8 one byte shape
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
      Some{B.bit8_value((False{}, y1, y2, y3, z1, z2, z3, z4))}
    case _:
      None{}

def one_byte_shape(cp: U32) -> Maybe<&2, U32>:
  one_byte_shape.bits(B.u32_byte4(cp))

# Specification for whether we can encode a codepoint as one byte: yes
# iff one_byte_shape matches.

def can_encode_as_one_byte(cp: U32) -> Bool:
  Maybe.is_some(&2, U32, one_byte_shape(cp))

law utf8_can_encode_one:
  for +cp: U32
  {UTF8.can_encode_one(cp) == can_encode_as_one_byte(cp) : Bool}

law utf8_encode_one:
  for +cp: U32
  for valid: {U32.is_le(cp, 127) == True{} : Bool}
  {UTF8.encode_one(cp, valid) == cp : U32}


# UTF8 two byte shape
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
      Some{(B.bit8_value((True{}, True{}, False{}, x1, x2, x3, y1, y2)),
            B.bit8_value((True{}, False{}, y3, y4, z1, z2, z3, z4)))}
    case _:
      None{}

def two_byte_shape(cp: U32) -> Maybe<&1, U32 & U32>:
  two_byte_shape.bits(B.u32_byte4(cp))

# Specification for utf8.can_encode_two: if should return True iff
# two_byte_shape matches.

law utf8_can_encode_two:
  for +cp: U32
  {UTF8.can_encode_two(cp) == Maybe.is_some(&1, U32 & U32, two_byte_shape(cp)) : Bool}


# An eleven-bit payload covers exactly the two-byte encoding capacity.
def codepoint11(bits: Word(11n)) -> U32:
  match bits:
    case WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WNil{}}}}}}}}}}}}:
      U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, Word.zero(21n)}}}}}}}}}}}}

# Encoding functions expose the representation of a given code point.

# For every encodable code point, the bytes must equal the reference model.
law utf8_encode_two:
  for +cp: U32
  for valid: {Maybe.is_some(&1, U32 & U32, two_byte_shape(cp)) == True{} : Bool}
  exs accepted: {UTF8.can_encode_two(cp) == True{} : Bool}
  {Some{UTF8.encode_two(cp, accepted)} == two_byte_shape(cp) : Maybe<&1, U32 & U32>}

# Leading and continuation bytes have the table's literal prefix bits.
law utf8_two_byte_shape:
  for +b1: U32
  for +b2: U32
  {UTF8.two_byte_shape(b1, b2) ==
    (B.byte_mask("110xxxxx", b1, {==}) && B.byte_mask("10xxxxxx", b2, {==})) : Bool}

# Join the leading byte's five payload bits and the continuation's six bits.
law utf8_decode_two:
  for +b1: U32
  for +b2: U32
  {UTF8.decode_two(b1, b2) ==
    (U32.shln(U32.and(b1, 31), 6n) + U32.and(b2, 63) : U32) : U32}

# Overlong means that the same decoded code point fits in one byte.
law utf8_overlong_two:
  for +b1: U32
  for +b2: U32
  {UTF8.overlong_two(b1, b2) ==
    (UTF8.two_byte_shape(b1, b2) &&
     UTF8.can_encode_one(UTF8.decode_two(b1, b2))) : Bool}

law utf8_valid_two:
  for +b1: U32
  for +b2: U32
  {UTF8.valid_two(b1, b2) ==
    (UTF8.two_byte_shape(b1, b2) &&
     Bool.not(UTF8.overlong_two(b1, b2))) : Bool}

# Every eleven-bit code point has a two-byte representation. It round-trips,
# and is valid exactly when its code point needs more than one byte.
# The first-byte range is a consequence, rather than the validity definition.
law utf8_two_capacity:
  for +bits: Word(11n)
  +cp = codepoint11(bits)
  {Maybe.is_some(&1, U32 & U32, two_byte_shape(cp)) == True{} : Bool}

law utf8_two_roundtrip:
  for +bits: Word(11n)
  +cp = codepoint11(bits)
  +accepted = Equal.trans(Bool, UTF8.can_encode_two(cp),
    Maybe.is_some(&1, U32 & U32, two_byte_shape(cp)), True{},
    utf8_can_encode_two(cp), utf8_two_capacity(bits))
  +b1 = B.first(UTF8.encode_two(cp, accepted))
  +b2 = B.second(UTF8.encode_two(cp, accepted))
  {UTF8.decode_two(b1, b2) == cp : U32} &
  {UTF8.two_byte_shape(b1, b2) == True{} : Bool} &
  {UTF8.overlong_two(b1, b2) == UTF8.can_encode_one(cp) : Bool} &
  {UTF8.valid_two(b1, b2) == U32.is_ge(cp, 128) : Bool} &
  {UTF8.valid_two(b1, b2) ==
    ((U32.is_ge(b1, 194) && U32.is_le(b1, 223)) &&
     (U32.is_ge(b2, 128) && U32.is_le(b2, 191))) : Bool}

law utf8_encoding_examples:
  {UTF8.encode_one(0, {==}) == 0 : U32} &
  {UTF8.encode_one(127, {==}) == 127 : U32} &
  {UTF8.can_encode_one(128) == False{} : Bool} &
  {UTF8.encode_two(0, {==}) == (192, 128) : U32 & U32} &
  {UTF8.encode_two(127, {==}) == (193, 191) : U32 & U32} &
  {UTF8.encode_two(128, {==}) == (194, 128) : U32 & U32} &
  {UTF8.encode_two(2047, {==}) == (223, 191) : U32 & U32} &
  {UTF8.can_encode_two(2048) == False{} : Bool} &
  {UTF8.overlong_two(192, 128) == True{} : Bool} &
  {UTF8.overlong_two(193, 191) == True{} : Bool} &
  {UTF8.valid_two(192, 128) == False{} : Bool} &
  {UTF8.valid_two(193, 191) == False{} : Bool} &
  {UTF8.valid_two(194, 128) == True{} : Bool} &
  {UTF8.valid_two(223, 191) == True{} : Bool} &
  {UTF8.valid_two(194, 127) == False{} : Bool} &
  {UTF8.valid_two(224, 128) == False{} : Bool}

law two_byte_shape_examples:
  {two_byte_shape(0) == Some{(192, 128)} : Maybe<&1, U32 & U32>} &
  {two_byte_shape(127) == Some{(193, 191)} : Maybe<&1, U32 & U32>} &
  {two_byte_shape(128) == Some{(194, 128)} : Maybe<&1, U32 & U32>} &
  {two_byte_shape(2047) == Some{(223, 191)} : Maybe<&1, U32 & U32>} &
  {two_byte_shape(2048) == None{} : Maybe<&1, U32 & U32>} &
  {two_byte_shape(65536) == None{} : Maybe<&1, U32 & U32>} &
  {two_byte_shape(4294967295) == None{} : Maybe<&1, U32 & U32>}
