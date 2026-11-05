import Base
import ./defs.bend as Defs
import ./binary.bend as B
import ./utf8.bend as UTF8
import ./binary_LAWS.bend as BinaryLaws
import ./hexdigits.bend as H

# By a "byte shape" we mean a series of bytes that has the correct bit
# pattern for a UTF-8 encoding.  This includes invalid UTF-8 encodings
# such as overlong encodings, encodings of surrogate code points, and
# encodings of code points values above U+10FFFF.

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
      Some{B.bit8_value((False{}, y1, y2, y3, z1, z2, z3, z4))}
    case _:
      None{}

def one_byte_shape(cp: U32) -> Maybe<&2, U32>:
  one_byte_shape.bits(B.u32_byte4(cp))

# A code point can be encoded as one byte iff iff one_byte_shape
# matches.

def can_encode_as_one_byte(cp: U32) -> Bool:
  Maybe.is_some(&2, U32, one_byte_shape(cp))

law utf8_can_encode_as_one_byte:
  for +cp: U32
  {UTF8.can_encode_as_one_byte(cp) == can_encode_as_one_byte(cp) : Bool}

law utf8_encode_as_one_byte:
  for +cp: U32
  for valid: {UTF8.can_encode_as_one_byte(cp) == True{} : Bool}
  {Some{UTF8.encode_as_one_byte(cp, valid)} == one_byte_shape(cp) : Maybe<&2, U32>}

# True exactly when the byte is produced by the one-byte encoding table.
law utf8_has_one_byte_shape:
  for +byte: U32
  representation = Exists(U32, cp =>
    {one_byte_shape(cp) == Some{byte} : Maybe<&2, U32>})
  ({UTF8.has_one_byte_shape(byte) == True{} : Bool} -> representation) &
  (representation -> {UTF8.has_one_byte_shape(byte) == True{} : Bool})


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
      Some{(B.bit8_value((True{}, True{}, False{}, x1, x2, x3, y1, y2)),
            B.bit8_value((True{}, False{}, y3, y4, z1, z2, z3, z4)))}
    case _:
      None{}

def two_byte_shape(cp: U32) -> Maybe<&1, U32 & U32>:
  two_byte_shape.bits(B.u32_byte4(cp))

# Specification for UTF8.can_encode_as_two_bytes: it returns True iff
# two_byte_shape matches.

law utf8_can_encode_as_two_bytes:
  for +cp: U32
  {UTF8.can_encode_as_two_bytes(cp) == Maybe.is_some(&1, U32 & U32, two_byte_shape(cp)) : Bool}

# Given a code point and a proof that the code point can be encoded in
# a UTF-8 two-byte shape (as specified by two_byte_shape above),
# `UTF8.encode_as_two_bytes` returns the two bytes of the shape
# directly as U32 values without needing to use a Maybe.

law utf8_encode_as_two_bytes:
  for +cp: U32
  for valid: {UTF8.can_encode_as_two_bytes(cp) == True{} : Bool}
  {Some{UTF8.encode_as_two_bytes(cp, valid)} == two_byte_shape(cp) : Maybe<&1, U32 & U32>}

# `UTF8.has_two_byte_shape(b1, b2)` returns True iff `(b1, b2)` can be
# returned by `two_byte_shape` for some code point.

law utf8_has_two_byte_shape:
  for +b1: U32
  for +b2: U32
  representation = Exists(U32, cp =>
    {two_byte_shape(cp) == Some{(b1, b2)} : Maybe<&1, U32 & U32>})
  ({UTF8.has_two_byte_shape(b1, b2) == True{} : Bool} -> representation) &
  (representation -> {UTF8.has_two_byte_shape(b1, b2) == True{} : Bool})

# We require that `encode_as_two_bytes` be bijective between accepted
# code points and byte pairs satisfying `has_two_byte_shape`, and we
# specify that `decode_two_bytes` is exactly its inverse.

# Decoding an encoded code point returns the original input.

law utf8_decode_encode_as_two_bytes:
  for +cp: U32
  for +valid: {UTF8.can_encode_as_two_bytes(cp) == True{} : Bool}
  +b1 = B.first(UTF8.encode_as_two_bytes(cp, valid))
  +b2 = B.second(UTF8.encode_as_two_bytes(cp, valid))
  Exists({UTF8.has_two_byte_shape(b1, b2) == True{} : Bool}, shape =>
    {UTF8.decode_two_bytes(b1, b2, shape) == cp : U32})

# Encoding a decoded pair returns the original bytes.

law utf8_decode_two_bytes:
  for +b1: U32
  for +b2: U32
  for +valid_shape: {UTF8.has_two_byte_shape(b1, b2) == True{} : Bool}
  +cp = UTF8.decode_two_bytes(b1, b2, valid_shape)
  Exists({UTF8.can_encode_as_two_bytes(cp) == True{} : Bool}, accepted =>
    {UTF8.encode_as_two_bytes(cp, accepted) == (b1, b2) : U32 & U32})

# Surrogate code points are U+D800..U+DFFF.

def is_surrogate_code_point(+cp: U32) -> Bool:
  U32.is_ge(cp, H.hex_u32("D800", {==})) &&
  U32.is_le(cp, H.hex_u32("DFFF", {==}))

law is_surrogate_code_point_examples:
  {is_surrogate_code_point(H.hex_u32("0000", {==})) == False{} : Bool} &
  {is_surrogate_code_point(H.hex_u32("D7FF", {==})) == False{} : Bool} &
  {is_surrogate_code_point(H.hex_u32("D800", {==})) == True{} : Bool} &
  {is_surrogate_code_point(H.hex_u32("DC00", {==})) == True{} : Bool} &
  {is_surrogate_code_point(H.hex_u32("DFFF", {==})) == True{} : Bool} &
  {is_surrogate_code_point(H.hex_u32("E000", {==})) == False{} : Bool}

# A Unicode scalar is any code point from U+0000 to U+10FFFF excluding
# surrogate code points.

def is_unicode_scalar(+cp: U32) -> Bool:
  U32.is_ge(cp, H.hex_u32("000000", {==})) &&
  U32.is_le(cp, H.hex_u32("10FFFF", {==})) &&
  Bool.not(is_surrogate_code_point(cp))

# Overlong means that the decoded code point fits in one byte.
law utf8_overlong_two_bytes:
  for +b1: U32
  for +b2: U32
  for -valid_shape: {UTF8.has_two_byte_shape(b1, b2) == True{} : Bool}
  {UTF8.overlong_two_bytes(b1, b2, valid_shape) ==
    UTF8.can_encode_as_one_byte(UTF8.decode_two_bytes(b1, b2, valid_shape)) : Bool}

law utf8_valid_two_bytes:
  for +b1: U32
  for +b2: U32
  (@valid_shape: {UTF8.has_two_byte_shape(b1, b2) == True{} : Bool} ->
    {UTF8.valid_two_bytes(b1, b2) == Bool.not(UTF8.overlong_two_bytes(b1, b2, valid_shape)) : Bool}) &
  ({UTF8.has_two_byte_shape(b1, b2) == False{} : Bool} ->
    {UTF8.valid_two_bytes(b1, b2) == False{} : Bool})

# An eleven-bit payload covers exactly the two-byte encoding capacity.
def codepoint11(bits: Word(11n)) -> U32:
  match bits:
    case WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WNil{}}}}}}}}}}}}:
      U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, Word.zero(21n)}}}}}}}}}}}}

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
  +accepted = Equal.trans(Bool, UTF8.can_encode_as_two_bytes(cp),
    Maybe.is_some(&1, U32 & U32, two_byte_shape(cp)), True{},
    utf8_can_encode_as_two_bytes(cp), utf8_two_capacity(bits))
  +b1 = B.first(UTF8.encode_as_two_bytes(cp, accepted))
  +b2 = B.second(UTF8.encode_as_two_bytes(cp, accepted))
  Exists({UTF8.has_two_byte_shape(b1, b2) == True{} : Bool}, shape =>
    {UTF8.decode_two_bytes(b1, b2, shape) == cp : U32} &
    {UTF8.overlong_two_bytes(b1, b2, shape) == UTF8.can_encode_as_one_byte(cp) : Bool} &
    {UTF8.valid_two_bytes(b1, b2) == U32.is_ge(cp, 128) : Bool} &
    {UTF8.valid_two_bytes(b1, b2) ==
      ((U32.is_ge(b1, 194) && U32.is_le(b1, 223)) &&
       (U32.is_ge(b2, 128) && U32.is_le(b2, 191))) : Bool})

law utf8_encoding_examples:
  {UTF8.encode_as_one_byte(0, {==}) == 0 : U32} &
  {UTF8.encode_as_one_byte(127, {==}) == 127 : U32} &
  {UTF8.can_encode_as_one_byte(128) == False{} : Bool} &
  {UTF8.encode_as_two_bytes(0, {==}) == (192, 128) : U32 & U32} &
  {UTF8.encode_as_two_bytes(127, {==}) == (193, 191) : U32 & U32} &
  {UTF8.encode_as_two_bytes(128, {==}) == (194, 128) : U32 & U32} &
  {UTF8.encode_as_two_bytes(2047, {==}) == (223, 191) : U32 & U32} &
  {UTF8.can_encode_as_two_bytes(2048) == False{} : Bool} &
  {UTF8.overlong_two_bytes(192, 128, {==}) == True{} : Bool} &
  {UTF8.overlong_two_bytes(193, 191, {==}) == True{} : Bool} &
  {UTF8.valid_two_bytes(192, 128) == False{} : Bool} &
  {UTF8.valid_two_bytes(193, 191) == False{} : Bool} &
  {UTF8.valid_two_bytes(194, 128) == True{} : Bool} &
  {UTF8.valid_two_bytes(223, 191) == True{} : Bool} &
  {UTF8.valid_two_bytes(194, 127) == False{} : Bool} &
  {UTF8.valid_two_bytes(224, 128) == False{} : Bool}

law two_byte_shape_examples:
  {two_byte_shape(0) == Some{(192, 128)} : Maybe<&1, U32 & U32>} &
  {two_byte_shape(127) == Some{(193, 191)} : Maybe<&1, U32 & U32>} &
  {two_byte_shape(128) == Some{(194, 128)} : Maybe<&1, U32 & U32>} &
  {two_byte_shape(2047) == Some{(223, 191)} : Maybe<&1, U32 & U32>} &
  {two_byte_shape(2048) == None{} : Maybe<&1, U32 & U32>} &
  {two_byte_shape(65536) == None{} : Maybe<&1, U32 & U32>} &
  {two_byte_shape(4294967295) == None{} : Maybe<&1, U32 & U32>}
