import Base
import ./binary.bend as B

# strbyte: binary byte literals
#
# strbyte("10000001", {==}) == 129
#
# The first argument is a string.  The second argument provides a
# proof that the string is exactly eight characters, each '0' or '1'.


# A binary digit in the string is '0' or '1'.

law is_binary_digit:
  for +c: Char
  {B.is_binary_digit(c) == (Char.is_eq('0', c) || Char.is_eq('1', c)) : Bool}

# A valid input string is eight characters, each '0' or '1'.

law valid_byte_string:
  for +s: String
  {B.valid_byte_string(s) ==
    (Nat.is_eq(String.length(s), 8n) &&
     List.all(~&2, ~Char, ~(c => B.is_binary_digit(c)), String.to_list(s))) : Bool}

# Type alias for a tuple of eight bools.

def Bool8() -> Type:
  Bool & Bool & Bool & Bool & Bool & Bool & Bool & Bool

# As of Bend 2.0.39 "if" statements are written this way.

def str_bits.if(valid: Bool, bits: Bool8()) -> Maybe<&1, Bool8()>:
  match valid:
    case False{}: None{}
    case True{}: Some{bits}

# If `s` is a valid input, converts the string to a tuple of eight
# bools, otherwise returns None.

def str_bits(+s: String) -> Maybe<&1, Bool8()>:
  match s:
    case SCon{c1, SCon{c2, SCon{c3, SCon{c4, SCon{c5, SCon{c6, SCon{c7, SCon{c8, SNil{}}}}}}}}}:
      str_bits.if(B.valid_byte_string(s),
        (Char.is_eq(c1, '1'),
         Char.is_eq(c2, '1'),
         Char.is_eq(c3, '1'),
         Char.is_eq(c4, '1'),
         Char.is_eq(c5, '1'),
         Char.is_eq(c6, '1'),
         Char.is_eq(c7, '1'),
         Char.is_eq(c8, '1')))
    case _: None{}

# Given a tuple of eight bools, return the U32 value of the binary
# integer, most significant bit first.

def bits_value(bits: Bool8()) -> U32:
  (b1, b2, b3, b4, b5, b6, b7, b8) = bits
  (Bool.to_u32(b1) * 128 +
   Bool.to_u32(b2) * 64 +
   Bool.to_u32(b3) * 32 +
   Bool.to_u32(b4) * 16 +
   Bool.to_u32(b5) * 8 +
   Bool.to_u32(b6) * 4 +
   Bool.to_u32(b7) * 2 +
   Bool.to_u32(b8) * 1 : U32)

law strbyte:
  for +s: String
  for +valid: {B.valid_byte_string(s) == True{} : Bool}
  exs accepted: {B.valid_byte_string(s) == True{} : Bool}
  exs bits: Bool8()
  {Some{bits} == str_bits(s) : Maybe<&1, Bool8()>} &
  {B.strbyte(s, accepted) == bits_value(bits) : U32}

law strbyte_examples:
  {B.strbyte("00000000", {==}) ==   0 : U32} &
  {B.strbyte("10000000", {==}) == 128 : U32} &
  {B.strbyte("10000001", {==}) == 129 : U32} &
  {B.strbyte("11111111", {==}) == 255 : U32}

# A redundant check of our spec: a byte value is always < 256.

law strbyte_lt_256:
  for +s: String
  for valid: {B.valid_byte_string(s) == True{} : Bool}
  exs accepted: {B.valid_byte_string(s) == True{} : Bool}
  {U32.is_lt(B.strbyte(s, accepted), 256) == True{} : Bool}

# Another redundant check for our spec: `strbyte` is injective: each
# different input produces a different output value.  If the output
# values are the same that implies the inputs were the same.

law strbyte_injective:
  for +s1: String
  for +s2: String
  for +valid1: {B.valid_byte_string(s1) == True{} : Bool}
  for +valid2: {B.valid_byte_string(s2) == True{} : Bool}
  for equal: {B.strbyte(s1, valid1) == B.strbyte(s2, valid2) : U32}
  {s1 == s2 : String}

# A well-formed mask has eight symbols, each from the fixed mask alphabet.
law is_mask_digit:
  for +c: Char
  {B.is_mask_digit(c) ==
    (Char.is_eq(c, '0') || Char.is_eq(c, '1') || Char.is_eq(c, 'x')) : Bool}

law is_valid_byte_mask:
  for +mask: String
  {B.is_valid_byte_mask(mask) ==
    (Nat.is_eq(String.length(mask), 8n) &&
     List.all(~&2, ~Char, ~(c => B.is_mask_digit(c)), String.to_list(mask))) : Bool}

def mask_positions(mask: String, weights: +List<U32>, +byte: U32) -> Bool:
  match mask weights:
    case SNil{} Nil{}:
      True{}
    case SCon{+c, rest} Con{+weight, tail}:
      (Char.is_eq(c, 'x') ||
       (Char.is_eq(c, '0') && U32.is_eq(U32.and(byte, weight), 0)) ||
       (Char.is_eq(c, '1') && U32.is_eq(U32.and(byte, weight), weight))) &&
      mask_positions(rest, tail, byte)
    case _ _:
      False{}

# First position = bit 7; U32 values above 255 never match.
law byte_mask:
  for +mask: String
  for +byte: U32
  for valid: {B.is_valid_byte_mask(mask) == True{} : Bool}
  exs accepted: {B.is_valid_byte_mask(mask) == True{} : Bool}
  {B.byte_mask(mask, byte, accepted) ==
    (U32.is_le(byte, 255) && mask_positions(mask, [128, 64, 32, 16, 8, 4, 2, 1], byte)) : Bool}

law byte_mask_examples:
  {B.byte_mask("01xxxxxx", 64, {==}) == True{} : Bool} &
  {B.byte_mask("01xxxxxx", 127, {==}) == True{} : Bool} &
  {B.byte_mask("01xxxxxx", 128, {==}) == False{} : Bool} &
  {B.byte_mask("xxxxxxxx", 255, {==}) == True{} : Bool} &
  {B.byte_mask("xxxxxxxx", 256, {==}) == False{} : Bool} &
  {B.byte_mask("10000001", 129, {==}) == True{} : Bool} &
  {B.byte_mask("10000001", 128, {==}) == False{} : Bool}

# A byte's tuple is most significant bit first; all higher U32 bits are zero.
law byte8:
  for +b7: Bool
  for +b6: Bool
  for +b5: Bool
  for +b4: Bool
  for +b3: Bool
  for +b2: Bool
  for +b1: Bool
  for +b0: Bool
  {B.byte8((b7, b6, b5, b4, b3, b2, b1, b0)) == U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, Word.zero(24n)}}}}}}}}} : U32}

# Canonical decomposition: most significant byte and bit first.
law bit32:
  for +b31: Bool
  for +b30: Bool
  for +b29: Bool
  for +b28: Bool
  for +b27: Bool
  for +b26: Bool
  for +b25: Bool
  for +b24: Bool
  for +b23: Bool
  for +b22: Bool
  for +b21: Bool
  for +b20: Bool
  for +b19: Bool
  for +b18: Bool
  for +b17: Bool
  for +b16: Bool
  for +b15: Bool
  for +b14: Bool
  for +b13: Bool
  for +b12: Bool
  for +b11: Bool
  for +b10: Bool
  for +b9: Bool
  for +b8: Bool
  for +b7: Bool
  for +b6: Bool
  for +b5: Bool
  for +b4: Bool
  for +b3: Bool
  for +b2: Bool
  for +b1: Bool
  for +b0: Bool
  {B.bit32(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}) ==
    ((b31, b30, b29, b28, b27, b26, b25, b24),
     (b23, b22, b21, b20, b19, b18, b17, b16),
     (b15, b14, b13, b12, b11, b10, b9, b8),
     (b7, b6, b5, b4, b3, b2, b1, b0)) : B.Bits32()}

law bit8:
  for +byte: U32
  for valid: {U32.is_le(byte, 255) == True{} : Bool}
  {B.bit8(byte, valid) ==
    (U32.is_ne(U32.and(byte, 128), 0),
     U32.is_ne(U32.and(byte, 64), 0),
     U32.is_ne(U32.and(byte, 32), 0),
     U32.is_ne(U32.and(byte, 16), 0),
     U32.is_ne(U32.and(byte, 8), 0),
     U32.is_ne(U32.and(byte, 4), 0),
     U32.is_ne(U32.and(byte, 2), 0),
     U32.is_ne(U32.and(byte, 1), 0)) : Bool & Bool & Bool & Bool & Bool & Bool & Bool & Bool}

law bit8_examples:
  {B.bit8(0, {==}) == (False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}) : Bool & Bool & Bool & Bool & Bool & Bool & Bool & Bool} &
  {B.bit8(65, {==}) == (False{}, True{}, False{}, False{}, False{}, False{}, False{}, True{}) : Bool & Bool & Bool & Bool & Bool & Bool & Bool & Bool} &
  {B.bit8(255, {==}) == (True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}) : Bool & Bool & Bool & Bool & Bool & Bool & Bool & Bool}

# Every byte survives conversion to eight bits and back without loss.
law byte8_bit8_roundtrip:
  for +byte: U32
  for valid: {U32.is_le(byte, 255) == True{} : Bool}
  {B.byte8(B.bit8(byte, valid)) == byte : U32}

# Reference byte order: the high byte occupies bits 15..8, the low byte 7..0.
# Split bits 15..8 and 7..0 into high and low bytes.
law u32_byte2:
  for +b31: Bool
  for +b30: Bool
  for +b29: Bool
  for +b28: Bool
  for +b27: Bool
  for +b26: Bool
  for +b25: Bool
  for +b24: Bool
  for +b23: Bool
  for +b22: Bool
  for +b21: Bool
  for +b20: Bool
  for +b19: Bool
  for +b18: Bool
  for +b17: Bool
  for +b16: Bool
  for +b15: Bool
  for +b14: Bool
  for +b13: Bool
  for +b12: Bool
  for +b11: Bool
  for +b10: Bool
  for +b9: Bool
  for +b8: Bool
  for +b7: Bool
  for +b6: Bool
  for +b5: Bool
  for +b4: Bool
  for +b3: Bool
  for +b2: Bool
  for +b1: Bool
  for +b0: Bool
  for valid: {U32.is_le(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 65535) == True{} : Bool}
  {B.u32_byte2(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, valid) ==
    (B.byte8((b15, b14, b13, b12, b11, b10, b9, b8)), B.byte8((b7, b6, b5, b4, b3, b2, b1, b0))) : U32 & U32}

# Pack the low eight bits of each argument; discard the remaining bits.
law byte2_u32:
  for +h7: Bool
  for +h6: Bool
  for +h5: Bool
  for +h4: Bool
  for +h3: Bool
  for +h2: Bool
  for +h1: Bool
  for +h0: Bool
  for +l7: Bool
  for +l6: Bool
  for +l5: Bool
  for +l4: Bool
  for +l3: Bool
  for +l2: Bool
  for +l1: Bool
  for +l0: Bool
  for rest_high: Word(24n)
  for rest_low: Word(24n)
  {B.byte2_u32(U32{WCon{h0, WCon{h1, WCon{h2, WCon{h3, WCon{h4, WCon{h5, WCon{h6, WCon{h7, rest_high}}}}}}}}}, U32{WCon{l0, WCon{l1, WCon{l2, WCon{l3, WCon{l4, WCon{l5, WCon{l6, WCon{l7, rest_low}}}}}}}}}) ==
    U32{WCon{l0, WCon{l1, WCon{l2, WCon{l3, WCon{l4, WCon{l5, WCon{l6, WCon{l7, WCon{h0, WCon{h1, WCon{h2, WCon{h3, WCon{h4, WCon{h5, WCon{h6, WCon{h7, Word.zero(16n)}}}}}}}}}}}}}}}}} : U32}

law first:
  for +high: U32
  for low: U32
  {B.first((high, low)) == high : U32}

law second:
  for high: U32
  for +low: U32
  {B.second((high, low)) == low : U32}

# Two-byte values are split and packed in big-endian order.
law u32_byte2_roundtrip:
  for +value: U32
  for valid: {U32.is_le(value, 65535) == True{} : Bool}
  {B.byte2_u32(B.first(B.u32_byte2(value, valid)),
               B.second(B.u32_byte2(value, valid))) == value : U32}

law byte2_examples:
  {B.u32_byte2(0, {==}) == (0, 0) : U32 & U32} &
  {B.u32_byte2(4660, {==}) == (18, 52) : U32 & U32} &
  {B.u32_byte2(65535, {==}) == (255, 255) : U32 & U32} &
  {B.byte2_u32(18, 52) == 4660 : U32}
