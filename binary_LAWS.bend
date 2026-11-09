import Base
import ./defs.bend as Defs
import ./binary.bend as B

# Given 8 booleans used as bits, most significant bit first, convert
# to its U32 value 0..255.  Higher U32 bits are zero.

law bit8_value:
  for +b7: Bool
  for +b6: Bool
  for +b5: Bool
  for +b4: Bool
  for +b3: Bool
  for +b2: Bool
  for +b1: Bool
  for +b0: Bool
  {B.bit8_value((b7, b6, b5, b4, b3, b2, b1, b0)) ==
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
  {B.bit8_value((b7, b6, b5, b4, b3, b2, b1, b0)) ==
    U32.from_nat(Word.to_nat(8n, word)) : U32}

# Byte masks
#
#
# A byte mask is a string of exactly eight characters, each '0', '1',
# or 'x'.
#
# A byte matches a mask if for each '0' and '1' in the mask, the byte
# has a matching 0 or 1 at that position.

law byte_mask_examples:
  {B.byte_mask("01xxxxxx",  64, {==}) == True{}  : Bool} &
  {B.byte_mask("01xxxxxx", 127, {==}) == True{}  : Bool} &
  {B.byte_mask("01xxxxxx", 128, {==}) == False{} : Bool} &
  {B.byte_mask("xxxxxxxx", 255, {==}) == True{}  : Bool} &
  {B.byte_mask("xxxxxxxx", 256, {==}) == False{} : Bool} &
  {B.byte_mask("10000001", 129, {==}) == True{}  : Bool} &
  {B.byte_mask("10000001", 128, {==}) == False{} : Bool}

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

# u32_byte4

law u32_byte4:
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
  {B.u32_byte4(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}) ==
    ((b31, b30, b29, b28, b27, b26, b25, b24),
     (b23, b22, b21, b20, b19, b18, b17, b16),
     (b15, b14, b13, b12, b11, b10, b9, b8),
     (b7, b6, b5, b4, b3, b2, b1, b0)) : Defs.Byte4()}

law first:
  for +high: U32
  for low: U32
  {B.first((high, low)) == high : U32}

law second:
  for high: U32
  for +low: U32
  {B.second((high, low)) == low : U32}
