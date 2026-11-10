import Base
import ./defs.bend as Defs

# Masks are written most significant bit first. Only lowercase x is a wildcard.
def is_mask_digit(+c: Char) -> Bool:
  Char.is_eq(c, '0') || Char.is_eq(c, '1') || Char.is_eq(c, 'x')

def is_valid_byte_mask(+mask: String) -> Bool:
  Nat.is_eq(String.length(mask), 8n) &&
  List.all(~&2, ~Char, ~(c => is_mask_digit(c)), String.to_list(mask))

def byte_mask.bit(+c: Char, +byte: U32, +weight: U32) -> Bool:
  Char.is_eq(c, 'x') ||
  (Char.is_eq(c, '0') && U32.is_eq(U32.and(byte, weight), 0)) ||
  (Char.is_eq(c, '1') && U32.is_eq(U32.and(byte, weight), weight))

# The proof is the last argument: byte_mask("01xxxxxx", byte, {==}).
# U32 is the numeric carrier; values outside the byte range do not match.
def byte_mask(+mask: String, +byte: U32,
  -valid: {is_valid_byte_mask(mask) == True{} : Bool}) -> Bool:
  match mask:
    case SCon{c1, SCon{c2, SCon{c3, SCon{c4, SCon{c5, SCon{c6, SCon{c7, SCon{c8, SNil{}}}}}}}}}:
      Bool.and(U32.is_le(byte, 255), Bool.and(byte_mask.bit(c1, byte, 128), Bool.and(byte_mask.bit(c2, byte, 64), Bool.and(byte_mask.bit(c3, byte, 32), Bool.and(byte_mask.bit(c4, byte, 16), Bool.and(byte_mask.bit(c5, byte, 8), Bool.and(byte_mask.bit(c6, byte, 4), Bool.and(byte_mask.bit(c7, byte, 2), Bool.and(byte_mask.bit(c8, byte, 1), True{})))))))))
    case _:
      False{}

# Given a tuple of eight bools, return the U32 value of the binary
# integer, most significant bit first.
def bit8_value(bit8: Defs.Bit8()) -> U32:
  (b7, b6, b5, b4, b3, b2, b1, b0) = bit8
  U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, Word.zero(24n)}}}}}}}}}

def u32_byte4(value: U32) -> Defs.Byte4():
  match value:
    case U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      ((b31, b30, b29, b28, b27, b26, b25, b24),
       (b23, b22, b21, b20, b19, b18, b17, b16),
       (b15, b14, b13, b12, b11, b10, b9, b8),
       (b7, b6, b5, b4, b3, b2, b1, b0))
