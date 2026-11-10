import Base

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
