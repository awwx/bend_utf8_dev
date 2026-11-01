import Base

def is_binary_digit(+c: Char) -> Bool:
  Char.is_eq('0', c) || Char.is_eq('1', c)

def bit_to_char(bit: Bool) -> Char:
  match bit:
    case False{}: '0'
    case True{}: '1'

def char_to_bit(c: Char) -> Bool:
  Char.is_eq(c, '1')

def is_valid_binary_byte(+s: String) -> Bool:
  Nat.is_eq(String.length(s), 8n) &&
  List.all(~&2, ~Char, ~(c => is_binary_digit(c)), String.to_list(s))

# Fold in textual order: the first bit has weight 128, the last weight 1.
def binary_byte.fold_bits(bits: +List<Bool>, acc: U32) -> U32:
  match bits:
    case Nil{}:
      acc
    case Con{bit, rest}:
      binary_byte.fold_bits(rest, (acc * 2 + Bool.to_u32(bit) : U32))

def binary_byte(+s: String, valid: {is_valid_binary_byte(s) == True{} : Bool}) -> U32:
  match s:
    case SCon{c1, SCon{c2, SCon{c3, SCon{c4, SCon{c5, SCon{c6, SCon{c7, SCon{c8, SNil{}}}}}}}}}:
      binary_byte.fold_bits([char_to_bit(c1), char_to_bit(c2), char_to_bit(c3), char_to_bit(c4), char_to_bit(c5), char_to_bit(c6), char_to_bit(c7), char_to_bit(c8)], 0)
    case _:
      0

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
  valid: {is_valid_byte_mask(mask) == True{} : Bool}) -> Bool:
  match mask:
    case SCon{c1, SCon{c2, SCon{c3, SCon{c4, SCon{c5, SCon{c6, SCon{c7, SCon{c8, SNil{}}}}}}}}}:
      Bool.and(U32.is_le(byte, 255), Bool.and(byte_mask.bit(c1, byte, 128), Bool.and(byte_mask.bit(c2, byte, 64), Bool.and(byte_mask.bit(c3, byte, 32), Bool.and(byte_mask.bit(c4, byte, 16), Bool.and(byte_mask.bit(c5, byte, 8), Bool.and(byte_mask.bit(c6, byte, 4), Bool.and(byte_mask.bit(c7, byte, 2), Bool.and(byte_mask.bit(c8, byte, 1), True{})))))))))
    case _:
      False{}

# Eight bits, most significant first. U32 is unsigned, so <=255 establishes
# the full byte range 0..255. The final argument is a proof, not a runtime test.
def bit8(+byte: U32,
  valid: {U32.is_le(byte, 255) == True{} : Bool}) -> Bool & Bool & Bool & Bool & Bool & Bool & Bool & Bool:
  (U32.is_ne(U32.and(byte, 128), 0),
   U32.is_ne(U32.and(byte, 64), 0),
   U32.is_ne(U32.and(byte, 32), 0),
   U32.is_ne(U32.and(byte, 16), 0),
   U32.is_ne(U32.and(byte, 8), 0),
   U32.is_ne(U32.and(byte, 4), 0),
   U32.is_ne(U32.and(byte, 2), 0),
   U32.is_ne(U32.and(byte, 1), 0))

# Inverse of bit8: tuple order is bit 7 through bit 0.
def byte8(bits: Bool & Bool & Bool & Bool & Bool & Bool & Bool & Bool) -> U32:
  (b7, b6, b5, b4, b3, b2, b1, b0) = bits
  U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, Word.zero(24n)}}}}}}}}}

# Split a sixteen-bit number into high and low bytes (big endian).
def u32_byte2(+value: U32,
  valid: {U32.is_le(value, 65535) == True{} : Bool}) -> U32 & U32:
  match value:
    case U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      (byte8((b15, b14, b13, b12, b11, b10, b9, b8)),
       byte8((b7, b6, b5, b4, b3, b2, b1, b0)))

# Pack the low eight bits of each argument, high byte first.
def byte2_u32(high: U32, low: U32) -> U32:
  match high low:
    case U32{WCon{h0, WCon{h1, WCon{h2, WCon{h3, WCon{h4, WCon{h5, WCon{h6, WCon{h7, rest_high}}}}}}}}} U32{WCon{l0, WCon{l1, WCon{l2, WCon{l3, WCon{l4, WCon{l5, WCon{l6, WCon{l7, rest_low}}}}}}}}}:
      U32{WCon{l0, WCon{l1, WCon{l2, WCon{l3, WCon{l4, WCon{l5, WCon{l6, WCon{l7, WCon{h0, WCon{h1, WCon{h2, WCon{h3, WCon{h4, WCon{h5, WCon{h6, WCon{h7, Word.zero(16n)}}}}}}}}}}}}}}}}}

# Bits are grouped into bytes, most significant byte and bit first.
def Bits8() -> Type:
  Bool & Bool & Bool & Bool & Bool & Bool & Bool & Bool

def Bits32() -> Type:
  Bits8() & Bits8() & Bits8() & Bits8()

def bit32(value: U32) -> Bits32():
  match value:
    case U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      ((b31, b30, b29, b28, b27, b26, b25, b24),
       (b23, b22, b21, b20, b19, b18, b17, b16),
       (b15, b14, b13, b12, b11, b10, b9, b8),
       (b7, b6, b5, b4, b3, b2, b1, b0))

def first(pair: U32 & U32) -> U32:
  (a, b) = pair
  a

def second(pair: U32 & U32) -> U32:
  (a, b) = pair
  b
