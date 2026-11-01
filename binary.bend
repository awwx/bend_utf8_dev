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

# Encoding capacity is separate from shortest-form validity.
def utf8.can_encode_one(+cp: U32) -> Bool:
  U32.is_le(cp, 127)

def utf8.can_encode_two(+cp: U32) -> Bool:
  U32.is_le(cp, 2047)

def utf8.encode_one(+cp: U32,
  valid: {utf8.can_encode_one(cp) == True{} : Bool}) -> U32:
  cp

# Deliberately permits overlong encodings of code points 0..127.
def utf8.encode_two(+cp: U32,
  valid: {utf8.can_encode_two(cp) == True{} : Bool}) -> U32 & U32:
  ((192 + U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(cp)))))) : U32),
   (128 + U32.and(cp, 63) : U32))

def utf8.two_byte_shape(b1: U32, b2: U32) -> Bool:
  byte_mask("110xxxxx", b1, {==}) && byte_mask("10xxxxxx", b2, {==})

# Decode the payload; callers establish the two-byte shape separately.
def utf8.decode_two(b1: U32, b2: U32) -> U32:
  (U32.shl(U32.shl(U32.shl(U32.shl(U32.shl(U32.shl(U32.and(b1, 31))))))) + U32.and(b2, 63) : U32)

# The decoded code point also has a one-byte representation.
def utf8.overlong_two(+b1: U32, +b2: U32) -> Bool:
  utf8.two_byte_shape(b1, b2) &&
  utf8.can_encode_one(utf8.decode_two(b1, b2))

def utf8.valid_two(+b1: U32, +b2: U32) -> Bool:
  utf8.two_byte_shape(b1, b2) && Bool.not(utf8.overlong_two(b1, b2))

# An eleven-bit payload covers exactly the two-byte encoding capacity.
def utf8.codepoint11(bits: Word(11n)) -> U32:
  match bits:
    case WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WNil{}}}}}}}}}}}}:
      U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, Word.zero(21n)}}}}}}}}}}}}

def utf8.first(pair: U32 & U32) -> U32:
  (a, b) = pair
  a

def utf8.second(pair: U32 & U32) -> U32:
  (a, b) = pair
  b

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
