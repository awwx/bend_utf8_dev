import Base
import ./binary.bend as B

# A binary digit is '0' or '1'.

def spec_is_binary_digit(+c: Char) -> Bool:
  Char.is_eq('0', c) || Char.is_eq('1', c)

# The proof restricts the character to '0' or '1', with numeric values 0 and 1.
def bit_value(+c: Char,
  valid: {spec_is_binary_digit(c) == True{} : Bool}) -> U32:
  Bool.to_u32(Char.is_eq(c, '1'))

law is_binary_digit:
  for +c: Char
  {B.is_binary_digit(c) == spec_is_binary_digit(c) : Bool}

def spec_valid_byte_string(+s: String) -> Bool:
  Nat.is_eq(String.length(s), 8n) &&
  List.all(~&2, ~Char, ~(c => spec_is_binary_digit(c)), String.to_list(s))

law valid_byte_string:
  for +s: String
  {B.valid_byte_string(s) == spec_valid_byte_string(s) : Bool}

# Bool represents a single binary digit: False is '0', True is '1'.
def bit_to_char(bit: Bool) -> Char:
  match bit:
    case False{}: '0'
    case True{}: '1'

def bits_to_string(bits: +List<Bool>) -> String:
  match bits:
    case Nil{}:
      SNil{}
    case Con{bit, rest}:
      SCon{bit_to_char(bit), bits_to_string(rest)}

law strbyte:
  for +s: String
  for valid: {spec_valid_byte_string(s) == True{} : Bool}
  exs accepted: {B.valid_byte_string(s) == True{} : Bool}
  exs c1: Char
  exs c2: Char
  exs c3: Char
  exs c4: Char
  exs c5: Char
  exs c6: Char
  exs c7: Char
  exs c8: Char
  exs p1: {spec_is_binary_digit(c1) == True{} : Bool}
  exs p2: {spec_is_binary_digit(c2) == True{} : Bool}
  exs p3: {spec_is_binary_digit(c3) == True{} : Bool}
  exs p4: {spec_is_binary_digit(c4) == True{} : Bool}
  exs p5: {spec_is_binary_digit(c5) == True{} : Bool}
  exs p6: {spec_is_binary_digit(c6) == True{} : Bool}
  exs p7: {spec_is_binary_digit(c7) == True{} : Bool}
  exs p8: {spec_is_binary_digit(c8) == True{} : Bool}
  {s == SCon{c1, SCon{c2, SCon{c3, SCon{c4, SCon{c5, SCon{c6, SCon{c7, SCon{c8, SNil{}}}}}}}}} : String} &
  {B.strbyte(s, accepted) ==
    (bit_value(c1, p1) * 128 +
     bit_value(c2, p2) * 64 +
     bit_value(c3, p3) * 32 +
     bit_value(c4, p4) * 16 +
     bit_value(c5, p5) * 8 +
     bit_value(c6, p6) * 4 +
     bit_value(c7, p7) * 2 +
     bit_value(c8, p8) * 1 : U32) : U32}

law strbyte_lt_256:
  for +s: String
  for valid: {spec_valid_byte_string(s) == True{} : Bool}
  exs accepted: {B.valid_byte_string(s) == True{} : Bool}
  {U32.is_lt(B.strbyte(s, accepted), 256) == True{} : Bool}

# A well-formed mask has eight symbols, each from the fixed mask alphabet.
def is_mask_digit_spec(+c: Char) -> Bool:
  Char.is_eq(c, '0') || Char.is_eq(c, '1') || Char.is_eq(c, 'x')

def is_valid_byte_mask_spec(+mask: String) -> Bool:
  Nat.is_eq(String.length(mask), 8n) &&
  List.all(~&2, ~Char, ~(c => is_mask_digit_spec(c)), String.to_list(mask))

law is_valid_byte_mask:
  for +mask: String
  {B.is_valid_byte_mask(mask) == is_valid_byte_mask_spec(mask) : Bool}

# Independent specification: pair each textual position with its bit weight.
# Both sequences must end together. An x accepts either bit value, while a
# literal accepts precisely its requested value. No implementation helpers used.
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
def byte_mask_spec(mask: String, +byte: U32) -> Bool:
  U32.is_le(byte, 255) && mask_positions(mask, [128, 64, 32, 16, 8, 4, 2, 1], byte)

law byte_mask:
  for +mask: String
  for +byte: U32
  for valid: {is_valid_byte_mask_spec(mask) == True{} : Bool}
  exs accepted: {B.is_valid_byte_mask(mask) == True{} : Bool}
  {B.byte_mask(mask, byte, accepted) == byte_mask_spec(mask, byte) : Bool}

law byte_mask_examples:
  {B.byte_mask("01xxxxxx", 64, {==}) == True{} : Bool} &
  {B.byte_mask("01xxxxxx", 127, {==}) == True{} : Bool} &
  {B.byte_mask("01xxxxxx", 128, {==}) == False{} : Bool} &
  {B.byte_mask("xxxxxxxx", 255, {==}) == True{} : Bool} &
  {B.byte_mask("xxxxxxxx", 256, {==}) == False{} : Bool} &
  {B.byte_mask("10000001", 129, {==}) == True{} : Bool} &
  {B.byte_mask("10000001", 128, {==}) == False{} : Bool}

# A byte's tuple is most significant bit first; all higher U32 bits are zero.
def byte8_spec(bits: B.Bits8()) -> U32:
  (b7, b6, b5, b4, b3, b2, b1, b0) = bits
  U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, Word.zero(24n)}}}}}}}}}

law byte8:
  for bits: B.Bits8()
  {B.byte8(bits) == byte8_spec(bits) : U32}

# Canonical decomposition: four bytes, most significant byte and bit first.
# Read the U32 representation directly, independently of B.bit32.
def bit32_spec(value: U32) -> B.Bits32():
  match value:
    case U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      ((b31, b30, b29, b28, b27, b26, b25, b24),
       (b23, b22, b21, b20, b19, b18, b17, b16),
       (b15, b14, b13, b12, b11, b10, b9, b8),
       (b7, b6, b5, b4, b3, b2, b1, b0))

law bit32:
  for +value: U32
  {B.bit32(value) == bit32_spec(value) : B.Bits32()}

# Tuple positions correspond to weights 128,64,32,16,8,4,2,1.
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
def u32_byte2_spec.bits(bits: B.Bits32()) -> U32 & U32:
  (_, _, high, low) = bits
  (byte8_spec(high), byte8_spec(low))

def u32_byte2_spec(value: U32) -> U32 & U32:
  u32_byte2_spec.bits(bit32_spec(value))

law u32_byte2:
  for +value: U32
  for valid: {U32.is_le(value, 65535) == True{} : Bool}
  {B.u32_byte2(value, valid) == u32_byte2_spec(value) : U32 & U32}

# Packing keeps the low eight bits of each U32, even for out-of-range arguments.
def byte2_u32_spec.bits(high: B.Bits32(), low: B.Bits32()) -> U32:
  (_, _, _, (h7, h6, h5, h4, h3, h2, h1, h0)) = high
  (_, _, _, (l7, l6, l5, l4, l3, l2, l1, l0)) = low
  U32{WCon{l0, WCon{l1, WCon{l2, WCon{l3, WCon{l4, WCon{l5, WCon{l6, WCon{l7, WCon{h0, WCon{h1, WCon{h2, WCon{h3, WCon{h4, WCon{h5, WCon{h6, WCon{h7, Word.zero(16n)}}}}}}}}}}}}}}}}}

def byte2_u32_spec(high: U32, low: U32) -> U32:
  byte2_u32_spec.bits(bit32_spec(high), bit32_spec(low))

law byte2_u32:
  for +high: U32
  for +low: U32
  {B.byte2_u32(high, low) == byte2_u32_spec(high, low) : U32}

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
