import Base
import ./hexdigits.bend as H
import ./binary.bend as B

# A "nibble" is half of a byte, a four-bit numeral, which can be
# represented by a single hexadecimal digit.

def Nibble() -> Data:
  Word(4n)

# The complete set of accepted hexadecimal characters.
def hex_digits() -> +List<Char>:
  ['0', '1', '2', '3', '4', '5', '6', '7',
   '8', '9', 'A', 'B', 'C', 'D', 'E', 'F']

# Independent character domain and hexadecimal decoding table.
def is_hex_digit_spec(c: Char) -> Bool:
  List.contains(~Char, ~Char.is_eq, hex_digits(), c)

law is_hex_digit:
  for +c: Char
  {H.is_hex_digit(c) == is_hex_digit_spec(c) : Bool}

# The low four bits represent a nibble, least significant bit first.
def nibble_spec(value: U32) -> Nibble():
  match value:
    case U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, rest}}}}}:
      WCon{b0, WCon{b1, WCon{b2, WCon{b3, WNil{}}}}}

def decode_spec(c: Char) -> Maybe<&2, Nibble()>:
  match c:
    case '0': Some{nibble_spec(0)}
    case '1': Some{nibble_spec(1)}
    case '2': Some{nibble_spec(2)}
    case '3': Some{nibble_spec(3)}
    case '4': Some{nibble_spec(4)}
    case '5': Some{nibble_spec(5)}
    case '6': Some{nibble_spec(6)}
    case '7': Some{nibble_spec(7)}
    case '8': Some{nibble_spec(8)}
    case '9': Some{nibble_spec(9)}
    case 'A': Some{nibble_spec(10)}
    case 'B': Some{nibble_spec(11)}
    case 'C': Some{nibble_spec(12)}
    case 'D': Some{nibble_spec(13)}
    case 'E': Some{nibble_spec(14)}
    case 'F': Some{nibble_spec(15)}
    case _: None{}

# Used only for valid digits in the multi-digit reference calculation.
def decode_value_spec(c: Char) -> Nibble():
  Maybe.default(&2, Nibble(), decode_spec(c), Word.zero(4n))

# Every character accepted by the specification must be accepted and decoded
# correctly by the implementation, regardless of its packaged input type.
law decode:
  for +c: Char
  for valid: {is_hex_digit_spec(c) == True{} : Bool}
  exs accepted: {H.is_hex_digit(c) == True{} : Bool}
  {Some{H.decode(H.HexDigitChar{c, accepted})} == decode_spec(c) : Maybe<&2, Nibble()>}

# A valid input to hex_u32 is a string of exactly eight characters,
# each of which is a valid hexadecimal digit.

law is_valid_hex_u32_input:
  for +s: String
  {H.is_valid_hex_u32(s) == (
    Nat.is_eq(String.length(s), 8n) &&
    List.all(~&2, ~Char, ~(c => H.is_hex_digit(c)), String.to_list(s))
  ) : Bool}

# Convert a list of hex digits to a string of those digit characters.

def digits_to_string(digits: +List<H.HexDigitChar>) -> String:
  match digits:
    case Nil{}:
      SNil{}
    case Con{digit, rest}:
      SCon{H.HexDigitChar.char(digit), digits_to_string(rest)}

# Convert a list of hexadecimal digit characters to a list of their
# associated nibble values.

def digits_to_nibbles(digits: +List<H.HexDigitChar>) -> +List<Nibble>:
  match digits:
    case Nil{}:
      Nil{}
    case Con{H.HexDigitChar{c, valid}, rest}:
      decode_value_spec(c) <> digits_to_nibbles(rest)

def nibble_list_value(nibbles: +List<Nibble>) -> U32:
  List.foldl(~&2, ~Nibble, ~U32,
    ~(acc => n => (acc * 16 + U32.from_nat(Word.to_nat(4n, n)) : U32)),
    nibbles, 0)

# A valid input string decomposes into eight hexidecimal digit
# characters, which produces the matching U32 output value.

law hex_u32:
  for +s: String
  for valid: {H.is_valid_hex_u32(s) == True{} : Bool}
  exs digits: +List<H.HexDigitChar>
  {List.length(&2, H.HexDigitChar, digits) == 8n : Nat} &
  {s == digits_to_string(digits) : String} &
  {H.hex_u32(s, valid) == nibble_list_value(digits_to_nibbles(digits)) : U32}

law example_zero:
  {H.hex_u32("00000000", {==}) == 0 : U32}

# The complete set of accepted binary characters.
def binary_digits() -> +List<Char>:
  ['0', '1']

law is_binary_digit:
  for +c: Char
  {B.is_binary_digit(c) == List.contains(~Char, ~Char.is_eq, binary_digits(), c) : Bool}

law is_valid_binary_byte_input:
  for +s: String
  {B.is_valid_binary_byte(s) == (
    Nat.is_eq(String.length(s), 8n) &&
    List.all(~&2, ~Char, ~(c => B.is_binary_digit(c)), String.to_list(s))
  ) : Bool}

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

# Read the bits most significant first, as in "10000000" = 128.
def bit_list_value(bits: +List<Bool>) -> U32:
  List.foldl(~&2, ~Bool, ~U32,
    ~(acc => bit => (acc * 2 + Bool.to_u32(bit) : U32)), bits, 0)

# A valid input spells exactly eight bits and yields their byte value.
law binary_byte:
  for +s: String
  for valid: {B.is_valid_binary_byte(s) == True{} : Bool}
  exs bits: +List<Bool>
  {List.length(&2, Bool, bits) == 8n : Nat} &
  {s == bits_to_string(bits) : String} &
  {B.binary_byte(s, valid) == bit_list_value(bits) : U32} &
  {U32.is_le(B.binary_byte(s, valid), 255) == True{} : Bool}

# A well-formed mask contains exactly eight symbols from this alphabet.
law is_valid_byte_mask:
  for +mask: String
  {B.is_valid_byte_mask(mask) == (
    Nat.is_eq(String.length(mask), 8n) &&
    List.all(~&2, ~Char,
      ~(c => Char.is_eq(c, '0') || Char.is_eq(c, '1') || Char.is_eq(c, 'x')),
      String.to_list(mask))) : Bool}

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

# This specifies the result for every well-formed mask and every U32 byte
# argument, including rejection of out-of-range numbers. First position = bit 7.
law byte_mask:
  for +mask: String
  for +byte: U32
  for valid: {B.is_valid_byte_mask(mask) == True{} : Bool}
  {B.byte_mask(mask, byte, valid) ==
    (U32.is_le(byte, 255) &&
     mask_positions(mask, [128, 64, 32, 16, 8, 4, 2, 1], byte)) : Bool}

law byte_mask_examples:
  {B.byte_mask("01xxxxxx", 64, {==}) == True{} : Bool} &
  {B.byte_mask("01xxxxxx", 127, {==}) == True{} : Bool} &
  {B.byte_mask("01xxxxxx", 128, {==}) == False{} : Bool} &
  {B.byte_mask("xxxxxxxx", 255, {==}) == True{} : Bool} &
  {B.byte_mask("xxxxxxxx", 256, {==}) == False{} : Bool} &
  {B.byte_mask("10000001", 129, {==}) == True{} : Bool} &
  {B.byte_mask("10000001", 128, {==}) == False{} : Bool}

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

# Reference model: 00000000 00000000 00000xxx yyyyzzzz -> 110xxxyy 10yyzzzz.
# The leading zeros enforce the input shape; any other shape returns None.
# Capacity includes overlong encodings of 0..127; shortest-form validity is separate.
# https://en.wikipedia.org/wiki/UTF-8#Description
def maybe_encode_two.bits(bits: B.Bits32()) -> Maybe<&1, U32 & U32>:
  match bits:
    case ((False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}),
          (False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}),
          (False{}, False{}, False{}, False{}, False{}, x1, x2, x3),
          (y1, y2, y3, y4, z1, z2, z3, z4)):
      Some{(B.byte8((True{}, True{}, False{}, x1, x2, x3, y1, y2)),
            B.byte8((True{}, False{}, y3, y4, z1, z2, z3, z4)))}
    case _:
      None{}

def maybe_encode_two(cp: U32) -> Maybe<&1, U32 & U32>:
  maybe_encode_two.bits(bit32_spec(cp))

# Operations under specification. PROOF.bend binds them to the implementation.
law utf8.can_encode_one:
  for +cp: U32
  Bool

law utf8.can_encode_two:
  for +cp: U32
  Bool

law utf8.encode_one:
  for +cp: U32
  for valid: {U32.is_le(cp, 127) == True{} : Bool}
  U32

law utf8.encode_two:
  for +cp: U32
  for valid: {Maybe.is_some(&1, U32 & U32, maybe_encode_two(cp)) == True{} : Bool}
  U32 & U32

law utf8.two_byte_shape:
  for b1: U32
  for b2: U32
  Bool

law utf8.decode_two:
  for b1: U32
  for b2: U32
  U32

law utf8.overlong_two:
  for +b1: U32
  for +b2: U32
  Bool

# The capacity test is determined by whether the reference model produced bytes.
law utf8_can_encode_two:
  for +cp: U32
  {utf8.can_encode_two(cp) == Maybe.is_some(&1, U32 & U32, maybe_encode_two(cp)) : Bool}

law utf8_can_encode_one:
  for +cp: U32
  {utf8.can_encode_one(cp) == U32.is_le(cp, 127) : Bool}

# An eleven-bit payload covers exactly the two-byte encoding capacity.
def codepoint11(bits: Word(11n)) -> U32:
  match bits:
    case WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WNil{}}}}}}}}}}}}:
      U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, Word.zero(21n)}}}}}}}}}}}}

def valid_utf8_one_byte(b1: U32) -> Bool:
  B.byte_mask("0xxxxxxx", b1, {==})

law valid_utf8_one_byte_examples:
  {valid_utf8_one_byte(0) == True{} : Bool} &
  {valid_utf8_one_byte(127) == True{} : Bool} &
  {valid_utf8_one_byte(128) == False{} : Bool}

law valid_utf8_two_bytes:
  for +b1: U32
  for +b2: U32
  Bool

# Encoding functions expose the representation of a given code point.
law utf8_encode_one:
  for +cp: U32
  for valid: {U32.is_le(cp, 127) == True{} : Bool}
  {utf8.encode_one(cp, valid) == cp : U32}

# For every encodable code point, the bytes must equal the reference model.
law utf8_encode_two:
  for +cp: U32
  for valid: {Maybe.is_some(&1, U32 & U32, maybe_encode_two(cp)) == True{} : Bool}
  {Some{utf8.encode_two(cp, valid)} == maybe_encode_two(cp) : Maybe<&1, U32 & U32>}

# Leading and continuation bytes have the table's literal prefix bits.
law utf8_two_byte_shape:
  for +b1: U32
  for +b2: U32
  {utf8.two_byte_shape(b1, b2) ==
    (B.byte_mask("110xxxxx", b1, {==}) && B.byte_mask("10xxxxxx", b2, {==})) : Bool}

# Join the leading byte's five payload bits and the continuation's six bits.
law utf8_decode_two:
  for +b1: U32
  for +b2: U32
  {utf8.decode_two(b1, b2) ==
    (U32.shln(U32.and(b1, 31), 6n) + U32.and(b2, 63) : U32) : U32}

# Overlong means that the same decoded code point fits in one byte.
law utf8_overlong_two:
  for +b1: U32
  for +b2: U32
  {utf8.overlong_two(b1, b2) ==
    (utf8.two_byte_shape(b1, b2) &&
     utf8.can_encode_one(utf8.decode_two(b1, b2))) : Bool}

law utf8_valid_two:
  for +b1: U32
  for +b2: U32
  {valid_utf8_two_bytes(b1, b2) ==
    (utf8.two_byte_shape(b1, b2) &&
     Bool.not(utf8.overlong_two(b1, b2))) : Bool}

# Every eleven-bit code point has a two-byte representation. It round-trips,
# and is valid exactly when its code point needs more than one byte.
# The first-byte range is a consequence, rather than the validity definition.
law utf8_two_capacity:
  for +bits: Word(11n)
  +cp = codepoint11(bits)
  {Maybe.is_some(&1, U32 & U32, maybe_encode_two(cp)) == True{} : Bool}

law utf8_two_roundtrip:
  for +bits: Word(11n)
  +cp = codepoint11(bits)
  +b1 = B.first(utf8.encode_two(cp, utf8_two_capacity(bits)))
  +b2 = B.second(utf8.encode_two(cp, utf8_two_capacity(bits)))
  {utf8.decode_two(b1, b2) == cp : U32} &
  {utf8.two_byte_shape(b1, b2) == True{} : Bool} &
  {utf8.overlong_two(b1, b2) == utf8.can_encode_one(cp) : Bool} &
  {valid_utf8_two_bytes(b1, b2) == U32.is_ge(cp, 128) : Bool} &
  {valid_utf8_two_bytes(b1, b2) ==
    ((U32.is_ge(b1, 194) && U32.is_le(b1, 223)) &&
     (U32.is_ge(b2, 128) && U32.is_le(b2, 191))) : Bool}

law utf8_encoding_examples:
  {utf8.encode_one(0, {==}) == 0 : U32} &
  {utf8.encode_one(127, {==}) == 127 : U32} &
  {utf8.can_encode_one(128) == False{} : Bool} &
  {utf8.encode_two(0, {==}) == (192, 128) : U32 & U32} &
  {utf8.encode_two(127, {==}) == (193, 191) : U32 & U32} &
  {utf8.encode_two(128, {==}) == (194, 128) : U32 & U32} &
  {utf8.encode_two(2047, {==}) == (223, 191) : U32 & U32} &
  {utf8.can_encode_two(2048) == False{} : Bool} &
  {utf8.overlong_two(192, 128) == True{} : Bool} &
  {utf8.overlong_two(193, 191) == True{} : Bool} &
  {valid_utf8_two_bytes(192, 128) == False{} : Bool} &
  {valid_utf8_two_bytes(193, 191) == False{} : Bool} &
  {valid_utf8_two_bytes(194, 128) == True{} : Bool} &
  {valid_utf8_two_bytes(223, 191) == True{} : Bool} &
  {valid_utf8_two_bytes(194, 127) == False{} : Bool} &
  {valid_utf8_two_bytes(224, 128) == False{} : Bool}

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

law maybe_encode_two_examples:
  {maybe_encode_two(0) == Some{(192, 128)} : Maybe<&1, U32 & U32>} &
  {maybe_encode_two(127) == Some{(193, 191)} : Maybe<&1, U32 & U32>} &
  {maybe_encode_two(128) == Some{(194, 128)} : Maybe<&1, U32 & U32>} &
  {maybe_encode_two(2047) == Some{(223, 191)} : Maybe<&1, U32 & U32>} &
  {maybe_encode_two(2048) == None{} : Maybe<&1, U32 & U32>} &
  {maybe_encode_two(65536) == None{} : Maybe<&1, U32 & U32>} &
  {maybe_encode_two(4294967295) == None{} : Maybe<&1, U32 & U32>}
