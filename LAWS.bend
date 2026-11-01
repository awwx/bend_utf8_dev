import Base
import ./hexdigits.bend as H
import ./binary.bend as B
import ./utf8.bend as UTF8

# A "nibble" is half of a byte, a four-bit numeral, which can be
# represented by a single hexadecimal digit.

def Nibble() -> Data:
  Word(4n)

# The complete set of accepted hexadecimal characters.
def hex_digits() -> +List<Char>:
  ['0', '1', '2', '3', '4', '5', '6', '7',
   '8', '9', 'A', 'B', 'C', 'D', 'E', 'F']

# A character is a hexadecimal digit when it is present in the hex_digits list.
law is_hex_digit:
  for +c: Char
  {H.is_hex_digit(c) == List.contains(~Char, ~Char.is_eq, hex_digits(), c) : Bool}

# For each valid input hexadecimal digit character, directly specify
# the output nibble value.

law decode:
  for +digit: H.HexDigitChar
  c = H.HexDigitChar.char(digit)
  v = Word.to_nat(4n, H.decode(digit))
  ({c == '0' : Char} & {v == 0n : Nat}) |
  ({c == '1' : Char} & {v == 1n : Nat}) |
  ({c == '2' : Char} & {v == 2n : Nat}) |
  ({c == '3' : Char} & {v == 3n : Nat}) |
  ({c == '4' : Char} & {v == 4n : Nat}) |
  ({c == '5' : Char} & {v == 5n : Nat}) |
  ({c == '6' : Char} & {v == 6n : Nat}) |
  ({c == '7' : Char} & {v == 7n : Nat}) |
  ({c == '8' : Char} & {v == 8n : Nat}) |
  ({c == '9' : Char} & {v == 9n : Nat}) |
  ({c == 'A' : Char} & {v == 10n : Nat}) |
  ({c == 'B' : Char} & {v == 11n : Nat}) |
  ({c == 'C' : Char} & {v == 12n : Nat}) |
  ({c == 'D' : Char} & {v == 13n : Nat}) |
  ({c == 'E' : Char} & {v == 14n : Nat}) |
  ({c == 'F' : Char} & {v == 15n : Nat})

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
    case Con{digit, rest}:
      H.decode(digit) <> digits_to_nibbles(rest)

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
def bits_to_string(bits: +List<Bool>) -> String:
  match bits:
    case Nil{}:
      SNil{}
    case Con{bit, rest}:
      SCon{B.bit_to_char(bit), bits_to_string(rest)}

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

def valid_utf8_one_byte(b1: U32) -> Bool:
  B.byte_mask("0xxxxxxx", b1, {==})

law valid_utf8_one_byte_examples:
  {valid_utf8_one_byte(0) == True{} : Bool} &
  {valid_utf8_one_byte(127) == True{} : Bool} &
  {valid_utf8_one_byte(128) == False{} : Bool}

def valid_utf8_two_bytes(b1: U32, b2: U32) -> Bool:
  UTF8.valid_two(b1, b2)

# Encoding functions expose the representation of a given code point.
law utf8_encode_one:
  for +cp: U32
  for valid: {UTF8.can_encode_one(cp) == True{} : Bool}
  {UTF8.encode_one(cp, valid) == cp : U32}

# The table writes the code point as 00000xxx yyyyzzzz, then distributes
# those eleven payload bits into the output bytes 110xxxyy 10yyzzzz.
# https://en.wikipedia.org/wiki/UTF-8#Description
law utf8_encode_two:
  for +cp: U32
  for valid: {UTF8.can_encode_two(cp) == True{} : Bool}
  exs x1: Bool
  exs x2: Bool
  exs x3: Bool
  exs y1: Bool
  exs y2: Bool
  exs y3: Bool
  exs y4: Bool
  exs z1: Bool
  exs z2: Bool
  exs z3: Bool
  exs z4: Bool
  {cp == B.byte2_u32(
    B.byte8((False{}, False{}, False{}, False{}, False{}, x1, x2, x3)),
    B.byte8((y1, y2, y3, y4, z1, z2, z3, z4))) : U32} &
  {UTF8.encode_two(cp, valid) ==
    (B.byte8((True{}, True{}, False{}, x1, x2, x3, y1, y2)),
     B.byte8((True{}, False{}, y3, y4, z1, z2, z3, z4))) : U32 & U32}

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
  {valid_utf8_two_bytes(b1, b2) ==
    (UTF8.two_byte_shape(b1, b2) &&
     Bool.not(UTF8.overlong_two(b1, b2))) : Bool}

# Every eleven-bit code point has a two-byte representation. It round-trips,
# and is valid exactly when its code point needs more than one byte.
# The first-byte range is a consequence, rather than the validity definition.
law utf8_two_capacity:
  for +bits: Word(11n)
  +cp = UTF8.codepoint11(bits)
  {UTF8.can_encode_two(cp) == True{} : Bool}

law utf8_two_roundtrip:
  for +bits: Word(11n)
  +cp = UTF8.codepoint11(bits)
  +b1 = UTF8.first(UTF8.encode_two(cp, utf8_two_capacity(bits)))
  +b2 = UTF8.second(UTF8.encode_two(cp, utf8_two_capacity(bits)))
  {UTF8.decode_two(b1, b2) == cp : U32} &
  {UTF8.two_byte_shape(b1, b2) == True{} : Bool} &
  {UTF8.overlong_two(b1, b2) == UTF8.can_encode_one(cp) : Bool} &
  {valid_utf8_two_bytes(b1, b2) == U32.is_ge(cp, 128) : Bool} &
  {valid_utf8_two_bytes(b1, b2) ==
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
  {B.byte2_u32(UTF8.first(B.u32_byte2(value, valid)),
               UTF8.second(B.u32_byte2(value, valid))) == value : U32}

law byte2_examples:
  {B.u32_byte2(0, {==}) == (0, 0) : U32 & U32} &
  {B.u32_byte2(4660, {==}) == (18, 52) : U32 & U32} &
  {B.u32_byte2(65535, {==}) == (255, 255) : U32 & U32} &
  {B.byte2_u32(18, 52) == 4660 : U32}
