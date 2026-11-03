import Base
import ./defs.bend as Defs
import ./hexdigits.bend as H
import ./binary.bend as B
import ./binary_LAWS.bend as BinaryLaws

# The complete set of accepted hexadecimal characters.
def hex_digits() -> +List<Char>:
  ['0', '1', '2', '3', '4', '5', '6', '7',
   '8', '9', 'A', 'B', 'C', 'D', 'E', 'F']

law is_hex_digit:
  for +c: Char
  {H.is_hex_digit(c) == List.contains(~Char, ~Char.is_eq, hex_digits(), c) : Bool}

# The low four bits represent a nibble, least significant bit first.
def nibble_spec(value: U32) -> Defs.Nibble():
  match value:
    case U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, rest}}}}}:
      WCon{b0, WCon{b1, WCon{b2, WCon{b3, WNil{}}}}}

def decode_spec(c: Char) -> Maybe<&2, Defs.Nibble()>:
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
def decode_value_spec(c: Char) -> Defs.Nibble():
  Maybe.default(&2, Defs.Nibble(), decode_spec(c), Word.zero(4n))

# Every character accepted by the specification must be accepted and decoded
# correctly by the implementation, regardless of its packaged input type.
law decode:
  for +c: Char
  for valid: {H.is_hex_digit(c) == True{} : Bool}
  exs accepted: {H.is_hex_digit(c) == True{} : Bool}
  {Some{H.decode(H.HexDigitChar{c, accepted})} == decode_spec(c) : Maybe<&2, Defs.Nibble()>}

# A valid input to hex_u32 is a string of exactly eight characters,
# each of which is a valid hexadecimal digit.

law is_valid_hex_u32_input:
  for +s: String
  {H.is_valid_hex_u32(s) ==
    (Nat.is_eq(String.length(s), 8n) &&
     List.all(~&2, ~Char, ~(c => H.is_hex_digit(c)), String.to_list(s))) : Bool}

# Decode the characters using the reference table, in textual order.
def hex_nibbles_spec(s: String) -> +List<Defs.Nibble>:
  match s:
    case SNil{}: Nil{}
    case SCon{c, rest}: decode_value_spec(c) <> hex_nibbles_spec(rest)

def nibble_list_value(nibbles: +List<Defs.Nibble>) -> U32:
  List.foldl(~&2, ~Defs.Nibble, ~U32,
    ~(acc => n => (acc * 16 + U32.from_nat(Word.to_nat(4n, n)) : U32)),
    nibbles, 0)

# The first digit has weight 16^7; the last has weight 1.
def hex_u32_spec(s: String) -> U32:
  nibble_list_value(hex_nibbles_spec(s))

law hex_u32:
  for +s: String
  for valid: {H.is_valid_hex_u32(s) == True{} : Bool}
  exs accepted: {H.is_valid_hex_u32(s) == True{} : Bool}
  {H.hex_u32(s, accepted) == hex_u32_spec(s) : U32}

law example_zero:
  {H.hex_u32("00000000", {==}) == 0 : U32}

# Reference model: 00000000 00000000 00000xxx yyyyzzzz -> 110xxxyy 10yyzzzz.
# The leading zeros enforce the input shape; any other shape returns None.
# Capacity includes overlong encodings of 0..127; shortest-form validity is separate.
# https://en.wikipedia.org/wiki/UTF-8#Description
def maybe_encode_two.bits(bits: Defs.Bit32()) -> Maybe<&1, U32 & U32>:
  match bits:
    case ((False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}),
          (False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}),
          (False{}, False{}, False{}, False{}, False{}, x1, x2, x3),
          (y1, y2, y3, y4, z1, z2, z3, z4)):
      Some{(B.bit8_value((True{}, True{}, False{}, x1, x2, x3, y1, y2)),
            B.bit8_value((True{}, False{}, y3, y4, z1, z2, z3, z4)))}
    case _:
      None{}

def maybe_encode_two(cp: U32) -> Maybe<&1, U32 & U32>:
  maybe_encode_two.bits(B.bit32(cp))

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

law maybe_encode_two_examples:
  {maybe_encode_two(0) == Some{(192, 128)} : Maybe<&1, U32 & U32>} &
  {maybe_encode_two(127) == Some{(193, 191)} : Maybe<&1, U32 & U32>} &
  {maybe_encode_two(128) == Some{(194, 128)} : Maybe<&1, U32 & U32>} &
  {maybe_encode_two(2047) == Some{(223, 191)} : Maybe<&1, U32 & U32>} &
  {maybe_encode_two(2048) == None{} : Maybe<&1, U32 & U32>} &
  {maybe_encode_two(65536) == None{} : Maybe<&1, U32 & U32>} &
  {maybe_encode_two(4294967295) == None{} : Maybe<&1, U32 & U32>}
