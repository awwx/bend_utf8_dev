import Base
import ./hexdigits.bend as H

# A "nibble" is half of a byte, four bits, which can be represented by
# a single hexadecimal digit.

def Nibble() -> Data:
  Word(4n)

# The complete set of accepted hexadecimal characters.
def hex_digits() -> +List<Char>:
  ['0', '1', '2', '3', '4', '5', '6', '7',
   '8', '9', 'A', 'B', 'C', 'D', 'E', 'F']

law is_hex_digit:
  for +c: Char
  {H.is_hex_digit(c) == List.contains(~Char, ~Char.is_eq, hex_digits(), c) : Bool}

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
  for valid: {H.is_hex_digit(c) == True{} : Bool}
  exs accepted: {H.is_hex_digit(c) == True{} : Bool}
  {Some{H.decode(H.HexDigitChar{c, accepted})} == decode_spec(c) : Maybe<&2, Nibble()>}

# A valid input to hex_u32 is a string of one to eight characters,
# each of which is a valid hexadecimal digit.

law is_valid_hex_u32_input:
  for +s: String
  {H.is_valid_hex_u32(s) ==
    ((Nat.is_ge(String.length(s), 1n) && Nat.is_le(String.length(s), 8n)) &&
     List.all(~&2, ~Char, ~(c => H.is_hex_digit(c)), String.to_list(s))) : Bool}

law is_valid_hex_u32_examples:
  {H.is_valid_hex_u32("") == False{} : Bool} &
  {H.is_valid_hex_u32("0") == True{} : Bool} &
  {H.is_valid_hex_u32("FFFFFFFF") == True{} : Bool} &
  {H.is_valid_hex_u32("100000000") == False{} : Bool} &
  {H.is_valid_hex_u32("G") == False{} : Bool}

# Decode the characters using the reference table, in textual order.
def hex_nibbles_spec(s: String) -> +List<Nibble>:
  match s:
    case SNil{}: Nil{}
    case SCon{c, rest}: decode_value_spec(c) <> hex_nibbles_spec(rest)

def nibble_list_value(nibbles: +List<Nibble>) -> U32:
  List.foldl(~&2, ~Nibble, ~U32,
    ~(acc => n => (acc * 16 + U32.from_nat(Word.to_nat(4n, n)) : U32)),
    nibbles, 0)

# The last digit has weight 1 and each digit to its left 16 times the
# weight of the one after it, so fewer than eight digits read as if
# padded on the left with '0'.
def hex_u32_spec(s: String) -> U32:
  nibble_list_value(hex_nibbles_spec(s))

law hex_u32:
  for +s: String
  for valid: {H.is_valid_hex_u32(s) == True{} : Bool}
  exs accepted: {H.is_valid_hex_u32(s) == True{} : Bool}
  {H.hex_u32(s, accepted) == hex_u32_spec(s) : U32}

law example_zero:
  {H.hex_u32("0", {==}) == 0 : U32}

law hex_u32_padding_examples:
  {H.hex_u32("A", {==}) == 10 : U32} &
  {H.hex_u32("0000000A", {==}) == 10 : U32} &
  {H.hex_u32("10FFFF", {==}) == 1114111 : U32} &
  {H.hex_u32("FFFFFFFF", {==}) == 4294967295 : U32}
