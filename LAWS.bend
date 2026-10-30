import Base
import ./hexdigits.bend as H

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

# One list of exactly eight characters witnesses both spelling and value.
def HexU32Result(+s: String, result: U32) -> Type:
  &digits: +List<H.HexDigitChar> ->
  {List.length(&2, H.HexDigitChar, digits) == 8n : Nat} &
  {s == digits_to_string(digits) : String} &
  {result == nibble_list_value(digits_to_nibbles(digits)) : U32}

# A valid input decomposes into a list of eight validated hexadecimal characters.
# The first character is the most significant: "12345678" represents 0x12345678.
law hex_u32:
  for +s: String
  for valid: {H.is_valid_hex_u32(s) == True{} : Bool}
  HexU32Result(s, H.hex_u32(s, valid))
