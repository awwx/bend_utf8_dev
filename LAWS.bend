import Base
import ./hexdigits.bend as H

# A "nibble" is half of a byte, a four-bit numeral, which can be
# represented by a single hexadecimal digit.

def Nibble() -> Data:
  Word(4n)

def nibble(n: Nat) -> Nibble:
  match n:
    case 0n:
      Word.zero(4n)
    case 1n+p:
      Word.inc(4n, nibble(p))

# The complete set of accepted hexadecimal characters.
def hex_digits() -> +List<Char>:
  ['0', '1', '2', '3', '4', '5', '6', '7',
   '8', '9', 'A', 'B', 'C', 'D', 'E', 'F']

# A character is a hexadecimal digit when it is present in the hex_digits list.
law is_hex_digit:
  for +c: Char
  {H.is_hex_digit(c) == List.contains(~Char, ~Char.is_eq, hex_digits(), c) : Bool}

# The specification for decoding a hexadecimal digit character to a
# nibble value.  A bit verbose, but as far as I can tell the most
# straightforward way to specficy which nibble value a hexadecimal
# digit character represents.

law decode:
  for +digit: H.HexDigitChar
  c = H.HexDigitChar.char(digit)
  d = H.decode(digit)
  ({c == '0' : Char} & {d == nibble(0n) : Nibble}) |
  ({c == '1' : Char} & {d == nibble(1n) : Nibble}) |
  ({c == '2' : Char} & {d == nibble(2n) : Nibble}) |
  ({c == '3' : Char} & {d == nibble(3n) : Nibble}) |
  ({c == '4' : Char} & {d == nibble(4n) : Nibble}) |
  ({c == '5' : Char} & {d == nibble(5n) : Nibble}) |
  ({c == '6' : Char} & {d == nibble(6n) : Nibble}) |
  ({c == '7' : Char} & {d == nibble(7n) : Nibble}) |
  ({c == '8' : Char} & {d == nibble(8n) : Nibble}) |
  ({c == '9' : Char} & {d == nibble(9n) : Nibble}) |
  ({c == 'A' : Char} & {d == nibble(10n) : Nibble}) |
  ({c == 'B' : Char} & {d == nibble(11n) : Nibble}) |
  ({c == 'C' : Char} & {d == nibble(12n) : Nibble}) |
  ({c == 'D' : Char} & {d == nibble(13n) : Nibble}) |
  ({c == 'E' : Char} & {d == nibble(14n) : Nibble}) |
  ({c == 'F' : Char} & {d == nibble(15n) : Nibble})

# A valid input to hex_u32 is a string of exactly eight characters,
# each of which is a valid hexadecimal digit.

law is_valid_hex_u32_input:
  for +s: String
  {H.is_valid_hex_u32(s) == (
    Nat.is_eq(String.length(s), 8n) &&
    List.all(~&2, ~Char, ~(c => H.is_hex_digit(c)), String.to_list(s))
  ) : Bool}

# Project the validated characters back to their original string.
def hex_digit_chars(digits: +List<H.HexDigitChar>) -> String:
  match digits:
    case Nil{}:
      SNil{}
    case Con{digit, rest}:
      SCon{H.HexDigitChar.char(digit), hex_digit_chars(rest)}

# Derive one nibble for each validated character, preserving order and length.
def hex_digit_nibbles(digits: +List<H.HexDigitChar>) -> +List<Nibble>:
  match digits:
    case Nil{}:
      Nil{}
    case Con{digit, rest}:
      H.decode(digit) <> hex_digit_nibbles(rest)

# Accumulate hexadecimal digits from most significant to least significant.
def hex_u32_value(nibbles: +List<Nibble>) -> U32:
  List.foldl(~&2, ~Nibble, ~U32,
    ~(acc => n => (acc * 16 + U32.from_nat(Word.to_nat(4n, n)) : U32)),
    nibbles, 0)

# The validated character list spells the original input string.
def HexCharsSpell(+s: String, digits: +List<H.HexDigitChar>) -> Type:
  {s == hex_digit_chars(digits) : String}

# The derived nibble list has the stated numeric value.
def HexDigitsValue(result: U32, digits: +List<H.HexDigitChar>) -> Type:
  {result == hex_u32_value(hex_digit_nibbles(digits)) : U32}

# One list of exactly eight characters witnesses both spelling and value.
def HexU32Result(+s: String, result: U32) -> Type:
  &digits: +List<H.HexDigitChar> ->
  {List.length(&2, H.HexDigitChar, digits) == 8n : Nat} &
  HexCharsSpell(s, digits) &
  HexDigitsValue(result, digits)

# A valid input decomposes into a list of eight validated hexadecimal characters.
# The first character is the most significant: "12345678" represents 0x12345678.
law hex_u32:
  for +s: String
  for valid: {H.is_valid_hex_u32(s) == True{} : Bool}
  HexU32Result(s, H.hex_u32(s, valid))
