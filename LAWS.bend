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

# Eight nibbles is four bytes, which exactly covers a U32.

def hex_u32_value(
  n1: Nibble, n2: Nibble, n3: Nibble, n4: Nibble,
  n5: Nibble, n6: Nibble, n7: Nibble, n8: Nibble
) -> U32:
  (U32.from_nat(Word.to_nat(4n, n1)) * U32.pow(16, 7n) +
   U32.from_nat(Word.to_nat(4n, n2)) * U32.pow(16, 6n) +
   U32.from_nat(Word.to_nat(4n, n3)) * U32.pow(16, 5n) +
   U32.from_nat(Word.to_nat(4n, n4)) * U32.pow(16, 4n) +
   U32.from_nat(Word.to_nat(4n, n5)) * U32.pow(16, 3n) +
   U32.from_nat(Word.to_nat(4n, n6)) * U32.pow(16, 2n) +
   U32.from_nat(Word.to_nat(4n, n7)) * U32.pow(16, 1n) +
   U32.from_nat(Word.to_nat(4n, n8)) * U32.pow(16, 0n) : U32)

# The eight validated characters spell the original input string.
def HexCharsSpell(
  +s: String,
  c1: H.HexDigitChar, c2: H.HexDigitChar, c3: H.HexDigitChar, c4: H.HexDigitChar,
  c5: H.HexDigitChar, c6: H.HexDigitChar, c7: H.HexDigitChar, c8: H.HexDigitChar
) -> Type:
  {s == SCon{H.HexDigitChar.char(c1), SCon{H.HexDigitChar.char(c2),
        SCon{H.HexDigitChar.char(c3), SCon{H.HexDigitChar.char(c4),
        SCon{H.HexDigitChar.char(c5), SCon{H.HexDigitChar.char(c6),
        SCon{H.HexDigitChar.char(c7), SCon{H.HexDigitChar.char(c8), SNil{}}}}}}}}} : String}

# Decoding those characters gives the stated result, most significant first.
def HexDigitsValue(
  result: U32,
  c1: H.HexDigitChar, c2: H.HexDigitChar, c3: H.HexDigitChar, c4: H.HexDigitChar,
  c5: H.HexDigitChar, c6: H.HexDigitChar, c7: H.HexDigitChar, c8: H.HexDigitChar
) -> Type:
  n1 = H.decode(c1)
  n2 = H.decode(c2)
  n3 = H.decode(c3)
  n4 = H.decode(c4)
  n5 = H.decode(c5)
  n6 = H.decode(c6)
  n7 = H.decode(c7)
  n8 = H.decode(c8)
  {result == hex_u32_value(n1, n2, n3, n4, n5, n6, n7, n8) : U32}

# Both properties share the same eight character witnesses.
def HexU32Result(+s: String, result: U32) -> Type:
  &c1: H.HexDigitChar ->
  &c2: H.HexDigitChar ->
  &c3: H.HexDigitChar ->
  &c4: H.HexDigitChar ->
  &c5: H.HexDigitChar ->
  &c6: H.HexDigitChar ->
  &c7: H.HexDigitChar ->
  &c8: H.HexDigitChar ->
  HexCharsSpell(s, c1, c2, c3, c4, c5, c6, c7, c8) &
  HexDigitsValue(result, c1, c2, c3, c4, c5, c6, c7, c8)

# A valid input decomposes into eight proof-carrying hexadecimal characters.
# The first character is the most significant: "12345678" represents 0x12345678.
law hex_u32:
  for +s: String
  for valid: {H.is_valid_hex_u32(s) == True{} : Bool}
  HexU32Result(s, H.hex_u32(s, valid))
