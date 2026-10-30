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
  d1: Nibble, d2: Nibble, d3: Nibble, d4: Nibble,
  d5: Nibble, d6: Nibble, d7: Nibble, d8: Nibble
) -> U32:
  (U32.from_nat(Word.to_nat(4n, d1)) * U32.pow(16, 7n) +
   U32.from_nat(Word.to_nat(4n, d2)) * U32.pow(16, 6n) +
   U32.from_nat(Word.to_nat(4n, d3)) * U32.pow(16, 5n) +
   U32.from_nat(Word.to_nat(4n, d4)) * U32.pow(16, 4n) +
   U32.from_nat(Word.to_nat(4n, d5)) * U32.pow(16, 3n) +
   U32.from_nat(Word.to_nat(4n, d6)) * U32.pow(16, 2n) +
   U32.from_nat(Word.to_nat(4n, d7)) * U32.pow(16, 1n) +
   U32.from_nat(Word.to_nat(4n, d8)) * U32.pow(16, 0n) : U32)

# A valid input decomposes into eight proof-carrying hexadecimal characters.
# The first character is the most significant: "12345678" represents 0x12345678.
law hex_u32:
  for +s: String
  for valid: {H.is_valid_hex_u32(s) == True{} : Bool}
  exs c1: H.HexDigitChar
  exs c2: H.HexDigitChar
  exs c3: H.HexDigitChar
  exs c4: H.HexDigitChar
  exs c5: H.HexDigitChar
  exs c6: H.HexDigitChar
  exs c7: H.HexDigitChar
  exs c8: H.HexDigitChar
  d1 = H.decode(c1)
  d2 = H.decode(c2)
  d3 = H.decode(c3)
  d4 = H.decode(c4)
  d5 = H.decode(c5)
  d6 = H.decode(c6)
  d7 = H.decode(c7)
  d8 = H.decode(c8)
  {s == SCon{H.HexDigitChar.char(c1), SCon{H.HexDigitChar.char(c2), SCon{H.HexDigitChar.char(c3), SCon{H.HexDigitChar.char(c4), SCon{H.HexDigitChar.char(c5), SCon{H.HexDigitChar.char(c6), SCon{H.HexDigitChar.char(c7), SCon{H.HexDigitChar.char(c8), SNil{}}}}}}}}} : String} &
  {H.hex_u32(s, valid) == hex_u32_value(d1, d2, d3, d4, d5, d6, d7, d8) : U32}
