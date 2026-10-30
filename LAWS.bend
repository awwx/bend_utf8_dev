import Base
import ./hexdigits.bend as H

# The complete set of accepted hexadecimal characters.
def hex_digits() -> +List<Char>:
  ['0', '1', '2', '3', '4', '5', '6', '7',
   '8', '9', 'A', 'B', 'C', 'D', 'E', 'F']

# A character is a hexadecimal digit when it is present in the hex_digits list.
law is_hex_digit:
  for +c: Char
  {H.is_hex_digit(c) == List.contains(~Char, ~Char.is_eq, hex_digits(), c) : Bool}

# A "nibble" is half of a byte, a four-bit numeral.
def nibble(n: Nat) -> Word(4n):
  match n:
    case 0n:
      Word.zero(4n)
    case 1n+p:
      Word.inc(4n, nibble(p))

# Specify the conversion of a hex digit character to the corresponding
# value.  A bit verbose with the types, but seems like the most
# straightforward way of describing the mapping.

def hex_digit_values() -> List<(H.HexDigitChar & Word(4n))>:
  [(H.HexDigitChar{'0', {==}}, nibble(0n)),
   (H.HexDigitChar{'1', {==}}, nibble(1n)),
   (H.HexDigitChar{'2', {==}}, nibble(2n)),
   (H.HexDigitChar{'3', {==}}, nibble(3n)),
   (H.HexDigitChar{'4', {==}}, nibble(4n)),
   (H.HexDigitChar{'5', {==}}, nibble(5n)),
   (H.HexDigitChar{'6', {==}}, nibble(6n)),
   (H.HexDigitChar{'7', {==}}, nibble(7n)),
   (H.HexDigitChar{'8', {==}}, nibble(8n)),
   (H.HexDigitChar{'9', {==}}, nibble(9n)),
   (H.HexDigitChar{'A', {==}}, nibble(10n)),
   (H.HexDigitChar{'B', {==}}, nibble(11n)),
   (H.HexDigitChar{'C', {==}}, nibble(12n)),
   (H.HexDigitChar{'D', {==}}, nibble(13n)),
   (H.HexDigitChar{'E', {==}}, nibble(14n)),
   (H.HexDigitChar{'F', {==}}, nibble(15n))]

# Arbitrary tables may omit a key, so generic lookup remains optional.
def lookup_hex_digit_value(
  entries: List<(H.HexDigitChar & Word(4n))>, +digit: H.HexDigitChar
) -> Maybe<Word(4n)>:
  match entries:
    case Nil{}:
      None{}
    case Con{(key, value), rest}:
      Bool.pick(Maybe<Word(4n)>, H.HexDigitChar.is_eq(digit, key),
        Some{value}, lookup_hex_digit_value(rest, digit))

# The decoder's direct result must be present in the fixed table.
law decode:
  for +digit: H.HexDigitChar
  {lookup_hex_digit_value(hex_digit_values(), digit) ==
    Some{H.decode(digit)} : Maybe<Word(4n)>}

# Every validated hexadecimal character has an entry in the fixed table.
law hex_digit_values_complete:
  for +digit: H.HexDigitChar
  exs value: Word(4n)
  {lookup_hex_digit_value(hex_digit_values(), digit) == Some{value} : Maybe<Word(4n)>}

# Exactly eight characters, all uppercase hexadecimal digits.
law is_valid_hex_u32_input:
  for +s: String
  {H.is_valid_hex_u32(s) == (
    Nat.is_eq(String.length(s), 8n) &&
    List.all(~&2, ~Char, ~(c => H.is_hex_digit(c)), String.to_list(s))
  ) : Bool}

# Combine eight four-bit digit values, most significant first.
def hex_u32_value(
  d1: Word(4n), d2: Word(4n), d3: Word(4n), d4: Word(4n),
  d5: Word(4n), d6: Word(4n), d7: Word(4n), d8: Word(4n)
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
