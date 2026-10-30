import Base
import ./hexdigits.bend as H

# The complete set of accepted hexadecimal characters.
def hex_digits() -> +List<Char>:
  ['0', '1', '2', '3', '4', '5', '6', '7',
   '8', '9', 'A', 'B', 'C', 'D', 'E', 'F']

# A character is hexadecimal exactly when it occurs in hex_digits.
law is_hex_digit:
  for +c: Char
  {H.is_hex_digit(c) == List.contains(~Char, ~Char.is_eq, hex_digits(), c) : Bool}

# Construct a four-bit numeral; the table below uses only 0n through 15n.
def word4(n: Nat) -> Word(4n):
  match n:
    case 0n:
      Word.zero(4n)
    case 1n+p:
      Word.inc(4n, word4(p))

# The exact character-to-four-bit-value mapping.
def hex_digit_values() -> List<(Char & Word(4n))>:
  [('0', word4(0n)), ('1', word4(1n)), ('2', word4(2n)), ('3', word4(3n)),
   ('4', word4(4n)), ('5', word4(5n)), ('6', word4(6n)), ('7', word4(7n)),
   ('8', word4(8n)), ('9', word4(9n)), ('A', word4(10n)), ('B', word4(11n)),
   ('C', word4(12n)), ('D', word4(13n)), ('E', word4(14n)), ('F', word4(15n))]

def hex_digit_value(entries: List<(Char & Word(4n))>, +c: Char) -> Maybe<Word(4n)>:
  match entries:
    case Nil{}:
      None{}
    case Con{(key, value), rest}:
      Bool.pick(Maybe<Word(4n)>, Char.is_eq(c, key),
        Some{value}, hex_digit_value(rest, c))

# The proof-carrying decoder returns the four-bit value found in the table.
law decode:
  for +c: Char
  for valid: {H.is_hex_digit(c) == True{} : Bool}
  {hex_digit_value(hex_digit_values(), c) == Some{H.decode(c, valid)} : Maybe<Word(4n)>}

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

# Every valid input decomposes into eight valid characters and their values.
# The first character is the most significant: "12345678" represents 0x12345678.
law hex_u32:
  for +s: String
  for valid: {H.is_valid_hex_u32(s) == True{} : Bool}
  exs c1: Char
  exs c2: Char
  exs c3: Char
  exs c4: Char
  exs c5: Char
  exs c6: Char
  exs c7: Char
  exs c8: Char
  exs p1: {H.is_hex_digit(c1) == True{} : Bool}
  exs p2: {H.is_hex_digit(c2) == True{} : Bool}
  exs p3: {H.is_hex_digit(c3) == True{} : Bool}
  exs p4: {H.is_hex_digit(c4) == True{} : Bool}
  exs p5: {H.is_hex_digit(c5) == True{} : Bool}
  exs p6: {H.is_hex_digit(c6) == True{} : Bool}
  exs p7: {H.is_hex_digit(c7) == True{} : Bool}
  exs p8: {H.is_hex_digit(c8) == True{} : Bool}
  d1 = H.decode(c1, p1)
  d2 = H.decode(c2, p2)
  d3 = H.decode(c3, p3)
  d4 = H.decode(c4, p4)
  d5 = H.decode(c5, p5)
  d6 = H.decode(c6, p6)
  d7 = H.decode(c7, p7)
  d8 = H.decode(c8, p8)
  {s == SCon{c1, SCon{c2, SCon{c3, SCon{c4, SCon{c5, SCon{c6, SCon{c7, SCon{c8, SNil{}}}}}}}}} : String} &
  {H.hex_u32(s, valid) == hex_u32_value(d1, d2, d3, d4, d5, d6, d7, d8) : U32}
