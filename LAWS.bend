import Base
import ./hexdigits.bend as H

# Exactly the sixteen uppercase hexadecimal digits are accepted.
law is_hex_digit_spec:
  for +c: Char
  {H.is_hex_digit(c) == (
    Char.is_eq(c, '0') ||
    Char.is_eq(c, '1') ||
    Char.is_eq(c, '2') ||
    Char.is_eq(c, '3') ||
    Char.is_eq(c, '4') ||
    Char.is_eq(c, '5') ||
    Char.is_eq(c, '6') ||
    Char.is_eq(c, '7') ||
    Char.is_eq(c, '8') ||
    Char.is_eq(c, '9') ||
    Char.is_eq(c, 'A') ||
    Char.is_eq(c, 'B') ||
    Char.is_eq(c, 'C') ||
    Char.is_eq(c, 'D') ||
    Char.is_eq(c, 'E') ||
    Char.is_eq(c, 'F')
  ) : Bool}

# Bool.pick(U32, condition, yes, no) expresses each conditional.
# With valid input, the final else branch can only be 'F', whose value is 15.
law decode_spec:
  for +c: Char
  for valid: {H.is_hex_digit(c) == True{} : Bool}
  {H.decode(c, valid) ==
    Bool.pick(U32, Char.is_eq(c, '0'), 0,
    Bool.pick(U32, Char.is_eq(c, '1'), 1,
    Bool.pick(U32, Char.is_eq(c, '2'), 2,
    Bool.pick(U32, Char.is_eq(c, '3'), 3,
    Bool.pick(U32, Char.is_eq(c, '4'), 4,
    Bool.pick(U32, Char.is_eq(c, '5'), 5,
    Bool.pick(U32, Char.is_eq(c, '6'), 6,
    Bool.pick(U32, Char.is_eq(c, '7'), 7,
    Bool.pick(U32, Char.is_eq(c, '8'), 8,
    Bool.pick(U32, Char.is_eq(c, '9'), 9,
    Bool.pick(U32, Char.is_eq(c, 'A'), 10,
    Bool.pick(U32, Char.is_eq(c, 'B'), 11,
    Bool.pick(U32, Char.is_eq(c, 'C'), 12,
    Bool.pick(U32, Char.is_eq(c, 'D'), 13,
    Bool.pick(U32, Char.is_eq(c, 'E'), 14,
    15))))))))))))))) : U32}

# Exactly eight characters, all uppercase hexadecimal digits.
law is_valid_hex_u32_spec:
  for +s: String
  {H.is_valid_hex_u32(s) == (
    Nat.is_eq(String.length(s), 8n) &&
    List.all(~&2, ~Char, ~(c => H.is_hex_digit(c)), String.to_list(s))
  ) : Bool}

# Decompose every valid input into eight valid digits and their decoded values.
# The first character is the most significant: "12345678" represents 0x12345678.
law hex_u32_spec:
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
  h1 = H.decode(c1, p1)
  h2 = H.decode(c2, p2)
  h3 = H.decode(c3, p3)
  h4 = H.decode(c4, p4)
  h5 = H.decode(c5, p5)
  h6 = H.decode(c6, p6)
  h7 = H.decode(c7, p7)
  h8 = H.decode(c8, p8)
  {s == SCon{c1, SCon{c2, SCon{c3, SCon{c4,
        SCon{c5, SCon{c6, SCon{c7, SCon{c8, SNil{}}}}}}}}} : String} &
  {H.hex_u32(s, valid) == (
    h1 * U32.pow(16, 7n) +
    h2 * U32.pow(16, 6n) +
    h3 * U32.pow(16, 5n) +
    h4 * U32.pow(16, 4n) +
    h5 * U32.pow(16, 3n) +
    h6 * U32.pow(16, 2n) +
    h7 * U32.pow(16, 1n) +
    h8 * U32.pow(16, 0n) : U32
  ) : U32}
