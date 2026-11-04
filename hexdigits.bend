import Base

def is_hex_digit(+c: Char) -> Bool:
  +code = Char.to_u32(c)
  Char.is_digit(c) || Bool.and(U32.is_ge(code, 65), U32.is_le(code, 70))

# A reusable character packaged with erased evidence that it is a hex digit.
type HexDigitChar is Data:
  HexDigitChar{char: Char, -valid: {is_hex_digit(char) == True{} : Bool}}

# Four-bit words use least-significant-bit-first WCon fields.
def word4_from_u32(n: U32) -> Word(4n):
  match n:
    case U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, rest}}}}}:
      WCon{b0, WCon{b1, WCon{b2, WCon{b3, WNil{}}}}}

def word4_to_u32(d: Word(4n)) -> U32:
  U32.from_nat(Word.to_nat(4n, d))

# The input type carries all evidence needed for a direct four-bit result.
def decode(digit: HexDigitChar) -> Word(4n):
  match digit:
    case HexDigitChar{+c, valid}:
      +code = Char.to_u32(c)
      word4_from_u32(Bool.pick(U32, Char.is_digit(c),
        U32.sub(code, 48), U32.sub(code, 55)))

def is_valid_hex_u32(+s: String) -> Bool:
  Nat.is_eq(String.length(s), 8n) &&
  List.all(~&2, ~Char, ~(c => is_hex_digit(c)), String.to_list(s))

# A live proof of False == True rules out invalid input lengths.
def hex_u32.NotTrue(b: Bool) -> Type:
  match b:
    case False{}:
      Unit
    case True{}:
      Empty

def hex_u32.false_true(e: {False{} == True{} : Bool}) -> Empty:
  %e : hex_u32.NotTrue(_)
  Unit{}

# Project the head and tail validity proofs from List.all's conjunction.
def hex_u32.head_true(
  hit: Bool, -rest: Bool,
  e: {List.all.if(u => rest, hit) == True{} : Bool}
) -> {hit == True{} : Bool}:
  match hit:
    case False{}:
      e
    case True{}:
      {==}

def hex_u32.tail_true(
  hit: Bool, -rest: Bool,
  e: {List.all.if(u => rest, hit) == True{} : Bool}
) -> {rest == True{} : Bool}:
  match hit:
    case False{}:
      Empty.absurd({rest == True{} : Bool}, hex_u32.false_true(e))
    case True{}:
      e

# Eight valid characters give eight individual digit proofs.
def hex_u32.digit_proofs(
  +c1: Char, +c2: Char, +c3: Char, +c4: Char,
  +c5: Char, +c6: Char, +c7: Char, +c8: Char,
  +valid: {is_valid_hex_u32(SCon{c1, SCon{c2, SCon{c3, SCon{c4, SCon{c5, SCon{c6, SCon{c7, SCon{c8, SNil{}}}}}}}}}) == True{} : Bool}
) -> (
  {is_hex_digit(c1) == True{} : Bool} &
  {is_hex_digit(c2) == True{} : Bool} &
  {is_hex_digit(c3) == True{} : Bool} &
  {is_hex_digit(c4) == True{} : Bool} &
  {is_hex_digit(c5) == True{} : Bool} &
  {is_hex_digit(c6) == True{} : Bool} &
  {is_hex_digit(c7) == True{} : Bool} &
  {is_hex_digit(c8) == True{} : Bool}
):
  p1 = hex_u32.head_true(is_hex_digit(c1), List.all(~&2, ~Char, ~(c => is_hex_digit(c)), [c2, c3, c4, c5, c6, c7, c8]), valid)
  +e1 = hex_u32.tail_true(is_hex_digit(c1), List.all(~&2, ~Char, ~(c => is_hex_digit(c)), [c2, c3, c4, c5, c6, c7, c8]), valid)
  p2 = hex_u32.head_true(is_hex_digit(c2), List.all(~&2, ~Char, ~(c => is_hex_digit(c)), [c3, c4, c5, c6, c7, c8]), e1)
  +e2 = hex_u32.tail_true(is_hex_digit(c2), List.all(~&2, ~Char, ~(c => is_hex_digit(c)), [c3, c4, c5, c6, c7, c8]), e1)
  p3 = hex_u32.head_true(is_hex_digit(c3), List.all(~&2, ~Char, ~(c => is_hex_digit(c)), [c4, c5, c6, c7, c8]), e2)
  +e3 = hex_u32.tail_true(is_hex_digit(c3), List.all(~&2, ~Char, ~(c => is_hex_digit(c)), [c4, c5, c6, c7, c8]), e2)
  p4 = hex_u32.head_true(is_hex_digit(c4), List.all(~&2, ~Char, ~(c => is_hex_digit(c)), [c5, c6, c7, c8]), e3)
  +e4 = hex_u32.tail_true(is_hex_digit(c4), List.all(~&2, ~Char, ~(c => is_hex_digit(c)), [c5, c6, c7, c8]), e3)
  p5 = hex_u32.head_true(is_hex_digit(c5), List.all(~&2, ~Char, ~(c => is_hex_digit(c)), [c6, c7, c8]), e4)
  +e5 = hex_u32.tail_true(is_hex_digit(c5), List.all(~&2, ~Char, ~(c => is_hex_digit(c)), [c6, c7, c8]), e4)
  p6 = hex_u32.head_true(is_hex_digit(c6), List.all(~&2, ~Char, ~(c => is_hex_digit(c)), [c7, c8]), e5)
  +e6 = hex_u32.tail_true(is_hex_digit(c6), List.all(~&2, ~Char, ~(c => is_hex_digit(c)), [c7, c8]), e5)
  p7 = hex_u32.head_true(is_hex_digit(c7), List.all(~&2, ~Char, ~(c => is_hex_digit(c)), [c8]), e6)
  +e7 = hex_u32.tail_true(is_hex_digit(c7), List.all(~&2, ~Char, ~(c => is_hex_digit(c)), [c8]), e6)
  p8 = hex_u32.head_true(is_hex_digit(c8), List.all(~&2, ~Char, ~(c => is_hex_digit(c)), []), e7)
  (p1, p2, p3, p4, p5, p6, p7, p8)

# Fold validated characters into acc, most significant digit first. Each step
# splits List.all's conjunction into the head digit's proof and the tail's.
def hex_u32.combine(
  cs: +List<Char>,
  -valid: {List.all(~&2, ~Char, ~(c => is_hex_digit(c)), cs) == True{} : Bool},
  acc: U32
) -> U32:
  match cs:
    case Nil{}:
      acc
    case Con{c, rest}:
      -rest_ok = List.all(~&2, ~Char, ~(c => is_hex_digit(c)), rest)
      digit = decode(HexDigitChar{c, hex_u32.head_true(is_hex_digit(c), rest_ok, valid)})
      hex_u32.combine(rest, hex_u32.tail_true(is_hex_digit(c), rest_ok, valid),
        (acc * 16 + word4_to_u32(digit) : U32))

def hex_u32(+s: String, -valid: {is_valid_hex_u32(s) == True{} : Bool}) -> U32:
  match s:
    case SCon{c1, SCon{c2, SCon{c3, SCon{c4, SCon{c5, SCon{c6, SCon{c7, SCon{c8, SNil{}}}}}}}}}:
      hex_u32.combine([c1, c2, c3, c4, c5, c6, c7, c8], valid, 0)
    case _:
      0
