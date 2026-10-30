import Base

def is_hex_digit(+c: Char) -> Bool:
  +code = Char.to_u32(c)
  Char.is_digit(c) || Bool.and(U32.is_ge(code, 65), U32.is_le(code, 70))

def decode(+c: Char, valid: {is_hex_digit(c) == True{} : Bool}) -> U32:
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
  15)))))))))))))))

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

def hex_u32.combine(
  +c1: Char, +c2: Char, +c3: Char, +c4: Char, +c5: Char, +c6: Char, +c7: Char, +c8: Char,
  proofs: {is_hex_digit(c1) == True{} : Bool} & {is_hex_digit(c2) == True{} : Bool} & {is_hex_digit(c3) == True{} : Bool} & {is_hex_digit(c4) == True{} : Bool} & {is_hex_digit(c5) == True{} : Bool} & {is_hex_digit(c6) == True{} : Bool} & {is_hex_digit(c7) == True{} : Bool} & {is_hex_digit(c8) == True{} : Bool}
) -> U32:
  match proofs:
    case (p1, p2, p3, p4, p5, p6, p7, p8):
      h1 = decode(c1, p1)
      h2 = decode(c2, p2)
      h3 = decode(c3, p3)
      h4 = decode(c4, p4)
      h5 = decode(c5, p5)
      h6 = decode(c6, p6)
      h7 = decode(c7, p7)
      h8 = decode(c8, p8)
      (h1 * U32.pow(16, 7n) +
       h2 * U32.pow(16, 6n) +
       h3 * U32.pow(16, 5n) +
       h4 * U32.pow(16, 4n) +
       h5 * U32.pow(16, 3n) +
       h6 * U32.pow(16, 2n) +
       h7 * U32.pow(16, 1n) +
       h8 * U32.pow(16, 0n) : U32)

def hex_u32(+s: String, valid: {is_valid_hex_u32(s) == True{} : Bool}) -> U32:
  match s:
    case SCon{c1, SCon{c2, SCon{c3, SCon{c4, SCon{c5, SCon{c6, SCon{c7, SCon{c8, SNil{}}}}}}}}}:
      hex_u32.combine(c1, c2, c3, c4, c5, c6, c7, c8,
        hex_u32.digit_proofs(c1, c2, c3, c4, c5, c6, c7, c8, valid))
    case _:
      0
