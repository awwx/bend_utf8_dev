import Base

def is_binary_digit(+c: Char) -> Bool:
  Char.is_eq('0', c) || Char.is_eq('1', c)

def bit_to_char(bit: Bool) -> Char:
  match bit:
    case False{}: '0'
    case True{}: '1'

def char_to_bit(c: Char) -> Bool:
  Char.is_eq(c, '1')

def is_valid_binary_byte(+s: String) -> Bool:
  Nat.is_eq(String.length(s), 8n) &&
  List.all(~&2, ~Char, ~(c => is_binary_digit(c)), String.to_list(s))

# Fold in textual order: the first bit has weight 128, the last weight 1.
def binary_byte.fold_bits(bits: +List<Bool>, acc: U32) -> U32:
  match bits:
    case Nil{}:
      acc
    case Con{bit, rest}:
      binary_byte.fold_bits(rest, (acc * 2 + Bool.to_u32(bit) : U32))

def binary_byte(+s: String, valid: {is_valid_binary_byte(s) == True{} : Bool}) -> U32:
  match s:
    case SCon{c1, SCon{c2, SCon{c3, SCon{c4, SCon{c5, SCon{c6, SCon{c7, SCon{c8, SNil{}}}}}}}}}:
      binary_byte.fold_bits([char_to_bit(c1), char_to_bit(c2), char_to_bit(c3), char_to_bit(c4), char_to_bit(c5), char_to_bit(c6), char_to_bit(c7), char_to_bit(c8)], 0)
    case _:
      0
