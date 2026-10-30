import Base
import ./LAWS.bend as Laws
import ./hexdigits.bend as H

# State the membership specification as a type for the bit-level lemma.
def HexDigitSpec(+c: Char) -> Type:
  {H.is_hex_digit(c) == List.contains(~Char, ~Char.is_eq, Laws.hex_digits(), c) : Bool}

# Most-significant bits come first, matching Bend's binder order.
def char_from_bits(
  b31: Bool, b30: Bool, b29: Bool, b28: Bool, b27: Bool, b26: Bool, b25: Bool, b24: Bool,
  b23: Bool, b22: Bool, b21: Bool, b20: Bool, b19: Bool, b18: Bool, b17: Bool, b16: Bool,
  b15: Bool, b14: Bool, b13: Bool, b12: Bool, b11: Bool, b10: Bool, b9: Bool, b8: Bool,
  b7: Bool, b6: Bool, b5: Bool, b4: Bool, b3: Bool, b2: Bool, b1: Bool, b0: Bool
) -> Char:
  Chr{U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

law hex_digit_bits:
  for +b31: Bool
  for +b30: Bool
  for +b29: Bool
  for +b28: Bool
  for +b27: Bool
  for +b26: Bool
  for +b25: Bool
  for +b24: Bool
  for +b23: Bool
  for +b22: Bool
  for +b21: Bool
  for +b20: Bool
  for +b19: Bool
  for +b18: Bool
  for +b17: Bool
  for +b16: Bool
  for +b15: Bool
  for +b14: Bool
  for +b13: Bool
  for +b12: Bool
  for +b11: Bool
  for +b10: Bool
  for +b9: Bool
  for +b8: Bool
  for +b7: Bool
  for +b6: Bool
  for +b5: Bool
  for +b4: Bool
  for +b3: Bool
  for +b2: Bool
  for +b1: Bool
  for +b0: Bool
  HexDigitSpec(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))

def hex_digit_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0):
  # Any nonzero bit above bit 6 puts the code outside both ASCII ranges.
  match b31 b30 b29 b28 b27 b26 b25 b24 b23 b22 b21 b20 b19 b18 b17 b16 b15 b14 b13 b12 b11 b10 b9 b8 b7:
    case True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _:
      {==}
    case False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _:
      {==}
    case False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _:
      {==}
    case False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _:
      {==}
    case False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _:
      {==}
    case False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _:
      {==}
    case False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _:
      {==}
    case False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _:
      {==}
    case False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _:
      {==}
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _:
      {==}
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _:
      {==}
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _:
      {==}
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _:
      {==}
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _:
      {==}
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _:
      {==}
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _:
      {==}
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _:
      {==}
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _:
      {==}
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _:
      {==}
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _:
      {==}
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _:
      {==}
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _:
      {==}
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _:
      {==}
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _:
      {==}
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{}:
      {==}
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{}:
      match b6 b5 b4 b3 b2 b1 b0:
        case False{} False{} _ _ _ _ _:
          {==}
        case False{} True{} False{} _ _ _ _:
          {==}
        case False{} True{} True{} False{} False{} False{} False{}:
          {==}
        case False{} True{} True{} False{} False{} False{} True{}:
          {==}
        case False{} True{} True{} False{} False{} True{} False{}:
          {==}
        case False{} True{} True{} False{} False{} True{} True{}:
          {==}
        case False{} True{} True{} False{} True{} False{} False{}:
          {==}
        case False{} True{} True{} False{} True{} False{} True{}:
          {==}
        case False{} True{} True{} False{} True{} True{} False{}:
          {==}
        case False{} True{} True{} False{} True{} True{} True{}:
          {==}
        case False{} True{} True{} True{} False{} False{} False{}:
          {==}
        case False{} True{} True{} True{} False{} False{} True{}:
          {==}
        case False{} True{} True{} True{} False{} True{} _:
          {==}
        case False{} True{} True{} True{} True{} _ _:
          {==}
        case True{} False{} False{} False{} False{} False{} False{}:
          {==}
        case True{} False{} False{} False{} False{} False{} True{}:
          {==}
        case True{} False{} False{} False{} False{} True{} False{}:
          {==}
        case True{} False{} False{} False{} False{} True{} True{}:
          {==}
        case True{} False{} False{} False{} True{} False{} False{}:
          {==}
        case True{} False{} False{} False{} True{} False{} True{}:
          {==}
        case True{} False{} False{} False{} True{} True{} False{}:
          {==}
        case True{} False{} False{} False{} True{} True{} True{}:
          {==}
        case True{} False{} False{} True{} _ _ _:
          {==}
        case True{} False{} True{} _ _ _ _:
          {==}
        case True{} True{} _ _ _ _ _:
          {==}

def Laws.is_hex_digit(c):
  match c:
    case Chr{U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      hex_digit_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0)

# The direct decoder agrees with the table for every proven-valid character.
def DecodeSpec(+c: Char, valid: {H.is_hex_digit(c) == True{} : Bool}) -> Type:
  {Laws.hex_digit_value(Laws.hex_digit_values(), c) ==
    Some{H.decode(c, valid)} : Maybe<Word(4n)>}

law decode_bits:
  for +b31: Bool
  for +b30: Bool
  for +b29: Bool
  for +b28: Bool
  for +b27: Bool
  for +b26: Bool
  for +b25: Bool
  for +b24: Bool
  for +b23: Bool
  for +b22: Bool
  for +b21: Bool
  for +b20: Bool
  for +b19: Bool
  for +b18: Bool
  for +b17: Bool
  for +b16: Bool
  for +b15: Bool
  for +b14: Bool
  for +b13: Bool
  for +b12: Bool
  for +b11: Bool
  for +b10: Bool
  for +b9: Bool
  for +b8: Bool
  for +b7: Bool
  for +b6: Bool
  for +b5: Bool
  for +b4: Bool
  for +b3: Bool
  for +b2: Bool
  for +b1: Bool
  for +b0: Bool
  for valid: {H.is_hex_digit(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0)) == True{} : Bool}
  DecodeSpec(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0), valid)

def decode_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0, valid):
  match b31 b30 b29 b28 b27 b26 b25 b24 b23 b22 b21 b20 b19 b18 b17 b16 b15 b14 b13 b12 b11 b10 b9 b8 b7:
    case True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(DecodeSpec(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0), valid), H.hex_u32.false_true(valid))
    case False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(DecodeSpec(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0), valid), H.hex_u32.false_true(valid))
    case False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(DecodeSpec(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0), valid), H.hex_u32.false_true(valid))
    case False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(DecodeSpec(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0), valid), H.hex_u32.false_true(valid))
    case False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(DecodeSpec(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0), valid), H.hex_u32.false_true(valid))
    case False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(DecodeSpec(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0), valid), H.hex_u32.false_true(valid))
    case False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(DecodeSpec(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0), valid), H.hex_u32.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(DecodeSpec(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0), valid), H.hex_u32.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(DecodeSpec(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0), valid), H.hex_u32.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(DecodeSpec(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0), valid), H.hex_u32.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(DecodeSpec(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0), valid), H.hex_u32.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(DecodeSpec(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0), valid), H.hex_u32.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(DecodeSpec(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0), valid), H.hex_u32.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(DecodeSpec(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0), valid), H.hex_u32.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(DecodeSpec(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0), valid), H.hex_u32.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _:
      Empty.absurd(DecodeSpec(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0), valid), H.hex_u32.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _:
      Empty.absurd(DecodeSpec(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0), valid), H.hex_u32.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _:
      Empty.absurd(DecodeSpec(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0), valid), H.hex_u32.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _:
      Empty.absurd(DecodeSpec(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0), valid), H.hex_u32.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _:
      Empty.absurd(DecodeSpec(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0), valid), H.hex_u32.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _:
      Empty.absurd(DecodeSpec(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0), valid), H.hex_u32.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _:
      Empty.absurd(DecodeSpec(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0), valid), H.hex_u32.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _:
      Empty.absurd(DecodeSpec(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0), valid), H.hex_u32.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _:
      Empty.absurd(DecodeSpec(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0), valid), H.hex_u32.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{}:
      Empty.absurd(DecodeSpec(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0), valid), H.hex_u32.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{}:
      match b6 b5 b4 b3 b2 b1 b0:
        case False{} False{} _ _ _ _ _:
          Empty.absurd(DecodeSpec(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0), valid), H.hex_u32.false_true(valid))
        case False{} True{} False{} _ _ _ _:
          Empty.absurd(DecodeSpec(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0), valid), H.hex_u32.false_true(valid))
        case False{} True{} True{} False{} False{} False{} False{}:
          {==}
        case False{} True{} True{} False{} False{} False{} True{}:
          {==}
        case False{} True{} True{} False{} False{} True{} False{}:
          {==}
        case False{} True{} True{} False{} False{} True{} True{}:
          {==}
        case False{} True{} True{} False{} True{} False{} False{}:
          {==}
        case False{} True{} True{} False{} True{} False{} True{}:
          {==}
        case False{} True{} True{} False{} True{} True{} False{}:
          {==}
        case False{} True{} True{} False{} True{} True{} True{}:
          {==}
        case False{} True{} True{} True{} False{} False{} False{}:
          {==}
        case False{} True{} True{} True{} False{} False{} True{}:
          {==}
        case False{} True{} True{} True{} False{} True{} _:
          Empty.absurd(DecodeSpec(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0), valid), H.hex_u32.false_true(valid))
        case False{} True{} True{} True{} True{} _ _:
          Empty.absurd(DecodeSpec(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0), valid), H.hex_u32.false_true(valid))
        case True{} False{} False{} False{} False{} False{} False{}:
          Empty.absurd(DecodeSpec(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0), valid), H.hex_u32.false_true(valid))
        case True{} False{} False{} False{} False{} False{} True{}:
          {==}
        case True{} False{} False{} False{} False{} True{} False{}:
          {==}
        case True{} False{} False{} False{} False{} True{} True{}:
          {==}
        case True{} False{} False{} False{} True{} False{} False{}:
          {==}
        case True{} False{} False{} False{} True{} False{} True{}:
          {==}
        case True{} False{} False{} False{} True{} True{} False{}:
          {==}
        case True{} False{} False{} False{} True{} True{} True{}:
          Empty.absurd(DecodeSpec(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0), valid), H.hex_u32.false_true(valid))
        case True{} False{} False{} True{} _ _ _:
          Empty.absurd(DecodeSpec(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0), valid), H.hex_u32.false_true(valid))
        case True{} False{} True{} _ _ _ _:
          Empty.absurd(DecodeSpec(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0), valid), H.hex_u32.false_true(valid))
        case True{} True{} _ _ _ _ _:
          Empty.absurd(DecodeSpec(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0), valid), H.hex_u32.false_true(valid))

def Laws.decode(c, valid):
  match c:
    case Chr{U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      decode_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0, valid)

def Laws.is_valid_hex_u32_input(s):
  {==}

def HexU32Spec(+s: String, valid: {H.is_valid_hex_u32(s) == True{} : Bool}) -> Type:
  &c1: Char ->
  &c2: Char ->
  &c3: Char ->
  &c4: Char ->
  &c5: Char ->
  &c6: Char ->
  &c7: Char ->
  &c8: Char ->
  &p1: {H.is_hex_digit(c1) == True{} : Bool} ->
  &p2: {H.is_hex_digit(c2) == True{} : Bool} ->
  &p3: {H.is_hex_digit(c3) == True{} : Bool} ->
  &p4: {H.is_hex_digit(c4) == True{} : Bool} ->
  &p5: {H.is_hex_digit(c5) == True{} : Bool} ->
  &p6: {H.is_hex_digit(c6) == True{} : Bool} ->
  &p7: {H.is_hex_digit(c7) == True{} : Bool} ->
  &p8: {H.is_hex_digit(c8) == True{} : Bool} ->
  (
    d1 = H.decode(c1, p1)
    d2 = H.decode(c2, p2)
    d3 = H.decode(c3, p3)
    d4 = H.decode(c4, p4)
    d5 = H.decode(c5, p5)
    d6 = H.decode(c6, p6)
    d7 = H.decode(c7, p7)
    d8 = H.decode(c8, p8)
    {s == SCon{c1, SCon{c2, SCon{c3, SCon{c4, SCon{c5, SCon{c6, SCon{c7, SCon{c8, SNil{}}}}}}}}} : String} &
    {H.hex_u32(s, valid) == Laws.hex_u32_value(d1, d2, d3, d4, d5, d6, d7, d8) : U32}
  )

def hex_u32_complete(
  +c1: Char, +c2: Char, +c3: Char, +c4: Char, +c5: Char, +c6: Char, +c7: Char, +c8: Char,
  valid: {H.is_valid_hex_u32(SCon{c1, SCon{c2, SCon{c3, SCon{c4, SCon{c5, SCon{c6, SCon{c7, SCon{c8, SNil{}}}}}}}}}) == True{} : Bool},
  proofs: {H.is_hex_digit(c1) == True{} : Bool} & {H.is_hex_digit(c2) == True{} : Bool} & {H.is_hex_digit(c3) == True{} : Bool} & {H.is_hex_digit(c4) == True{} : Bool} & {H.is_hex_digit(c5) == True{} : Bool} & {H.is_hex_digit(c6) == True{} : Bool} & {H.is_hex_digit(c7) == True{} : Bool} & {H.is_hex_digit(c8) == True{} : Bool}
) -> HexU32Spec(SCon{c1, SCon{c2, SCon{c3, SCon{c4, SCon{c5, SCon{c6, SCon{c7, SCon{c8, SNil{}}}}}}}}}, valid):
  match proofs:
    case (p1, p2, p3, p4, p5, p6, p7, p8):
      (c1, c2, c3, c4, c5, c6, c7, c8, p1, p2, p3, p4, p5, p6, p7, p8, ({==}, {==}))

def Laws.hex_u32(s, valid):
  match s:
    case SNil{}:
      Empty.absurd(HexU32Spec(SNil{}, valid), H.hex_u32.false_true(valid))
    case SCon{c1, SNil{}}:
      Empty.absurd(HexU32Spec(SCon{c1, SNil{}}, valid), H.hex_u32.false_true(valid))
    case SCon{c1, SCon{c2, SNil{}}}:
      Empty.absurd(HexU32Spec(SCon{c1, SCon{c2, SNil{}}}, valid), H.hex_u32.false_true(valid))
    case SCon{c1, SCon{c2, SCon{c3, SNil{}}}}:
      Empty.absurd(HexU32Spec(SCon{c1, SCon{c2, SCon{c3, SNil{}}}}, valid), H.hex_u32.false_true(valid))
    case SCon{c1, SCon{c2, SCon{c3, SCon{c4, SNil{}}}}}:
      Empty.absurd(HexU32Spec(SCon{c1, SCon{c2, SCon{c3, SCon{c4, SNil{}}}}}, valid), H.hex_u32.false_true(valid))
    case SCon{c1, SCon{c2, SCon{c3, SCon{c4, SCon{c5, SNil{}}}}}}:
      Empty.absurd(HexU32Spec(SCon{c1, SCon{c2, SCon{c3, SCon{c4, SCon{c5, SNil{}}}}}}, valid), H.hex_u32.false_true(valid))
    case SCon{c1, SCon{c2, SCon{c3, SCon{c4, SCon{c5, SCon{c6, SNil{}}}}}}}:
      Empty.absurd(HexU32Spec(SCon{c1, SCon{c2, SCon{c3, SCon{c4, SCon{c5, SCon{c6, SNil{}}}}}}}, valid), H.hex_u32.false_true(valid))
    case SCon{c1, SCon{c2, SCon{c3, SCon{c4, SCon{c5, SCon{c6, SCon{c7, SNil{}}}}}}}}:
      Empty.absurd(HexU32Spec(SCon{c1, SCon{c2, SCon{c3, SCon{c4, SCon{c5, SCon{c6, SCon{c7, SNil{}}}}}}}}, valid), H.hex_u32.false_true(valid))
    case SCon{c1, SCon{c2, SCon{c3, SCon{c4, SCon{c5, SCon{c6, SCon{c7, SCon{c8, SNil{}}}}}}}}}:
      +v = valid
      hex_u32_complete(c1, c2, c3, c4, c5, c6, c7, c8, v,
        H.hex_u32.digit_proofs(c1, c2, c3, c4, c5, c6, c7, c8, v))
    case SCon{c1, SCon{c2, SCon{c3, SCon{c4, SCon{c5, SCon{c6, SCon{c7, SCon{c8, SCon{c9, rest}}}}}}}}}:
      Empty.absurd(HexU32Spec(SCon{c1, SCon{c2, SCon{c3, SCon{c4, SCon{c5, SCon{c6, SCon{c7, SCon{c8, SCon{c9, rest}}}}}}}}}, valid), H.hex_u32.false_true(valid))
