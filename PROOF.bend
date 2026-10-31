import Base
import ./LAWS.bend as Laws
import ./hexdigits.bend as H
import ./binary.bend as B

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

# The decode law directly enumerates the possible character/value cases.
def EnumeratedDecodeSpec(+digit: H.HexDigitChar) -> Type:
  c = H.HexDigitChar.char(digit)
  v = Word.to_nat(4n, H.decode(digit))
  ({c == '0' : Char} & {v == 0n : Nat}) |
  ({c == '1' : Char} & {v == 1n : Nat}) |
  ({c == '2' : Char} & {v == 2n : Nat}) |
  ({c == '3' : Char} & {v == 3n : Nat}) |
  ({c == '4' : Char} & {v == 4n : Nat}) |
  ({c == '5' : Char} & {v == 5n : Nat}) |
  ({c == '6' : Char} & {v == 6n : Nat}) |
  ({c == '7' : Char} & {v == 7n : Nat}) |
  ({c == '8' : Char} & {v == 8n : Nat}) |
  ({c == '9' : Char} & {v == 9n : Nat}) |
  ({c == 'A' : Char} & {v == 10n : Nat}) |
  ({c == 'B' : Char} & {v == 11n : Nat}) |
  ({c == 'C' : Char} & {v == 12n : Nat}) |
  ({c == 'D' : Char} & {v == 13n : Nat}) |
  ({c == 'E' : Char} & {v == 14n : Nat}) |
  ({c == 'F' : Char} & {v == 15n : Nat})

# Bit-level case analysis proves the enumerated decode law.
def DecodeSpec(+c: Char, +valid: {H.is_hex_digit(c) == True{} : Bool}) -> Type:
  EnumeratedDecodeSpec(H.HexDigitChar{c, valid})

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
          Inl{({==}, {==})}
        case False{} True{} True{} False{} False{} False{} True{}:
          Inr{Inl{({==}, {==})}}
        case False{} True{} True{} False{} False{} True{} False{}:
          Inr{Inr{Inl{({==}, {==})}}}
        case False{} True{} True{} False{} False{} True{} True{}:
          Inr{Inr{Inr{Inl{({==}, {==})}}}}
        case False{} True{} True{} False{} True{} False{} False{}:
          Inr{Inr{Inr{Inr{Inl{({==}, {==})}}}}}
        case False{} True{} True{} False{} True{} False{} True{}:
          Inr{Inr{Inr{Inr{Inr{Inl{({==}, {==})}}}}}}
        case False{} True{} True{} False{} True{} True{} False{}:
          Inr{Inr{Inr{Inr{Inr{Inr{Inl{({==}, {==})}}}}}}}
        case False{} True{} True{} False{} True{} True{} True{}:
          Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inl{({==}, {==})}}}}}}}}
        case False{} True{} True{} True{} False{} False{} False{}:
          Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inl{({==}, {==})}}}}}}}}}
        case False{} True{} True{} True{} False{} False{} True{}:
          Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inl{({==}, {==})}}}}}}}}}}
        case False{} True{} True{} True{} False{} True{} _:
          Empty.absurd(DecodeSpec(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0), valid), H.hex_u32.false_true(valid))
        case False{} True{} True{} True{} True{} _ _:
          Empty.absurd(DecodeSpec(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0), valid), H.hex_u32.false_true(valid))
        case True{} False{} False{} False{} False{} False{} False{}:
          Empty.absurd(DecodeSpec(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0), valid), H.hex_u32.false_true(valid))
        case True{} False{} False{} False{} False{} False{} True{}:
          Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inl{({==}, {==})}}}}}}}}}}}
        case True{} False{} False{} False{} False{} True{} False{}:
          Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inl{({==}, {==})}}}}}}}}}}}}
        case True{} False{} False{} False{} False{} True{} True{}:
          Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inl{({==}, {==})}}}}}}}}}}}}}
        case True{} False{} False{} False{} True{} False{} False{}:
          Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inl{({==}, {==})}}}}}}}}}}}}}}
        case True{} False{} False{} False{} True{} False{} True{}:
          Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inl{({==}, {==})}}}}}}}}}}}}}}}
        case True{} False{} False{} False{} True{} True{} False{}:
          Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{Inr{({==}, {==})}}}}}}}}}}}}}}}
        case True{} False{} False{} False{} True{} True{} True{}:
          Empty.absurd(DecodeSpec(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0), valid), H.hex_u32.false_true(valid))
        case True{} False{} False{} True{} _ _ _:
          Empty.absurd(DecodeSpec(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0), valid), H.hex_u32.false_true(valid))
        case True{} False{} True{} _ _ _ _:
          Empty.absurd(DecodeSpec(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0), valid), H.hex_u32.false_true(valid))
        case True{} True{} _ _ _ _ _:
          Empty.absurd(DecodeSpec(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0), valid), H.hex_u32.false_true(valid))

def Laws.decode(digit):
  match digit:
    case H.HexDigitChar{Chr{U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, valid}:
      decode_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0, valid)

def Laws.is_valid_hex_u32_input(s):
  {==}

def HexU32Spec(+s: String, valid: {H.is_valid_hex_u32(s) == True{} : Bool}) -> Type:
  &digits: +List<H.HexDigitChar> ->
  {List.length(&2, H.HexDigitChar, digits) == 8n : Nat} &
  {s == Laws.digits_to_string(digits) : String} &
  {H.hex_u32(s, valid) == Laws.nibble_list_value(Laws.digits_to_nibbles(digits)) : U32}

def hex_u32_complete(
  +c1: Char, +c2: Char, +c3: Char, +c4: Char, +c5: Char, +c6: Char, +c7: Char, +c8: Char,
  valid: {H.is_valid_hex_u32(SCon{c1, SCon{c2, SCon{c3, SCon{c4, SCon{c5, SCon{c6, SCon{c7, SCon{c8, SNil{}}}}}}}}}) == True{} : Bool},
  proofs: {H.is_hex_digit(c1) == True{} : Bool} & {H.is_hex_digit(c2) == True{} : Bool} & {H.is_hex_digit(c3) == True{} : Bool} & {H.is_hex_digit(c4) == True{} : Bool} & {H.is_hex_digit(c5) == True{} : Bool} & {H.is_hex_digit(c6) == True{} : Bool} & {H.is_hex_digit(c7) == True{} : Bool} & {H.is_hex_digit(c8) == True{} : Bool}
) -> HexU32Spec(SCon{c1, SCon{c2, SCon{c3, SCon{c4, SCon{c5, SCon{c6, SCon{c7, SCon{c8, SNil{}}}}}}}}}, valid):
  match proofs:
    case (p1, p2, p3, p4, p5, p6, p7, p8):
      ([H.HexDigitChar{c1, p1}, H.HexDigitChar{c2, p2}, H.HexDigitChar{c3, p3}, H.HexDigitChar{c4, p4}, H.HexDigitChar{c5, p5}, H.HexDigitChar{c6, p6}, H.HexDigitChar{c7, p7}, H.HexDigitChar{c8, p8}],
       ({==}, {==}, {==}))

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

def Laws.example_zero():
  {==}

# Binary input validation and byte conversion.
def binary_membership(+a: Bool, +b: Bool) ->
  {Bool.or(a, b) == List.any.if(u => List.any.if(u => False{}, b), a) : Bool}:
  match a b:
    case False{} False{}: {==}
    case False{} True{}: {==}
    case True{} _: {==}

def Laws.is_binary_digit(c):
  binary_membership(Char.is_eq('0', c), Char.is_eq('1', c))

def Laws.is_valid_binary_byte_input(s):
  {==}

# A valid binary character is recovered from its decoded bit.
def BinaryCharSpec(+c: Char, valid: {B.is_binary_digit(c) == True{} : Bool}) -> Type:
  {c == B.bit_to_char(B.char_to_bit(c)) : Char}

law binary_char_bits:
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
  for valid: {B.is_binary_digit(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0)) == True{} : Bool}
  BinaryCharSpec(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0), valid)

def binary_char_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0, valid):
  match b31 b30 b29 b28 b27 b26 b25 b24 b23 b22 b21 b20 b19 b18 b17 b16 b15 b14 b13 b12 b11 b10 b9 b8 b7 b6 b5 b4 b3 b2 b1:
    case True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(BinaryCharSpec(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0), valid), H.hex_u32.false_true(valid))
    case False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(BinaryCharSpec(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0), valid), H.hex_u32.false_true(valid))
    case False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(BinaryCharSpec(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0), valid), H.hex_u32.false_true(valid))
    case False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(BinaryCharSpec(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0), valid), H.hex_u32.false_true(valid))
    case False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(BinaryCharSpec(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0), valid), H.hex_u32.false_true(valid))
    case False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(BinaryCharSpec(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0), valid), H.hex_u32.false_true(valid))
    case False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(BinaryCharSpec(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0), valid), H.hex_u32.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(BinaryCharSpec(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0), valid), H.hex_u32.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(BinaryCharSpec(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0), valid), H.hex_u32.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(BinaryCharSpec(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0), valid), H.hex_u32.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(BinaryCharSpec(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0), valid), H.hex_u32.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(BinaryCharSpec(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0), valid), H.hex_u32.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(BinaryCharSpec(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0), valid), H.hex_u32.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(BinaryCharSpec(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0), valid), H.hex_u32.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(BinaryCharSpec(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0), valid), H.hex_u32.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(BinaryCharSpec(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0), valid), H.hex_u32.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(BinaryCharSpec(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0), valid), H.hex_u32.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(BinaryCharSpec(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0), valid), H.hex_u32.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(BinaryCharSpec(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0), valid), H.hex_u32.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(BinaryCharSpec(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0), valid), H.hex_u32.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(BinaryCharSpec(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0), valid), H.hex_u32.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _:
      Empty.absurd(BinaryCharSpec(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0), valid), H.hex_u32.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _:
      Empty.absurd(BinaryCharSpec(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0), valid), H.hex_u32.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _:
      Empty.absurd(BinaryCharSpec(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0), valid), H.hex_u32.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _:
      Empty.absurd(BinaryCharSpec(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0), valid), H.hex_u32.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _:
      Empty.absurd(BinaryCharSpec(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0), valid), H.hex_u32.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} _ _ _ _:
      Empty.absurd(BinaryCharSpec(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0), valid), H.hex_u32.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} False{} _ _ _:
      Empty.absurd(BinaryCharSpec(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0), valid), H.hex_u32.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} True{} True{} _ _:
      Empty.absurd(BinaryCharSpec(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0), valid), H.hex_u32.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} True{} False{} True{} _:
      Empty.absurd(BinaryCharSpec(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0), valid), H.hex_u32.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} True{} False{} False{} True{}:
      Empty.absurd(BinaryCharSpec(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0), valid), H.hex_u32.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} True{} False{} False{} False{}:
      match b0:
        case False{}: {==}
        case True{}: {==}

def binary_char_roundtrip(+c: Char, valid: {B.is_binary_digit(c) == True{} : Bool}) -> BinaryCharSpec(c, valid):
  match c:
    case Chr{U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      binary_char_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0, valid)

def eight_bits_bound(+b1: Bool, +b2: Bool, +b3: Bool, +b4: Bool, +b5: Bool, +b6: Bool, +b7: Bool, +b8: Bool) -> {U32.is_le(Laws.bit_list_value([b1, b2, b3, b4, b5, b6, b7, b8]), 255) == True{} : Bool}:
  match b1 b2 b3 b4 b5 b6 b7 b8:
    case False{} False{} False{} False{} False{} False{} False{} False{}: {==}
    case False{} False{} False{} False{} False{} False{} False{} True{}: {==}
    case False{} False{} False{} False{} False{} False{} True{} False{}: {==}
    case False{} False{} False{} False{} False{} False{} True{} True{}: {==}
    case False{} False{} False{} False{} False{} True{} False{} False{}: {==}
    case False{} False{} False{} False{} False{} True{} False{} True{}: {==}
    case False{} False{} False{} False{} False{} True{} True{} False{}: {==}
    case False{} False{} False{} False{} False{} True{} True{} True{}: {==}
    case False{} False{} False{} False{} True{} False{} False{} False{}: {==}
    case False{} False{} False{} False{} True{} False{} False{} True{}: {==}
    case False{} False{} False{} False{} True{} False{} True{} False{}: {==}
    case False{} False{} False{} False{} True{} False{} True{} True{}: {==}
    case False{} False{} False{} False{} True{} True{} False{} False{}: {==}
    case False{} False{} False{} False{} True{} True{} False{} True{}: {==}
    case False{} False{} False{} False{} True{} True{} True{} False{}: {==}
    case False{} False{} False{} False{} True{} True{} True{} True{}: {==}
    case False{} False{} False{} True{} False{} False{} False{} False{}: {==}
    case False{} False{} False{} True{} False{} False{} False{} True{}: {==}
    case False{} False{} False{} True{} False{} False{} True{} False{}: {==}
    case False{} False{} False{} True{} False{} False{} True{} True{}: {==}
    case False{} False{} False{} True{} False{} True{} False{} False{}: {==}
    case False{} False{} False{} True{} False{} True{} False{} True{}: {==}
    case False{} False{} False{} True{} False{} True{} True{} False{}: {==}
    case False{} False{} False{} True{} False{} True{} True{} True{}: {==}
    case False{} False{} False{} True{} True{} False{} False{} False{}: {==}
    case False{} False{} False{} True{} True{} False{} False{} True{}: {==}
    case False{} False{} False{} True{} True{} False{} True{} False{}: {==}
    case False{} False{} False{} True{} True{} False{} True{} True{}: {==}
    case False{} False{} False{} True{} True{} True{} False{} False{}: {==}
    case False{} False{} False{} True{} True{} True{} False{} True{}: {==}
    case False{} False{} False{} True{} True{} True{} True{} False{}: {==}
    case False{} False{} False{} True{} True{} True{} True{} True{}: {==}
    case False{} False{} True{} False{} False{} False{} False{} False{}: {==}
    case False{} False{} True{} False{} False{} False{} False{} True{}: {==}
    case False{} False{} True{} False{} False{} False{} True{} False{}: {==}
    case False{} False{} True{} False{} False{} False{} True{} True{}: {==}
    case False{} False{} True{} False{} False{} True{} False{} False{}: {==}
    case False{} False{} True{} False{} False{} True{} False{} True{}: {==}
    case False{} False{} True{} False{} False{} True{} True{} False{}: {==}
    case False{} False{} True{} False{} False{} True{} True{} True{}: {==}
    case False{} False{} True{} False{} True{} False{} False{} False{}: {==}
    case False{} False{} True{} False{} True{} False{} False{} True{}: {==}
    case False{} False{} True{} False{} True{} False{} True{} False{}: {==}
    case False{} False{} True{} False{} True{} False{} True{} True{}: {==}
    case False{} False{} True{} False{} True{} True{} False{} False{}: {==}
    case False{} False{} True{} False{} True{} True{} False{} True{}: {==}
    case False{} False{} True{} False{} True{} True{} True{} False{}: {==}
    case False{} False{} True{} False{} True{} True{} True{} True{}: {==}
    case False{} False{} True{} True{} False{} False{} False{} False{}: {==}
    case False{} False{} True{} True{} False{} False{} False{} True{}: {==}
    case False{} False{} True{} True{} False{} False{} True{} False{}: {==}
    case False{} False{} True{} True{} False{} False{} True{} True{}: {==}
    case False{} False{} True{} True{} False{} True{} False{} False{}: {==}
    case False{} False{} True{} True{} False{} True{} False{} True{}: {==}
    case False{} False{} True{} True{} False{} True{} True{} False{}: {==}
    case False{} False{} True{} True{} False{} True{} True{} True{}: {==}
    case False{} False{} True{} True{} True{} False{} False{} False{}: {==}
    case False{} False{} True{} True{} True{} False{} False{} True{}: {==}
    case False{} False{} True{} True{} True{} False{} True{} False{}: {==}
    case False{} False{} True{} True{} True{} False{} True{} True{}: {==}
    case False{} False{} True{} True{} True{} True{} False{} False{}: {==}
    case False{} False{} True{} True{} True{} True{} False{} True{}: {==}
    case False{} False{} True{} True{} True{} True{} True{} False{}: {==}
    case False{} False{} True{} True{} True{} True{} True{} True{}: {==}
    case False{} True{} False{} False{} False{} False{} False{} False{}: {==}
    case False{} True{} False{} False{} False{} False{} False{} True{}: {==}
    case False{} True{} False{} False{} False{} False{} True{} False{}: {==}
    case False{} True{} False{} False{} False{} False{} True{} True{}: {==}
    case False{} True{} False{} False{} False{} True{} False{} False{}: {==}
    case False{} True{} False{} False{} False{} True{} False{} True{}: {==}
    case False{} True{} False{} False{} False{} True{} True{} False{}: {==}
    case False{} True{} False{} False{} False{} True{} True{} True{}: {==}
    case False{} True{} False{} False{} True{} False{} False{} False{}: {==}
    case False{} True{} False{} False{} True{} False{} False{} True{}: {==}
    case False{} True{} False{} False{} True{} False{} True{} False{}: {==}
    case False{} True{} False{} False{} True{} False{} True{} True{}: {==}
    case False{} True{} False{} False{} True{} True{} False{} False{}: {==}
    case False{} True{} False{} False{} True{} True{} False{} True{}: {==}
    case False{} True{} False{} False{} True{} True{} True{} False{}: {==}
    case False{} True{} False{} False{} True{} True{} True{} True{}: {==}
    case False{} True{} False{} True{} False{} False{} False{} False{}: {==}
    case False{} True{} False{} True{} False{} False{} False{} True{}: {==}
    case False{} True{} False{} True{} False{} False{} True{} False{}: {==}
    case False{} True{} False{} True{} False{} False{} True{} True{}: {==}
    case False{} True{} False{} True{} False{} True{} False{} False{}: {==}
    case False{} True{} False{} True{} False{} True{} False{} True{}: {==}
    case False{} True{} False{} True{} False{} True{} True{} False{}: {==}
    case False{} True{} False{} True{} False{} True{} True{} True{}: {==}
    case False{} True{} False{} True{} True{} False{} False{} False{}: {==}
    case False{} True{} False{} True{} True{} False{} False{} True{}: {==}
    case False{} True{} False{} True{} True{} False{} True{} False{}: {==}
    case False{} True{} False{} True{} True{} False{} True{} True{}: {==}
    case False{} True{} False{} True{} True{} True{} False{} False{}: {==}
    case False{} True{} False{} True{} True{} True{} False{} True{}: {==}
    case False{} True{} False{} True{} True{} True{} True{} False{}: {==}
    case False{} True{} False{} True{} True{} True{} True{} True{}: {==}
    case False{} True{} True{} False{} False{} False{} False{} False{}: {==}
    case False{} True{} True{} False{} False{} False{} False{} True{}: {==}
    case False{} True{} True{} False{} False{} False{} True{} False{}: {==}
    case False{} True{} True{} False{} False{} False{} True{} True{}: {==}
    case False{} True{} True{} False{} False{} True{} False{} False{}: {==}
    case False{} True{} True{} False{} False{} True{} False{} True{}: {==}
    case False{} True{} True{} False{} False{} True{} True{} False{}: {==}
    case False{} True{} True{} False{} False{} True{} True{} True{}: {==}
    case False{} True{} True{} False{} True{} False{} False{} False{}: {==}
    case False{} True{} True{} False{} True{} False{} False{} True{}: {==}
    case False{} True{} True{} False{} True{} False{} True{} False{}: {==}
    case False{} True{} True{} False{} True{} False{} True{} True{}: {==}
    case False{} True{} True{} False{} True{} True{} False{} False{}: {==}
    case False{} True{} True{} False{} True{} True{} False{} True{}: {==}
    case False{} True{} True{} False{} True{} True{} True{} False{}: {==}
    case False{} True{} True{} False{} True{} True{} True{} True{}: {==}
    case False{} True{} True{} True{} False{} False{} False{} False{}: {==}
    case False{} True{} True{} True{} False{} False{} False{} True{}: {==}
    case False{} True{} True{} True{} False{} False{} True{} False{}: {==}
    case False{} True{} True{} True{} False{} False{} True{} True{}: {==}
    case False{} True{} True{} True{} False{} True{} False{} False{}: {==}
    case False{} True{} True{} True{} False{} True{} False{} True{}: {==}
    case False{} True{} True{} True{} False{} True{} True{} False{}: {==}
    case False{} True{} True{} True{} False{} True{} True{} True{}: {==}
    case False{} True{} True{} True{} True{} False{} False{} False{}: {==}
    case False{} True{} True{} True{} True{} False{} False{} True{}: {==}
    case False{} True{} True{} True{} True{} False{} True{} False{}: {==}
    case False{} True{} True{} True{} True{} False{} True{} True{}: {==}
    case False{} True{} True{} True{} True{} True{} False{} False{}: {==}
    case False{} True{} True{} True{} True{} True{} False{} True{}: {==}
    case False{} True{} True{} True{} True{} True{} True{} False{}: {==}
    case False{} True{} True{} True{} True{} True{} True{} True{}: {==}
    case True{} False{} False{} False{} False{} False{} False{} False{}: {==}
    case True{} False{} False{} False{} False{} False{} False{} True{}: {==}
    case True{} False{} False{} False{} False{} False{} True{} False{}: {==}
    case True{} False{} False{} False{} False{} False{} True{} True{}: {==}
    case True{} False{} False{} False{} False{} True{} False{} False{}: {==}
    case True{} False{} False{} False{} False{} True{} False{} True{}: {==}
    case True{} False{} False{} False{} False{} True{} True{} False{}: {==}
    case True{} False{} False{} False{} False{} True{} True{} True{}: {==}
    case True{} False{} False{} False{} True{} False{} False{} False{}: {==}
    case True{} False{} False{} False{} True{} False{} False{} True{}: {==}
    case True{} False{} False{} False{} True{} False{} True{} False{}: {==}
    case True{} False{} False{} False{} True{} False{} True{} True{}: {==}
    case True{} False{} False{} False{} True{} True{} False{} False{}: {==}
    case True{} False{} False{} False{} True{} True{} False{} True{}: {==}
    case True{} False{} False{} False{} True{} True{} True{} False{}: {==}
    case True{} False{} False{} False{} True{} True{} True{} True{}: {==}
    case True{} False{} False{} True{} False{} False{} False{} False{}: {==}
    case True{} False{} False{} True{} False{} False{} False{} True{}: {==}
    case True{} False{} False{} True{} False{} False{} True{} False{}: {==}
    case True{} False{} False{} True{} False{} False{} True{} True{}: {==}
    case True{} False{} False{} True{} False{} True{} False{} False{}: {==}
    case True{} False{} False{} True{} False{} True{} False{} True{}: {==}
    case True{} False{} False{} True{} False{} True{} True{} False{}: {==}
    case True{} False{} False{} True{} False{} True{} True{} True{}: {==}
    case True{} False{} False{} True{} True{} False{} False{} False{}: {==}
    case True{} False{} False{} True{} True{} False{} False{} True{}: {==}
    case True{} False{} False{} True{} True{} False{} True{} False{}: {==}
    case True{} False{} False{} True{} True{} False{} True{} True{}: {==}
    case True{} False{} False{} True{} True{} True{} False{} False{}: {==}
    case True{} False{} False{} True{} True{} True{} False{} True{}: {==}
    case True{} False{} False{} True{} True{} True{} True{} False{}: {==}
    case True{} False{} False{} True{} True{} True{} True{} True{}: {==}
    case True{} False{} True{} False{} False{} False{} False{} False{}: {==}
    case True{} False{} True{} False{} False{} False{} False{} True{}: {==}
    case True{} False{} True{} False{} False{} False{} True{} False{}: {==}
    case True{} False{} True{} False{} False{} False{} True{} True{}: {==}
    case True{} False{} True{} False{} False{} True{} False{} False{}: {==}
    case True{} False{} True{} False{} False{} True{} False{} True{}: {==}
    case True{} False{} True{} False{} False{} True{} True{} False{}: {==}
    case True{} False{} True{} False{} False{} True{} True{} True{}: {==}
    case True{} False{} True{} False{} True{} False{} False{} False{}: {==}
    case True{} False{} True{} False{} True{} False{} False{} True{}: {==}
    case True{} False{} True{} False{} True{} False{} True{} False{}: {==}
    case True{} False{} True{} False{} True{} False{} True{} True{}: {==}
    case True{} False{} True{} False{} True{} True{} False{} False{}: {==}
    case True{} False{} True{} False{} True{} True{} False{} True{}: {==}
    case True{} False{} True{} False{} True{} True{} True{} False{}: {==}
    case True{} False{} True{} False{} True{} True{} True{} True{}: {==}
    case True{} False{} True{} True{} False{} False{} False{} False{}: {==}
    case True{} False{} True{} True{} False{} False{} False{} True{}: {==}
    case True{} False{} True{} True{} False{} False{} True{} False{}: {==}
    case True{} False{} True{} True{} False{} False{} True{} True{}: {==}
    case True{} False{} True{} True{} False{} True{} False{} False{}: {==}
    case True{} False{} True{} True{} False{} True{} False{} True{}: {==}
    case True{} False{} True{} True{} False{} True{} True{} False{}: {==}
    case True{} False{} True{} True{} False{} True{} True{} True{}: {==}
    case True{} False{} True{} True{} True{} False{} False{} False{}: {==}
    case True{} False{} True{} True{} True{} False{} False{} True{}: {==}
    case True{} False{} True{} True{} True{} False{} True{} False{}: {==}
    case True{} False{} True{} True{} True{} False{} True{} True{}: {==}
    case True{} False{} True{} True{} True{} True{} False{} False{}: {==}
    case True{} False{} True{} True{} True{} True{} False{} True{}: {==}
    case True{} False{} True{} True{} True{} True{} True{} False{}: {==}
    case True{} False{} True{} True{} True{} True{} True{} True{}: {==}
    case True{} True{} False{} False{} False{} False{} False{} False{}: {==}
    case True{} True{} False{} False{} False{} False{} False{} True{}: {==}
    case True{} True{} False{} False{} False{} False{} True{} False{}: {==}
    case True{} True{} False{} False{} False{} False{} True{} True{}: {==}
    case True{} True{} False{} False{} False{} True{} False{} False{}: {==}
    case True{} True{} False{} False{} False{} True{} False{} True{}: {==}
    case True{} True{} False{} False{} False{} True{} True{} False{}: {==}
    case True{} True{} False{} False{} False{} True{} True{} True{}: {==}
    case True{} True{} False{} False{} True{} False{} False{} False{}: {==}
    case True{} True{} False{} False{} True{} False{} False{} True{}: {==}
    case True{} True{} False{} False{} True{} False{} True{} False{}: {==}
    case True{} True{} False{} False{} True{} False{} True{} True{}: {==}
    case True{} True{} False{} False{} True{} True{} False{} False{}: {==}
    case True{} True{} False{} False{} True{} True{} False{} True{}: {==}
    case True{} True{} False{} False{} True{} True{} True{} False{}: {==}
    case True{} True{} False{} False{} True{} True{} True{} True{}: {==}
    case True{} True{} False{} True{} False{} False{} False{} False{}: {==}
    case True{} True{} False{} True{} False{} False{} False{} True{}: {==}
    case True{} True{} False{} True{} False{} False{} True{} False{}: {==}
    case True{} True{} False{} True{} False{} False{} True{} True{}: {==}
    case True{} True{} False{} True{} False{} True{} False{} False{}: {==}
    case True{} True{} False{} True{} False{} True{} False{} True{}: {==}
    case True{} True{} False{} True{} False{} True{} True{} False{}: {==}
    case True{} True{} False{} True{} False{} True{} True{} True{}: {==}
    case True{} True{} False{} True{} True{} False{} False{} False{}: {==}
    case True{} True{} False{} True{} True{} False{} False{} True{}: {==}
    case True{} True{} False{} True{} True{} False{} True{} False{}: {==}
    case True{} True{} False{} True{} True{} False{} True{} True{}: {==}
    case True{} True{} False{} True{} True{} True{} False{} False{}: {==}
    case True{} True{} False{} True{} True{} True{} False{} True{}: {==}
    case True{} True{} False{} True{} True{} True{} True{} False{}: {==}
    case True{} True{} False{} True{} True{} True{} True{} True{}: {==}
    case True{} True{} True{} False{} False{} False{} False{} False{}: {==}
    case True{} True{} True{} False{} False{} False{} False{} True{}: {==}
    case True{} True{} True{} False{} False{} False{} True{} False{}: {==}
    case True{} True{} True{} False{} False{} False{} True{} True{}: {==}
    case True{} True{} True{} False{} False{} True{} False{} False{}: {==}
    case True{} True{} True{} False{} False{} True{} False{} True{}: {==}
    case True{} True{} True{} False{} False{} True{} True{} False{}: {==}
    case True{} True{} True{} False{} False{} True{} True{} True{}: {==}
    case True{} True{} True{} False{} True{} False{} False{} False{}: {==}
    case True{} True{} True{} False{} True{} False{} False{} True{}: {==}
    case True{} True{} True{} False{} True{} False{} True{} False{}: {==}
    case True{} True{} True{} False{} True{} False{} True{} True{}: {==}
    case True{} True{} True{} False{} True{} True{} False{} False{}: {==}
    case True{} True{} True{} False{} True{} True{} False{} True{}: {==}
    case True{} True{} True{} False{} True{} True{} True{} False{}: {==}
    case True{} True{} True{} False{} True{} True{} True{} True{}: {==}
    case True{} True{} True{} True{} False{} False{} False{} False{}: {==}
    case True{} True{} True{} True{} False{} False{} False{} True{}: {==}
    case True{} True{} True{} True{} False{} False{} True{} False{}: {==}
    case True{} True{} True{} True{} False{} False{} True{} True{}: {==}
    case True{} True{} True{} True{} False{} True{} False{} False{}: {==}
    case True{} True{} True{} True{} False{} True{} False{} True{}: {==}
    case True{} True{} True{} True{} False{} True{} True{} False{}: {==}
    case True{} True{} True{} True{} False{} True{} True{} True{}: {==}
    case True{} True{} True{} True{} True{} False{} False{} False{}: {==}
    case True{} True{} True{} True{} True{} False{} False{} True{}: {==}
    case True{} True{} True{} True{} True{} False{} True{} False{}: {==}
    case True{} True{} True{} True{} True{} False{} True{} True{}: {==}
    case True{} True{} True{} True{} True{} True{} False{} False{}: {==}
    case True{} True{} True{} True{} True{} True{} False{} True{}: {==}
    case True{} True{} True{} True{} True{} True{} True{} False{}: {==}
    case True{} True{} True{} True{} True{} True{} True{} True{}: {==}

def binary_byte.digit_proofs(
  +c1: Char, +c2: Char, +c3: Char, +c4: Char,
  +c5: Char, +c6: Char, +c7: Char, +c8: Char,
  +valid: {B.is_valid_binary_byte(SCon{c1, SCon{c2, SCon{c3, SCon{c4, SCon{c5, SCon{c6, SCon{c7, SCon{c8, SNil{}}}}}}}}}) == True{} : Bool}
) -> (
  {B.is_binary_digit(c1) == True{} : Bool} &
  {B.is_binary_digit(c2) == True{} : Bool} &
  {B.is_binary_digit(c3) == True{} : Bool} &
  {B.is_binary_digit(c4) == True{} : Bool} &
  {B.is_binary_digit(c5) == True{} : Bool} &
  {B.is_binary_digit(c6) == True{} : Bool} &
  {B.is_binary_digit(c7) == True{} : Bool} &
  {B.is_binary_digit(c8) == True{} : Bool}
):
  p1 = H.hex_u32.head_true(B.is_binary_digit(c1), List.all(~&2, ~Char, ~(c => B.is_binary_digit(c)), [c2, c3, c4, c5, c6, c7, c8]), valid)
  +e1 = H.hex_u32.tail_true(B.is_binary_digit(c1), List.all(~&2, ~Char, ~(c => B.is_binary_digit(c)), [c2, c3, c4, c5, c6, c7, c8]), valid)
  p2 = H.hex_u32.head_true(B.is_binary_digit(c2), List.all(~&2, ~Char, ~(c => B.is_binary_digit(c)), [c3, c4, c5, c6, c7, c8]), e1)
  +e2 = H.hex_u32.tail_true(B.is_binary_digit(c2), List.all(~&2, ~Char, ~(c => B.is_binary_digit(c)), [c3, c4, c5, c6, c7, c8]), e1)
  p3 = H.hex_u32.head_true(B.is_binary_digit(c3), List.all(~&2, ~Char, ~(c => B.is_binary_digit(c)), [c4, c5, c6, c7, c8]), e2)
  +e3 = H.hex_u32.tail_true(B.is_binary_digit(c3), List.all(~&2, ~Char, ~(c => B.is_binary_digit(c)), [c4, c5, c6, c7, c8]), e2)
  p4 = H.hex_u32.head_true(B.is_binary_digit(c4), List.all(~&2, ~Char, ~(c => B.is_binary_digit(c)), [c5, c6, c7, c8]), e3)
  +e4 = H.hex_u32.tail_true(B.is_binary_digit(c4), List.all(~&2, ~Char, ~(c => B.is_binary_digit(c)), [c5, c6, c7, c8]), e3)
  p5 = H.hex_u32.head_true(B.is_binary_digit(c5), List.all(~&2, ~Char, ~(c => B.is_binary_digit(c)), [c6, c7, c8]), e4)
  +e5 = H.hex_u32.tail_true(B.is_binary_digit(c5), List.all(~&2, ~Char, ~(c => B.is_binary_digit(c)), [c6, c7, c8]), e4)
  p6 = H.hex_u32.head_true(B.is_binary_digit(c6), List.all(~&2, ~Char, ~(c => B.is_binary_digit(c)), [c7, c8]), e5)
  +e6 = H.hex_u32.tail_true(B.is_binary_digit(c6), List.all(~&2, ~Char, ~(c => B.is_binary_digit(c)), [c7, c8]), e5)
  p7 = H.hex_u32.head_true(B.is_binary_digit(c7), List.all(~&2, ~Char, ~(c => B.is_binary_digit(c)), [c8]), e6)
  +e7 = H.hex_u32.tail_true(B.is_binary_digit(c7), List.all(~&2, ~Char, ~(c => B.is_binary_digit(c)), [c8]), e6)
  p8 = H.hex_u32.head_true(B.is_binary_digit(c8), List.all(~&2, ~Char, ~(c => B.is_binary_digit(c)), []), e7)
  (p1, p2, p3, p4, p5, p6, p7, p8)

def BinaryByteSpec(+s: String, valid: {B.is_valid_binary_byte(s) == True{} : Bool}) -> Type:
  &bits: +List<Bool> ->
  {List.length(&2, Bool, bits) == 8n : Nat} &
  {s == Laws.bits_to_string(bits) : String} &
  {B.binary_byte(s, valid) == Laws.bit_list_value(bits) : U32} &
  {U32.is_le(B.binary_byte(s, valid), 255) == True{} : Bool}

def binary_byte.spells(
  +c1: Char, +c2: Char, +c3: Char, +c4: Char, +c5: Char, +c6: Char, +c7: Char, +c8: Char,
  proofs: {B.is_binary_digit(c1) == True{} : Bool} & {B.is_binary_digit(c2) == True{} : Bool} & {B.is_binary_digit(c3) == True{} : Bool} & {B.is_binary_digit(c4) == True{} : Bool} & {B.is_binary_digit(c5) == True{} : Bool} & {B.is_binary_digit(c6) == True{} : Bool} & {B.is_binary_digit(c7) == True{} : Bool} & {B.is_binary_digit(c8) == True{} : Bool}
) -> {SCon{c1, SCon{c2, SCon{c3, SCon{c4, SCon{c5, SCon{c6, SCon{c7, SCon{c8, SNil{}}}}}}}}} == Laws.bits_to_string([B.char_to_bit(c1), B.char_to_bit(c2), B.char_to_bit(c3), B.char_to_bit(c4), B.char_to_bit(c5), B.char_to_bit(c6), B.char_to_bit(c7), B.char_to_bit(c8)]) : String}:
  match proofs:
    case (p1, p2, p3, p4, p5, p6, p7, p8):
      e8 = binary_char_roundtrip(c8, p8)
      %e8 : {SCon{c1, SCon{c2, SCon{c3, SCon{c4, SCon{c5, SCon{c6, SCon{c7, SCon{c8, SNil{}}}}}}}}} == SCon{B.bit_to_char(B.char_to_bit(c1)), SCon{B.bit_to_char(B.char_to_bit(c2)), SCon{B.bit_to_char(B.char_to_bit(c3)), SCon{B.bit_to_char(B.char_to_bit(c4)), SCon{B.bit_to_char(B.char_to_bit(c5)), SCon{B.bit_to_char(B.char_to_bit(c6)), SCon{B.bit_to_char(B.char_to_bit(c7)), SCon{_, SNil{}}}}}}}}} : String}
      e7 = binary_char_roundtrip(c7, p7)
      %e7 : {SCon{c1, SCon{c2, SCon{c3, SCon{c4, SCon{c5, SCon{c6, SCon{c7, SCon{c8, SNil{}}}}}}}}} == SCon{B.bit_to_char(B.char_to_bit(c1)), SCon{B.bit_to_char(B.char_to_bit(c2)), SCon{B.bit_to_char(B.char_to_bit(c3)), SCon{B.bit_to_char(B.char_to_bit(c4)), SCon{B.bit_to_char(B.char_to_bit(c5)), SCon{B.bit_to_char(B.char_to_bit(c6)), SCon{_, SCon{c8, SNil{}}}}}}}}} : String}
      e6 = binary_char_roundtrip(c6, p6)
      %e6 : {SCon{c1, SCon{c2, SCon{c3, SCon{c4, SCon{c5, SCon{c6, SCon{c7, SCon{c8, SNil{}}}}}}}}} == SCon{B.bit_to_char(B.char_to_bit(c1)), SCon{B.bit_to_char(B.char_to_bit(c2)), SCon{B.bit_to_char(B.char_to_bit(c3)), SCon{B.bit_to_char(B.char_to_bit(c4)), SCon{B.bit_to_char(B.char_to_bit(c5)), SCon{_, SCon{c7, SCon{c8, SNil{}}}}}}}}} : String}
      e5 = binary_char_roundtrip(c5, p5)
      %e5 : {SCon{c1, SCon{c2, SCon{c3, SCon{c4, SCon{c5, SCon{c6, SCon{c7, SCon{c8, SNil{}}}}}}}}} == SCon{B.bit_to_char(B.char_to_bit(c1)), SCon{B.bit_to_char(B.char_to_bit(c2)), SCon{B.bit_to_char(B.char_to_bit(c3)), SCon{B.bit_to_char(B.char_to_bit(c4)), SCon{_, SCon{c6, SCon{c7, SCon{c8, SNil{}}}}}}}}} : String}
      e4 = binary_char_roundtrip(c4, p4)
      %e4 : {SCon{c1, SCon{c2, SCon{c3, SCon{c4, SCon{c5, SCon{c6, SCon{c7, SCon{c8, SNil{}}}}}}}}} == SCon{B.bit_to_char(B.char_to_bit(c1)), SCon{B.bit_to_char(B.char_to_bit(c2)), SCon{B.bit_to_char(B.char_to_bit(c3)), SCon{_, SCon{c5, SCon{c6, SCon{c7, SCon{c8, SNil{}}}}}}}}} : String}
      e3 = binary_char_roundtrip(c3, p3)
      %e3 : {SCon{c1, SCon{c2, SCon{c3, SCon{c4, SCon{c5, SCon{c6, SCon{c7, SCon{c8, SNil{}}}}}}}}} == SCon{B.bit_to_char(B.char_to_bit(c1)), SCon{B.bit_to_char(B.char_to_bit(c2)), SCon{_, SCon{c4, SCon{c5, SCon{c6, SCon{c7, SCon{c8, SNil{}}}}}}}}} : String}
      e2 = binary_char_roundtrip(c2, p2)
      %e2 : {SCon{c1, SCon{c2, SCon{c3, SCon{c4, SCon{c5, SCon{c6, SCon{c7, SCon{c8, SNil{}}}}}}}}} == SCon{B.bit_to_char(B.char_to_bit(c1)), SCon{_, SCon{c3, SCon{c4, SCon{c5, SCon{c6, SCon{c7, SCon{c8, SNil{}}}}}}}}} : String}
      e1 = binary_char_roundtrip(c1, p1)
      %e1 : {SCon{c1, SCon{c2, SCon{c3, SCon{c4, SCon{c5, SCon{c6, SCon{c7, SCon{c8, SNil{}}}}}}}}} == SCon{_, SCon{c2, SCon{c3, SCon{c4, SCon{c5, SCon{c6, SCon{c7, SCon{c8, SNil{}}}}}}}}} : String}
      {==}

def binary_byte_complete(
  +c1: Char, +c2: Char, +c3: Char, +c4: Char, +c5: Char, +c6: Char, +c7: Char, +c8: Char,
  valid: {B.is_valid_binary_byte(SCon{c1, SCon{c2, SCon{c3, SCon{c4, SCon{c5, SCon{c6, SCon{c7, SCon{c8, SNil{}}}}}}}}}) == True{} : Bool},
  proofs: {B.is_binary_digit(c1) == True{} : Bool} & {B.is_binary_digit(c2) == True{} : Bool} & {B.is_binary_digit(c3) == True{} : Bool} & {B.is_binary_digit(c4) == True{} : Bool} & {B.is_binary_digit(c5) == True{} : Bool} & {B.is_binary_digit(c6) == True{} : Bool} & {B.is_binary_digit(c7) == True{} : Bool} & {B.is_binary_digit(c8) == True{} : Bool}
) -> BinaryByteSpec(SCon{c1, SCon{c2, SCon{c3, SCon{c4, SCon{c5, SCon{c6, SCon{c7, SCon{c8, SNil{}}}}}}}}}, valid):
  ([B.char_to_bit(c1), B.char_to_bit(c2), B.char_to_bit(c3), B.char_to_bit(c4), B.char_to_bit(c5), B.char_to_bit(c6), B.char_to_bit(c7), B.char_to_bit(c8)],
    ({==}, binary_byte.spells(c1, c2, c3, c4, c5, c6, c7, c8, proofs), {==},
     eight_bits_bound(B.char_to_bit(c1), B.char_to_bit(c2), B.char_to_bit(c3), B.char_to_bit(c4), B.char_to_bit(c5), B.char_to_bit(c6), B.char_to_bit(c7), B.char_to_bit(c8))))

def Laws.binary_byte(s, valid):
  match s:
    case SNil{}:
      Empty.absurd(BinaryByteSpec(SNil{}, valid), H.hex_u32.false_true(valid))
    case SCon{c1, SNil{}}:
      Empty.absurd(BinaryByteSpec(SCon{c1, SNil{}}, valid), H.hex_u32.false_true(valid))
    case SCon{c1, SCon{c2, SNil{}}}:
      Empty.absurd(BinaryByteSpec(SCon{c1, SCon{c2, SNil{}}}, valid), H.hex_u32.false_true(valid))
    case SCon{c1, SCon{c2, SCon{c3, SNil{}}}}:
      Empty.absurd(BinaryByteSpec(SCon{c1, SCon{c2, SCon{c3, SNil{}}}}, valid), H.hex_u32.false_true(valid))
    case SCon{c1, SCon{c2, SCon{c3, SCon{c4, SNil{}}}}}:
      Empty.absurd(BinaryByteSpec(SCon{c1, SCon{c2, SCon{c3, SCon{c4, SNil{}}}}}, valid), H.hex_u32.false_true(valid))
    case SCon{c1, SCon{c2, SCon{c3, SCon{c4, SCon{c5, SNil{}}}}}}:
      Empty.absurd(BinaryByteSpec(SCon{c1, SCon{c2, SCon{c3, SCon{c4, SCon{c5, SNil{}}}}}}, valid), H.hex_u32.false_true(valid))
    case SCon{c1, SCon{c2, SCon{c3, SCon{c4, SCon{c5, SCon{c6, SNil{}}}}}}}:
      Empty.absurd(BinaryByteSpec(SCon{c1, SCon{c2, SCon{c3, SCon{c4, SCon{c5, SCon{c6, SNil{}}}}}}}, valid), H.hex_u32.false_true(valid))
    case SCon{c1, SCon{c2, SCon{c3, SCon{c4, SCon{c5, SCon{c6, SCon{c7, SNil{}}}}}}}}:
      Empty.absurd(BinaryByteSpec(SCon{c1, SCon{c2, SCon{c3, SCon{c4, SCon{c5, SCon{c6, SCon{c7, SNil{}}}}}}}}, valid), H.hex_u32.false_true(valid))
    case SCon{c1, SCon{c2, SCon{c3, SCon{c4, SCon{c5, SCon{c6, SCon{c7, SCon{c8, SNil{}}}}}}}}}:
      +v = valid
      binary_byte_complete(c1, c2, c3, c4, c5, c6, c7, c8, v,
        binary_byte.digit_proofs(c1, c2, c3, c4, c5, c6, c7, c8, v))
    case SCon{c1, SCon{c2, SCon{c3, SCon{c4, SCon{c5, SCon{c6, SCon{c7, SCon{c8, SCon{c9, rest}}}}}}}}}:
      Empty.absurd(BinaryByteSpec(SCon{c1, SCon{c2, SCon{c3, SCon{c4, SCon{c5, SCon{c6, SCon{c7, SCon{c8, SCon{c9, rest}}}}}}}}}, valid), H.hex_u32.false_true(valid))

def Laws.is_valid_byte_mask(mask):
  {==}

def ByteMaskSpec(+mask: String, +byte: U32,
  valid: {B.is_valid_byte_mask(mask) == True{} : Bool}) -> Type:
  {B.byte_mask(mask, byte, valid) ==
    (U32.is_le(byte, 255) &&
     Laws.mask_positions(mask, [128, 64, 32, 16, 8, 4, 2, 1], byte)) : Bool}

def Laws.byte_mask(mask, byte, valid):
  match mask:
    case SNil{}:
      Empty.absurd(ByteMaskSpec(SNil{}, byte, valid), H.hex_u32.false_true(valid))
    case SCon{c1, SNil{}}:
      Empty.absurd(ByteMaskSpec(SCon{c1, SNil{}}, byte, valid), H.hex_u32.false_true(valid))
    case SCon{c1, SCon{c2, SNil{}}}:
      Empty.absurd(ByteMaskSpec(SCon{c1, SCon{c2, SNil{}}}, byte, valid), H.hex_u32.false_true(valid))
    case SCon{c1, SCon{c2, SCon{c3, SNil{}}}}:
      Empty.absurd(ByteMaskSpec(SCon{c1, SCon{c2, SCon{c3, SNil{}}}}, byte, valid), H.hex_u32.false_true(valid))
    case SCon{c1, SCon{c2, SCon{c3, SCon{c4, SNil{}}}}}:
      Empty.absurd(ByteMaskSpec(SCon{c1, SCon{c2, SCon{c3, SCon{c4, SNil{}}}}}, byte, valid), H.hex_u32.false_true(valid))
    case SCon{c1, SCon{c2, SCon{c3, SCon{c4, SCon{c5, SNil{}}}}}}:
      Empty.absurd(ByteMaskSpec(SCon{c1, SCon{c2, SCon{c3, SCon{c4, SCon{c5, SNil{}}}}}}, byte, valid), H.hex_u32.false_true(valid))
    case SCon{c1, SCon{c2, SCon{c3, SCon{c4, SCon{c5, SCon{c6, SNil{}}}}}}}:
      Empty.absurd(ByteMaskSpec(SCon{c1, SCon{c2, SCon{c3, SCon{c4, SCon{c5, SCon{c6, SNil{}}}}}}}, byte, valid), H.hex_u32.false_true(valid))
    case SCon{c1, SCon{c2, SCon{c3, SCon{c4, SCon{c5, SCon{c6, SCon{c7, SNil{}}}}}}}}:
      Empty.absurd(ByteMaskSpec(SCon{c1, SCon{c2, SCon{c3, SCon{c4, SCon{c5, SCon{c6, SCon{c7, SNil{}}}}}}}}, byte, valid), H.hex_u32.false_true(valid))
    case SCon{c1, SCon{c2, SCon{c3, SCon{c4, SCon{c5, SCon{c6, SCon{c7, SCon{c8, SNil{}}}}}}}}}:
      {==}
    case SCon{c1, SCon{c2, SCon{c3, SCon{c4, SCon{c5, SCon{c6, SCon{c7, SCon{c8, SCon{c9, rest}}}}}}}}}:
      Empty.absurd(ByteMaskSpec(SCon{c1, SCon{c2, SCon{c3, SCon{c4, SCon{c5, SCon{c6, SCon{c7, SCon{c8, SCon{c9, rest}}}}}}}}}, byte, valid), H.hex_u32.false_true(valid))

def Laws.byte_mask_examples():
  ({==}, {==}, {==}, {==}, {==}, {==}, {==})

def Laws.valid_utf8_one_byte_examples():
  ({==}, {==}, {==})
