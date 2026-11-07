import Base
import ./defs.bend as Defs
import ./LAWS.bend as Laws
import ./binary_LAWS.bend as BinaryLaws
import ./hexdigits_LAWS.bend as HexLaws
import ./hexdigits.bend as H
import ./binary.bend as B
import ./utf8.bend as UTF8

# State the membership specification as a type for the bit-level lemma.
def HexDigitSpec(+c: Char) -> Type:
  {H.is_hex_digit(c) == List.contains(~Char, ~Char.is_eq, HexLaws.hex_digits(), c) : Bool}

# Most-significant bits come first, matching Bend's binder order.
def char_from_bits(
  b31: Bool, b30: Bool, b29: Bool, b28: Bool, b27: Bool, b26: Bool, b25: Bool, b24: Bool,
  b23: Bool, b22: Bool, b21: Bool, b20: Bool, b19: Bool, b18: Bool, b17: Bool, b16: Bool,
  b15: Bool, b14: Bool, b13: Bool, b12: Bool, b11: Bool, b10: Bool, b9: Bool, b8: Bool,
  b7: Bool, b6: Bool, b5: Bool, b4: Bool, b3: Bool, b2: Bool, b1: Bool, b0: Bool
) -> Char:
  Chr{U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

def utf8_proof.capacity_bits(+b10: Bool, +b9: Bool, +b8: Bool, +b7: Bool, +b6: Bool, +b5: Bool, +b4: Bool, +b3: Bool, +b2: Bool, +b1: Bool, +b0: Bool) -> {UTF8.can_encode_as_two_bytes(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, Word.zero(21n)}}}}}}}}}}}}) == True{} : Bool}:
  match b10 b9 b8 b7 b6 b5 b4 b3 b2 b1 b0:
    case False{} _ _ _ _ _ _ _ _ _ _: {==}
    case True{} False{} _ _ _ _ _ _ _ _ _: {==}
    case True{} True{} False{} _ _ _ _ _ _ _ _: {==}
    case True{} True{} True{} False{} _ _ _ _ _ _ _: {==}
    case True{} True{} True{} True{} False{} _ _ _ _ _ _: {==}
    case True{} True{} True{} True{} True{} False{} _ _ _ _ _: {==}
    case True{} True{} True{} True{} True{} True{} False{} _ _ _ _: {==}
    case True{} True{} True{} True{} True{} True{} True{} False{} _ _ _: {==}
    case True{} True{} True{} True{} True{} True{} True{} True{} False{} _ _: {==}
    case True{} True{} True{} True{} True{} True{} True{} True{} True{} False{} _: {==}
    case True{} True{} True{} True{} True{} True{} True{} True{} True{} True{} False{}: {==}
    case True{} True{} True{} True{} True{} True{} True{} True{} True{} True{} True{}: {==}


def utf8_proof.capacity_model_bits(+b31: Bool, +b30: Bool, +b29: Bool, +b28: Bool, +b27: Bool, +b26: Bool, +b25: Bool, +b24: Bool, +b23: Bool, +b22: Bool, +b21: Bool, +b20: Bool, +b19: Bool, +b18: Bool, +b17: Bool, +b16: Bool, +b15: Bool, +b14: Bool, +b13: Bool, +b12: Bool, +b11: Bool, +b10: Bool, +b9: Bool, +b8: Bool, +b7: Bool, +b6: Bool, +b5: Bool, +b4: Bool, +b3: Bool, +b2: Bool, +b1: Bool, +b0: Bool) ->
  {UTF8.can_encode_as_two_bytes(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))) == Maybe.is_some(&1, U32 & U32, Laws.two_byte_shape(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0)))) : Bool}:
  match b31 b30 b29 b28 b27 b26 b25 b24 b23 b22 b21 b20 b19 b18 b17 b16 b15 b14 b13 b12 b11:
    case True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _: {==}
    case False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _: {==}
    case False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _: {==}
    case False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _: {==}
    case False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _: {==}
    case False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _: {==}
    case False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _: {==}
    case False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _: {==}
    case False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _: {==}
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _: {==}
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _: {==}
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _: {==}
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _: {==}
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _: {==}
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _: {==}
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _: {==}
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _: {==}
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _: {==}
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _: {==}
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _: {==}
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{}: {==}
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{}:
      utf8_proof.capacity_bits(b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0)

def Laws.utf8_can_encode_as_two_bytes(cp):
  match cp:
    case U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      utf8_proof.capacity_model_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0)

def utf8_proof.one_capacity_model_bits(+b31: Bool, +b30: Bool, +b29: Bool, +b28: Bool, +b27: Bool, +b26: Bool, +b25: Bool, +b24: Bool, +b23: Bool, +b22: Bool, +b21: Bool, +b20: Bool, +b19: Bool, +b18: Bool, +b17: Bool, +b16: Bool, +b15: Bool, +b14: Bool, +b13: Bool, +b12: Bool, +b11: Bool, +b10: Bool, +b9: Bool, +b8: Bool, +b7: Bool, +b6: Bool, +b5: Bool, +b4: Bool, +b3: Bool, +b2: Bool, +b1: Bool, +b0: Bool) ->
  {UTF8.can_encode_as_one_byte(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))) == Maybe.is_some(&2, U32, Laws.one_byte_shape(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0)))) : Bool}:
  match b31 b30 b29 b28 b27 b26 b25 b24 b23 b22 b21 b20 b19 b18 b17 b16 b15 b14 b13 b12 b11 b10 b9 b8 b7:
    case True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _: {==}
    case False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _: {==}
    case False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _: {==}
    case False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _: {==}
    case False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _: {==}
    case False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _: {==}
    case False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _: {==}
    case False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _: {==}
    case False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _: {==}
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _: {==}
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _: {==}
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _: {==}
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _: {==}
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _: {==}
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _: {==}
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _: {==}
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _: {==}
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _: {==}
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _: {==}
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _: {==}
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _: {==}
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _: {==}
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _: {==}
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _: {==}
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{}: {==}
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{}:
      match b6 b5 b4 b3 b2 b1 b0:
        case False{} _ _ _ _ _ _: {==}
        case True{} False{} _ _ _ _ _: {==}
        case True{} True{} False{} _ _ _ _: {==}
        case True{} True{} True{} False{} _ _ _: {==}
        case True{} True{} True{} True{} False{} _ _: {==}
        case True{} True{} True{} True{} True{} False{} _: {==}
        case True{} True{} True{} True{} True{} True{} False{}: {==}
        case True{} True{} True{} True{} True{} True{} True{}: {==}

def Laws.utf8_can_encode_as_one_byte(cp):
  match cp:
    case U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      utf8_proof.one_capacity_model_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0)


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

def HexLaws.is_hex_digit(c):
  match c:
    case Chr{U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      hex_digit_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0)

# Compare every implemented digit conversion with the independent table.
def DecodeSpec(+c: Char, -valid: {H.is_hex_digit(c) == True{} : Bool}) -> Type:
  {Some{H.decode(H.HexDigitChar{c, valid})} == HexLaws.decode_spec(c) : Maybe<&2, HexLaws.Nibble()>}

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

def decode_agrees(+c: Char, +valid: {H.is_hex_digit(c) == True{} : Bool}) -> DecodeSpec(c, valid):
  match c:
    case Chr{U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      decode_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0, valid)

def HexLaws.decode(c, valid):
  +accepted = valid
  (accepted, decode_agrees(c, accepted))

def decode_value_agrees(+c: Char, +valid: {H.is_hex_digit(c) == True{} : Bool}) ->
  {H.decode(H.HexDigitChar{c, valid}) == HexLaws.decode_value_spec(c) : HexLaws.Nibble()}:
  Equal.cong(Maybe<&2, HexLaws.Nibble()>, HexLaws.Nibble(),
    result => Maybe.default(&2, HexLaws.Nibble(), result, Word.zero(4n)),
    Some{H.decode(H.HexDigitChar{c, valid})}, HexLaws.decode_spec(c), decode_agrees(c, valid))

def HexLaws.is_valid_hex_u32_input(s):
  {==}

def HexLaws.is_valid_hex_u32_examples():
  ({==}, {==}, {==}, {==}, {==})

def HexU32Spec(+s: String, -valid: {H.is_valid_hex_u32(s) == True{} : Bool}) -> Type:
  {H.hex_u32(s, valid) == HexLaws.hex_u32_spec(s) : U32}

# combine folds the reference nibbles of s onto any accumulator.
def hex_u32.combine_agrees(
  +s: String,
  +valid: {List.all(~&2, ~Char, ~(c => H.is_hex_digit(c)), String.to_list(s)) == True{} : Bool},
  +acc: U32
) -> {H.hex_u32.combine(s, valid, acc) ==
  List.foldl(~&2, ~HexLaws.Nibble, ~U32, ~(total => n => (total * 16 + U32.from_nat(Word.to_nat(4n, n)) : U32)), HexLaws.hex_nibbles_spec(s), acc) : U32}:
  match s:
    case SNil{}:
      {==}
    case SCon{c, rest}:
      -rest_ok = List.all(~&2, ~Char, ~(c => H.is_hex_digit(c)), String.to_list(rest))
      +digit_ok = H.hex_u32.head_true(H.is_hex_digit(c), rest_ok, valid)
      +step = (acc * 16 + H.word4_to_u32(H.decode(H.HexDigitChar{c, digit_ok})) : U32)
      %decode_value_agrees(c, digit_ok) : {H.hex_u32.combine(SCon{c, rest}, valid, acc) ==
        List.foldl(~&2, ~HexLaws.Nibble, ~U32, ~(total => n => (total * 16 + U32.from_nat(Word.to_nat(4n, n)) : U32)), HexLaws.hex_nibbles_spec(rest),
          (acc * 16 + U32.from_nat(Word.to_nat(4n, _)) : U32)) : U32}
      hex_u32.combine_agrees(rest, H.hex_u32.tail_true(H.is_hex_digit(c), rest_ok, valid), step)

def hex_u32_agrees(+s: String, valid: {H.is_valid_hex_u32(s) == True{} : Bool}) -> HexU32Spec(s, valid):
  hex_u32.combine_agrees(s, H.hex_u32.all_digits(s, valid), 0)

def HexLaws.example_zero():
  {==}

def HexLaws.hex_u32_padding_examples():
  ({==}, {==}, {==}, {==})

# Binary input validation and byte conversion.
def BinaryLaws.is_binary_digit(c):
  {==}

def BinaryLaws.valid_byte_string(s):
  {==}

def BinaryLaws.is_mask_digit(c):
  {==}

def BinaryLaws.is_valid_byte_mask(mask):
  {==}

def ByteMaskSpec(+mask: String, +byte: U32,
  -valid: {B.is_valid_byte_mask(mask) == True{} : Bool}) -> Type:
  {B.byte_mask(mask, byte, valid) == (U32.is_le(byte, 255) && BinaryLaws.mask_positions(mask, [128, 64, 32, 16, 8, 4, 2, 1], byte)) : Bool}

def byte_mask_agrees(+mask: String, +byte: U32, valid: {B.is_valid_byte_mask(mask) == True{} : Bool}) -> ByteMaskSpec(mask, byte, valid):
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

def BinaryLaws.byte_mask_examples():
  ({==}, {==}, {==}, {==}, {==}, {==}, {==})

def Utf8EncodeOneSpec(+cp: U32,
  -valid: {UTF8.can_encode_as_one_byte(cp) == True{} : Bool}) -> Type:
  {Some{UTF8.encode_as_one_byte(cp, valid)} == Laws.one_byte_shape(cp) : Maybe<&2, U32>}

def utf8_proof.encode_as_one_byte_bits(+b31: Bool, +b30: Bool, +b29: Bool, +b28: Bool, +b27: Bool, +b26: Bool, +b25: Bool, +b24: Bool, +b23: Bool, +b22: Bool, +b21: Bool, +b20: Bool, +b19: Bool, +b18: Bool, +b17: Bool, +b16: Bool, +b15: Bool, +b14: Bool, +b13: Bool, +b12: Bool, +b11: Bool, +b10: Bool, +b9: Bool, +b8: Bool, +b7: Bool, +b6: Bool, +b5: Bool, +b4: Bool, +b3: Bool, +b2: Bool, +b1: Bool, +b0: Bool,
  valid: {UTF8.can_encode_as_one_byte(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))) == True{} : Bool}
) -> Utf8EncodeOneSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0)), valid):
  match b31 b30 b29 b28 b27 b26 b25 b24 b23 b22 b21 b20 b19 b18 b17 b16 b15 b14 b13 b12 b11 b10 b9 b8 b7:
    case True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(Utf8EncodeOneSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0)), valid), H.hex_u32.false_true(valid))
    case False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(Utf8EncodeOneSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0)), valid), H.hex_u32.false_true(valid))
    case False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(Utf8EncodeOneSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0)), valid), H.hex_u32.false_true(valid))
    case False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(Utf8EncodeOneSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0)), valid), H.hex_u32.false_true(valid))
    case False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(Utf8EncodeOneSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0)), valid), H.hex_u32.false_true(valid))
    case False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(Utf8EncodeOneSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0)), valid), H.hex_u32.false_true(valid))
    case False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(Utf8EncodeOneSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0)), valid), H.hex_u32.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(Utf8EncodeOneSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0)), valid), H.hex_u32.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(Utf8EncodeOneSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0)), valid), H.hex_u32.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(Utf8EncodeOneSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0)), valid), H.hex_u32.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(Utf8EncodeOneSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0)), valid), H.hex_u32.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(Utf8EncodeOneSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0)), valid), H.hex_u32.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(Utf8EncodeOneSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0)), valid), H.hex_u32.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(Utf8EncodeOneSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0)), valid), H.hex_u32.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(Utf8EncodeOneSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0)), valid), H.hex_u32.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _:
      Empty.absurd(Utf8EncodeOneSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0)), valid), H.hex_u32.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _:
      Empty.absurd(Utf8EncodeOneSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0)), valid), H.hex_u32.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _:
      Empty.absurd(Utf8EncodeOneSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0)), valid), H.hex_u32.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _:
      Empty.absurd(Utf8EncodeOneSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0)), valid), H.hex_u32.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _:
      Empty.absurd(Utf8EncodeOneSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0)), valid), H.hex_u32.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _:
      Empty.absurd(Utf8EncodeOneSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0)), valid), H.hex_u32.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _:
      Empty.absurd(Utf8EncodeOneSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0)), valid), H.hex_u32.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _:
      Empty.absurd(Utf8EncodeOneSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0)), valid), H.hex_u32.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _:
      Empty.absurd(Utf8EncodeOneSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0)), valid), H.hex_u32.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{}:
      Empty.absurd(Utf8EncodeOneSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0)), valid), H.hex_u32.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{}: {==}

def Laws.utf8_encode_as_one_byte(cp, valid):
  match cp:
    case U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      utf8_proof.encode_as_one_byte_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0, valid)


# A one-byte encoding preserves the code point, so the byte itself is a witness.
def Utf8OneShapeRepresentation(+byte: U32) -> Type:
  Exists(U32, cp => {Laws.one_byte_shape(cp) == Some{byte} : Maybe<&2, U32>})

def utf8_proof.one_shape_witness(+byte: U32,
  accepted: {UTF8.has_one_byte_shape(byte) == True{} : Bool}) -> Utf8OneShapeRepresentation(byte):
  (byte, Equal.sym(Maybe<&2, U32>, Some{byte}, Laws.one_byte_shape(byte),
    Laws.utf8_encode_as_one_byte(byte, accepted)))

# Reuse the capacity and encoding proofs to recover the produced byte's value.
def utf8_proof.one_model_byte_accepted(+cp: U32, +byte: U32,
  +produced: {Laws.one_byte_shape(cp) == Some{byte} : Maybe<&2, U32>}) ->
  {UTF8.has_one_byte_shape(byte) == True{} : Bool}:
  +accepted = Equal.trans(Bool, UTF8.can_encode_as_one_byte(cp), Maybe.is_some(&2, U32, Laws.one_byte_shape(cp)), True{},
    Laws.utf8_can_encode_as_one_byte(cp),
    Equal.cong(Maybe<&2, U32>, Bool, shape => Maybe.is_some(&2, U32, shape),
      Laws.one_byte_shape(cp), Some{byte}, produced))
  equal = Equal.cong(Maybe<&2, U32>, U32, shape => Maybe.default(&2, U32, shape, 0),
    Some{cp}, Some{byte},
    Equal.trans(Maybe<&2, U32>, Some{cp}, Laws.one_byte_shape(cp), Some{byte},
      Laws.utf8_encode_as_one_byte(cp, accepted), produced))
  Equal.trans(Bool, UTF8.has_one_byte_shape(byte), UTF8.has_one_byte_shape(cp), True{},
    Equal.sym(Bool, UTF8.has_one_byte_shape(cp), UTF8.has_one_byte_shape(byte),
      Equal.cong(U32, Bool, value => UTF8.has_one_byte_shape(value), cp, byte, equal)), accepted)

def utf8_proof.one_shape_witness_accepted(+byte: U32, representation: Utf8OneShapeRepresentation(byte)) ->
  {UTF8.has_one_byte_shape(byte) == True{} : Bool}:
  (cp, produced) = representation
  utf8_proof.one_model_byte_accepted(cp, byte, produced)

def Laws.utf8_has_one_byte_shape(byte):
  (accepted => utf8_proof.one_shape_witness(byte, accepted),
   representation => utf8_proof.one_shape_witness_accepted(byte, representation))

# Both functions return their argument, so each proof is the one given.
def Laws.utf8_one_byte_inverse():
  (cp => +valid => (valid, {==}),
   byte => +valid => (valid, {==}))

# Validity reduces to shape once the shape fixes the high 25 bits to zero.
def Utf8ValidOneSpec(+cp: U32) -> Type:
  {UTF8.valid_one_byte(cp) ==
    (Bool.not(Laws.overlong_one_byte(cp)) && Laws.is_unicode_scalar(cp)) : Bool}

# A set high bit contradicts the shape.  Otherwise the low seven bits are
# split until the scalar range check computes, leaving the shape proof.
def utf8_proof.valid_one_byte_bits(+b31: Bool, +b30: Bool, +b29: Bool, +b28: Bool, +b27: Bool, +b26: Bool, +b25: Bool, +b24: Bool, +b23: Bool, +b22: Bool, +b21: Bool, +b20: Bool, +b19: Bool, +b18: Bool, +b17: Bool, +b16: Bool, +b15: Bool, +b14: Bool, +b13: Bool, +b12: Bool, +b11: Bool, +b10: Bool, +b9: Bool, +b8: Bool, +b7: Bool, +b6: Bool, +b5: Bool, +b4: Bool, +b3: Bool, +b2: Bool, +b1: Bool, +b0: Bool,
  valid: {UTF8.has_one_byte_shape(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))) == True{} : Bool}) -> Utf8ValidOneSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))):
  match b31 b30 b29 b28 b27 b26 b25 b24 b23 b22 b21 b20 b19 b18 b17 b16 b15 b14 b13 b12 b11 b10 b9 b8 b7:
    case True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(Utf8ValidOneSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))), H.hex_u32.false_true(valid))
    case False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(Utf8ValidOneSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))), H.hex_u32.false_true(valid))
    case False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(Utf8ValidOneSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))), H.hex_u32.false_true(valid))
    case False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(Utf8ValidOneSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))), H.hex_u32.false_true(valid))
    case False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(Utf8ValidOneSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))), H.hex_u32.false_true(valid))
    case False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(Utf8ValidOneSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))), H.hex_u32.false_true(valid))
    case False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(Utf8ValidOneSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))), H.hex_u32.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(Utf8ValidOneSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))), H.hex_u32.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(Utf8ValidOneSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))), H.hex_u32.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(Utf8ValidOneSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))), H.hex_u32.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(Utf8ValidOneSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))), H.hex_u32.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(Utf8ValidOneSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))), H.hex_u32.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(Utf8ValidOneSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))), H.hex_u32.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(Utf8ValidOneSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))), H.hex_u32.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(Utf8ValidOneSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))), H.hex_u32.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _:
      Empty.absurd(Utf8ValidOneSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))), H.hex_u32.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _:
      Empty.absurd(Utf8ValidOneSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))), H.hex_u32.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _:
      Empty.absurd(Utf8ValidOneSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))), H.hex_u32.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _:
      Empty.absurd(Utf8ValidOneSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))), H.hex_u32.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _:
      Empty.absurd(Utf8ValidOneSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))), H.hex_u32.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _:
      Empty.absurd(Utf8ValidOneSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))), H.hex_u32.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _:
      Empty.absurd(Utf8ValidOneSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))), H.hex_u32.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _:
      Empty.absurd(Utf8ValidOneSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))), H.hex_u32.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _:
      Empty.absurd(Utf8ValidOneSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))), H.hex_u32.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{}:
      Empty.absurd(Utf8ValidOneSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))), H.hex_u32.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{}:
      match b6 b5 b4 b3 b2 b1 b0:
        case True{} _ _ _ _ _ _: valid
        case False{} True{} _ _ _ _ _: valid
        case False{} False{} True{} _ _ _ _: valid
        case False{} False{} False{} True{} _ _ _: valid
        case False{} False{} False{} False{} True{} _ _: valid
        case False{} False{} False{} False{} False{} True{} _: valid
        case False{} False{} False{} False{} False{} False{} True{}: valid
        case False{} False{} False{} False{} False{} False{} False{}: valid

def utf8_proof.valid_one_byte(+byte: U32,
  valid: {UTF8.has_one_byte_shape(byte) == True{} : Bool}) -> Utf8ValidOneSpec(byte):
  match byte:
    case U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      utf8_proof.valid_one_byte_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0, valid)

# Split on the shape the same way the specification does.
def utf8_proof.valid_one_byte_if(+byte: U32, shape: Bool,
  checked: {UTF8.has_one_byte_shape(byte) == shape : Bool}) ->
  {UTF8.valid_one_byte(byte) == Laws.valid_one_byte.if(byte, shape, checked) : Bool}:
  match shape:
    case False{}:
      checked
    case True{}:
      utf8_proof.valid_one_byte(byte, checked)

def Laws.utf8_valid_one_byte(byte):
  utf8_proof.valid_one_byte_if(byte, UTF8.has_one_byte_shape(byte), {==})

def Laws.utf8_overlong_two_bytes(b1, b2, valid):
  {==}

# Prove UTF-8 encoding and decoding once for arbitrary payload fields.
# Byte shape and range checks then inspect each field independently.
# Low bits precede high bits in the underlying Word representation.
def word_join(n: Nat, low: Word(n), -m: Nat, high: Word(m)) -> Word(Nat.add(n, m)):
  match n:
    case 0n: high
    case 1n+p:
      match low:
        case WCon{b, rest}: WCon{b, word_join(p, rest, m, high)}

def word_ones(n: Nat) -> Word(n):
  match n:
    case 0n: WNil{}
    case 1n+p: WCon{True{}, word_ones(p)}

def word_add_zero(n: Nat, +bits: Word(n)) -> {Word.add(n, bits, Word.zero(n)) == bits : Word(n)}:
  match n:
    case 0n:
      match bits:
        case WNil{}: {==}
    case 1n+p:
      match bits:
        case WCon{False{}, rest}:
          %word_add_zero(p, rest) : {WCon{False{}, Word.add(p, rest, Word.zero(p))} == WCon{False{}, _} : Word(1n+p)}
          {==}
        case WCon{True{}, rest}:
          %word_add_zero(p, rest) : {WCon{True{}, Word.add(p, rest, Word.zero(p))} == WCon{True{}, _} : Word(1n+p)}
          {==}

def word_and_zero(n: Nat, +bits: Word(n)) -> {Word.and(n, bits, Word.zero(n)) == Word.zero(n) : Word(n)}:
  match n:
    case 0n: {==}
    case 1n+p:
      match bits:
        case WCon{False{}, rest}:
          %word_and_zero(p, rest) : {WCon{False{}, Word.and(p, rest, Word.zero(p))} == WCon{False{}, _} : Word(1n+p)}
          {==}
        case WCon{True{}, rest}:
          %word_and_zero(p, rest) : {WCon{False{}, Word.and(p, rest, Word.zero(p))} == WCon{False{}, _} : Word(1n+p)}
          {==}

# Adding disjoint low/high fields cannot carry between them.
def word_add_fields(n: Nat, +low: Word(n), m: Nat, +high: Word(m)) ->
  {Word.add(Nat.add(n, m), word_join(n, Word.zero(n), m, high), word_join(n, low, m, Word.zero(m))) == word_join(n, low, m, high) : Word(Nat.add(n, m))}:
  match n:
    case 0n: word_add_zero(m, high)
    case 1n+p:
      match low:
        case WCon{False{}, rest}:
          %word_add_fields(p, rest, m, high) : {WCon{False{}, Word.add(Nat.add(p, m), word_join(p, Word.zero(p), m, high), word_join(p, rest, m, Word.zero(m)))} == WCon{False{}, _} : Word(1n+Nat.add(p, m))}
          {==}
        case WCon{True{}, rest}:
          %word_add_fields(p, rest, m, high) : {WCon{True{}, Word.add(Nat.add(p, m), word_join(p, Word.zero(p), m, high), word_join(p, rest, m, Word.zero(m)))} == WCon{True{}, _} : Word(1n+Nat.add(p, m))}
          {==}

# An all-word_ones low mask keeps its field and clears the high field.
def word_mask_fields(n: Nat, +low: Word(n), m: Nat, +high: Word(m)) ->
  {Word.and(Nat.add(n, m), word_join(n, low, m, high), word_join(n, word_ones(n), m, Word.zero(m))) == word_join(n, low, m, Word.zero(m)) : Word(Nat.add(n, m))}:
  match n:
    case 0n: word_and_zero(m, high)
    case 1n+p:
      match low:
        case WCon{False{}, rest}:
          %word_mask_fields(p, rest, m, high) : {WCon{False{}, Word.and(Nat.add(p, m), word_join(p, rest, m, high), word_join(p, word_ones(p), m, Word.zero(m)))} == WCon{False{}, _} : Word(1n+Nat.add(p, m))}
          {==}
        case WCon{True{}, rest}:
          %word_mask_fields(p, rest, m, high) : {WCon{True{}, Word.and(Nat.add(p, m), word_join(p, rest, m, high), word_join(p, word_ones(p), m, Word.zero(m)))} == WCon{True{}, _} : Word(1n+Nat.add(p, m))}
          {==}

# Split the eleven-bit code point into six low bits and five high bits.
def utf8_proof.codepoint(+low: Word(6n), high: Word(5n)) -> U32:
  U32{word_join(6n, low, 26n, word_join(5n, high, 21n, Word.zero(21n)))}

def utf8_proof.first_byte(high: Word(5n)) -> U32:
  U32{word_join(5n, high, 27n, WCon{False{}, WCon{True{}, WCon{True{}, Word.zero(24n)}}})}

def utf8_proof.second_byte(low: Word(6n)) -> U32:
  U32{word_join(6n, low, 26n, WCon{False{}, WCon{True{}, Word.zero(24n)}})}

# A code point fits in seven bits exactly when its high field is 0 or 1.
def utf8_proof.fits_one_byte(high: Word(5n)) -> Bool:
  U32.is_le(U32{word_join(5n, high, 27n, Word.zero(27n))}, 1)

def utf8_proof.mask_codepoint(+low: Word(6n), +high: Word(5n)) ->
  {U32.and(utf8_proof.codepoint(low, high), 63) == U32{word_join(6n, low, 26n, Word.zero(26n))} : U32}:
  Equal.cong(Word(32n), U32, x => U32{x},
    Word.and(32n, word_join(6n, low, 26n, word_join(5n, high, 21n, Word.zero(21n))), word_join(6n, word_ones(6n), 26n, Word.zero(26n))),
    word_join(6n, low, 26n, Word.zero(26n)),
    word_mask_fields(6n, low, 26n, word_join(5n, high, 21n, Word.zero(21n))))

def utf8_proof.encode_first(+low: Word(6n), +high: Word(5n),
  -valid: {UTF8.can_encode_as_two_bytes(utf8_proof.codepoint(low, high)) == True{} : Bool}) ->
  {B.first(UTF8.encode_as_two_bytes(utf8_proof.codepoint(low, high), valid)) == utf8_proof.first_byte(high) : U32}:
  match low high:
    case WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WNil{}}}}}}} WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WNil{}}}}}}:
      Equal.cong(Word(32n), U32, x => U32{x},
        Word.add(32n, word_join(5n, Word.zero(5n), 27n, WCon{False{}, WCon{True{}, WCon{True{}, Word.zero(24n)}}}), word_join(5n, high, 27n, Word.zero(27n))),
        word_join(5n, high, 27n, WCon{False{}, WCon{True{}, WCon{True{}, Word.zero(24n)}}}),
        word_add_fields(5n, high, 27n, WCon{False{}, WCon{True{}, WCon{True{}, Word.zero(24n)}}}))

def utf8_proof.encode_second(+low: Word(6n), +high: Word(5n),
  -valid: {UTF8.can_encode_as_two_bytes(utf8_proof.codepoint(low, high)) == True{} : Bool}) ->
  {B.second(UTF8.encode_as_two_bytes(utf8_proof.codepoint(low, high), valid)) == utf8_proof.second_byte(low) : U32}:
  Equal.trans(U32,
    (128 + U32.and(utf8_proof.codepoint(low, high), 63) : U32),
    (128 + U32{word_join(6n, low, 26n, Word.zero(26n))} : U32), utf8_proof.second_byte(low),
    Equal.cong(U32, U32, x => (128 + x : U32), U32.and(utf8_proof.codepoint(low, high), 63),
      U32{word_join(6n, low, 26n, Word.zero(26n))}, utf8_proof.mask_codepoint(low, high)),
    Equal.cong(Word(32n), U32, x => U32{x},
      Word.add(32n, word_join(6n, Word.zero(6n), 26n, WCon{False{}, WCon{True{}, Word.zero(24n)}}), word_join(6n, low, 26n, Word.zero(26n))),
      word_join(6n, low, 26n, WCon{False{}, WCon{True{}, Word.zero(24n)}}), word_add_fields(6n, low, 26n, WCon{False{}, WCon{True{}, Word.zero(24n)}})))

def utf8_proof.mask_first(+high: Word(5n)) ->
  {U32.and(utf8_proof.first_byte(high), 31) == U32{word_join(5n, high, 27n, Word.zero(27n))} : U32}:
  Equal.cong(Word(32n), U32, x => U32{x},
    Word.and(32n, word_join(5n, high, 27n, WCon{False{}, WCon{True{}, WCon{True{}, Word.zero(24n)}}}), word_join(5n, word_ones(5n), 27n, Word.zero(27n))),
    word_join(5n, high, 27n, Word.zero(27n)), word_mask_fields(5n, high, 27n, WCon{False{}, WCon{True{}, WCon{True{}, Word.zero(24n)}}}))

def utf8_proof.mask_second(+low: Word(6n)) ->
  {U32.and(utf8_proof.second_byte(low), 63) == U32{word_join(6n, low, 26n, Word.zero(26n))} : U32}:
  Equal.cong(Word(32n), U32, x => U32{x},
    Word.and(32n, word_join(6n, low, 26n, WCon{False{}, WCon{True{}, Word.zero(24n)}}), word_join(6n, word_ones(6n), 26n, Word.zero(26n))),
    word_join(6n, low, 26n, Word.zero(26n)), word_mask_fields(6n, low, 26n, WCon{False{}, WCon{True{}, Word.zero(24n)}}))

# Unrestricted arithmetic expression used only to reason about payload bits.
def utf8_proof.decode_payload(b1: U32, b2: U32) -> U32:
  (U32.shln(U32.and(b1, 31), 6n) + U32.and(b2, 63) : U32)

def utf8_proof.decode_fields(+low: Word(6n), +high: Word(5n)) ->
  {utf8_proof.decode_payload(utf8_proof.first_byte(high), utf8_proof.second_byte(low)) == utf8_proof.codepoint(low, high) : U32}:
  match low high:
    case WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WNil{}}}}}}} WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WNil{}}}}}}:
      %Equal.sym(U32, U32.and(utf8_proof.first_byte(high), 31), U32{word_join(5n, high, 27n, Word.zero(27n))}, utf8_proof.mask_first(high)) : {(U32.shl(U32.shl(U32.shl(U32.shl(U32.shl(U32.shl(_)))))) + U32.and(utf8_proof.second_byte(low), 63) : U32) == utf8_proof.codepoint(low, high) : U32}
      %Equal.sym(U32, U32.and(utf8_proof.second_byte(low), 63), U32{word_join(6n, low, 26n, Word.zero(26n))}, utf8_proof.mask_second(low)) : {(U32.shl(U32.shl(U32.shl(U32.shl(U32.shl(U32.shl(U32{word_join(5n, high, 27n, Word.zero(27n))})))))) + _ : U32) == utf8_proof.codepoint(low, high) : U32}
      Equal.cong(Word(32n), U32, x => U32{x},
        Word.add(32n, word_join(6n, Word.zero(6n), 26n, word_join(5n, high, 21n, Word.zero(21n))), word_join(6n, low, 26n, Word.zero(26n))),
        word_join(6n, low, 26n, word_join(5n, high, 21n, Word.zero(21n))),
        word_add_fields(6n, low, 26n, word_join(5n, high, 21n, Word.zero(21n))))

# Only 32 high-field values are relevant to the leading byte.
def utf8_proof.first_byte_facts(+high: Word(5n)) ->
  {B.byte_mask("110xxxxx", utf8_proof.first_byte(high), {==}) == True{} : Bool} &
  {(U32.is_ge(utf8_proof.first_byte(high), 194) && U32.is_le(utf8_proof.first_byte(high), 223)) == Bool.not(utf8_proof.fits_one_byte(high)) : Bool}:
  match high:
    case WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}: ({==}, {==})
    case WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}: ({==}, {==})
    case WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}: ({==}, {==})
    case WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}: ({==}, {==})
    case WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WNil{}}}}}}: ({==}, {==})
    case WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WNil{}}}}}}: ({==}, {==})
    case WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WNil{}}}}}}: ({==}, {==})
    case WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WNil{}}}}}}: ({==}, {==})
    case WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WNil{}}}}}}: ({==}, {==})
    case WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WNil{}}}}}}: ({==}, {==})
    case WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WNil{}}}}}}: ({==}, {==})
    case WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WNil{}}}}}}: ({==}, {==})
    case WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WNil{}}}}}}: ({==}, {==})
    case WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WNil{}}}}}}: ({==}, {==})
    case WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WNil{}}}}}}: ({==}, {==})
    case WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WNil{}}}}}}: ({==}, {==})
    case WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}}: ({==}, {==})
    case WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}}: ({==}, {==})
    case WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}}: ({==}, {==})
    case WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}}: ({==}, {==})
    case WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WNil{}}}}}}: ({==}, {==})
    case WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WNil{}}}}}}: ({==}, {==})
    case WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WNil{}}}}}}: ({==}, {==})
    case WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WNil{}}}}}}: ({==}, {==})
    case WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WNil{}}}}}}: ({==}, {==})
    case WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WNil{}}}}}}: ({==}, {==})
    case WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WNil{}}}}}}: ({==}, {==})
    case WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WNil{}}}}}}: ({==}, {==})
    case WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WNil{}}}}}}: ({==}, {==})
    case WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WNil{}}}}}}: ({==}, {==})
    case WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WNil{}}}}}}: ({==}, {==})
    case WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WNil{}}}}}}: ({==}, {==})

# Only 64 low-field values are relevant to the continuation byte.
def utf8_proof.second_byte_facts(+low: Word(6n)) ->
  {B.byte_mask("10xxxxxx", utf8_proof.second_byte(low), {==}) == True{} : Bool} &
  {(U32.is_ge(utf8_proof.second_byte(low), 128) && U32.is_le(utf8_proof.second_byte(low), 191)) == True{} : Bool}:
  match low:
    case WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}: ({==}, {==})
    case WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}: ({==}, {==})
    case WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}: ({==}, {==})
    case WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}: ({==}, {==})
    case WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}: ({==}, {==})
    case WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}: ({==}, {==})
    case WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}: ({==}, {==})
    case WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}: ({==}, {==})
    case WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}: ({==}, {==})
    case WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}: ({==}, {==})
    case WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}: ({==}, {==})
    case WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}: ({==}, {==})
    case WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}: ({==}, {==})
    case WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}: ({==}, {==})
    case WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}: ({==}, {==})
    case WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}: ({==}, {==})
    case WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}: ({==}, {==})
    case WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}: ({==}, {==})
    case WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}: ({==}, {==})
    case WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}: ({==}, {==})
    case WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}: ({==}, {==})
    case WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}: ({==}, {==})
    case WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}: ({==}, {==})
    case WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}: ({==}, {==})
    case WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}: ({==}, {==})
    case WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}: ({==}, {==})
    case WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}: ({==}, {==})
    case WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}: ({==}, {==})
    case WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}: ({==}, {==})
    case WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}: ({==}, {==})
    case WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}: ({==}, {==})
    case WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WNil{}}}}}}}: ({==}, {==})
    case WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}: ({==}, {==})
    case WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}: ({==}, {==})
    case WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}: ({==}, {==})
    case WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}: ({==}, {==})
    case WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}: ({==}, {==})
    case WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}: ({==}, {==})
    case WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}: ({==}, {==})
    case WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}: ({==}, {==})
    case WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}: ({==}, {==})
    case WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}: ({==}, {==})
    case WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}: ({==}, {==})
    case WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}: ({==}, {==})
    case WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}: ({==}, {==})
    case WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}: ({==}, {==})
    case WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}: ({==}, {==})
    case WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}: ({==}, {==})
    case WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}: ({==}, {==})
    case WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}: ({==}, {==})
    case WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}: ({==}, {==})
    case WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}: ({==}, {==})
    case WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}: ({==}, {==})
    case WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}: ({==}, {==})
    case WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}: ({==}, {==})
    case WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}: ({==}, {==})
    case WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}: ({==}, {==})
    case WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}: ({==}, {==})
    case WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}: ({==}, {==})
    case WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}: ({==}, {==})
    case WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}: ({==}, {==})
    case WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}: ({==}, {==})
    case WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}: ({==}, {==})
    case WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}: ({==}, {==})

def bool_and_true(+b: Bool) -> {Bool.and(b, True{}) == b : Bool}:
  match b:
    case False{}: {==}
    case True{}: {==}

def bool_and_equal(+a: Bool, +b: Bool, +x: Bool, +y: Bool,
  ax: {a == x : Bool}, by: {b == y : Bool}) -> {Bool.and(a, b) == Bool.and(x, y) : Bool}:
  %ax : {Bool.and(a, b) == Bool.and(_, y) : Bool}
  %by : {Bool.and(a, b) == Bool.and(a, _) : Bool}
  {==}

def utf8_proof.shape_from_masks(+b1: U32, +b2: U32,
  first: {B.byte_mask("110xxxxx", b1, {==}) == True{} : Bool},
  second: {B.byte_mask("10xxxxxx", b2, {==}) == True{} : Bool}) ->
  {UTF8.has_two_byte_shape(b1, b2) == True{} : Bool}:
  bool_and_equal(B.byte_mask("110xxxxx", b1, {==}), B.byte_mask("10xxxxxx", b2, {==}), True{}, True{}, first, second)

def Laws.is_surrogate_code_point_examples():
  ({==}, {==}, {==}, {==}, {==}, {==})

def BinaryLaws.bit8(byte, valid):
  {==}

def BinaryLaws.bit8_examples():
  ({==}, {==}, {==})

def Bit8ValueRoundtripSpec(+byte: U32,
  -valid: {U32.is_le(byte, 255) == True{} : Bool}) -> Type:
  {B.bit8_value(B.bit8(byte, valid)) == byte : U32}

# Any set bit above bit 7 contradicts the byte-range premise. Once those
# high bits are zero, exhaust the 256 possibilities for the eight low bits.
def bit8_value_roundtrip_bits(
  +b31: Bool,
  +b30: Bool,
  +b29: Bool,
  +b28: Bool,
  +b27: Bool,
  +b26: Bool,
  +b25: Bool,
  +b24: Bool,
  +b23: Bool,
  +b22: Bool,
  +b21: Bool,
  +b20: Bool,
  +b19: Bool,
  +b18: Bool,
  +b17: Bool,
  +b16: Bool,
  +b15: Bool,
  +b14: Bool,
  +b13: Bool,
  +b12: Bool,
  +b11: Bool,
  +b10: Bool,
  +b9: Bool,
  +b8: Bool,
  +b7: Bool,
  +b6: Bool,
  +b5: Bool,
  +b4: Bool,
  +b3: Bool,
  +b2: Bool,
  +b1: Bool,
  +b0: Bool,
  valid: {U32.is_le(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0)), 255) == True{} : Bool}
) -> Bit8ValueRoundtripSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0)), valid):
  match b31 b30 b29 b28 b27 b26 b25 b24 b23 b22 b21 b20 b19 b18 b17 b16 b15 b14 b13 b12 b11 b10 b9 b8:
    case True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(Bit8ValueRoundtripSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0)), valid), H.hex_u32.false_true(valid))
    case False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(Bit8ValueRoundtripSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0)), valid), H.hex_u32.false_true(valid))
    case False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(Bit8ValueRoundtripSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0)), valid), H.hex_u32.false_true(valid))
    case False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(Bit8ValueRoundtripSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0)), valid), H.hex_u32.false_true(valid))
    case False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(Bit8ValueRoundtripSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0)), valid), H.hex_u32.false_true(valid))
    case False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(Bit8ValueRoundtripSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0)), valid), H.hex_u32.false_true(valid))
    case False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(Bit8ValueRoundtripSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0)), valid), H.hex_u32.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(Bit8ValueRoundtripSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0)), valid), H.hex_u32.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(Bit8ValueRoundtripSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0)), valid), H.hex_u32.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(Bit8ValueRoundtripSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0)), valid), H.hex_u32.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(Bit8ValueRoundtripSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0)), valid), H.hex_u32.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(Bit8ValueRoundtripSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0)), valid), H.hex_u32.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(Bit8ValueRoundtripSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0)), valid), H.hex_u32.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(Bit8ValueRoundtripSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0)), valid), H.hex_u32.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _:
      Empty.absurd(Bit8ValueRoundtripSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0)), valid), H.hex_u32.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _:
      Empty.absurd(Bit8ValueRoundtripSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0)), valid), H.hex_u32.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _:
      Empty.absurd(Bit8ValueRoundtripSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0)), valid), H.hex_u32.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _:
      Empty.absurd(Bit8ValueRoundtripSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0)), valid), H.hex_u32.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _:
      Empty.absurd(Bit8ValueRoundtripSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0)), valid), H.hex_u32.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _:
      Empty.absurd(Bit8ValueRoundtripSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0)), valid), H.hex_u32.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _:
      Empty.absurd(Bit8ValueRoundtripSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0)), valid), H.hex_u32.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _:
      Empty.absurd(Bit8ValueRoundtripSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0)), valid), H.hex_u32.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _:
      Empty.absurd(Bit8ValueRoundtripSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0)), valid), H.hex_u32.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{}:
      Empty.absurd(Bit8ValueRoundtripSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0)), valid), H.hex_u32.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{}:
      match b7 b6 b5 b4 b3 b2 b1 b0:
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

def BinaryLaws.bit8_value_bit8_roundtrip(byte, valid):
  match byte:
    case U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      bit8_value_roundtrip_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0, valid)

def Byte2RoundtripSpec(+value: U32,
  -valid: {U32.is_le(value, 65535) == True{} : Bool}) -> Type:
  {B.byte2_u32(B.first(B.u32_byte2(value, valid)),
               B.second(B.u32_byte2(value, valid))) == value : U32}

def byte2_roundtrip_bits(+b31: Bool, +b30: Bool, +b29: Bool, +b28: Bool, +b27: Bool, +b26: Bool, +b25: Bool, +b24: Bool, +b23: Bool, +b22: Bool, +b21: Bool, +b20: Bool, +b19: Bool, +b18: Bool, +b17: Bool, +b16: Bool, +b15: Bool, +b14: Bool, +b13: Bool, +b12: Bool, +b11: Bool, +b10: Bool, +b9: Bool, +b8: Bool, +b7: Bool, +b6: Bool, +b5: Bool, +b4: Bool, +b3: Bool, +b2: Bool, +b1: Bool, +b0: Bool,
  valid: {U32.is_le(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0)), 65535) == True{} : Bool}) -> Byte2RoundtripSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0)), valid):
  match b31 b30 b29 b28 b27 b26 b25 b24 b23 b22 b21 b20 b19 b18 b17 b16:
    case True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(Byte2RoundtripSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0)), valid), H.hex_u32.false_true(valid))
    case False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(Byte2RoundtripSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0)), valid), H.hex_u32.false_true(valid))
    case False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(Byte2RoundtripSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0)), valid), H.hex_u32.false_true(valid))
    case False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(Byte2RoundtripSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0)), valid), H.hex_u32.false_true(valid))
    case False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(Byte2RoundtripSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0)), valid), H.hex_u32.false_true(valid))
    case False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(Byte2RoundtripSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0)), valid), H.hex_u32.false_true(valid))
    case False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _:
      Empty.absurd(Byte2RoundtripSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0)), valid), H.hex_u32.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _:
      Empty.absurd(Byte2RoundtripSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0)), valid), H.hex_u32.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _:
      Empty.absurd(Byte2RoundtripSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0)), valid), H.hex_u32.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _:
      Empty.absurd(Byte2RoundtripSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0)), valid), H.hex_u32.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _:
      Empty.absurd(Byte2RoundtripSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0)), valid), H.hex_u32.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _:
      Empty.absurd(Byte2RoundtripSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0)), valid), H.hex_u32.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _:
      Empty.absurd(Byte2RoundtripSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0)), valid), H.hex_u32.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _:
      Empty.absurd(Byte2RoundtripSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0)), valid), H.hex_u32.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _:
      Empty.absurd(Byte2RoundtripSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0)), valid), H.hex_u32.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{}:
      Empty.absurd(Byte2RoundtripSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0)), valid), H.hex_u32.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{}: {==}

def BinaryLaws.u32_byte2_roundtrip(value, valid):
  match value:
    case U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      byte2_roundtrip_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0, valid)

def BinaryLaws.byte2_examples():
  ({==}, {==}, {==}, {==})


def Utf8EncodeTwoSpec(+cp: U32,
  -valid: {UTF8.can_encode_as_two_bytes(cp) == True{} : Bool}) -> Type:
  {Some{UTF8.encode_as_two_bytes(cp, valid)} == Laws.two_byte_shape(cp) : Maybe<&1, U32 & U32>}

def utf8_proof.table_pair(+low: Word(6n), +high: Word(5n),
  -valid: {UTF8.can_encode_as_two_bytes(utf8_proof.codepoint(low, high)) == True{} : Bool}) ->
  {UTF8.encode_as_two_bytes(utf8_proof.codepoint(low, high), valid) ==
    (utf8_proof.first_byte(high), utf8_proof.second_byte(low)) : U32 & U32}:
  match low high:
    case WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WNil{}}}}}}} WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WNil{}}}}}}:
      %utf8_proof.encode_first(low, high, valid) :
        {UTF8.encode_as_two_bytes(utf8_proof.codepoint(low, high), valid) == (_, utf8_proof.second_byte(low)) : U32 & U32}
      %utf8_proof.encode_second(low, high, valid) :
        {UTF8.encode_as_two_bytes(utf8_proof.codepoint(low, high), valid) == (B.first(UTF8.encode_as_two_bytes(utf8_proof.codepoint(low, high), valid)), _) : U32 & U32}
      {==}

def utf8_proof.encode_as_two_bytes_bits(+b31: Bool, +b30: Bool, +b29: Bool, +b28: Bool, +b27: Bool, +b26: Bool, +b25: Bool, +b24: Bool, +b23: Bool, +b22: Bool, +b21: Bool, +b20: Bool, +b19: Bool, +b18: Bool, +b17: Bool, +b16: Bool, +b15: Bool, +b14: Bool, +b13: Bool, +b12: Bool, +b11: Bool, +b10: Bool, +b9: Bool, +b8: Bool, +b7: Bool, +b6: Bool, +b5: Bool, +b4: Bool, +b3: Bool, +b2: Bool, +b1: Bool, +b0: Bool,
  valid: {UTF8.can_encode_as_two_bytes(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))) == True{} : Bool}) -> Utf8EncodeTwoSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0)), valid):
  match b31 b30 b29 b28 b27 b26 b25 b24 b23 b22 b21 b20 b19 b18 b17 b16 b15 b14 b13 b12 b11:
    case True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(Utf8EncodeTwoSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0)), valid), H.hex_u32.false_true(valid))
    case False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(Utf8EncodeTwoSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0)), valid), H.hex_u32.false_true(valid))
    case False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(Utf8EncodeTwoSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0)), valid), H.hex_u32.false_true(valid))
    case False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(Utf8EncodeTwoSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0)), valid), H.hex_u32.false_true(valid))
    case False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(Utf8EncodeTwoSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0)), valid), H.hex_u32.false_true(valid))
    case False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(Utf8EncodeTwoSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0)), valid), H.hex_u32.false_true(valid))
    case False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(Utf8EncodeTwoSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0)), valid), H.hex_u32.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(Utf8EncodeTwoSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0)), valid), H.hex_u32.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(Utf8EncodeTwoSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0)), valid), H.hex_u32.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(Utf8EncodeTwoSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0)), valid), H.hex_u32.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(Utf8EncodeTwoSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0)), valid), H.hex_u32.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _:
      Empty.absurd(Utf8EncodeTwoSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0)), valid), H.hex_u32.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _:
      Empty.absurd(Utf8EncodeTwoSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0)), valid), H.hex_u32.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _:
      Empty.absurd(Utf8EncodeTwoSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0)), valid), H.hex_u32.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _:
      Empty.absurd(Utf8EncodeTwoSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0)), valid), H.hex_u32.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _:
      Empty.absurd(Utf8EncodeTwoSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0)), valid), H.hex_u32.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _:
      Empty.absurd(Utf8EncodeTwoSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0)), valid), H.hex_u32.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _:
      Empty.absurd(Utf8EncodeTwoSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0)), valid), H.hex_u32.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _:
      Empty.absurd(Utf8EncodeTwoSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0)), valid), H.hex_u32.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _:
      Empty.absurd(Utf8EncodeTwoSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0)), valid), H.hex_u32.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{}:
      Empty.absurd(Utf8EncodeTwoSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0)), valid), H.hex_u32.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{}:
      Equal.cong(U32 & U32, Maybe<&1, U32 & U32>, bytes => Some{bytes},
        UTF8.encode_as_two_bytes(utf8_proof.codepoint(WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WNil{}}}}}}}, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WNil{}}}}}}), utf8_proof.capacity_bits(b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0)),
        (utf8_proof.first_byte(WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WNil{}}}}}}), utf8_proof.second_byte(WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WNil{}}}}}}})),
        utf8_proof.table_pair(WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WNil{}}}}}}}, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WNil{}}}}}}, utf8_proof.capacity_bits(b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0)))

def Laws.utf8_encode_as_two_bytes(cp, valid):
  match cp:
    case U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      utf8_proof.encode_as_two_bytes_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0, valid)

def bool_and_left_true(+left: Bool, -right: Bool, valid: {Bool.and(left, right) == True{} : Bool}) ->
  {left == True{} : Bool}:
  match left:
    case False{}: valid
    case True{}: {==}

def bool_and_right_true(left: Bool, -right: Bool, valid: {Bool.and(left, right) == True{} : Bool}) ->
  {right == True{} : Bool}:
  match left:
    case False{}: Empty.absurd({right == True{} : Bool}, H.hex_u32.false_true(valid))
    case True{}: valid

# Clear an arbitrary low field without enumerating its possible values.
def word_mask_high(n: Nat, +low: Word(n), m: Nat, +high: Word(m), +mask: Word(m)) ->
  {Word.and(Nat.add(n, m), word_join(n, low, m, high), word_join(n, Word.zero(n), m, mask)) ==
    word_join(n, Word.zero(n), m, Word.and(m, high, mask)) : Word(Nat.add(n, m))}:
  match n:
    case 0n: {==}
    case 1n+p:
      match low:
        case WCon{False{}, rest}:
          Equal.cong(Word(Nat.add(p, m)), Word(1n+Nat.add(p, m)), w => WCon{False{}, w},
            Word.and(Nat.add(p, m), word_join(p, rest, m, high), word_join(p, Word.zero(p), m, mask)),
            word_join(p, Word.zero(p), m, Word.and(m, high, mask)),
            word_mask_high(p, rest, m, high, mask))
        case WCon{True{}, rest}:
          Equal.cong(Word(Nat.add(p, m)), Word(1n+Nat.add(p, m)), w => WCon{False{}, w},
            Word.and(Nat.add(p, m), word_join(p, rest, m, high), word_join(p, Word.zero(p), m, mask)),
            word_join(p, Word.zero(p), m, Word.and(m, high, mask)),
            word_mask_high(p, rest, m, high, mask))

def utf8_proof.first_prefix(low: Word(5n), +p7: Bool, +p6: Bool, +p5: Bool) -> U32:
  U32{word_join(5n, low, 27n, WCon{p5, WCon{p6, WCon{p7, Word.zero(24n)}}})}

def utf8_proof.first_mask_parts(+byte: U32, m128: U32, m64: U32, m32: U32) -> Bool:
  Bool.and(U32.is_le(byte, 255), Bool.and(U32.is_eq(m128, 128), Bool.and(U32.is_eq(m64, 64), Bool.and(Bool.or(U32.is_eq(m32, 0), False{}), True{}))))

def utf8_proof.first_prefix_checks(+low: Word(5n), +p7: Bool, +p6: Bool, +p5: Bool) ->
  {utf8_proof.first_mask_parts(utf8_proof.first_prefix(low, p7, p6, p5), U32{word_join(5n, Word.zero(5n), 27n, Word.and(27n, WCon{p5, WCon{p6, WCon{p7, Word.zero(24n)}}}, WCon{False{}, WCon{False{}, WCon{True{}, Word.zero(24n)}}}))}, U32{word_join(5n, Word.zero(5n), 27n, Word.and(27n, WCon{p5, WCon{p6, WCon{p7, Word.zero(24n)}}}, WCon{False{}, WCon{True{}, WCon{False{}, Word.zero(24n)}}}))}, U32{word_join(5n, Word.zero(5n), 27n, Word.and(27n, WCon{p5, WCon{p6, WCon{p7, Word.zero(24n)}}}, WCon{True{}, WCon{False{}, WCon{False{}, Word.zero(24n)}}}))}) == Bool.and(U32.is_le(utf8_proof.first_prefix(low, p7, p6, p5), 255), Bool.and(p7, Bool.and(p6, Bool.not(p5)))) : Bool}:
  match p7 p6 p5:
    case False{} False{} False{}: {==}
    case False{} False{} True{}: {==}
    case False{} True{} False{}: {==}
    case False{} True{} True{}: {==}
    case True{} False{} False{}: {==}
    case True{} False{} True{}: {==}
    case True{} True{} False{}: {==}
    case True{} True{} True{}: {==}

def utf8_proof.first_prefix_mask(+low: Word(5n), +p7: Bool, +p6: Bool, +p5: Bool) ->
  {B.byte_mask("110xxxxx", utf8_proof.first_prefix(low, p7, p6, p5), {==}) == Bool.and(U32.is_le(utf8_proof.first_prefix(low, p7, p6, p5), 255), Bool.and(p7, Bool.and(p6, Bool.not(p5)))) : Bool}:
  %Equal.sym(U32, U32.and(utf8_proof.first_prefix(low, p7, p6, p5), 128), U32{word_join(5n, Word.zero(5n), 27n, Word.and(27n, WCon{p5, WCon{p6, WCon{p7, Word.zero(24n)}}}, WCon{False{}, WCon{False{}, WCon{True{}, Word.zero(24n)}}}))},
    Equal.cong(Word(32n), U32, w => U32{w},
      Word.and(32n, word_join(5n, low, 27n, WCon{p5, WCon{p6, WCon{p7, Word.zero(24n)}}}), word_join(5n, Word.zero(5n), 27n, WCon{False{}, WCon{False{}, WCon{True{}, Word.zero(24n)}}})),
      word_join(5n, Word.zero(5n), 27n, Word.and(27n, WCon{p5, WCon{p6, WCon{p7, Word.zero(24n)}}}, WCon{False{}, WCon{False{}, WCon{True{}, Word.zero(24n)}}})),
      word_mask_high(5n, low, 27n, WCon{p5, WCon{p6, WCon{p7, Word.zero(24n)}}}, WCon{False{}, WCon{False{}, WCon{True{}, Word.zero(24n)}}}))) : {utf8_proof.first_mask_parts(utf8_proof.first_prefix(low, p7, p6, p5), _, U32.and(utf8_proof.first_prefix(low, p7, p6, p5), 64), U32.and(utf8_proof.first_prefix(low, p7, p6, p5), 32)) == Bool.and(U32.is_le(utf8_proof.first_prefix(low, p7, p6, p5), 255), Bool.and(p7, Bool.and(p6, Bool.not(p5)))) : Bool}
  %Equal.sym(U32, U32.and(utf8_proof.first_prefix(low, p7, p6, p5), 64), U32{word_join(5n, Word.zero(5n), 27n, Word.and(27n, WCon{p5, WCon{p6, WCon{p7, Word.zero(24n)}}}, WCon{False{}, WCon{True{}, WCon{False{}, Word.zero(24n)}}}))},
    Equal.cong(Word(32n), U32, w => U32{w},
      Word.and(32n, word_join(5n, low, 27n, WCon{p5, WCon{p6, WCon{p7, Word.zero(24n)}}}), word_join(5n, Word.zero(5n), 27n, WCon{False{}, WCon{True{}, WCon{False{}, Word.zero(24n)}}})),
      word_join(5n, Word.zero(5n), 27n, Word.and(27n, WCon{p5, WCon{p6, WCon{p7, Word.zero(24n)}}}, WCon{False{}, WCon{True{}, WCon{False{}, Word.zero(24n)}}})),
      word_mask_high(5n, low, 27n, WCon{p5, WCon{p6, WCon{p7, Word.zero(24n)}}}, WCon{False{}, WCon{True{}, WCon{False{}, Word.zero(24n)}}}))) : {utf8_proof.first_mask_parts(utf8_proof.first_prefix(low, p7, p6, p5), U32{word_join(5n, Word.zero(5n), 27n, Word.and(27n, WCon{p5, WCon{p6, WCon{p7, Word.zero(24n)}}}, WCon{False{}, WCon{False{}, WCon{True{}, Word.zero(24n)}}}))}, _, U32.and(utf8_proof.first_prefix(low, p7, p6, p5), 32)) == Bool.and(U32.is_le(utf8_proof.first_prefix(low, p7, p6, p5), 255), Bool.and(p7, Bool.and(p6, Bool.not(p5)))) : Bool}
  %Equal.sym(U32, U32.and(utf8_proof.first_prefix(low, p7, p6, p5), 32), U32{word_join(5n, Word.zero(5n), 27n, Word.and(27n, WCon{p5, WCon{p6, WCon{p7, Word.zero(24n)}}}, WCon{True{}, WCon{False{}, WCon{False{}, Word.zero(24n)}}}))},
    Equal.cong(Word(32n), U32, w => U32{w},
      Word.and(32n, word_join(5n, low, 27n, WCon{p5, WCon{p6, WCon{p7, Word.zero(24n)}}}), word_join(5n, Word.zero(5n), 27n, WCon{True{}, WCon{False{}, WCon{False{}, Word.zero(24n)}}})),
      word_join(5n, Word.zero(5n), 27n, Word.and(27n, WCon{p5, WCon{p6, WCon{p7, Word.zero(24n)}}}, WCon{True{}, WCon{False{}, WCon{False{}, Word.zero(24n)}}})),
      word_mask_high(5n, low, 27n, WCon{p5, WCon{p6, WCon{p7, Word.zero(24n)}}}, WCon{True{}, WCon{False{}, WCon{False{}, Word.zero(24n)}}}))) : {utf8_proof.first_mask_parts(utf8_proof.first_prefix(low, p7, p6, p5), U32{word_join(5n, Word.zero(5n), 27n, Word.and(27n, WCon{p5, WCon{p6, WCon{p7, Word.zero(24n)}}}, WCon{False{}, WCon{False{}, WCon{True{}, Word.zero(24n)}}}))}, U32{word_join(5n, Word.zero(5n), 27n, Word.and(27n, WCon{p5, WCon{p6, WCon{p7, Word.zero(24n)}}}, WCon{False{}, WCon{True{}, WCon{False{}, Word.zero(24n)}}}))}, _) == Bool.and(U32.is_le(utf8_proof.first_prefix(low, p7, p6, p5), 255), Bool.and(p7, Bool.and(p6, Bool.not(p5)))) : Bool}
  utf8_proof.first_prefix_checks(low, p7, p6, p5)

def utf8_proof.first_prefix_payload(+low: Word(5n), +p7: Bool, +p6: Bool, +p5: Bool, valid: {Bool.and(p7, Bool.and(p6, Bool.not(p5))) == True{} : Bool}) ->
  Exists(Word(5n), payload => {utf8_proof.first_prefix(low, p7, p6, p5) == utf8_proof.first_byte(payload) : U32}):
  match p7 p6 p5:
    case False{} False{} False{}:
      Empty.absurd(Exists(Word(5n), payload => {utf8_proof.first_prefix(low, p7, p6, p5) == utf8_proof.first_byte(payload) : U32}), H.hex_u32.false_true(valid))
    case False{} False{} True{}:
      Empty.absurd(Exists(Word(5n), payload => {utf8_proof.first_prefix(low, p7, p6, p5) == utf8_proof.first_byte(payload) : U32}), H.hex_u32.false_true(valid))
    case False{} True{} False{}:
      Empty.absurd(Exists(Word(5n), payload => {utf8_proof.first_prefix(low, p7, p6, p5) == utf8_proof.first_byte(payload) : U32}), H.hex_u32.false_true(valid))
    case False{} True{} True{}:
      Empty.absurd(Exists(Word(5n), payload => {utf8_proof.first_prefix(low, p7, p6, p5) == utf8_proof.first_byte(payload) : U32}), H.hex_u32.false_true(valid))
    case True{} False{} False{}:
      Empty.absurd(Exists(Word(5n), payload => {utf8_proof.first_prefix(low, p7, p6, p5) == utf8_proof.first_byte(payload) : U32}), H.hex_u32.false_true(valid))
    case True{} False{} True{}:
      Empty.absurd(Exists(Word(5n), payload => {utf8_proof.first_prefix(low, p7, p6, p5) == utf8_proof.first_byte(payload) : U32}), H.hex_u32.false_true(valid))
    case True{} True{} False{}:
      (low, {==})
    case True{} True{} True{}:
      Empty.absurd(Exists(Word(5n), payload => {utf8_proof.first_prefix(low, p7, p6, p5) == utf8_proof.first_byte(payload) : U32}), H.hex_u32.false_true(valid))

def utf8_proof.first_payload_bits(+low: Word(5n), +p7: Bool, +p6: Bool, +p5: Bool,
  valid: {B.byte_mask("110xxxxx", utf8_proof.first_prefix(low, p7, p6, p5), {==}) == True{} : Bool}) -> Exists(Word(5n), payload => {utf8_proof.first_prefix(low, p7, p6, p5) == utf8_proof.first_byte(payload) : U32}):
  utf8_proof.first_prefix_payload(low, p7, p6, p5,
    bool_and_right_true(U32.is_le(utf8_proof.first_prefix(low, p7, p6, p5), 255), Bool.and(p7, Bool.and(p6, Bool.not(p5))),
      Equal.trans(Bool, Bool.and(U32.is_le(utf8_proof.first_prefix(low, p7, p6, p5), 255), Bool.and(p7, Bool.and(p6, Bool.not(p5)))), B.byte_mask("110xxxxx", utf8_proof.first_prefix(low, p7, p6, p5), {==}), True{},
        Equal.sym(Bool, B.byte_mask("110xxxxx", utf8_proof.first_prefix(low, p7, p6, p5), {==}), Bool.and(U32.is_le(utf8_proof.first_prefix(low, p7, p6, p5), 255), Bool.and(p7, Bool.and(p6, Bool.not(p5)))),
          utf8_proof.first_prefix_mask(low, p7, p6, p5)), valid)))

def utf8_proof.first_payload_tuple(bits: Defs.Bit8(),
  valid: {B.byte_mask("110xxxxx", B.bit8_value(bits), {==}) == True{} : Bool}) ->
  Exists(Word(5n), payload => {B.bit8_value(bits) == utf8_proof.first_byte(payload) : U32}):
  match bits:
    case (b7, b6, b5, b4, b3, b2, b1, b0):
      utf8_proof.first_payload_bits(WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WNil{}}}}}}, b7, b6, b5, valid)

def utf8_proof.first_payload_finish(+byte: U32, -converted: U32,
  equal: {converted == byte : U32},
  result: Exists(Word(5n), payload => {converted == utf8_proof.first_byte(payload) : U32})) ->
  Exists(Word(5n), payload => {byte == utf8_proof.first_byte(payload) : U32}):
  (payload, matches) = result
  (payload, Equal.trans(U32, byte, converted, utf8_proof.first_byte(payload),
    Equal.sym(U32, converted, byte, equal), matches))

def utf8_proof.first_payload(+byte: U32,
  +valid: {B.byte_mask("110xxxxx", byte, {==}) == True{} : Bool}) ->
  Exists(Word(5n), payload => {byte == utf8_proof.first_byte(payload) : U32}):
  +bounded = bool_and_left_true(U32.is_le(byte, 255), Bool.and(B.byte_mask.bit('1', byte, 128), Bool.and(B.byte_mask.bit('1', byte, 64), Bool.and(B.byte_mask.bit('0', byte, 32), True{}))), valid)
  +equal = BinaryLaws.bit8_value_bit8_roundtrip(byte, bounded)
  result = utf8_proof.first_payload_tuple(B.bit8(byte, bounded),
    Equal.trans(Bool, B.byte_mask("110xxxxx", B.bit8_value(B.bit8(byte, bounded)), {==}),
      B.byte_mask("110xxxxx", byte, {==}), True{},
      Equal.cong(U32, Bool, x => B.byte_mask("110xxxxx", x, {==}),
        B.bit8_value(B.bit8(byte, bounded)), byte, equal), valid))
  utf8_proof.first_payload_finish(byte, B.bit8_value(B.bit8(byte, bounded)), equal, result)

def utf8_proof.second_prefix(low: Word(6n), +p7: Bool, +p6: Bool) -> U32:
  U32{word_join(6n, low, 26n, WCon{p6, WCon{p7, Word.zero(24n)}})}

def utf8_proof.second_mask_parts(+byte: U32, m128: U32, m64: U32) -> Bool:
  Bool.and(U32.is_le(byte, 255), Bool.and(U32.is_eq(m128, 128), Bool.and(Bool.or(U32.is_eq(m64, 0), False{}), True{})))

def utf8_proof.second_prefix_checks(+low: Word(6n), +p7: Bool, +p6: Bool) ->
  {utf8_proof.second_mask_parts(utf8_proof.second_prefix(low, p7, p6), U32{word_join(6n, Word.zero(6n), 26n, Word.and(26n, WCon{p6, WCon{p7, Word.zero(24n)}}, WCon{False{}, WCon{True{}, Word.zero(24n)}}))}, U32{word_join(6n, Word.zero(6n), 26n, Word.and(26n, WCon{p6, WCon{p7, Word.zero(24n)}}, WCon{True{}, WCon{False{}, Word.zero(24n)}}))}) == Bool.and(U32.is_le(utf8_proof.second_prefix(low, p7, p6), 255), Bool.and(p7, Bool.not(p6))) : Bool}:
  match p7 p6:
    case False{} False{}: {==}
    case False{} True{}: {==}
    case True{} False{}: {==}
    case True{} True{}: {==}

def utf8_proof.second_prefix_mask(+low: Word(6n), +p7: Bool, +p6: Bool) ->
  {B.byte_mask("10xxxxxx", utf8_proof.second_prefix(low, p7, p6), {==}) == Bool.and(U32.is_le(utf8_proof.second_prefix(low, p7, p6), 255), Bool.and(p7, Bool.not(p6))) : Bool}:
  %Equal.sym(U32, U32.and(utf8_proof.second_prefix(low, p7, p6), 128), U32{word_join(6n, Word.zero(6n), 26n, Word.and(26n, WCon{p6, WCon{p7, Word.zero(24n)}}, WCon{False{}, WCon{True{}, Word.zero(24n)}}))},
    Equal.cong(Word(32n), U32, w => U32{w},
      Word.and(32n, word_join(6n, low, 26n, WCon{p6, WCon{p7, Word.zero(24n)}}), word_join(6n, Word.zero(6n), 26n, WCon{False{}, WCon{True{}, Word.zero(24n)}})),
      word_join(6n, Word.zero(6n), 26n, Word.and(26n, WCon{p6, WCon{p7, Word.zero(24n)}}, WCon{False{}, WCon{True{}, Word.zero(24n)}})),
      word_mask_high(6n, low, 26n, WCon{p6, WCon{p7, Word.zero(24n)}}, WCon{False{}, WCon{True{}, Word.zero(24n)}}))) : {utf8_proof.second_mask_parts(utf8_proof.second_prefix(low, p7, p6), _, U32.and(utf8_proof.second_prefix(low, p7, p6), 64)) == Bool.and(U32.is_le(utf8_proof.second_prefix(low, p7, p6), 255), Bool.and(p7, Bool.not(p6))) : Bool}
  %Equal.sym(U32, U32.and(utf8_proof.second_prefix(low, p7, p6), 64), U32{word_join(6n, Word.zero(6n), 26n, Word.and(26n, WCon{p6, WCon{p7, Word.zero(24n)}}, WCon{True{}, WCon{False{}, Word.zero(24n)}}))},
    Equal.cong(Word(32n), U32, w => U32{w},
      Word.and(32n, word_join(6n, low, 26n, WCon{p6, WCon{p7, Word.zero(24n)}}), word_join(6n, Word.zero(6n), 26n, WCon{True{}, WCon{False{}, Word.zero(24n)}})),
      word_join(6n, Word.zero(6n), 26n, Word.and(26n, WCon{p6, WCon{p7, Word.zero(24n)}}, WCon{True{}, WCon{False{}, Word.zero(24n)}})),
      word_mask_high(6n, low, 26n, WCon{p6, WCon{p7, Word.zero(24n)}}, WCon{True{}, WCon{False{}, Word.zero(24n)}}))) : {utf8_proof.second_mask_parts(utf8_proof.second_prefix(low, p7, p6), U32{word_join(6n, Word.zero(6n), 26n, Word.and(26n, WCon{p6, WCon{p7, Word.zero(24n)}}, WCon{False{}, WCon{True{}, Word.zero(24n)}}))}, _) == Bool.and(U32.is_le(utf8_proof.second_prefix(low, p7, p6), 255), Bool.and(p7, Bool.not(p6))) : Bool}
  utf8_proof.second_prefix_checks(low, p7, p6)

def utf8_proof.second_prefix_payload(+low: Word(6n), +p7: Bool, +p6: Bool, valid: {Bool.and(p7, Bool.not(p6)) == True{} : Bool}) ->
  Exists(Word(6n), payload => {utf8_proof.second_prefix(low, p7, p6) == utf8_proof.second_byte(payload) : U32}):
  match p7 p6:
    case False{} False{}:
      Empty.absurd(Exists(Word(6n), payload => {utf8_proof.second_prefix(low, p7, p6) == utf8_proof.second_byte(payload) : U32}), H.hex_u32.false_true(valid))
    case False{} True{}:
      Empty.absurd(Exists(Word(6n), payload => {utf8_proof.second_prefix(low, p7, p6) == utf8_proof.second_byte(payload) : U32}), H.hex_u32.false_true(valid))
    case True{} False{}:
      (low, {==})
    case True{} True{}:
      Empty.absurd(Exists(Word(6n), payload => {utf8_proof.second_prefix(low, p7, p6) == utf8_proof.second_byte(payload) : U32}), H.hex_u32.false_true(valid))

def utf8_proof.second_payload_bits(+low: Word(6n), +p7: Bool, +p6: Bool,
  valid: {B.byte_mask("10xxxxxx", utf8_proof.second_prefix(low, p7, p6), {==}) == True{} : Bool}) -> Exists(Word(6n), payload => {utf8_proof.second_prefix(low, p7, p6) == utf8_proof.second_byte(payload) : U32}):
  utf8_proof.second_prefix_payload(low, p7, p6,
    bool_and_right_true(U32.is_le(utf8_proof.second_prefix(low, p7, p6), 255), Bool.and(p7, Bool.not(p6)),
      Equal.trans(Bool, Bool.and(U32.is_le(utf8_proof.second_prefix(low, p7, p6), 255), Bool.and(p7, Bool.not(p6))), B.byte_mask("10xxxxxx", utf8_proof.second_prefix(low, p7, p6), {==}), True{},
        Equal.sym(Bool, B.byte_mask("10xxxxxx", utf8_proof.second_prefix(low, p7, p6), {==}), Bool.and(U32.is_le(utf8_proof.second_prefix(low, p7, p6), 255), Bool.and(p7, Bool.not(p6))),
          utf8_proof.second_prefix_mask(low, p7, p6)), valid)))

def utf8_proof.second_payload_tuple(bits: Defs.Bit8(),
  valid: {B.byte_mask("10xxxxxx", B.bit8_value(bits), {==}) == True{} : Bool}) ->
  Exists(Word(6n), payload => {B.bit8_value(bits) == utf8_proof.second_byte(payload) : U32}):
  match bits:
    case (b7, b6, b5, b4, b3, b2, b1, b0):
      utf8_proof.second_payload_bits(WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WNil{}}}}}}}, b7, b6, valid)

def utf8_proof.second_payload_finish(+byte: U32, -converted: U32,
  equal: {converted == byte : U32},
  result: Exists(Word(6n), payload => {converted == utf8_proof.second_byte(payload) : U32})) ->
  Exists(Word(6n), payload => {byte == utf8_proof.second_byte(payload) : U32}):
  (payload, matches) = result
  (payload, Equal.trans(U32, byte, converted, utf8_proof.second_byte(payload),
    Equal.sym(U32, converted, byte, equal), matches))

def utf8_proof.second_payload(+byte: U32,
  +valid: {B.byte_mask("10xxxxxx", byte, {==}) == True{} : Bool}) ->
  Exists(Word(6n), payload => {byte == utf8_proof.second_byte(payload) : U32}):
  +bounded = bool_and_left_true(U32.is_le(byte, 255), Bool.and(B.byte_mask.bit('1', byte, 128), Bool.and(B.byte_mask.bit('0', byte, 64), True{})), valid)
  +equal = BinaryLaws.bit8_value_bit8_roundtrip(byte, bounded)
  result = utf8_proof.second_payload_tuple(B.bit8(byte, bounded),
    Equal.trans(Bool, B.byte_mask("10xxxxxx", B.bit8_value(B.bit8(byte, bounded)), {==}),
      B.byte_mask("10xxxxxx", byte, {==}), True{},
      Equal.cong(U32, Bool, x => B.byte_mask("10xxxxxx", x, {==}),
        B.bit8_value(B.bit8(byte, bounded)), byte, equal), valid))
  utf8_proof.second_payload_finish(byte, B.bit8_value(B.bit8(byte, bounded)), equal, result)

# Reassemble the eleven payload bits into a code-point witness.
def utf8_proof.table_shape(+low: Word(6n), +high: Word(5n)) ->
  {Laws.two_byte_shape(utf8_proof.codepoint(low, high)) ==
    Some{(utf8_proof.first_byte(high), utf8_proof.second_byte(low))} : Maybe<&1, U32 & U32>}:
  match low high:
    case WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WNil{}}}}}}} WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WNil{}}}}}}: {==}

def utf8_proof.table_shape_pair(+low: Word(6n), +high: Word(5n), +b1: U32, +b2: U32,
  first: {b1 == utf8_proof.first_byte(high) : U32},
  second: {b2 == utf8_proof.second_byte(low) : U32}) ->
  {Laws.two_byte_shape(utf8_proof.codepoint(low, high)) == Some{(b1, b2)} : Maybe<&1, U32 & U32>}:
  %Equal.sym(U32, b1, utf8_proof.first_byte(high), first) : {Laws.two_byte_shape(utf8_proof.codepoint(low, high)) == Some{(_, b2)} : Maybe<&1, U32 & U32>}
  %Equal.sym(U32, b2, utf8_proof.second_byte(low), second) : {Laws.two_byte_shape(utf8_proof.codepoint(low, high)) == Some{(utf8_proof.first_byte(high), _)} : Maybe<&1, U32 & U32>}
  utf8_proof.table_shape(low, high)

def Utf8ShapeRepresentation(+b1: U32, +b2: U32) -> Type:
  Exists(U32, cp => {Laws.two_byte_shape(cp) == Some{(b1, b2)} : Maybe<&1, U32 & U32>})

def utf8_proof.shape_witness_fields(+b1: U32, +b2: U32,
  first: Exists(Word(5n), high => {b1 == utf8_proof.first_byte(high) : U32}),
  second: Exists(Word(6n), low => {b2 == utf8_proof.second_byte(low) : U32})) -> Utf8ShapeRepresentation(b1, b2):
  (+high, first_equal) = first
  (+low, second_equal) = second
  (utf8_proof.codepoint(low, high), utf8_proof.table_shape_pair(low, high, b1, b2, first_equal, second_equal))

def utf8_proof.shape_witness(+b1: U32, +b2: U32,
  +accepted: {UTF8.has_two_byte_shape(b1, b2) == True{} : Bool}) -> Utf8ShapeRepresentation(b1, b2):
  utf8_proof.shape_witness_fields(b1, b2,
    utf8_proof.first_payload(b1, bool_and_left_true(B.byte_mask("110xxxxx", b1, {==}), B.byte_mask("10xxxxxx", b2, {==}), accepted)),
    utf8_proof.second_payload(b2, bool_and_right_true(B.byte_mask("110xxxxx", b1, {==}), B.byte_mask("10xxxxxx", b2, {==}), accepted)))

# Every Some produced by the table has an accepted pair.
def utf8_proof.model_shape_accepted(shape: Maybe<&1, U32 & U32>) -> Bool:
  match shape:
    case None{}: False{}
    case Some{(b1, b2)}: UTF8.has_two_byte_shape(b1, b2)

def utf8_proof.model_fields(+low: Word(6n), +high: Word(5n),
  first_facts: {B.byte_mask("110xxxxx", utf8_proof.first_byte(high), {==}) == True{} : Bool} &
  {(U32.is_ge(utf8_proof.first_byte(high), 194) && U32.is_le(utf8_proof.first_byte(high), 223)) == Bool.not(utf8_proof.fits_one_byte(high)) : Bool},
  second_facts: {B.byte_mask("10xxxxxx", utf8_proof.second_byte(low), {==}) == True{} : Bool} &
  {(U32.is_ge(utf8_proof.second_byte(low), 128) && U32.is_le(utf8_proof.second_byte(low), 191)) == True{} : Bool}) ->
  {UTF8.has_two_byte_shape(utf8_proof.first_byte(high), utf8_proof.second_byte(low)) == True{} : Bool}:
  (first, _) = first_facts
  (second, _) = second_facts
  utf8_proof.shape_from_masks(utf8_proof.first_byte(high), utf8_proof.second_byte(low), first, second)

def utf8_proof.model_shape_bits(+b31: Bool, +b30: Bool, +b29: Bool, +b28: Bool, +b27: Bool, +b26: Bool, +b25: Bool, +b24: Bool, +b23: Bool, +b22: Bool, +b21: Bool, +b20: Bool, +b19: Bool, +b18: Bool, +b17: Bool, +b16: Bool, +b15: Bool, +b14: Bool, +b13: Bool, +b12: Bool, +b11: Bool, +b10: Bool, +b9: Bool, +b8: Bool, +b7: Bool, +b6: Bool, +b5: Bool, +b4: Bool, +b3: Bool, +b2: Bool, +b1: Bool, +b0: Bool) ->
  {utf8_proof.model_shape_accepted(Laws.two_byte_shape(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0)))) ==
    Maybe.is_some(&1, U32 & U32, Laws.two_byte_shape(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0)))) : Bool}:
  match b31 b30 b29 b28 b27 b26 b25 b24 b23 b22 b21 b20 b19 b18 b17 b16 b15 b14 b13 b12 b11:
    case True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _: {==}
    case False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _: {==}
    case False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _: {==}
    case False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _: {==}
    case False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _: {==}
    case False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _: {==}
    case False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _: {==}
    case False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _: {==}
    case False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _: {==}
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _: {==}
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _: {==}
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _: {==}
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _: {==}
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _: {==}
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _: {==}
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _: {==}
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _: {==}
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _: {==}
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _: {==}
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _: {==}
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{}: {==}
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{}:
      utf8_proof.model_fields(WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WNil{}}}}}}}, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WNil{}}}}}}, utf8_proof.first_byte_facts(WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WNil{}}}}}}), utf8_proof.second_byte_facts(WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WNil{}}}}}}}))

def utf8_proof.model_shape(cp: U32) ->
  {utf8_proof.model_shape_accepted(Laws.two_byte_shape(cp)) ==
    Maybe.is_some(&1, U32 & U32, Laws.two_byte_shape(cp)) : Bool}:
  match cp:
    case U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      utf8_proof.model_shape_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0)

def utf8_proof.model_pair_accepted(+cp: U32, +b1: U32, +b2: U32,
  +produced: {Laws.two_byte_shape(cp) == Some{(b1, b2)} : Maybe<&1, U32 & U32>}) ->
  {UTF8.has_two_byte_shape(b1, b2) == True{} : Bool}:
  Equal.trans(Bool, UTF8.has_two_byte_shape(b1, b2), utf8_proof.model_shape_accepted(Laws.two_byte_shape(cp)), True{},
    Equal.sym(Bool, utf8_proof.model_shape_accepted(Laws.two_byte_shape(cp)), UTF8.has_two_byte_shape(b1, b2),
      Equal.cong(Maybe<&1, U32 & U32>, Bool, shape => utf8_proof.model_shape_accepted(shape),
        Laws.two_byte_shape(cp), Some{(b1, b2)}, produced)),
    Equal.trans(Bool, utf8_proof.model_shape_accepted(Laws.two_byte_shape(cp)),
      Maybe.is_some(&1, U32 & U32, Laws.two_byte_shape(cp)), True{}, utf8_proof.model_shape(cp),
      Equal.cong(Maybe<&1, U32 & U32>, Bool, shape => Maybe.is_some(&1, U32 & U32, shape),
        Laws.two_byte_shape(cp), Some{(b1, b2)}, produced)))

def utf8_proof.shape_witness_accepted(+b1: U32, +b2: U32, representation: Utf8ShapeRepresentation(b1, b2)) ->
  {UTF8.has_two_byte_shape(b1, b2) == True{} : Bool}:
  (cp, produced) = representation
  utf8_proof.model_pair_accepted(cp, b1, b2, produced)

def Laws.utf8_has_two_byte_shape(b1, b2):
  (accepted => utf8_proof.shape_witness(b1, b2, accepted),
   representation => utf8_proof.shape_witness_accepted(b1, b2, representation))

# Applying the payload calculation to a table result recovers its input.
def utf8_proof.decode_model_result(shape: Maybe<&1, U32 & U32>) -> U32:
  match shape:
    case None{}: 0
    case Some{(b1, b2)}: utf8_proof.decode_payload(b1, b2)

def Utf8ModelDecodeSpec(+cp: U32) -> Type:
  {utf8_proof.decode_model_result(Laws.two_byte_shape(cp)) == cp : U32}

def utf8_proof.decode_model_bits(+b31: Bool, +b30: Bool, +b29: Bool, +b28: Bool, +b27: Bool, +b26: Bool, +b25: Bool, +b24: Bool, +b23: Bool, +b22: Bool, +b21: Bool, +b20: Bool, +b19: Bool, +b18: Bool, +b17: Bool, +b16: Bool, +b15: Bool, +b14: Bool, +b13: Bool, +b12: Bool, +b11: Bool, +b10: Bool, +b9: Bool, +b8: Bool, +b7: Bool, +b6: Bool, +b5: Bool, +b4: Bool, +b3: Bool, +b2: Bool, +b1: Bool, +b0: Bool,
  accepted: {UTF8.can_encode_as_two_bytes(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))) == True{} : Bool}) -> Utf8ModelDecodeSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))):
  match b31 b30 b29 b28 b27 b26 b25 b24 b23 b22 b21 b20 b19 b18 b17 b16 b15 b14 b13 b12 b11:
    case True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(Utf8ModelDecodeSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))), H.hex_u32.false_true(accepted))
    case False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(Utf8ModelDecodeSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))), H.hex_u32.false_true(accepted))
    case False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(Utf8ModelDecodeSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))), H.hex_u32.false_true(accepted))
    case False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(Utf8ModelDecodeSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))), H.hex_u32.false_true(accepted))
    case False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(Utf8ModelDecodeSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))), H.hex_u32.false_true(accepted))
    case False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(Utf8ModelDecodeSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))), H.hex_u32.false_true(accepted))
    case False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(Utf8ModelDecodeSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))), H.hex_u32.false_true(accepted))
    case False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(Utf8ModelDecodeSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))), H.hex_u32.false_true(accepted))
    case False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(Utf8ModelDecodeSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))), H.hex_u32.false_true(accepted))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(Utf8ModelDecodeSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))), H.hex_u32.false_true(accepted))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(Utf8ModelDecodeSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))), H.hex_u32.false_true(accepted))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _:
      Empty.absurd(Utf8ModelDecodeSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))), H.hex_u32.false_true(accepted))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _:
      Empty.absurd(Utf8ModelDecodeSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))), H.hex_u32.false_true(accepted))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _:
      Empty.absurd(Utf8ModelDecodeSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))), H.hex_u32.false_true(accepted))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _:
      Empty.absurd(Utf8ModelDecodeSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))), H.hex_u32.false_true(accepted))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _:
      Empty.absurd(Utf8ModelDecodeSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))), H.hex_u32.false_true(accepted))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _:
      Empty.absurd(Utf8ModelDecodeSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))), H.hex_u32.false_true(accepted))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _:
      Empty.absurd(Utf8ModelDecodeSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))), H.hex_u32.false_true(accepted))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _:
      Empty.absurd(Utf8ModelDecodeSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))), H.hex_u32.false_true(accepted))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _:
      Empty.absurd(Utf8ModelDecodeSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))), H.hex_u32.false_true(accepted))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{}:
      Empty.absurd(Utf8ModelDecodeSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))), H.hex_u32.false_true(accepted))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{}:
      utf8_proof.decode_fields(WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WNil{}}}}}}}, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WNil{}}}}}})

def utf8_proof.decode_model(+cp: U32,
  accepted: {UTF8.can_encode_as_two_bytes(cp) == True{} : Bool}) -> Utf8ModelDecodeSpec(cp):
  match cp:
    case U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      utf8_proof.decode_model_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0, accepted)

# Any code point producing these bytes must equal their decoded payload.
def utf8_proof.decode_model_produced(+cp: U32, +b1: U32, +b2: U32,
  -valid: {UTF8.has_two_byte_shape(b1, b2) == True{} : Bool},
  +produced: {Laws.two_byte_shape(cp) == Some{(b1, b2)} : Maybe<&1, U32 & U32>}) ->
  {UTF8.decode_two_bytes(b1, b2, valid) == cp : U32}:
  accepted = Equal.trans(Bool, UTF8.can_encode_as_two_bytes(cp),
    Maybe.is_some(&1, U32 & U32, Laws.two_byte_shape(cp)), True{}, Laws.utf8_can_encode_as_two_bytes(cp),
    Equal.cong(Maybe<&1, U32 & U32>, Bool, shape => Maybe.is_some(&1, U32 & U32, shape),
      Laws.two_byte_shape(cp), Some{(b1, b2)}, produced))
  Equal.trans(U32, UTF8.decode_two_bytes(b1, b2, valid),
    utf8_proof.decode_model_result(Laws.two_byte_shape(cp)), cp,
    Equal.sym(U32, utf8_proof.decode_model_result(Laws.two_byte_shape(cp)), UTF8.decode_two_bytes(b1, b2, valid),
      Equal.cong(Maybe<&1, U32 & U32>, U32, shape => utf8_proof.decode_model_result(shape),
        Laws.two_byte_shape(cp), Some{(b1, b2)}, produced)),
    utf8_proof.decode_model(cp, accepted))

# The shape law supplies existence; the inverse calculation identifies its witness.
def utf8_proof.decode_result_produced(+cp: U32, +b1: U32, +b2: U32,
  -valid: {UTF8.has_two_byte_shape(b1, b2) == True{} : Bool},
  +produced: {Laws.two_byte_shape(cp) == Some{(b1, b2)} : Maybe<&1, U32 & U32>}) ->
  {Laws.two_byte_shape(UTF8.decode_two_bytes(b1, b2, valid)) == Some{(b1, b2)} : Maybe<&1, U32 & U32>}:
  Equal.trans(Maybe<&1, U32 & U32>, Laws.two_byte_shape(UTF8.decode_two_bytes(b1, b2, valid)),
    Laws.two_byte_shape(cp), Some{(b1, b2)},
    Equal.cong(U32, Maybe<&1, U32 & U32>, value => Laws.two_byte_shape(value),
      UTF8.decode_two_bytes(b1, b2, valid), cp, utf8_proof.decode_model_produced(cp, b1, b2, valid, produced)), produced)

def utf8_proof.decode_result_representation(+b1: U32, +b2: U32,
  -valid: {UTF8.has_two_byte_shape(b1, b2) == True{} : Bool},
  representation: Utf8ShapeRepresentation(b1, b2)) ->
  {Laws.two_byte_shape(UTF8.decode_two_bytes(b1, b2, valid)) == Some{(b1, b2)} : Maybe<&1, U32 & U32>}:
  (cp, produced) = representation
  utf8_proof.decode_result_produced(cp, b1, b2, valid, produced)

def utf8_proof.two_decode_encode(+cp: U32,
  +valid: {UTF8.can_encode_as_two_bytes(cp) == True{} : Bool}) ->
  Exists({UTF8.has_two_byte_shape(B.first(UTF8.encode_as_two_bytes(cp, valid)),
      B.second(UTF8.encode_as_two_bytes(cp, valid))) == True{} : Bool}, shape =>
    {UTF8.decode_two_bytes(B.first(UTF8.encode_as_two_bytes(cp, valid)),
      B.second(UTF8.encode_as_two_bytes(cp, valid)), shape) == cp : U32}):
  +b1 = B.first(UTF8.encode_as_two_bytes(cp, valid))
  +b2 = B.second(UTF8.encode_as_two_bytes(cp, valid))
  +produced = Equal.sym(Maybe<&1, U32 & U32>, Some{UTF8.encode_as_two_bytes(cp, valid)}, Laws.two_byte_shape(cp),
    Laws.utf8_encode_as_two_bytes(cp, valid))
  +shape = utf8_proof.model_pair_accepted(cp, b1, b2, produced)
  (shape, utf8_proof.decode_model_produced(cp, b1, b2, shape, produced))

def utf8_proof.encode_decoded(+b1: U32, +b2: U32,
  -valid: {UTF8.has_two_byte_shape(b1, b2) == True{} : Bool},
  +produced: {Laws.two_byte_shape(UTF8.decode_two_bytes(b1, b2, valid)) == Some{(b1, b2)} : Maybe<&1, U32 & U32>}) ->
  Exists({UTF8.can_encode_as_two_bytes(UTF8.decode_two_bytes(b1, b2, valid)) == True{} : Bool}, accepted =>
    {UTF8.encode_as_two_bytes(UTF8.decode_two_bytes(b1, b2, valid), accepted) == (b1, b2) : U32 & U32}):
  +cp = UTF8.decode_two_bytes(b1, b2, valid)
  +accepted = Equal.trans(Bool, UTF8.can_encode_as_two_bytes(cp),
    Maybe.is_some(&1, U32 & U32, Laws.two_byte_shape(cp)), True{}, Laws.utf8_can_encode_as_two_bytes(cp),
    Equal.cong(Maybe<&1, U32 & U32>, Bool, shape => Maybe.is_some(&1, U32 & U32, shape),
      Laws.two_byte_shape(cp), Some{(b1, b2)}, produced))
  (accepted, Equal.cong(Maybe<&1, U32 & U32>, U32 & U32,
    shape => Maybe.default(&1, U32 & U32, shape, (0, 0)),
    Some{UTF8.encode_as_two_bytes(cp, accepted)}, Some{(b1, b2)},
    Equal.trans(Maybe<&1, U32 & U32>, Some{UTF8.encode_as_two_bytes(cp, accepted)},
      Laws.two_byte_shape(cp), Some{(b1, b2)}, Laws.utf8_encode_as_two_bytes(cp, accepted), produced)))

# Matching the pair exposes its bytes to the two-byte lemmas.
def utf8_proof.two_encode_decode(p: U32 & U32,
  +valid: {UTF8.has_two_byte_shape(B.first(p), B.second(p)) == True{} : Bool}) ->
  Exists({UTF8.can_encode_as_two_bytes(UTF8.decode_two_bytes(B.first(p), B.second(p), valid)) == True{} : Bool}, accepted =>
    {UTF8.encode_as_two_bytes(UTF8.decode_two_bytes(B.first(p), B.second(p), valid), accepted) == p : U32 & U32}):
  match p:
    case (+b1, +b2):
      utf8_proof.encode_decoded(b1, b2, valid,
        utf8_proof.decode_result_representation(b1, b2, valid, utf8_proof.shape_witness(b1, b2, valid)))

def Laws.utf8_two_byte_inverse():
  (cp => +valid => utf8_proof.two_decode_encode(cp, valid),
   p => +valid => utf8_proof.two_encode_decode(p, valid))

# Code points up to 2047 are scalars.  A set high bit contradicts the
# bound.  Otherwise the low eleven bits are split until the range check
# computes.
def utf8_proof.two_capacity_scalar_bits(+b31: Bool, +b30: Bool, +b29: Bool, +b28: Bool, +b27: Bool, +b26: Bool, +b25: Bool, +b24: Bool, +b23: Bool, +b22: Bool, +b21: Bool, +b20: Bool, +b19: Bool, +b18: Bool, +b17: Bool, +b16: Bool, +b15: Bool, +b14: Bool, +b13: Bool, +b12: Bool, +b11: Bool, +b10: Bool, +b9: Bool, +b8: Bool, +b7: Bool, +b6: Bool, +b5: Bool, +b4: Bool, +b3: Bool, +b2: Bool, +b1: Bool, +b0: Bool,
  accepted: {UTF8.can_encode_as_two_bytes(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))) == True{} : Bool}) ->
  {Laws.is_unicode_scalar(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))) == True{} : Bool}:
  match b31 b30 b29 b28 b27 b26 b25 b24 b23 b22 b21 b20 b19 b18 b17 b16 b15 b14 b13 b12 b11:
    case True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd({Laws.is_unicode_scalar(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))) == True{} : Bool}, H.hex_u32.false_true(accepted))
    case False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd({Laws.is_unicode_scalar(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))) == True{} : Bool}, H.hex_u32.false_true(accepted))
    case False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd({Laws.is_unicode_scalar(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))) == True{} : Bool}, H.hex_u32.false_true(accepted))
    case False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd({Laws.is_unicode_scalar(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))) == True{} : Bool}, H.hex_u32.false_true(accepted))
    case False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd({Laws.is_unicode_scalar(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))) == True{} : Bool}, H.hex_u32.false_true(accepted))
    case False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd({Laws.is_unicode_scalar(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))) == True{} : Bool}, H.hex_u32.false_true(accepted))
    case False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd({Laws.is_unicode_scalar(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))) == True{} : Bool}, H.hex_u32.false_true(accepted))
    case False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd({Laws.is_unicode_scalar(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))) == True{} : Bool}, H.hex_u32.false_true(accepted))
    case False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd({Laws.is_unicode_scalar(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))) == True{} : Bool}, H.hex_u32.false_true(accepted))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd({Laws.is_unicode_scalar(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))) == True{} : Bool}, H.hex_u32.false_true(accepted))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _:
      Empty.absurd({Laws.is_unicode_scalar(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))) == True{} : Bool}, H.hex_u32.false_true(accepted))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _:
      Empty.absurd({Laws.is_unicode_scalar(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))) == True{} : Bool}, H.hex_u32.false_true(accepted))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _:
      Empty.absurd({Laws.is_unicode_scalar(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))) == True{} : Bool}, H.hex_u32.false_true(accepted))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _:
      Empty.absurd({Laws.is_unicode_scalar(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))) == True{} : Bool}, H.hex_u32.false_true(accepted))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _:
      Empty.absurd({Laws.is_unicode_scalar(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))) == True{} : Bool}, H.hex_u32.false_true(accepted))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _:
      Empty.absurd({Laws.is_unicode_scalar(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))) == True{} : Bool}, H.hex_u32.false_true(accepted))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _:
      Empty.absurd({Laws.is_unicode_scalar(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))) == True{} : Bool}, H.hex_u32.false_true(accepted))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _:
      Empty.absurd({Laws.is_unicode_scalar(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))) == True{} : Bool}, H.hex_u32.false_true(accepted))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _:
      Empty.absurd({Laws.is_unicode_scalar(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))) == True{} : Bool}, H.hex_u32.false_true(accepted))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _:
      Empty.absurd({Laws.is_unicode_scalar(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))) == True{} : Bool}, H.hex_u32.false_true(accepted))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{}:
      Empty.absurd({Laws.is_unicode_scalar(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))) == True{} : Bool}, H.hex_u32.false_true(accepted))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{}:
      match b10 b9 b8 b7 b6 b5 b4 b3 b2 b1 b0:
        case True{} _ _ _ _ _ _ _ _ _ _: {==}
        case False{} True{} _ _ _ _ _ _ _ _ _: {==}
        case False{} False{} True{} _ _ _ _ _ _ _ _: {==}
        case False{} False{} False{} True{} _ _ _ _ _ _ _: {==}
        case False{} False{} False{} False{} True{} _ _ _ _ _ _: {==}
        case False{} False{} False{} False{} False{} True{} _ _ _ _ _: {==}
        case False{} False{} False{} False{} False{} False{} True{} _ _ _ _: {==}
        case False{} False{} False{} False{} False{} False{} False{} True{} _ _ _: {==}
        case False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _: {==}
        case False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _: {==}
        case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{}: {==}
        case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{}: {==}

def utf8_proof.two_capacity_scalar(+cp: U32,
  accepted: {UTF8.can_encode_as_two_bytes(cp) == True{} : Bool}) ->
  {Laws.is_unicode_scalar(cp) == True{} : Bool}:
  match cp:
    case U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      utf8_proof.two_capacity_scalar_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0, accepted)

def utf8_proof.exists_witness(-A: Type, -P: @-x: A -> Type, e: Exists(A, P)) -> A:
  (x, holds) = e
  x

# The right-inverse half of the bijection law makes the decoded value
# encodable, so it is at most 2047.
def utf8_proof.two_decoded_scalar(+b1: U32, +b2: U32,
  checked: {UTF8.has_two_byte_shape(b1, b2) == True{} : Bool}) ->
  {Laws.is_unicode_scalar(UTF8.decode_two_bytes(b1, b2, checked)) == True{} : Bool}:
  utf8_proof.two_capacity_scalar(UTF8.decode_two_bytes(b1, b2, checked),
    utf8_proof.exists_witness(
      {UTF8.can_encode_as_two_bytes(UTF8.decode_two_bytes(b1, b2, checked)) == True{} : Bool},
      accepted => {UTF8.encode_as_two_bytes(UTF8.decode_two_bytes(b1, b2, checked), accepted) == (b1, b2) : U32 & U32},
      utf8_proof.two_encode_decode((b1, b2), checked)))

# With the scalar check proved True, the specification's conjunction
# reduces to the implementation's overlong test.
def utf8_proof.valid_two_bytes_true(+b1: U32, +b2: U32,
  checked: {UTF8.has_two_byte_shape(b1, b2) == True{} : Bool}) ->
  {Bool.not(UTF8.overlong_two_bytes(b1, b2, checked)) ==
    (Bool.not(UTF8.overlong_two_bytes(b1, b2, checked)) &&
     Laws.is_unicode_scalar(UTF8.decode_two_bytes(b1, b2, checked))) : Bool}:
  +scalar = Equal.sym(Bool, Laws.is_unicode_scalar(UTF8.decode_two_bytes(b1, b2, checked)), True{},
    utf8_proof.two_decoded_scalar(b1, b2, checked))
  %scalar : {Bool.not(UTF8.overlong_two_bytes(b1, b2, checked)) ==
    (Bool.not(UTF8.overlong_two_bytes(b1, b2, checked)) && _) : Bool}
  Equal.sym(Bool, Bool.and(Bool.not(UTF8.overlong_two_bytes(b1, b2, checked)), True{}),
    Bool.not(UTF8.overlong_two_bytes(b1, b2, checked)),
    bool_and_true(Bool.not(UTF8.overlong_two_bytes(b1, b2, checked))))

# Split on the shape the same way the specification does.
def utf8_proof.valid_two_bytes_if(+b1: U32, +b2: U32, shape: Bool,
  checked: {UTF8.has_two_byte_shape(b1, b2) == shape : Bool}) ->
  {UTF8.valid_two_bytes.if(b1, b2, shape, checked) ==
    Laws.valid_two_bytes.if(b1, b2, shape, checked) : Bool}:
  match shape:
    case False{}: {==}
    case True{}: utf8_proof.valid_two_bytes_true(b1, b2, checked)

def Laws.utf8_valid_two_bytes(b1, b2):
  utf8_proof.valid_two_bytes_if(b1, b2, UTF8.has_two_byte_shape(b1, b2), {==})

def BinaryLaws.u32_byte4(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0):
  {==}

def HexLaws.hex_u32(s, valid):
  +accepted = valid
  (accepted, hex_u32_agrees(s, accepted))

def BinaryLaws.byte_mask(mask, byte, valid):
  +accepted = valid
  (accepted, byte_mask_agrees(mask, byte, accepted))

def BinaryLaws.bit8_value(b7, b6, b5, b4, b3, b2, b1, b0):
  match b7 b6 b5 b4 b3 b2 b1 b0:
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

# Shifting in a low bit commutes with incrementing the remaining bits.
def word_put_inc_false(n: Nat, +bits: Word(n)) ->
  {Word.inc(n, Word.shl.put(n, False{}, bits)) == Word.shl.put(n, True{}, bits) : Word(n)}:
  match n:
    case 0n: {==}
    case 1n+p:
      match bits:
        case WCon{b, rest}: {==}

def word_put_inc_true(n: Nat, +bits: Word(n)) ->
  {Word.inc(n, Word.shl.put(n, True{}, bits)) == Word.shl.put(n, False{}, Word.inc(n, bits)) : Word(n)}:
  match n:
    case 0n: {==}
    case 1n+p:
      match bits:
        case WCon{False{}, rest}:
          Equal.cong(Word(p), Word(1n+p), w => WCon{False{}, w},
            Word.inc(p, Word.shl.put(p, False{}, rest)), Word.shl.put(p, True{}, rest),
            word_put_inc_false(p, rest))
        case WCon{True{}, rest}:
          Equal.cong(Word(p), Word(1n+p), w => WCon{False{}, w},
            Word.inc(p, Word.shl.put(p, True{}, rest)), Word.shl.put(p, False{}, Word.inc(p, rest)),
            word_put_inc_true(p, rest))

def word_shift_inc(n: Nat, +bits: Word(n)) ->
  {Word.inc(n, Word.inc(n, Word.shl(n, bits))) == Word.shl(n, Word.inc(n, bits)) : Word(n)}:
  match n:
    case 0n: {==}
    case 1n+p:
      match bits:
        case WCon{False{}, rest}:
          Equal.cong(Word(p), Word(1n+p), w => WCon{False{}, w},
            Word.inc(p, Word.shl.put(p, False{}, rest)), Word.shl.put(p, True{}, rest),
            word_put_inc_false(p, rest))
        case WCon{True{}, rest}:
          Equal.cong(Word(p), Word(1n+p), w => WCon{False{}, w},
            Word.inc(p, Word.shl.put(p, True{}, rest)), Word.shl.put(p, False{}, Word.inc(p, rest)),
            word_put_inc_true(p, rest))

def u32_shift_inc(+value: U32) ->
  {U32.inc(U32.inc(U32.shl(value))) == U32.shl(U32.inc(value)) : U32}:
  match value:
    case U32{bits}:
      Equal.cong(Word(32n), U32, w => U32{w},
        Word.inc(32n, Word.inc(32n, Word.shl(32n, bits))), Word.shl(32n, Word.inc(32n, bits)),
        word_shift_inc(32n, bits))

# Convert a doubled Nat without expanding it into individual successors.
def u32_from_nat_double(+n: Nat) ->
  {U32.from_nat(Nat.double(n)) == U32.shl(U32.from_nat(n)) : U32}:
  match n:
    case 0n: {==}
    case 1n+p:
      %u32_shift_inc(U32.from_nat(p)) : {U32.inc(U32.inc(U32.from_nat(Nat.double(p)))) == _ : U32}
      Equal.cong(U32, U32, x => U32.inc(U32.inc(x)),
        U32.from_nat(Nat.double(p)), U32.shl(U32.from_nat(p)),
        u32_from_nat_double(p))

# Prepend a low bit, dropping any bit above the U32 width.
def u32_prepend(bit: Bool, value: U32) -> U32:
  match value:
    case U32{bits}: U32{Word.shl.put(32n, bit, bits)}

def u32_prepend_false(+value: U32) ->
  {U32.shl(value) == u32_prepend(False{}, value) : U32}:
  match value:
    case U32{WCon{b, rest}}: {==}

def u32_prepend_true(+value: U32) ->
  {U32.inc(U32.shl(value)) == u32_prepend(True{}, value) : U32}:
  match value:
    case U32{WCon{b, rest}}: {==}

def word_to_u32(n: Nat, bits: Word(n)) -> U32:
  match n:
    case 0n: 0
    case 1n+p:
      match bits:
        case WCon{b, rest}: u32_prepend(b, word_to_u32(p, rest))

def word_to_u32_from_nat(+n: Nat, +bits: Word(n)) ->
  {U32.from_nat(Word.to_nat(n, bits)) == word_to_u32(n, bits) : U32}:
  match n:
    case 0n: {==}
    case 1n+p:
      match bits:
        case WCon{False{}, rest}:
          %word_to_u32_from_nat(p, rest) : {U32.from_nat(Nat.double(Word.to_nat(p, rest))) == u32_prepend(False{}, _) : U32}
          %u32_prepend_false(U32.from_nat(Word.to_nat(p, rest))) : {U32.from_nat(Nat.double(Word.to_nat(p, rest))) == _ : U32}
          u32_from_nat_double(Word.to_nat(p, rest))
        case WCon{True{}, rest}:
          %word_to_u32_from_nat(p, rest) : {U32.inc(U32.from_nat(Nat.double(Word.to_nat(p, rest)))) == u32_prepend(True{}, _) : U32}
          %u32_prepend_true(U32.from_nat(Word.to_nat(p, rest))) : {U32.inc(U32.from_nat(Nat.double(Word.to_nat(p, rest)))) == _ : U32}
          Equal.cong(U32, U32, x => U32.inc(x),
            U32.from_nat(Nat.double(Word.to_nat(p, rest))), U32.shl(U32.from_nat(Word.to_nat(p, rest))),
            u32_from_nat_double(Word.to_nat(p, rest)))

def BinaryLaws.bit8_value_word(b7, b6, b5, b4, b3, b2, b1, b0):
  word = {WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WNil{}}}}}}}}} : Word(8n)}
  Equal.sym(U32, U32.from_nat(Word.to_nat(8n, word)), word_to_u32(8n, word),
    word_to_u32_from_nat(8n, word))

def BinaryLaws.u32_byte2(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0, valid):
  {==}

def BinaryLaws.byte2_u32(h7, h6, h5, h4, h3, h2, h1, h0, l7, l6, l5, l4, l3, l2, l1, l0, rest_high, rest_low):
  {==}

def BinaryLaws.first(high, low):
  {==}

def BinaryLaws.second(high, low):
  {==}

def StrbyteSpec(+s: String) -> Type:
  Exists({B.valid_byte_string(s) == True{} : Bool}, accepted =>
  Exists(Defs.Bit8(), bits =>
    {Some{bits} == BinaryLaws.str_bit8(s) : Maybe<&1, Defs.Bit8()>} &
    {B.strbyte(s, accepted) == B.bit8_value(bits) : U32}))

def strbyte.parsed(+valid: Bool, bits: Defs.Bit8(),
  evidence: {valid == True{} : Bool}) ->
  {Some{bits} == BinaryLaws.str_bit8.if(valid, bits) : Maybe<&1, Defs.Bit8()>}:
  Equal.cong(Bool, Maybe<&1, Defs.Bit8()>, hit => BinaryLaws.str_bit8.if(hit, bits),
    True{}, valid, Equal.sym(Bool, valid, True{}, evidence))

# Shifting an accumulator and adding a bit inserts that bit without a carry.
def u32_shift_add_bit(+value: U32, +bit: Bool) ->
  {(U32.shl(value) + Bool.to_u32(bit) : U32) == u32_prepend(bit, value) : U32}:
  match value:
    case U32{WCon{b, rest}}:
      match bit:
        case False{}:
          Equal.cong(Word(32n), U32, w => U32{w},
            Word.add(32n, Word.shl(32n, WCon{b, rest}), Word.zero(32n)), Word.shl(32n, WCon{b, rest}),
            word_add_zero(32n, Word.shl(32n, WCon{b, rest})))
        case True{}:
          Equal.cong(Word(32n), U32, w => U32{w},
            Word.add(32n, word_join(1n, WCon{False{}, WNil{}}, 31n, Word.shl.put(31n, b, rest)),
              word_join(1n, WCon{True{}, WNil{}}, 31n, Word.zero(31n))),
            word_join(1n, WCon{True{}, WNil{}}, 31n, Word.shl.put(31n, b, rest)),
            word_add_fields(1n, WCon{True{}, WNil{}}, 31n, Word.shl.put(31n, b, rest)))

def strbyte_fold_value(bits: +List<Bool>, value: U32) -> U32:
  match bits:
    case Nil{}: value
    case Con{bit, rest}: strbyte_fold_value(rest, u32_prepend(bit, value))

def strbyte_fold_prepend(+bits: +List<Bool>, +value: U32) ->
  {B.strbyte.fold_bits(bits, value) == strbyte_fold_value(bits, value) : U32}:
  match bits:
    case Nil{}: {==}
    case Con{bit, rest}:
      %strbyte_fold_prepend(rest, u32_prepend(bit, value)) : {B.strbyte.fold_bits(rest, (U32.shl(value) + Bool.to_u32(bit) : U32)) == _ : U32}
      Equal.cong(U32, U32, acc => B.strbyte.fold_bits(rest, acc),
        (U32.shl(value) + Bool.to_u32(bit) : U32), u32_prepend(bit, value),
        u32_shift_add_bit(value, bit))

def strbyte_injective.fold_bits(+b1: Bool, +b2: Bool, +b3: Bool, +b4: Bool, +b5: Bool, +b6: Bool, +b7: Bool, +b8: Bool) ->
  {B.strbyte.fold_bits([b1, b2, b3, b4, b5, b6, b7, b8], 0) == B.bit8_value((b1, b2, b3, b4, b5, b6, b7, b8)) : U32}:
  strbyte_fold_prepend([b1, b2, b3, b4, b5, b6, b7, b8], 0)

def BinaryLaws.strbyte(s, valid):
  match s:
    case SNil{}:
      Empty.absurd(StrbyteSpec(SNil{}), H.hex_u32.false_true(valid))
    case SCon{c1, SNil{}}:
      Empty.absurd(StrbyteSpec(SCon{c1, SNil{}}), H.hex_u32.false_true(valid))
    case SCon{c1, SCon{c2, SNil{}}}:
      Empty.absurd(StrbyteSpec(SCon{c1, SCon{c2, SNil{}}}), H.hex_u32.false_true(valid))
    case SCon{c1, SCon{c2, SCon{c3, SNil{}}}}:
      Empty.absurd(StrbyteSpec(SCon{c1, SCon{c2, SCon{c3, SNil{}}}}), H.hex_u32.false_true(valid))
    case SCon{c1, SCon{c2, SCon{c3, SCon{c4, SNil{}}}}}:
      Empty.absurd(StrbyteSpec(SCon{c1, SCon{c2, SCon{c3, SCon{c4, SNil{}}}}}), H.hex_u32.false_true(valid))
    case SCon{c1, SCon{c2, SCon{c3, SCon{c4, SCon{c5, SNil{}}}}}}:
      Empty.absurd(StrbyteSpec(SCon{c1, SCon{c2, SCon{c3, SCon{c4, SCon{c5, SNil{}}}}}}), H.hex_u32.false_true(valid))
    case SCon{c1, SCon{c2, SCon{c3, SCon{c4, SCon{c5, SCon{c6, SNil{}}}}}}}:
      Empty.absurd(StrbyteSpec(SCon{c1, SCon{c2, SCon{c3, SCon{c4, SCon{c5, SCon{c6, SNil{}}}}}}}), H.hex_u32.false_true(valid))
    case SCon{c1, SCon{c2, SCon{c3, SCon{c4, SCon{c5, SCon{c6, SCon{c7, SNil{}}}}}}}}:
      Empty.absurd(StrbyteSpec(SCon{c1, SCon{c2, SCon{c3, SCon{c4, SCon{c5, SCon{c6, SCon{c7, SNil{}}}}}}}}), H.hex_u32.false_true(valid))
    case SCon{c1, SCon{c2, SCon{c3, SCon{c4, SCon{c5, SCon{c6, SCon{c7, SCon{c8, SNil{}}}}}}}}}:
      +v = valid
      accepted = v
      (accepted, ((Char.is_eq(c1, '1'), Char.is_eq(c2, '1'), Char.is_eq(c3, '1'), Char.is_eq(c4, '1'), Char.is_eq(c5, '1'), Char.is_eq(c6, '1'), Char.is_eq(c7, '1'), Char.is_eq(c8, '1')) : Defs.Bit8()), strbyte.parsed(B.valid_byte_string(SCon{c1, SCon{c2, SCon{c3, SCon{c4, SCon{c5, SCon{c6, SCon{c7, SCon{c8, SNil{}}}}}}}}}), ((Char.is_eq(c1, '1'), Char.is_eq(c2, '1'), Char.is_eq(c3, '1'), Char.is_eq(c4, '1'), Char.is_eq(c5, '1'), Char.is_eq(c6, '1'), Char.is_eq(c7, '1'), Char.is_eq(c8, '1')) : Defs.Bit8()), v),
        strbyte_injective.fold_bits(Char.is_eq(c1, '1'), Char.is_eq(c2, '1'), Char.is_eq(c3, '1'), Char.is_eq(c4, '1'), Char.is_eq(c5, '1'), Char.is_eq(c6, '1'), Char.is_eq(c7, '1'), Char.is_eq(c8, '1')))
    case SCon{c1, SCon{c2, SCon{c3, SCon{c4, SCon{c5, SCon{c6, SCon{c7, SCon{c8, SCon{c9, rest}}}}}}}}}:
      Empty.absurd(StrbyteSpec(SCon{c1, SCon{c2, SCon{c3, SCon{c4, SCon{c5, SCon{c6, SCon{c7, SCon{c8, SCon{c9, rest}}}}}}}}}), H.hex_u32.false_true(valid))

def strbyte_lt_256.parsed_value(m: Maybe<&1, Defs.Bit8()>) -> U32:
  match m:
    case None{}: 0
    case Some{bits}: B.bit8_value(bits)

def strbyte_lt_256.reference_if(+valid: Bool, bits: Defs.Bit8(),
  bound: {U32.is_lt(B.bit8_value(bits), 256) == True{} : Bool}) ->
  {U32.is_lt(strbyte_lt_256.parsed_value(BinaryLaws.str_bit8.if(valid, bits)), 256) == True{} : Bool}:
  match valid:
    case False{}: {==}
    case True{}: bound

def strbyte_lt_256.reference(+s: String) ->
  {U32.is_lt(strbyte_lt_256.parsed_value(BinaryLaws.str_bit8(s)), 256) == True{} : Bool}:
  match s:
    case SCon{c1, SCon{c2, SCon{c3, SCon{c4, SCon{c5, SCon{c6, SCon{c7, SCon{c8, SNil{}}}}}}}}}:
      strbyte_lt_256.reference_if(B.valid_byte_string(SCon{c1, SCon{c2, SCon{c3, SCon{c4, SCon{c5, SCon{c6, SCon{c7, SCon{c8, SNil{}}}}}}}}}),
        (Char.is_eq(c1, '1'), Char.is_eq(c2, '1'), Char.is_eq(c3, '1'), Char.is_eq(c4, '1'), Char.is_eq(c5, '1'), Char.is_eq(c6, '1'), Char.is_eq(c7, '1'), Char.is_eq(c8, '1')),
        {==})
    case SNil{}: {==}
    case SCon{c1, SNil{}}: {==}
    case SCon{c1, SCon{c2, SNil{}}}: {==}
    case SCon{c1, SCon{c2, SCon{c3, SNil{}}}}: {==}
    case SCon{c1, SCon{c2, SCon{c3, SCon{c4, SNil{}}}}}: {==}
    case SCon{c1, SCon{c2, SCon{c3, SCon{c4, SCon{c5, SNil{}}}}}}: {==}
    case SCon{c1, SCon{c2, SCon{c3, SCon{c4, SCon{c5, SCon{c6, SNil{}}}}}}}: {==}
    case SCon{c1, SCon{c2, SCon{c3, SCon{c4, SCon{c5, SCon{c6, SCon{c7, SNil{}}}}}}}}: {==}
    case SCon{c1, SCon{c2, SCon{c3, SCon{c4, SCon{c5, SCon{c6, SCon{c7, SCon{c8, SCon{c9, rest}}}}}}}}}: {==}

def strbyte_lt_256.bits(+s: String, bits: Defs.Bit8(),
  parsed: {Some{bits} == BinaryLaws.str_bit8(s) : Maybe<&1, Defs.Bit8()>}) ->
  {U32.is_lt(B.bit8_value(bits), 256) == True{} : Bool}:
  %Equal.sym(Maybe<&1, Defs.Bit8()>, Some{bits}, BinaryLaws.str_bit8(s), parsed) :
    {U32.is_lt(strbyte_lt_256.parsed_value(_), 256) == True{} : Bool}
  strbyte_lt_256.reference(s)

def strbyte_lt_256.finish(+s: String, evidence: StrbyteSpec(s)) ->
  Exists({B.valid_byte_string(s) == True{} : Bool}, accepted =>
    {U32.is_lt(B.strbyte(s, accepted), 256) == True{} : Bool}):
  (accepted, bits, parsed, value) = evidence
  +a = accepted
  bs = bits
  (a, Equal.trans(Bool, U32.is_lt(B.strbyte(s, a), 256),
    U32.is_lt(B.bit8_value(bs), 256), True{},
    Equal.cong(U32, Bool, n => U32.is_lt(n, 256), B.strbyte(s, a),
      B.bit8_value(bs), value),
    strbyte_lt_256.bits(s, bs, parsed)))

def BinaryLaws.strbyte_examples():
  ({==}, {==}, {==}, {==})

def BinaryLaws.strbyte_lt_256(s, valid):
  strbyte_lt_256.finish(s, BinaryLaws.strbyte(s, valid))

# Render a single binary digit for the inverse used by injectivity.
def strbyte_injective.bit_char(bit: Bool) -> Char:
  match bit:
    case False{}: '0'
    case True{}: '1'

def strbyte_injective.char_bits(+b31: Bool, +b30: Bool, +b29: Bool, +b28: Bool, +b27: Bool, +b26: Bool, +b25: Bool, +b24: Bool, +b23: Bool, +b22: Bool, +b21: Bool, +b20: Bool, +b19: Bool, +b18: Bool, +b17: Bool, +b16: Bool, +b15: Bool, +b14: Bool, +b13: Bool, +b12: Bool, +b11: Bool, +b10: Bool, +b9: Bool, +b8: Bool, +b7: Bool, +b6: Bool, +b5: Bool, +b4: Bool, +b3: Bool, +b2: Bool, +b1: Bool, +b0: Bool,
  valid: {B.is_binary_digit(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0)) == True{} : Bool}) ->
  {strbyte_injective.bit_char(B.char_to_bit(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))) == char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0) : Char}:
  match b31 b30 b29 b28 b27 b26 b25 b24 b23 b22 b21 b20 b19 b18 b17 b16 b15 b14 b13 b12 b11 b10 b9 b8 b7 b6 b5 b4 b3 b2 b1 b0:
    case True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd({strbyte_injective.bit_char(B.char_to_bit(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))) == char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0) : Char}, H.hex_u32.false_true(valid))
    case False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd({strbyte_injective.bit_char(B.char_to_bit(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))) == char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0) : Char}, H.hex_u32.false_true(valid))
    case False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd({strbyte_injective.bit_char(B.char_to_bit(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))) == char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0) : Char}, H.hex_u32.false_true(valid))
    case False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd({strbyte_injective.bit_char(B.char_to_bit(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))) == char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0) : Char}, H.hex_u32.false_true(valid))
    case False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd({strbyte_injective.bit_char(B.char_to_bit(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))) == char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0) : Char}, H.hex_u32.false_true(valid))
    case False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd({strbyte_injective.bit_char(B.char_to_bit(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))) == char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0) : Char}, H.hex_u32.false_true(valid))
    case False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd({strbyte_injective.bit_char(B.char_to_bit(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))) == char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0) : Char}, H.hex_u32.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd({strbyte_injective.bit_char(B.char_to_bit(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))) == char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0) : Char}, H.hex_u32.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd({strbyte_injective.bit_char(B.char_to_bit(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))) == char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0) : Char}, H.hex_u32.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd({strbyte_injective.bit_char(B.char_to_bit(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))) == char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0) : Char}, H.hex_u32.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd({strbyte_injective.bit_char(B.char_to_bit(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))) == char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0) : Char}, H.hex_u32.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd({strbyte_injective.bit_char(B.char_to_bit(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))) == char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0) : Char}, H.hex_u32.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd({strbyte_injective.bit_char(B.char_to_bit(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))) == char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0) : Char}, H.hex_u32.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd({strbyte_injective.bit_char(B.char_to_bit(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))) == char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0) : Char}, H.hex_u32.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd({strbyte_injective.bit_char(B.char_to_bit(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))) == char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0) : Char}, H.hex_u32.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd({strbyte_injective.bit_char(B.char_to_bit(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))) == char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0) : Char}, H.hex_u32.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd({strbyte_injective.bit_char(B.char_to_bit(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))) == char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0) : Char}, H.hex_u32.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd({strbyte_injective.bit_char(B.char_to_bit(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))) == char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0) : Char}, H.hex_u32.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd({strbyte_injective.bit_char(B.char_to_bit(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))) == char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0) : Char}, H.hex_u32.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd({strbyte_injective.bit_char(B.char_to_bit(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))) == char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0) : Char}, H.hex_u32.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd({strbyte_injective.bit_char(B.char_to_bit(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))) == char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0) : Char}, H.hex_u32.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _:
      Empty.absurd({strbyte_injective.bit_char(B.char_to_bit(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))) == char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0) : Char}, H.hex_u32.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _:
      Empty.absurd({strbyte_injective.bit_char(B.char_to_bit(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))) == char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0) : Char}, H.hex_u32.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _:
      Empty.absurd({strbyte_injective.bit_char(B.char_to_bit(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))) == char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0) : Char}, H.hex_u32.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _:
      Empty.absurd({strbyte_injective.bit_char(B.char_to_bit(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))) == char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0) : Char}, H.hex_u32.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _:
      Empty.absurd({strbyte_injective.bit_char(B.char_to_bit(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))) == char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0) : Char}, H.hex_u32.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} _ _ _ _ _:
      Empty.absurd({strbyte_injective.bit_char(B.char_to_bit(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))) == char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0) : Char}, H.hex_u32.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} False{} _ _ _ _:
      Empty.absurd({strbyte_injective.bit_char(B.char_to_bit(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))) == char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0) : Char}, H.hex_u32.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} True{} True{} _ _ _:
      Empty.absurd({strbyte_injective.bit_char(B.char_to_bit(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))) == char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0) : Char}, H.hex_u32.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} True{} False{} True{} _ _:
      Empty.absurd({strbyte_injective.bit_char(B.char_to_bit(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))) == char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0) : Char}, H.hex_u32.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} True{} False{} False{} True{} _:
      Empty.absurd({strbyte_injective.bit_char(B.char_to_bit(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))) == char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0) : Char}, H.hex_u32.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} True{} False{} False{} False{} False{}: {==}
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} True{} False{} False{} False{} True{}: {==}

def strbyte_injective.char(+c: Char,
  valid: {B.is_binary_digit(c) == True{} : Bool}) ->
  {strbyte_injective.bit_char(B.char_to_bit(c)) == c : Char}:
  match c:
    case Chr{U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      strbyte_injective.char_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0, valid)

# A left inverse reads the eight low bits back in textual order.
def strbyte_injective.render(value: U32) -> String:
  match value:
    case U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      SCon{strbyte_injective.bit_char(b7), SCon{strbyte_injective.bit_char(b6), SCon{strbyte_injective.bit_char(b5), SCon{strbyte_injective.bit_char(b4), SCon{strbyte_injective.bit_char(b3), SCon{strbyte_injective.bit_char(b2), SCon{strbyte_injective.bit_char(b1), SCon{strbyte_injective.bit_char(b0), SNil{}}}}}}}}}

def StrbyteInverseSpec(+s: String,
  -valid: {B.valid_byte_string(s) == True{} : Bool}) -> Type:
  {strbyte_injective.render(B.strbyte(s, valid)) == s : String}

def strbyte_injective.inverse(s: String,
  +valid: {B.valid_byte_string(s) == True{} : Bool}) -> StrbyteInverseSpec(s, valid):
  match s:
    case SNil{}:
      Empty.absurd(StrbyteInverseSpec(SNil{}, valid), H.hex_u32.false_true(valid))
    case SCon{c1, SNil{}}:
      Empty.absurd(StrbyteInverseSpec(SCon{c1, SNil{}}, valid), H.hex_u32.false_true(valid))
    case SCon{c1, SCon{c2, SNil{}}}:
      Empty.absurd(StrbyteInverseSpec(SCon{c1, SCon{c2, SNil{}}}, valid), H.hex_u32.false_true(valid))
    case SCon{c1, SCon{c2, SCon{c3, SNil{}}}}:
      Empty.absurd(StrbyteInverseSpec(SCon{c1, SCon{c2, SCon{c3, SNil{}}}}, valid), H.hex_u32.false_true(valid))
    case SCon{c1, SCon{c2, SCon{c3, SCon{c4, SNil{}}}}}:
      Empty.absurd(StrbyteInverseSpec(SCon{c1, SCon{c2, SCon{c3, SCon{c4, SNil{}}}}}, valid), H.hex_u32.false_true(valid))
    case SCon{c1, SCon{c2, SCon{c3, SCon{c4, SCon{c5, SNil{}}}}}}:
      Empty.absurd(StrbyteInverseSpec(SCon{c1, SCon{c2, SCon{c3, SCon{c4, SCon{c5, SNil{}}}}}}, valid), H.hex_u32.false_true(valid))
    case SCon{c1, SCon{c2, SCon{c3, SCon{c4, SCon{c5, SCon{c6, SNil{}}}}}}}:
      Empty.absurd(StrbyteInverseSpec(SCon{c1, SCon{c2, SCon{c3, SCon{c4, SCon{c5, SCon{c6, SNil{}}}}}}}, valid), H.hex_u32.false_true(valid))
    case SCon{c1, SCon{c2, SCon{c3, SCon{c4, SCon{c5, SCon{c6, SCon{c7, SNil{}}}}}}}}:
      Empty.absurd(StrbyteInverseSpec(SCon{c1, SCon{c2, SCon{c3, SCon{c4, SCon{c5, SCon{c6, SCon{c7, SNil{}}}}}}}}, valid), H.hex_u32.false_true(valid))
    case SCon{+c1, SCon{+c2, SCon{+c3, SCon{+c4, SCon{+c5, SCon{+c6, SCon{+c7, SCon{+c8, SNil{}}}}}}}}}:
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
      %strbyte_injective.char(c1, p1) : {strbyte_injective.render(B.strbyte(SCon{c1, SCon{c2, SCon{c3, SCon{c4, SCon{c5, SCon{c6, SCon{c7, SCon{c8, SNil{}}}}}}}}}, valid)) == SCon{_, SCon{c2, SCon{c3, SCon{c4, SCon{c5, SCon{c6, SCon{c7, SCon{c8, SNil{}}}}}}}}} : String}
      %strbyte_injective.char(c2, p2) : {strbyte_injective.render(B.strbyte(SCon{c1, SCon{c2, SCon{c3, SCon{c4, SCon{c5, SCon{c6, SCon{c7, SCon{c8, SNil{}}}}}}}}}, valid)) == SCon{strbyte_injective.bit_char(B.char_to_bit(c1)), SCon{_, SCon{c3, SCon{c4, SCon{c5, SCon{c6, SCon{c7, SCon{c8, SNil{}}}}}}}}} : String}
      %strbyte_injective.char(c3, p3) : {strbyte_injective.render(B.strbyte(SCon{c1, SCon{c2, SCon{c3, SCon{c4, SCon{c5, SCon{c6, SCon{c7, SCon{c8, SNil{}}}}}}}}}, valid)) == SCon{strbyte_injective.bit_char(B.char_to_bit(c1)), SCon{strbyte_injective.bit_char(B.char_to_bit(c2)), SCon{_, SCon{c4, SCon{c5, SCon{c6, SCon{c7, SCon{c8, SNil{}}}}}}}}} : String}
      %strbyte_injective.char(c4, p4) : {strbyte_injective.render(B.strbyte(SCon{c1, SCon{c2, SCon{c3, SCon{c4, SCon{c5, SCon{c6, SCon{c7, SCon{c8, SNil{}}}}}}}}}, valid)) == SCon{strbyte_injective.bit_char(B.char_to_bit(c1)), SCon{strbyte_injective.bit_char(B.char_to_bit(c2)), SCon{strbyte_injective.bit_char(B.char_to_bit(c3)), SCon{_, SCon{c5, SCon{c6, SCon{c7, SCon{c8, SNil{}}}}}}}}} : String}
      %strbyte_injective.char(c5, p5) : {strbyte_injective.render(B.strbyte(SCon{c1, SCon{c2, SCon{c3, SCon{c4, SCon{c5, SCon{c6, SCon{c7, SCon{c8, SNil{}}}}}}}}}, valid)) == SCon{strbyte_injective.bit_char(B.char_to_bit(c1)), SCon{strbyte_injective.bit_char(B.char_to_bit(c2)), SCon{strbyte_injective.bit_char(B.char_to_bit(c3)), SCon{strbyte_injective.bit_char(B.char_to_bit(c4)), SCon{_, SCon{c6, SCon{c7, SCon{c8, SNil{}}}}}}}}} : String}
      %strbyte_injective.char(c6, p6) : {strbyte_injective.render(B.strbyte(SCon{c1, SCon{c2, SCon{c3, SCon{c4, SCon{c5, SCon{c6, SCon{c7, SCon{c8, SNil{}}}}}}}}}, valid)) == SCon{strbyte_injective.bit_char(B.char_to_bit(c1)), SCon{strbyte_injective.bit_char(B.char_to_bit(c2)), SCon{strbyte_injective.bit_char(B.char_to_bit(c3)), SCon{strbyte_injective.bit_char(B.char_to_bit(c4)), SCon{strbyte_injective.bit_char(B.char_to_bit(c5)), SCon{_, SCon{c7, SCon{c8, SNil{}}}}}}}}} : String}
      %strbyte_injective.char(c7, p7) : {strbyte_injective.render(B.strbyte(SCon{c1, SCon{c2, SCon{c3, SCon{c4, SCon{c5, SCon{c6, SCon{c7, SCon{c8, SNil{}}}}}}}}}, valid)) == SCon{strbyte_injective.bit_char(B.char_to_bit(c1)), SCon{strbyte_injective.bit_char(B.char_to_bit(c2)), SCon{strbyte_injective.bit_char(B.char_to_bit(c3)), SCon{strbyte_injective.bit_char(B.char_to_bit(c4)), SCon{strbyte_injective.bit_char(B.char_to_bit(c5)), SCon{strbyte_injective.bit_char(B.char_to_bit(c6)), SCon{_, SCon{c8, SNil{}}}}}}}}} : String}
      %strbyte_injective.char(c8, p8) : {strbyte_injective.render(B.strbyte(SCon{c1, SCon{c2, SCon{c3, SCon{c4, SCon{c5, SCon{c6, SCon{c7, SCon{c8, SNil{}}}}}}}}}, valid)) == SCon{strbyte_injective.bit_char(B.char_to_bit(c1)), SCon{strbyte_injective.bit_char(B.char_to_bit(c2)), SCon{strbyte_injective.bit_char(B.char_to_bit(c3)), SCon{strbyte_injective.bit_char(B.char_to_bit(c4)), SCon{strbyte_injective.bit_char(B.char_to_bit(c5)), SCon{strbyte_injective.bit_char(B.char_to_bit(c6)), SCon{strbyte_injective.bit_char(B.char_to_bit(c7)), SCon{_, SNil{}}}}}}}}} : String}
      Equal.cong(U32, String, value => strbyte_injective.render(value),
        B.strbyte.fold_bits([B.char_to_bit(c1), B.char_to_bit(c2), B.char_to_bit(c3), B.char_to_bit(c4), B.char_to_bit(c5), B.char_to_bit(c6), B.char_to_bit(c7), B.char_to_bit(c8)], 0), B.bit8_value((B.char_to_bit(c1), B.char_to_bit(c2), B.char_to_bit(c3), B.char_to_bit(c4), B.char_to_bit(c5), B.char_to_bit(c6), B.char_to_bit(c7), B.char_to_bit(c8))),
        strbyte_injective.fold_bits(B.char_to_bit(c1), B.char_to_bit(c2), B.char_to_bit(c3), B.char_to_bit(c4), B.char_to_bit(c5), B.char_to_bit(c6), B.char_to_bit(c7), B.char_to_bit(c8)))
    case SCon{c1, SCon{c2, SCon{c3, SCon{c4, SCon{c5, SCon{c6, SCon{c7, SCon{c8, SCon{c9, rest}}}}}}}}}:
      Empty.absurd(StrbyteInverseSpec(SCon{c1, SCon{c2, SCon{c3, SCon{c4, SCon{c5, SCon{c6, SCon{c7, SCon{c8, SCon{c9, rest}}}}}}}}}, valid), H.hex_u32.false_true(valid))

def BinaryLaws.strbyte_injective(s1, s2, valid1, valid2, equal):
  +v1 = valid1
  +v2 = valid2
  Equal.trans(String, s1, strbyte_injective.render(B.strbyte(s1, v1)), s2,
    Equal.sym(String, strbyte_injective.render(B.strbyte(s1, v1)), s1,
      strbyte_injective.inverse(s1, v1)),
    Equal.trans(String, strbyte_injective.render(B.strbyte(s1, v1)),
      strbyte_injective.render(B.strbyte(s2, v2)), s2,
      Equal.cong(U32, String, value => strbyte_injective.render(value),
        B.strbyte(s1, v1), B.strbyte(s2, v2), equal),
      strbyte_injective.inverse(s2, v2)))

# A valid one-byte sequence has the one-byte shape: when the shape test
# fails, `valid_one_byte.if` is False, contradicting `valid`.
def utf8_proof.valid_one_byte_has_shape(+byte: U32, shape: Bool,
  checked: {UTF8.has_one_byte_shape(byte) == shape : Bool},
  valid: {Laws.valid_one_byte.if(byte, shape, checked) == True{} : Bool}) ->
  {UTF8.has_one_byte_shape(byte) == True{} : Bool}:
  match shape:
    case False{}:
      Empty.absurd({UTF8.has_one_byte_shape(byte) == True{} : Bool},
        H.hex_u32.false_true(valid))
    case True{}:
      checked

def Laws.valid_one_byte_has_shape(byte, valid):
  +shape = UTF8.has_one_byte_shape(byte)
  utf8_proof.valid_one_byte_has_shape(byte, shape, {==},
    Equal.trans(Bool, Laws.valid_one_byte.if(byte, shape, {==}), UTF8.valid_one_byte(byte), True{},
      Equal.sym(Bool, UTF8.valid_one_byte(byte), Laws.valid_one_byte.if(byte, shape, {==}),
        Laws.utf8_valid_one_byte(byte)),
      valid))

# A valid two-byte sequence has the two-byte shape, in the same way.
def utf8_proof.valid_two_bytes_has_shape(+b1: U32, +b2: U32, shape: Bool,
  checked: {UTF8.has_two_byte_shape(b1, b2) == shape : Bool},
  valid: {Laws.valid_two_bytes.if(b1, b2, shape, checked) == True{} : Bool}) ->
  {UTF8.has_two_byte_shape(b1, b2) == True{} : Bool}:
  match shape:
    case False{}:
      Empty.absurd({UTF8.has_two_byte_shape(b1, b2) == True{} : Bool},
        H.hex_u32.false_true(valid))
    case True{}:
      checked

def Laws.valid_two_bytes_has_shape(b1, b2, valid):
  +shape = UTF8.has_two_byte_shape(b1, b2)
  utf8_proof.valid_two_bytes_has_shape(b1, b2, shape, {==},
    Equal.trans(Bool, Laws.valid_two_bytes.if(b1, b2, shape, {==}), UTF8.valid_two_bytes(b1, b2), True{},
      Equal.sym(Bool, UTF8.valid_two_bytes(b1, b2), Laws.valid_two_bytes.if(b1, b2, shape, {==}),
        Laws.utf8_valid_two_bytes(b1, b2)),
      valid))

# Streaming decoder
# =================

# Whether a lead byte begins a valid two-byte sequence
# -----------------------------------------------------

# Compare high bits first; inspect the low bits only at the 127/128 boundary.
def utf8_proof.threshold_bits(+b10: Bool, +b9: Bool, +b8: Bool, +b7: Bool, +b6: Bool, +b5: Bool, +b4: Bool, +b3: Bool, +b2: Bool, +b1: Bool, +b0: Bool) ->
  {UTF8.can_encode_as_one_byte(utf8_proof.codepoint(WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WNil{}}}}}}}, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WNil{}}}}}})) == utf8_proof.fits_one_byte(WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WNil{}}}}}}) : Bool}:
  match b10 b9 b8 b7 b6 b5 b4 b3 b2 b1 b0:
    case True{} _ _ _ _ _ _ _ _ _ _: {==}
    case False{} True{} _ _ _ _ _ _ _ _ _: {==}
    case False{} False{} True{} _ _ _ _ _ _ _ _: {==}
    case False{} False{} False{} True{} True{} _ _ _ _ _ _: {==}
    case False{} False{} False{} True{} False{} True{} _ _ _ _ _: {==}
    case False{} False{} False{} True{} False{} False{} True{} _ _ _ _: {==}
    case False{} False{} False{} True{} False{} False{} False{} True{} _ _ _: {==}
    case False{} False{} False{} True{} False{} False{} False{} False{} True{} _ _: {==}
    case False{} False{} False{} True{} False{} False{} False{} False{} False{} True{} _: {==}
    case False{} False{} False{} True{} False{} False{} False{} False{} False{} False{} True{}: {==}
    case False{} False{} False{} True{} False{} False{} False{} False{} False{} False{} False{}: {==}
    case False{} False{} False{} False{} False{} _ _ _ _ _ _: {==}
    case False{} False{} False{} False{} True{} False{} _ _ _ _ _: {==}
    case False{} False{} False{} False{} True{} True{} False{} _ _ _ _: {==}
    case False{} False{} False{} False{} True{} True{} True{} False{} _ _ _: {==}
    case False{} False{} False{} False{} True{} True{} True{} True{} False{} _ _: {==}
    case False{} False{} False{} False{} True{} True{} True{} True{} True{} False{} _: {==}
    case False{} False{} False{} False{} True{} True{} True{} True{} True{} True{} False{}: {==}
    case False{} False{} False{} False{} True{} True{} True{} True{} True{} True{} True{}: {==}

def utf8_proof.threshold(+low: Word(6n), +high: Word(5n)) ->
  {UTF8.can_encode_as_one_byte(utf8_proof.codepoint(low, high)) == utf8_proof.fits_one_byte(high) : Bool}:
  match low high:
    case WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WNil{}}}}}}} WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WNil{}}}}}}:
      utf8_proof.threshold_bits(b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0)

def utf8_proof.valid_if_true(+b1: U32, +b2: U32, +shape: Bool,
  -checked: {UTF8.has_two_byte_shape(b1, b2) == shape : Bool},
  +valid: {shape == True{} : Bool}) ->
  {UTF8.valid_two_bytes.if(b1, b2, shape, checked) ==
    Bool.not(UTF8.overlong_two_bytes(b1, b2,
      Equal.trans(Bool, UTF8.has_two_byte_shape(b1, b2), shape, True{}, checked, valid))) : Bool}:
  match shape:
    case False{}:
      Empty.absurd({False{} == Bool.not(UTF8.overlong_two_bytes(b1, b2,
        Equal.trans(Bool, UTF8.has_two_byte_shape(b1, b2), False{}, True{}, checked, valid))) : Bool},
        H.hex_u32.false_true(valid))
    case True{}: {==}

def utf8_proof.overlong_from_facts(+cp: U32, +b1: U32, +b2: U32,
  -shape: {UTF8.has_two_byte_shape(b1, b2) == True{} : Bool},
  decoded: {utf8_proof.decode_payload(b1, b2) == cp : U32}) ->
  {UTF8.overlong_two_bytes(b1, b2, shape) == UTF8.can_encode_as_one_byte(cp) : Bool}:
  %decoded : {UTF8.overlong_two_bytes(b1, b2, shape) == UTF8.can_encode_as_one_byte(_) : Bool}
  {==}

def utf8_proof.valid_from_facts(+cp: U32, +b1: U32, +b2: U32,
  shape: {UTF8.has_two_byte_shape(b1, b2) == True{} : Bool},
  overlong: {UTF8.overlong_two_bytes(b1, b2, shape) == UTF8.can_encode_as_one_byte(cp) : Bool}) ->
  {UTF8.valid_two_bytes(b1, b2) == Bool.not(UTF8.can_encode_as_one_byte(cp)) : Bool}:
  %overlong : {UTF8.valid_two_bytes(b1, b2) == Bool.not(_) : Bool}
  utf8_proof.valid_if_true(b1, b2, UTF8.has_two_byte_shape(b1, b2), {==}, shape)

# Validity of a two-byte pair depends only on the lead byte's payload:
# the pair is valid exactly when the code point does not fit in one byte.
def utf8_proof.valid_two_fields.facts(+low: Word(6n), +high: Word(5n),
  first: {B.byte_mask("110xxxxx", utf8_proof.first_byte(high), {==}) == True{} : Bool} &
    {(U32.is_ge(utf8_proof.first_byte(high), 194) && U32.is_le(utf8_proof.first_byte(high), 223)) == Bool.not(utf8_proof.fits_one_byte(high)) : Bool},
  second: {B.byte_mask("10xxxxxx", utf8_proof.second_byte(low), {==}) == True{} : Bool} &
    {(U32.is_ge(utf8_proof.second_byte(low), 128) && U32.is_le(utf8_proof.second_byte(low), 191)) == True{} : Bool}) ->
  {UTF8.valid_two_bytes(utf8_proof.first_byte(high), utf8_proof.second_byte(low)) ==
    Bool.not(utf8_proof.fits_one_byte(high)) : Bool}:
  (shape1, range1) = first
  (shape2, range2) = second
  +shape = utf8_proof.shape_from_masks(utf8_proof.first_byte(high), utf8_proof.second_byte(low), shape1, shape2)
  +overlong = utf8_proof.overlong_from_facts(utf8_proof.codepoint(low, high),
    utf8_proof.first_byte(high), utf8_proof.second_byte(low), shape, utf8_proof.decode_fields(low, high))
  +valid = utf8_proof.valid_from_facts(utf8_proof.codepoint(low, high),
    utf8_proof.first_byte(high), utf8_proof.second_byte(low), shape, overlong)
  Equal.trans(Bool, UTF8.valid_two_bytes(utf8_proof.first_byte(high), utf8_proof.second_byte(low)),
    Bool.not(UTF8.can_encode_as_one_byte(utf8_proof.codepoint(low, high))),
    Bool.not(utf8_proof.fits_one_byte(high)), valid,
    Equal.cong(Bool, Bool, b => Bool.not(b),
      UTF8.can_encode_as_one_byte(utf8_proof.codepoint(low, high)),
      utf8_proof.fits_one_byte(high), utf8_proof.threshold(low, high)))

def utf8_proof.valid_two_fields(+low: Word(6n), +high: Word(5n)) ->
  {UTF8.valid_two_bytes(utf8_proof.first_byte(high), utf8_proof.second_byte(low)) ==
    Bool.not(utf8_proof.fits_one_byte(high)) : Bool}:
  utf8_proof.valid_two_fields.facts(low, high,
    utf8_proof.first_byte_facts(high), utf8_proof.second_byte_facts(low))


# For a lead byte in payload form, any valid continuation means 0x80 is
# valid too: both pairs are valid exactly when the payload does not fit in
# one byte.
def utf8_proof.any_continuation.payload(+b2: U32, +high: Word(5n), +low: Word(6n),
  second: {b2 == utf8_proof.second_byte(low) : U32}) ->
  {UTF8.valid_two_bytes(utf8_proof.first_byte(high), b2) == True{} : Bool} ->
  {UTF8.valid_two_bytes(utf8_proof.first_byte(high), 128) == True{} : Bool}:
  %Equal.sym(U32, b2, utf8_proof.second_byte(low), second) :
    {UTF8.valid_two_bytes(utf8_proof.first_byte(high), _) == True{} : Bool} ->
    {UTF8.valid_two_bytes(utf8_proof.first_byte(high), 128) == True{} : Bool}
  fields => Equal.trans(Bool, UTF8.valid_two_bytes(utf8_proof.first_byte(high), 128),
    Bool.not(utf8_proof.fits_one_byte(high)), True{},
    utf8_proof.valid_two_fields(WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}, high),
    Equal.trans(Bool, Bool.not(utf8_proof.fits_one_byte(high)),
      UTF8.valid_two_bytes(utf8_proof.first_byte(high), utf8_proof.second_byte(low)), True{},
      Equal.sym(Bool, UTF8.valid_two_bytes(utf8_proof.first_byte(high), utf8_proof.second_byte(low)),
        Bool.not(utf8_proof.fits_one_byte(high)), utf8_proof.valid_two_fields(low, high)),
      fields))

def utf8_proof.any_continuation.fields(+b1: U32, +b2: U32,
  first: Exists(Word(5n), high => {b1 == utf8_proof.first_byte(high) : U32}),
  second: Exists(Word(6n), low => {b2 == utf8_proof.second_byte(low) : U32})) ->
  {UTF8.valid_two_bytes(b1, b2) == True{} : Bool} ->
  {UTF8.valid_two_bytes(b1, 128) == True{} : Bool}:
  (+high, first_equal) = first
  (+low, second_equal) = second
  %Equal.sym(U32, b1, utf8_proof.first_byte(high), first_equal) :
    {UTF8.valid_two_bytes(_, b2) == True{} : Bool} ->
    {UTF8.valid_two_bytes(_, 128) == True{} : Bool}
  utf8_proof.any_continuation.payload(b2, high, low, second_equal)

# If some continuation byte completes a lead byte, 0x80 does too.
def utf8_proof.any_continuation(+b1: U32, +b2: U32,
  +valid: {UTF8.valid_two_bytes(b1, b2) == True{} : Bool}) ->
  {UTF8.valid_two_bytes(b1, 128) == True{} : Bool}:
  +shape = UTF8.valid_two_bytes.has_shape(b1, b2, valid)
  utf8_proof.any_continuation.fields(b1, b2,
    utf8_proof.first_payload(b1, bool_and_left_true(B.byte_mask("110xxxxx", b1, {==}), B.byte_mask("10xxxxxx", b2, {==}), shape)),
    utf8_proof.second_payload(b2, bool_and_right_true(B.byte_mask("110xxxxx", b1, {==}), B.byte_mask("10xxxxxx", b2, {==}), shape)),
    valid)

# `Bool.or(a, True)` is True whatever `a` is.
def bool_or_true(+a: Bool) -> {Bool.or(a, True{}) == True{} : Bool}:
  match a:
    case False{}: {==}
    case True{}: {==}

def BeginsCompletion(+seq: List<&2, U32>) -> Type:
  Exists(List<&2, U32>, rest =>
    {Laws.is_valid_sequence(List.append(&2, U32, seq, rest)) == True{} : Bool})

# A single byte that begins a sequence is either valid by itself, or
# completed by 0x80.
def utf8_proof.begins_one(+b1: U32, one: Bool,
  checked: {UTF8.valid_one_byte(b1) == one : Bool},
  begins: {Bool.or(one, UTF8.valid_two_bytes(b1, 128)) == True{} : Bool}) ->
  BeginsCompletion([b1]):
  match one:
    case True{}: (Nil{}, checked)
    case False{}: ([128], begins)

def utf8_proof.begins_completion(+seq: List<&2, U32>,
  begins: {UTF8.begins_valid_sequence(seq) == True{} : Bool}) -> BeginsCompletion(seq):
  match seq:
    case Nil{}:
      ([0], {==})
    case +b1 <> Nil{}:
      utf8_proof.begins_one(b1, UTF8.valid_one_byte(b1), {==}, begins)
    case +b1 <> +b2 <> Nil{}:
      (Nil{}, begins)
    case b1 <> b2 <> b3 <> rest:
      Empty.absurd(BeginsCompletion(b1 <> b2 <> b3 <> rest), H.hex_u32.false_true(begins))

def utf8_proof.begins_from(+seq: List<&2, U32>, +rest: List<&2, U32>,
  valid: {Laws.is_valid_sequence(List.append(&2, U32, seq, rest)) == True{} : Bool}) ->
  {UTF8.begins_valid_sequence(seq) == True{} : Bool}:
  match seq rest:
    case Nil{} _:
      {==}
    case +b1 <> Nil{} Nil{}:
      %Equal.sym(Bool, UTF8.valid_one_byte(b1), True{}, valid) :
        {Bool.or(_, UTF8.valid_two_bytes(b1, 128)) == True{} : Bool}
      {==}
    case +b1 <> Nil{} +b2 <> Nil{}:
      +lead = utf8_proof.any_continuation(b1, b2, valid)
      %Equal.sym(Bool, UTF8.valid_two_bytes(b1, 128), True{}, lead) :
        {Bool.or(UTF8.valid_one_byte(b1), _) == True{} : Bool}
      bool_or_true(UTF8.valid_one_byte(b1))
    case b1 <> Nil{} b2 <> b3 <> more:
      Empty.absurd({UTF8.begins_valid_sequence([b1]) == True{} : Bool}, H.hex_u32.false_true(valid))
    case +b1 <> +b2 <> Nil{} Nil{}:
      valid
    case b1 <> b2 <> Nil{} b3 <> more:
      Empty.absurd({UTF8.begins_valid_sequence([b1, b2]) == True{} : Bool}, H.hex_u32.false_true(valid))
    case b1 <> b2 <> b3 <> more _:
      Empty.absurd({UTF8.begins_valid_sequence(b1 <> b2 <> b3 <> more) == True{} : Bool}, H.hex_u32.false_true(valid))

def utf8_proof.begins_from_completion(+seq: List<&2, U32>, completion: BeginsCompletion(seq)) ->
  {UTF8.begins_valid_sequence(seq) == True{} : Bool}:
  (+rest, valid) = completion
  utf8_proof.begins_from(seq, rest, valid)

def Laws.utf8_begins_valid_sequence(seq):
  (begins => utf8_proof.begins_completion(seq, begins),
   completion => utf8_proof.begins_from_completion(seq, completion))

# The implementation's scalar functions agree with the specification's
# --------------------------------------------------------------------

def utf8_proof.true_false(e: {True{} == False{} : Bool}) -> Empty:
  H.hex_u32.false_true(Equal.sym(Bool, True{}, False{}, e))

# Both scalar functions branch on validity tests that the validity laws
# make equal, and decoding does not depend on its proof argument.
def utf8_proof.one_scalar_agrees(+byte: U32, impl: Bool,
  -impl_checked: {UTF8.valid_one_byte(byte) == impl : Bool}, spec: Bool,
  -spec_checked: {UTF8.valid_one_byte(byte) == spec : Bool},
  same: {impl == spec : Bool}) ->
  {UTF8.one_byte_scalar.if(byte, impl, impl_checked) ==
    Laws.one_byte_scalar.if(byte, spec, spec_checked) : Maybe<&2, U32>}:
  match impl spec:
    case False{} False{}: {==}
    case True{} True{}: {==}
    case False{} True{}:
      Empty.absurd({None{} == Some{UTF8.decode_one_byte(byte, Laws.valid_one_byte_has_shape(byte, spec_checked))} : Maybe<&2, U32>},
        H.hex_u32.false_true(same))
    case True{} False{}:
      Empty.absurd({Some{UTF8.decode_one_byte(byte, impl_checked)} == None{} : Maybe<&2, U32>},
        utf8_proof.true_false(same))

def utf8_proof.two_scalar_agrees(+b1: U32, +b2: U32, impl: Bool,
  -impl_checked: {UTF8.valid_two_bytes(b1, b2) == impl : Bool}, spec: Bool,
  -spec_checked: {UTF8.valid_two_bytes(b1, b2) == spec : Bool},
  same: {impl == spec : Bool}) ->
  {UTF8.two_byte_scalar.if(b1, b2, impl, impl_checked) ==
    Laws.two_byte_scalar.if(b1, b2, spec, spec_checked) : Maybe<&2, U32>}:
  match impl spec:
    case False{} False{}: {==}
    case True{} True{}: {==}
    case False{} True{}:
      Empty.absurd({None{} == Some{UTF8.decode_two_bytes(b1, b2, Laws.valid_two_bytes_has_shape(b1, b2, spec_checked))} : Maybe<&2, U32>},
        H.hex_u32.false_true(same))
    case True{} False{}:
      Empty.absurd({Some{UTF8.decode_two_bytes(b1, b2, UTF8.valid_two_bytes.has_shape(b1, b2, impl_checked))} == None{} : Maybe<&2, U32>},
        utf8_proof.true_false(same))

# Splitting the input
# -------------------

def utf8_proof.string_assoc(+a: String, +b: String, +c: String) ->
  {String.append(String.append(a, b), c) == String.append(a, String.append(b, c)) : String}:
  match a:
    case SNil{}: {==}
    case SCon{+h, +t}:
      %utf8_proof.string_assoc(t, b, c) :
        {SCon{h, String.append(String.append(t, b), c)} == SCon{h, _} : String}
      {==}

def utf8_proof.prepend_empty(step: UTF8.decode_buffer.Step()) ->
  {UTF8.decode_buffer.prepend("", step) == step : UTF8.decode_buffer.Step()}:
  (text, pending) = step
  {==}

def utf8_proof.prepend_assoc(+a: String, +b: String, step: UTF8.decode_buffer.Step()) ->
  {UTF8.decode_buffer.prepend(String.append(a, b), step) ==
    UTF8.decode_buffer.prepend(a, UTF8.decode_buffer.prepend(b, step)) : UTF8.decode_buffer.Step()}:
  (+c, +pending) = step
  %utf8_proof.string_assoc(a, b, c) :
    {(String.append(String.append(a, b), c), pending) == (_, pending) : UTF8.decode_buffer.Step()}
  {==}

# Continuing with `ys` after text was prepended is the same as prepending
# the text to the continuation.
def utf8_proof.prepend_then(+ys: List<&2, U32>, +text: String, step: UTF8.decode_buffer.Step()) ->
  {UTF8.decode_buffer.then(UTF8.decode_buffer.prepend(text, step), q => UTF8.decode_buffer.bytes(ys, q)) ==
    UTF8.decode_buffer.prepend(text, UTF8.decode_buffer.then(step, q => UTF8.decode_buffer.bytes(ys, q))) : UTF8.decode_buffer.Step()}:
  (+more, +pending) = step
  utf8_proof.prepend_assoc(text, more, UTF8.decode_buffer.bytes(ys, pending))

def utf8_proof.go_append.then(+t: List<&2, U32>, +ys: List<&2, U32>, stepped: UTF8.decode_buffer.Step(),
  same: @q: List<&2, U32> ->
    {UTF8.decode_buffer.bytes(List.append(&2, U32, t, ys), q) ==
      UTF8.decode_buffer.then(UTF8.decode_buffer.bytes(t, q), r => UTF8.decode_buffer.bytes(ys, r)) : UTF8.decode_buffer.Step()}) ->
  {UTF8.decode_buffer.then(stepped, q => UTF8.decode_buffer.bytes(List.append(&2, U32, t, ys), q)) ==
    UTF8.decode_buffer.then(UTF8.decode_buffer.then(stepped, q => UTF8.decode_buffer.bytes(t, q)),
      r => UTF8.decode_buffer.bytes(ys, r)) : UTF8.decode_buffer.Step()}:
  (+text, +q) = stepped
  %Equal.sym(UTF8.decode_buffer.Step(), UTF8.decode_buffer.bytes(List.append(&2, U32, t, ys), q),
      UTF8.decode_buffer.then(UTF8.decode_buffer.bytes(t, q), r => UTF8.decode_buffer.bytes(ys, r)), same(q)) :
    {UTF8.decode_buffer.prepend(text, _) ==
      UTF8.decode_buffer.then(UTF8.decode_buffer.prepend(text, UTF8.decode_buffer.bytes(t, q)), r => UTF8.decode_buffer.bytes(ys, r)) : UTF8.decode_buffer.Step()}
  Equal.sym(UTF8.decode_buffer.Step(),
    UTF8.decode_buffer.then(UTF8.decode_buffer.prepend(text, UTF8.decode_buffer.bytes(t, q)), r => UTF8.decode_buffer.bytes(ys, r)),
    UTF8.decode_buffer.prepend(text, UTF8.decode_buffer.then(UTF8.decode_buffer.bytes(t, q), r => UTF8.decode_buffer.bytes(ys, r))),
    utf8_proof.prepend_then(ys, text, UTF8.decode_buffer.bytes(t, q)))

# Decoding `xs` then `ys` is decoding `xs ++ ys`.
def utf8_proof.go_append(+xs: List<&2, U32>, +ys: List<&2, U32>, +pending: List<&2, U32>) ->
  {UTF8.decode_buffer.bytes(List.append(&2, U32, xs, ys), pending) ==
    UTF8.decode_buffer.then(UTF8.decode_buffer.bytes(xs, pending), q => UTF8.decode_buffer.bytes(ys, q)) : UTF8.decode_buffer.Step()}:
  match xs:
    case Nil{}:
      Equal.sym(UTF8.decode_buffer.Step(), UTF8.decode_buffer.prepend("", UTF8.decode_buffer.bytes(ys, pending)),
        UTF8.decode_buffer.bytes(ys, pending), utf8_proof.prepend_empty(UTF8.decode_buffer.bytes(ys, pending)))
    case +h <> +t:
      utf8_proof.go_append.then(t, ys, UTF8.decode_buffer.step(pending, h),
        q => utf8_proof.go_append(t, ys, q))

def utf8_proof.all_bytes_cons(+h: U32, ok: Bool, -checked: {U32.is_le(h, 255) == ok : Bool},
  -x: Bool, -y: Bool, -z: Bool, same: {x == Bool.and(y, z) : Bool}) ->
  {List.all.if(u => x, ok) == Bool.and(List.all.if(u => y, ok), z) : Bool}:
  match ok:
    case False{}: {==}
    case True{}: same

def utf8_proof.all_bytes_append(+xs: List<&2, U32>, +ys: List<&2, U32>) ->
  {Laws.all_bytes(List.append(&2, U32, xs, ys)) ==
    Bool.and(Laws.all_bytes(xs), Laws.all_bytes(ys)) : Bool}:
  match xs:
    case Nil{}: {==}
    case +h <> +t:
      utf8_proof.all_bytes_cons(h, U32.is_le(h, 255), {==},
        Laws.all_bytes(List.append(&2, U32, t, ys)), Laws.all_bytes(t), Laws.all_bytes(ys),
        utf8_proof.all_bytes_append(t, ys))

# Feeding buffers
# ---------------

# What feeding should give: None if some value is above 255, otherwise
# the byte loop's state and text.
def utf8_proof.fed_step(step: UTF8.decode_buffer.Step()) -> Laws.Fed():
  (text, pending) = step
  Some{(pending, text)}

def utf8_proof.expected_fed(ok: Bool, step: UTF8.decode_buffer.Step()) -> Laws.Fed():
  match ok:
    case False{}: None{}
    case True{}: utf8_proof.fed_step(step)

def utf8_proof.fed_prepend(+text: String, ok: Bool, step: UTF8.decode_buffer.Step()) ->
  {Laws.feed.prepend(text, utf8_proof.expected_fed(ok, step)) ==
    utf8_proof.expected_fed(ok, UTF8.decode_buffer.prepend(text, step)) : Laws.Fed()}:
  match ok:
    case False{}: {==}
    case True{}:
      (more, pending) = step
      {==}

def utf8_proof.feed_step(+rest: List<&2, List<&2, U32>>, stepped: UTF8.decode_buffer.Step(),
  same: @q: List<&2, U32> ->
    {Laws.feed(rest, q) == utf8_proof.expected_fed(Laws.all_bytes(List.concat(&2, U32, rest)),
      UTF8.decode_buffer.bytes(List.concat(&2, U32, rest), q)) : Laws.Fed()}) ->
  {Laws.feed.then(UTF8.decode_buffer.result(stepped), s => Laws.feed(rest, s)) ==
    utf8_proof.expected_fed(Laws.all_bytes(List.concat(&2, U32, rest)),
      UTF8.decode_buffer.then(stepped, q => UTF8.decode_buffer.bytes(List.concat(&2, U32, rest), q))) : Laws.Fed()}:
  (+text, +q) = stepped
  %Equal.sym(Laws.Fed(), Laws.feed(rest, q),
      utf8_proof.expected_fed(Laws.all_bytes(List.concat(&2, U32, rest)), UTF8.decode_buffer.bytes(List.concat(&2, U32, rest), q)),
      same(q)) :
    {Laws.feed.prepend(text, _) ==
      utf8_proof.expected_fed(Laws.all_bytes(List.concat(&2, U32, rest)),
        UTF8.decode_buffer.prepend(text, UTF8.decode_buffer.bytes(List.concat(&2, U32, rest), q))) : Laws.Fed()}
  utf8_proof.fed_prepend(text, Laws.all_bytes(List.concat(&2, U32, rest)),
    UTF8.decode_buffer.bytes(List.concat(&2, U32, rest), q))

def utf8_proof.feed_cons(+buffer: List<&2, U32>, +rest: List<&2, List<&2, U32>>,
  +pending: List<&2, U32>, ok: Bool,
  same: @q: List<&2, U32> ->
    {Laws.feed(rest, q) == utf8_proof.expected_fed(Laws.all_bytes(List.concat(&2, U32, rest)),
      UTF8.decode_buffer.bytes(List.concat(&2, U32, rest), q)) : Laws.Fed()}) ->
  {Laws.feed.then(UTF8.decode_buffer.if(pending, buffer, ok), s => Laws.feed(rest, s)) ==
    utf8_proof.expected_fed(Bool.and(ok, Laws.all_bytes(List.concat(&2, U32, rest))),
      UTF8.decode_buffer.then(UTF8.decode_buffer.bytes(buffer, pending),
        q => UTF8.decode_buffer.bytes(List.concat(&2, U32, rest), q))) : Laws.Fed()}:
  match ok:
    case False{}: {==}
    case True{}:
      utf8_proof.feed_step(rest, UTF8.decode_buffer.bytes(buffer, pending), same)

# Feeding any list of buffers gives what the byte loop gives for their
# concatenation.
def utf8_proof.feed_agrees(+buffers: List<&2, List<&2, U32>>, +pending: List<&2, U32>) ->
  {Laws.feed(buffers, pending) ==
    utf8_proof.expected_fed(Laws.all_bytes(List.concat(&2, U32, buffers)),
      UTF8.decode_buffer.bytes(List.concat(&2, U32, buffers), pending)) : Laws.Fed()}:
  match buffers:
    case Nil{}: {==}
    case +buffer <> +rest:
      %Equal.sym(Bool, Laws.all_bytes(List.append(&2, U32, buffer, List.concat(&2, U32, rest))),
          Bool.and(Laws.all_bytes(buffer), Laws.all_bytes(List.concat(&2, U32, rest))),
          utf8_proof.all_bytes_append(buffer, List.concat(&2, U32, rest))) :
        {Laws.feed(buffer <> rest, pending) ==
          utf8_proof.expected_fed(_,
            UTF8.decode_buffer.bytes(List.append(&2, U32, buffer, List.concat(&2, U32, rest)), pending)) : Laws.Fed()}
      %Equal.sym(UTF8.decode_buffer.Step(), UTF8.decode_buffer.bytes(List.append(&2, U32, buffer, List.concat(&2, U32, rest)), pending),
          UTF8.decode_buffer.then(UTF8.decode_buffer.bytes(buffer, pending), q => UTF8.decode_buffer.bytes(List.concat(&2, U32, rest), q)),
          utf8_proof.go_append(buffer, List.concat(&2, U32, rest), pending)) :
        {Laws.feed(buffer <> rest, pending) ==
          utf8_proof.expected_fed(Bool.and(Laws.all_bytes(buffer), Laws.all_bytes(List.concat(&2, U32, rest))), _) : Laws.Fed()}
      utf8_proof.feed_cons(buffer, rest, pending, Laws.all_bytes(buffer),
        q => utf8_proof.feed_agrees(rest, q))

# Uniqueness of maximal subparts and of decoding the first code point
# --------------------------------------------------------------------

def utf8_proof.head_or(d: U32, xs: List<&2, U32>) -> U32:
  match xs:
    case Nil{}: d
    case x <> rest: x

def utf8_proof.is_cons(xs: List<&2, U32>) -> Bool:
  match xs:
    case Nil{}: False{}
    case x <> rest: True{}

def utf8_proof.cons_head(+h1: U32, +h2: U32, +t1: List<&2, U32>, +t2: List<&2, U32>,
  +e: {h1 <> t1 == h2 <> t2 : List<&2, U32>}) -> {h1 == h2 : U32}:
  Equal.cong(List<&2, U32>, U32, xs => utf8_proof.head_or(h1, xs), h1 <> t1, h2 <> t2, e)

def utf8_proof.cons_tail(+h1: U32, +h2: U32, +t1: List<&2, U32>, +t2: List<&2, U32>,
  +e: {h1 <> t1 == h2 <> t2 : List<&2, U32>}) -> {t1 == t2 : List<&2, U32>}:
  Equal.cong(List<&2, U32>, List<&2, U32>, xs => List.tail(&2, U32, xs), h1 <> t1, h2 <> t2, e)

def utf8_proof.cons_nil(+h: U32, +t: List<&2, U32>, e: {h <> t == Nil{} : List<&2, U32>}) -> Empty:
  utf8_proof.true_false(Equal.cong(List<&2, U32>, Bool, utf8_proof.is_cons, h <> t, Nil{}, e))

def utf8_proof.cons_eq(+h1: U32, +h2: U32, +t1: List<&2, U32>, +t2: List<&2, U32>,
  eh: {h1 == h2 : U32}, et: {t1 == t2 : List<&2, U32>}) -> {h1 <> t1 == h2 <> t2 : List<&2, U32>}:
  %eh : {h1 <> t1 == _ <> t2 : List<&2, U32>}
  %et : {h1 <> t1 == h1 <> _ : List<&2, U32>}
  {==}

def utf8_proof.append_assoc(+x: List<&2, U32>, +y: List<&2, U32>, +z: List<&2, U32>) ->
  {List.append(&2, U32, List.append(&2, U32, x, y), z) ==
    List.append(&2, U32, x, List.append(&2, U32, y, z)) : List<&2, U32>}:
  match x:
    case Nil{}: {==}
    case +h <> +t:
      %utf8_proof.append_assoc(t, y, z) :
        {h <> List.append(&2, U32, List.append(&2, U32, t, y), z) == h <> _ : List<&2, U32>}
      {==}

# Every prefix of bytes that begin a valid sequence begins one too, by
# `utf8_begins_valid_sequence`.
def utf8_proof.valid_regroup(+x: List<&2, U32>, +y: List<&2, U32>, +z: List<&2, U32>,
  valid: {Laws.is_valid_sequence(List.append(&2, U32, List.append(&2, U32, x, y), z)) == True{} : Bool}) ->
  {Laws.is_valid_sequence(List.append(&2, U32, x, List.append(&2, U32, y, z))) == True{} : Bool}:
  %utf8_proof.append_assoc(x, y, z) : {Laws.is_valid_sequence(_) == True{} : Bool}
  valid

def utf8_proof.begins_prefix.completion(+x: List<&2, U32>, +y: List<&2, U32>,
  completion: BeginsCompletion(List.append(&2, U32, x, y))) ->
  {UTF8.begins_valid_sequence(x) == True{} : Bool}:
  (+rest, valid) = completion
  utf8_proof.begins_from_completion(x,
    (List.append(&2, U32, y, rest), utf8_proof.valid_regroup(x, y, rest, valid)))

def utf8_proof.begins_prefix(+x: List<&2, U32>, +y: List<&2, U32>,
  begins: {UTF8.begins_valid_sequence(List.append(&2, U32, x, y)) == True{} : Bool}) ->
  {UTF8.begins_valid_sequence(x) == True{} : Bool}:
  utf8_proof.begins_prefix.completion(x, y,
    utf8_proof.begins_completion(List.append(&2, U32, x, y), begins))

# `a` is shorter than `b`, both prefixes of `bytes`: `b` is `a` followed
# by `c` and more, and `c` is the byte after `a`.
def utf8_proof.Shorter(+a: List<&2, U32>, +b: List<&2, U32>, +bytes: List<&2, U32>) -> Type:
  Exists(U32, c => Exists(List<&2, U32>, extra =>
    {b == List.append(&2, U32, a, c <> extra) : List<&2, U32>} &
    {Laws.next_byte_after(bytes, a) == Some{c} : Maybe<&2, U32>}))

# Two prefixes of the same bytes are equal or one is shorter.
def utf8_proof.Compared(+s1: List<&2, U32>, +s2: List<&2, U32>, +bytes: List<&2, U32>) -> Type:
  Or({s1 == s2 : List<&2, U32>},
    Or(utf8_proof.Shorter(s1, s2, bytes), utf8_proof.Shorter(s2, s1, bytes)))

def utf8_proof.next_after_nil(+h: U32, +rest: List<&2, U32>, +bytes: List<&2, U32>,
  e: {h <> rest == bytes : List<&2, U32>}) ->
  {Laws.next_byte_after(bytes, Nil{}) == Some{h} : Maybe<&2, U32>}:
  %e : {Laws.next_byte_after(_, Nil{}) == Some{h} : Maybe<&2, U32>}
  {==}

def utf8_proof.shorter_cons(+h1: U32, +h2: U32, +t1: List<&2, U32>, +t2: List<&2, U32>,
  +b: U32, +bs: List<&2, U32>, eh: {h2 == h1 : U32},
  shorter: utf8_proof.Shorter(t1, t2, bs)) ->
  utf8_proof.Shorter(h1 <> t1, h2 <> t2, b <> bs):
  (+c, more) = shorter
  (+extra, facts) = more
  (eq, next) = facts
  (c, (extra, (utf8_proof.cons_eq(h2, h1, t2, List.append(&2, U32, t1, c <> extra), eh, eq), next)))

def utf8_proof.compared_cons(+h1: U32, +h2: U32, +t1: List<&2, U32>, +t2: List<&2, U32>,
  +b: U32, +bs: List<&2, U32>, +eh1: {h1 == b : U32}, +eh2: {h2 == b : U32},
  compared: utf8_proof.Compared(t1, t2, bs)) ->
  utf8_proof.Compared(h1 <> t1, h2 <> t2, b <> bs):
  match compared:
    case Inl{same}:
      Inl{utf8_proof.cons_eq(h1, h2, t1, t2,
        Equal.trans(U32, h1, b, h2, eh1, Equal.sym(U32, h2, b, eh2)), same)}
    case Inr{Inl{shorter}}:
      Inr{Inl{utf8_proof.shorter_cons(h1, h2, t1, t2, b, bs,
        Equal.trans(U32, h2, b, h1, eh2, Equal.sym(U32, h1, b, eh1)), shorter)}}
    case Inr{Inr{shorter}}:
      Inr{Inr{utf8_proof.shorter_cons(h2, h1, t2, t1, b, bs,
        Equal.trans(U32, h1, b, h2, eh1, Equal.sym(U32, h2, b, eh2)), shorter)}}

def utf8_proof.compare(+s1: List<&2, U32>, +s2: List<&2, U32>, +bytes: List<&2, U32>,
  +r1: List<&2, U32>, +r2: List<&2, U32>,
  +e1: {List.append(&2, U32, s1, r1) == bytes : List<&2, U32>},
  +e2: {List.append(&2, U32, s2, r2) == bytes : List<&2, U32>}) ->
  utf8_proof.Compared(s1, s2, bytes):
  match s1 s2:
    case Nil{} Nil{}:
      Inl{{==}}
    case Nil{} +h <> +t:
      Inr{Inl{(h, (t, ({==}, utf8_proof.next_after_nil(h, List.append(&2, U32, t, r2), bytes, e2))))}}
    case +h <> +t Nil{}:
      Inr{Inr{(h, (t, ({==}, utf8_proof.next_after_nil(h, List.append(&2, U32, t, r1), bytes, e1))))}}
    case +h1 <> +t1 +h2 <> +t2:
      match bytes:
        case Nil{}:
          Empty.absurd(utf8_proof.Compared(h1 <> t1, h2 <> t2, Nil{}),
            utf8_proof.cons_nil(h1, List.append(&2, U32, t1, r1), e1))
        case +b <> +bs:
          utf8_proof.compared_cons(h1, h2, t1, t2, b, bs,
            utf8_proof.cons_head(h1, b, List.append(&2, U32, t1, r1), bs, e1),
            utf8_proof.cons_head(h2, b, List.append(&2, U32, t2, r2), bs, e2),
            utf8_proof.compare(t1, t2, bs, r1, r2,
              utf8_proof.cons_tail(h1, b, List.append(&2, U32, t1, r1), bs, e1),
              utf8_proof.cons_tail(h2, b, List.append(&2, U32, t2, r2), bs, e2)))

def utf8_proof.longest_next(+a: List<&2, U32>, +bytes: List<&2, U32>, +c: U32,
  next: {Laws.next_byte_after(bytes, a) == Some{c} : Maybe<&2, U32>},
  longest: Laws.maximal_subpart.longest(a, Laws.next_byte_after(bytes, a))) ->
  Laws.maximal_subpart.longest(a, Some{c}):
  %next : Laws.maximal_subpart.longest(a, _)
  longest

def utf8_proof.begins_regroup(+a: List<&2, U32>, +c: U32, +extra: List<&2, U32>,
  +b: List<&2, U32>, eq: {b == List.append(&2, U32, a, c <> extra) : List<&2, U32>},
  begins: {UTF8.begins_valid_sequence(b) == True{} : Bool}) ->
  {UTF8.begins_valid_sequence(List.append(&2, U32, List.append(&2, U32, a, [c]), extra)) == True{} : Bool}:
  %Equal.sym(List<&2, U32>, List.append(&2, U32, List.append(&2, U32, a, [c]), extra),
      List.append(&2, U32, a, List.append(&2, U32, [c], extra)), utf8_proof.append_assoc(a, [c], extra)) :
    {UTF8.begins_valid_sequence(_) == True{} : Bool}
  %eq : {UTF8.begins_valid_sequence(_) == True{} : Bool}
  begins

# A prefix that begins a valid sequence and is longer than `a`
# contradicts `a` being the longest.
def utf8_proof.longer_not_begins(+a: List<&2, U32>, +b: List<&2, U32>, +bytes: List<&2, U32>,
  begins_b: {UTF8.begins_valid_sequence(b) == True{} : Bool},
  longest_a: Laws.maximal_subpart.longest(a, Laws.next_byte_after(bytes, a)),
  shorter: utf8_proof.Shorter(a, b, bytes)) -> Empty:
  (+c, more) = shorter
  (+extra, facts) = more
  (eq, next) = facts
  +ac = List.append(&2, U32, a, [c])
  not_begins = utf8_proof.longest_next(a, bytes, c, next, longest_a)
  begins_ac = utf8_proof.begins_prefix(ac, extra, utf8_proof.begins_regroup(a, c, extra, b, eq, begins_b))
  utf8_proof.true_false(Equal.trans(Bool, True{}, UTF8.begins_valid_sequence(ac), False{},
    Equal.sym(Bool, UTF8.begins_valid_sequence(ac), True{}, begins_ac), not_begins))

def utf8_proof.sequence_prefix_unique.compared(+s1: List<&2, U32>, +s2: List<&2, U32>,
  +bytes: List<&2, U32>,
  begins1: {UTF8.begins_valid_sequence(s1) == True{} : Bool},
  begins2: {UTF8.begins_valid_sequence(s2) == True{} : Bool},
  longest1: Laws.maximal_subpart.longest(s1, Laws.next_byte_after(bytes, s1)),
  longest2: Laws.maximal_subpart.longest(s2, Laws.next_byte_after(bytes, s2)),
  compared: utf8_proof.Compared(s1, s2, bytes)) -> {s1 == s2 : List<&2, U32>}:
  match compared:
    case Inl{same}:
      same
    case Inr{Inl{shorter}}:
      Empty.absurd({s1 == s2 : List<&2, U32>},
        utf8_proof.longer_not_begins(s1, s2, bytes, begins2, longest1, shorter))
    case Inr{Inr{shorter}}:
      Empty.absurd({s1 == s2 : List<&2, U32>},
        utf8_proof.longer_not_begins(s2, s1, bytes, begins1, longest2, shorter))

def utf8_proof.sequence_prefix_unique(+b1: U32, +more: List<&2, U32>,
  -first: {UTF8.begins_valid_sequence([b1]) == True{} : Bool},
  +s1: List<&2, U32>, +s2: List<&2, U32>,
  p1: Laws.maximal_subpart.sequence_prefix(b1, more, first, s1),
  p2: Laws.maximal_subpart.sequence_prefix(b1, more, first, s2)) -> {s1 == s2 : List<&2, U32>}:
  (prefix1, facts1) = p1
  (+r1, e1) = prefix1
  (begins1, longest1) = facts1
  (prefix2, facts2) = p2
  (+r2, e2) = prefix2
  (begins2, longest2) = facts2
  utf8_proof.sequence_prefix_unique.compared(s1, s2, b1 <> more, begins1, begins2, longest1, longest2,
    utf8_proof.compare(s1, s2, b1 <> more, r1, r2, e1, e2))

def utf8_proof.maximal_subpart_unique.if(+b1: U32, +more: List<&2, U32>, begins: Bool,
  -checked: {UTF8.begins_valid_sequence([b1]) == begins : Bool},
  +s1: List<&2, U32>, +s2: List<&2, U32>,
  p1: Laws.maximal_subpart.if(b1, more, begins, checked, s1),
  p2: Laws.maximal_subpart.if(b1, more, begins, checked, s2)) -> {s1 == s2 : List<&2, U32>}:
  match begins:
    case True{}:
      utf8_proof.sequence_prefix_unique(b1, more, checked, s1, s2, p1, p2)
    case False{}:
      Equal.trans(List<&2, U32>, s1, [b1], s2, p1, Equal.sym(List<&2, U32>, s2, [b1], p2))

def Laws.maximal_subpart_unique(b1, more, s1, s2, p1, p2):
  utf8_proof.maximal_subpart_unique.if(b1, more, UTF8.begins_valid_sequence([b1]), {==},
    s1, s2, p1, p2)

# Existence: scan forward from `[b1]`, extending the prefix while it
# still begins a valid sequence.

# What `maximal_subpart.sequence_prefix` asks for, for any bytes.
def utf8_proof.Longest(+bytes: List<&2, U32>) -> Type:
  Exists(List<&2, U32>, sub =>
    Laws.is_prefix(sub, bytes) &
    {UTF8.begins_valid_sequence(sub) == True{} : Bool} &
    Laws.maximal_subpart.longest(sub, Laws.next_byte_after(bytes, sub)))

def utf8_proof.next_after_append(+s: List<&2, U32>, +r: List<&2, U32>) ->
  {Laws.next_byte_after(List.append(&2, U32, s, r), s) == List.head(&2, U32, r) : Maybe<&2, U32>}:
  match s:
    case Nil{}:
      match r:
        case Nil{}: {==}
        case x <> xs: {==}
    case +h <> +t:
      utf8_proof.next_after_append(t, r)

def utf8_proof.next_after(+s: List<&2, U32>, +r: List<&2, U32>, +bytes: List<&2, U32>,
  e: {List.append(&2, U32, s, r) == bytes : List<&2, U32>}) ->
  {Laws.next_byte_after(bytes, s) == List.head(&2, U32, r) : Maybe<&2, U32>}:
  %e : {Laws.next_byte_after(_, s) == List.head(&2, U32, r) : Maybe<&2, U32>}
  utf8_proof.next_after_append(s, r)

def utf8_proof.longest_from_next(+s: List<&2, U32>, +bytes: List<&2, U32>,
  -next: Maybe<&2, U32>, same: {next == Laws.next_byte_after(bytes, s) : Maybe<&2, U32>},
  longest: Laws.maximal_subpart.longest(s, next)) ->
  Laws.maximal_subpart.longest(s, Laws.next_byte_after(bytes, s)):
  %same : Laws.maximal_subpart.longest(s, _)
  longest

# `s` begins a valid sequence and `s` followed by `c` does not.
def utf8_proof.longest_stop(+s: List<&2, U32>, +bytes: List<&2, U32>, +c: U32,
  +r: List<&2, U32>, +e: {List.append(&2, U32, s, c <> r) == bytes : List<&2, U32>},
  begins_s: {UTF8.begins_valid_sequence(s) == True{} : Bool},
  not_more: {UTF8.begins_valid_sequence(List.append(&2, U32, s, [c])) == False{} : Bool}) ->
  utf8_proof.Longest(bytes):
  (s, ((c <> r, e), (begins_s,
    utf8_proof.longest_from_next(s, bytes, Some{c},
      Equal.sym(Maybe<&2, U32>, Laws.next_byte_after(bytes, s), Some{c},
        utf8_proof.next_after(s, c <> r, bytes, e)),
      not_more))))

def utf8_proof.regroup_prefix(+s: List<&2, U32>, +c: U32, +r: List<&2, U32>,
  +bytes: List<&2, U32>, e: {List.append(&2, U32, s, c <> r) == bytes : List<&2, U32>}) ->
  {List.append(&2, U32, List.append(&2, U32, s, [c]), r) == bytes : List<&2, U32>}:
  Equal.trans(List<&2, U32>, List.append(&2, U32, List.append(&2, U32, s, [c]), r),
    List.append(&2, U32, s, c <> r), bytes, utf8_proof.append_assoc(s, [c], r), e)

def utf8_proof.longest_step(+s: List<&2, U32>, +bytes: List<&2, U32>, +c: U32,
  +r: List<&2, U32>, +e: {List.append(&2, U32, s, c <> r) == bytes : List<&2, U32>},
  begins_s: {UTF8.begins_valid_sequence(s) == True{} : Bool}, more: Bool,
  checked: {UTF8.begins_valid_sequence(List.append(&2, U32, s, [c])) == more : Bool},
  longer: {UTF8.begins_valid_sequence(List.append(&2, U32, s, [c])) == True{} : Bool} ->
    utf8_proof.Longest(bytes)) ->
  utf8_proof.Longest(bytes):
  match more:
    case False{}: utf8_proof.longest_stop(s, bytes, c, r, e, begins_s, checked)
    case True{}: longer(checked)

# `s` is a prefix of `bytes` that begins a valid sequence and `r` is the
# rest; some prefix at least as long is the longest.
def utf8_proof.longest_from(+r: List<&2, U32>, +s: List<&2, U32>, +bytes: List<&2, U32>,
  +e: {List.append(&2, U32, s, r) == bytes : List<&2, U32>},
  begins_s: {UTF8.begins_valid_sequence(s) == True{} : Bool}) ->
  utf8_proof.Longest(bytes):
  match r:
    case Nil{}:
      (s, ((Nil{}, e), (begins_s,
        utf8_proof.longest_from_next(s, bytes, None{},
          Equal.sym(Maybe<&2, U32>, Laws.next_byte_after(bytes, s), None{},
            utf8_proof.next_after(s, Nil{}, bytes, e)),
          Unit{}))))
    case +c <> +rest:
      utf8_proof.longest_step(s, bytes, c, rest, e, begins_s,
        UTF8.begins_valid_sequence(List.append(&2, U32, s, [c])), {==},
        t => utf8_proof.longest_from(rest, List.append(&2, U32, s, [c]), bytes,
          utf8_proof.regroup_prefix(s, c, rest, bytes, e), t))

def utf8_proof.maximal_subpart_exists.if(+b1: U32, +more: List<&2, U32>, begins: Bool,
  checked: {UTF8.begins_valid_sequence([b1]) == begins : Bool}) ->
  Exists(List<&2, U32>, s => Laws.maximal_subpart.if(b1, more, begins, checked, s)):
  match begins:
    case True{}: utf8_proof.longest_from(more, [b1], b1 <> more, {==}, checked)
    case False{}: ([b1], {==})

def Laws.maximal_subpart_exists(b1, more, invalid):
  utf8_proof.maximal_subpart_exists.if(b1, more, UTF8.begins_valid_sequence([b1]), {==})

def utf8_proof.append_cancel(+s: List<&2, U32>, +x: List<&2, U32>, +y: List<&2, U32>,
  +e: {List.append(&2, U32, s, x) == List.append(&2, U32, s, y) : List<&2, U32>}) ->
  {x == y : List<&2, U32>}:
  match s:
    case Nil{}: e
    case +h <> +t:
      utf8_proof.append_cancel(t, x, y,
        utf8_proof.cons_tail(h, h, List.append(&2, U32, t, x), List.append(&2, U32, t, y), e))

def utf8_proof.append_same_left(+s1: List<&2, U32>, +s2: List<&2, U32>, +rest: List<&2, U32>,
  +bytes: List<&2, U32>, same: {s1 == s2 : List<&2, U32>},
  e: {List.append(&2, U32, s2, rest) == bytes : List<&2, U32>}) ->
  {List.append(&2, U32, s1, rest) == bytes : List<&2, U32>}:
  %Equal.sym(List<&2, U32>, s1, s2, same) : {List.append(&2, U32, _, rest) == bytes : List<&2, U32>}
  e

# Decoding the first code point makes progress
# ---------------------------------------------
#
# Existence for `decodes` needs each step to consume at least one byte.
# These proofs construct a `decodes_first` result together with that
# fact; `decodes_first_exists` then drops it.

# `xs` is a suffix of `ys`.
def utf8_proof.Suffix(+xs: List<&2, U32>, +ys: List<&2, U32>) -> Type:
  Exists(List<&2, U32>, p => {List.append(&2, U32, p, xs) == ys : List<&2, U32>})

def utf8_proof.Progress.pair(+more: List<&2, U32>, p: U32 & List<&2, U32>) -> Type:
  (cp, rest) = p
  utf8_proof.Suffix(rest, more)

# A result for `b1 <> more` leaves a suffix of `more`.
def utf8_proof.Progress(+more: List<&2, U32>, result: Maybe<&1, U32 & List<&2, U32>>) -> Type:
  match result:
    case None{}: Unit
    case Some{p}: utf8_proof.Progress.pair(more, p)

def utf8_proof.next_found_progress(scalar: Maybe<&2, U32>, +rest: List<&2, U32>,
  -otherwise: List<&2, U32> -> Maybe<&1, U32 & List<&2, U32>>, +more: List<&2, U32>,
  suffix: utf8_proof.Suffix(rest, more),
  other: utf8_proof.Progress(more, otherwise(rest))) ->
  utf8_proof.Progress(more, Laws.next_scalar.found(scalar, rest, otherwise)):
  match scalar:
    case Some{cp}: suffix
    case None{}: other

def utf8_proof.next_two_progress(+b1: U32, +more: List<&2, U32>) ->
  utf8_proof.Progress(more, Laws.next_scalar.two(b1, more)):
  match more:
    case Nil{}:
      Unit{}
    case +b2 <> +after:
      utf8_proof.next_found_progress(Laws.two_byte_scalar(b1, b2), after, r => None{},
        b2 <> after, ([b2], {==}), Unit{})

def utf8_proof.next_progress(+b1: U32, +more: List<&2, U32>) ->
  utf8_proof.Progress(more, Laws.next_scalar(b1 <> more)):
  utf8_proof.next_found_progress(Laws.one_byte_scalar(b1), more,
    r => Laws.next_scalar.two(b1, r), more, (Nil{}, {==}),
    utf8_proof.next_two_progress(b1, more))

def utf8_proof.next_progress_at(+b1: U32, +more: List<&2, U32>,
  -found: Maybe<&1, U32 & List<&2, U32>>,
  checked: {Laws.next_scalar(b1 <> more) == found : Maybe<&1, U32 & List<&2, U32>>}) ->
  utf8_proof.Progress(more, found):
  %checked : utf8_proof.Progress(more, _)
  utf8_proof.next_progress(b1, more)

# The replaced result, given the maximal subpart: U+FFFD and the bytes
# after the subpart, which its `is_prefix` clause supplies.  The subpart
# is not empty, since `[b1]` begins a valid sequence and so `[]` is not
# the longest; so the bytes after it are a suffix of `more`.
def utf8_proof.replaced_from.sequence(+b1: U32, +more: List<&2, U32>,
  checked: {UTF8.begins_valid_sequence([b1]) == True{} : Bool},
  +sub: List<&2, U32>, +rest: List<&2, U32>,
  +split: {List.append(&2, U32, sub, rest) == b1 <> more : List<&2, U32>},
  facts: {UTF8.begins_valid_sequence(sub) == True{} : Bool} &
    Laws.maximal_subpart.longest(sub, Laws.next_byte_after(b1 <> more, sub))) ->
  Exists(Maybe<&1, U32 & List<&2, U32>>, result =>
    Exists(List<&2, U32>, subpart => Exists(List<&2, U32>, rest =>
      Laws.maximal_subpart.sequence_prefix(b1, more, checked, subpart) &
      {List.append(&2, U32, subpart, rest) == b1 <> more : List<&2, U32>} &
      {result == Some{(Laws.replacement_char(), rest)} : Maybe<&1, U32 & List<&2, U32>>})) &
    utf8_proof.Progress(more, result)):
  match sub:
    case Nil{}:
      (begins_sub, longest) = facts
      Empty.absurd(Exists(Maybe<&1, U32 & List<&2, U32>>, result =>
          Exists(List<&2, U32>, subpart => Exists(List<&2, U32>, rest =>
            Laws.maximal_subpart.sequence_prefix(b1, more, checked, subpart) &
            {List.append(&2, U32, subpart, rest) == b1 <> more : List<&2, U32>} &
            {result == Some{(Laws.replacement_char(), rest)} : Maybe<&1, U32 & List<&2, U32>>})) &
          utf8_proof.Progress(more, result)),
        utf8_proof.true_false(Equal.trans(Bool, True{}, UTF8.begins_valid_sequence([b1]), False{},
          Equal.sym(Bool, UTF8.begins_valid_sequence([b1]), True{}, checked), longest)))
    case +s <> +ss:
      (Some{(Laws.replacement_char(), rest)},
        ((s <> ss, (rest, (((rest, split), facts), (split, {==})))),
         (ss, utf8_proof.cons_tail(s, b1, List.append(&2, U32, ss, rest), more, split))))

def utf8_proof.replaced_from.if(+b1: U32, +more: List<&2, U32>, begins: Bool,
  checked: {UTF8.begins_valid_sequence([b1]) == begins : Bool},
  +sub: List<&2, U32>, maximal: Laws.maximal_subpart.if(b1, more, begins, checked, sub)) ->
  Exists(Maybe<&1, U32 & List<&2, U32>>, result =>
    Exists(List<&2, U32>, subpart => Exists(List<&2, U32>, rest =>
      Laws.maximal_subpart.if(b1, more, begins, checked, subpart) &
      {List.append(&2, U32, subpart, rest) == b1 <> more : List<&2, U32>} &
      {result == Some{(Laws.replacement_char(), rest)} : Maybe<&1, U32 & List<&2, U32>>})) &
    utf8_proof.Progress(more, result)):
  match begins:
    case True{}:
      (prefix, facts) = maximal
      (rest, split) = prefix
      utf8_proof.replaced_from.sequence(b1, more, checked, sub, rest, split, facts)
    case False{}:
      (Some{(Laws.replacement_char(), more)},
        (([b1], (more, ({==}, ({==}, {==})))), (Nil{}, {==})))

def utf8_proof.replaced_from(+b1: U32, +more: List<&2, U32>,
  found: Exists(List<&2, U32>, subpart => Laws.maximal_subpart(b1, more, subpart))) ->
  Exists(Maybe<&1, U32 & List<&2, U32>>, result =>
    Laws.decodes_first.replaced(b1, more, result) & utf8_proof.Progress(more, result)):
  (+sub, maximal) = found
  utf8_proof.replaced_from.if(b1, more, UTF8.begins_valid_sequence([b1]), {==}, sub, maximal)

def utf8_proof.found_exists(+b1: U32, +more: List<&2, U32>,
  found: Maybe<&1, U32 & List<&2, U32>>,
  checked: {Laws.next_scalar(b1 <> more) == found : Maybe<&1, U32 & List<&2, U32>>}) ->
  Exists(Maybe<&1, U32 & List<&2, U32>>, result =>
    Laws.decodes_first.found(b1, more, found, result) & utf8_proof.Progress(more, result)):
  match found:
    case Some{x}:
      (Some{x}, ({==}, utf8_proof.next_progress_at(b1, more, Some{x}, checked)))
    case None{}:
      utf8_proof.replaced_from(b1, more, Laws.maximal_subpart_exists(b1, more, checked))

# Decoding the first code point of a non-empty buffer has a result that
# leaves a suffix of the bytes after the first.
def utf8_proof.first_exists(+b1: U32, +more: List<&2, U32>) ->
  Exists(Maybe<&1, U32 & List<&2, U32>>, result =>
    Laws.decodes_first(b1 <> more, result) & utf8_proof.Progress(more, result)):
  utf8_proof.found_exists(b1, more, Laws.next_scalar(b1 <> more), {==})

def utf8_proof.first_exists.drop(+b1: U32, +more: List<&2, U32>,
  found: Exists(Maybe<&1, U32 & List<&2, U32>>, result =>
    Laws.decodes_first(b1 <> more, result) & utf8_proof.Progress(more, result))) ->
  Exists(Maybe<&1, U32 & List<&2, U32>>, result => Laws.decodes_first(b1 <> more, result)):
  (result, both) = found
  (decoded, progress) = both
  (result, decoded)

def Laws.decodes_first_exists(bytes):
  match bytes:
    case Nil{}:
      (None{}, {==})
    case +b1 <> +more:
      utf8_proof.first_exists.drop(b1, more, utf8_proof.first_exists(b1, more))

def Laws.decodes_first_empty(result, decoded):
  decoded

def utf8_proof.found_some(+b1: U32, +more: List<&2, U32>,
  found: Maybe<&1, U32 & List<&2, U32>>, result: Maybe<&1, U32 & List<&2, U32>>,
  decoded: Laws.decodes_first.found(b1, more, found, result)) ->
  {Maybe.is_some(&1, U32 & List<&2, U32>, result) == True{} : Bool}:
  match found:
    case Some{x}:
      %Equal.sym(Maybe<&1, U32 & List<&2, U32>>, result, Some{x}, decoded) :
        {Maybe.is_some(&1, U32 & List<&2, U32>, _) == True{} : Bool}
      {==}
    case None{}:
      (sub, more1) = decoded
      (rest, more2) = more1
      (maximal, more3) = more2
      (split, produced) = more3
      %Equal.sym(Maybe<&1, U32 & List<&2, U32>>, result,
          Some{(Laws.replacement_char(), rest)}, produced) :
        {Maybe.is_some(&1, U32 & List<&2, U32>, _) == True{} : Bool}
      {==}

def Laws.decodes_first_nonempty(b1, more, result, decoded):
  utf8_proof.found_some(b1, more, Laws.next_scalar(b1 <> more), result, decoded)

def utf8_proof.replaced_unique(+b1: U32, +more: List<&2, U32>,
  r1: Maybe<&1, U32 & List<&2, U32>>, r2: Maybe<&1, U32 & List<&2, U32>>,
  d1: Laws.decodes_first.replaced(b1, more, r1),
  d2: Laws.decodes_first.replaced(b1, more, r2)) ->
  {r1 == r2 : Maybe<&1, U32 & List<&2, U32>>}:
  (+sp1, d1a) = d1
  (+rest1, d1b) = d1a
  (m1, d1c) = d1b
  (a1, res1) = d1c
  (+sp2, d2a) = d2
  (+rest2, d2b) = d2a
  (m2, d2c) = d2b
  (a2, res2) = d2c
  +same_sp = Laws.maximal_subpart_unique(b1, more, sp1, sp2, m1, m2)
  +a2_sp1 = utf8_proof.append_same_left(sp1, sp2, rest2, b1 <> more, same_sp, a2)
  +same_rest = utf8_proof.append_cancel(sp1, rest1, rest2,
    Equal.trans(List<&2, U32>, List.append(&2, U32, sp1, rest1), b1 <> more,
      List.append(&2, U32, sp1, rest2), a1,
      Equal.sym(List<&2, U32>, List.append(&2, U32, sp1, rest2), b1 <> more, a2_sp1)))
  Equal.trans(Maybe<&1, U32 & List<&2, U32>>, r1, Some{(Laws.replacement_char(), rest1)}, r2, res1,
    Equal.trans(Maybe<&1, U32 & List<&2, U32>>, Some{(Laws.replacement_char(), rest1)},
      Some{(Laws.replacement_char(), rest2)}, r2,
      Equal.cong(List<&2, U32>, Maybe<&1, U32 & List<&2, U32>>,
        x => Some{(Laws.replacement_char(), x)}, rest1, rest2, same_rest),
      Equal.sym(Maybe<&1, U32 & List<&2, U32>>, r2, Some{(Laws.replacement_char(), rest2)}, res2)))

def utf8_proof.found_unique(+b1: U32, +more: List<&2, U32>,
  found: Maybe<&1, U32 & List<&2, U32>>,
  r1: Maybe<&1, U32 & List<&2, U32>>, r2: Maybe<&1, U32 & List<&2, U32>>,
  d1: Laws.decodes_first.found(b1, more, found, r1),
  d2: Laws.decodes_first.found(b1, more, found, r2)) ->
  {r1 == r2 : Maybe<&1, U32 & List<&2, U32>>}:
  match found:
    case Some{x}:
      Equal.trans(Maybe<&1, U32 & List<&2, U32>>, r1, Some{x}, r2, d1,
        Equal.sym(Maybe<&1, U32 & List<&2, U32>>, r2, Some{x}, d2))
    case None{}:
      utf8_proof.replaced_unique(b1, more, r1, r2, d1, d2)

def Laws.decodes_first_unique(bytes, r1, r2, d1, d2):
  match bytes:
    case Nil{}:
      Equal.trans(Maybe<&1, U32 & List<&2, U32>>, r1, None{}, r2, d1,
        Equal.sym(Maybe<&1, U32 & List<&2, U32>>, r2, None{}, d2))
    case +b1 <> +more:
      utf8_proof.found_unique(b1, more, Laws.next_scalar(b1 <> more), r1, r2, d1, d2)

# Decoding a complete buffer
# --------------------------

# Existence: decode one code point at a time.  Bend accepts a recursion
# only on a shrinking argument, so the recursion is on `fuel`, a list
# that the remaining bytes are always a suffix of.

def utf8_proof.suffix_nil(+b1: U32, +more: List<&2, U32>, +p: List<&2, U32>,
  e: {List.append(&2, U32, p, b1 <> more) == Nil{} : List<&2, U32>}) -> Empty:
  match p:
    case Nil{}: utf8_proof.cons_nil(b1, more, e)
    case +q <> +qs: utf8_proof.cons_nil(q, List.append(&2, U32, qs, b1 <> more), e)

def utf8_proof.suffix_tail.split(+f: U32, +fs: List<&2, U32>, +b1: U32, +more: List<&2, U32>,
  +p: List<&2, U32>, e: {List.append(&2, U32, p, b1 <> more) == f <> fs : List<&2, U32>}) ->
  utf8_proof.Suffix(more, fs):
  match p:
    case Nil{}:
      (Nil{}, utf8_proof.cons_tail(b1, f, more, fs, e))
    case +q <> +qs:
      (List.append(&2, U32, qs, [b1]),
        Equal.trans(List<&2, U32>, List.append(&2, U32, List.append(&2, U32, qs, [b1]), more),
          List.append(&2, U32, qs, b1 <> more), fs, utf8_proof.append_assoc(qs, [b1], more),
          utf8_proof.cons_tail(q, f, List.append(&2, U32, qs, b1 <> more), fs, e)))

# If `b1 <> more` is a suffix of `f <> fs`, `more` is a suffix of `fs`.
def utf8_proof.suffix_tail(+f: U32, +fs: List<&2, U32>, +b1: U32, +more: List<&2, U32>,
  suffix: utf8_proof.Suffix(b1 <> more, f <> fs)) -> utf8_proof.Suffix(more, fs):
  (+p, e) = suffix
  utf8_proof.suffix_tail.split(f, fs, b1, more, p, e)

def utf8_proof.suffix_nil_absurd(+b1: U32, +more: List<&2, U32>,
  suffix: utf8_proof.Suffix(b1 <> more, Nil{})) -> Empty:
  (+p, e) = suffix
  utf8_proof.suffix_nil(b1, more, p, e)

def utf8_proof.suffix_trans.regroup(+q: List<&2, U32>, +p: List<&2, U32>, +xs: List<&2, U32>,
  +ys: List<&2, U32>, +zs: List<&2, U32>,
  xy: {List.append(&2, U32, p, xs) == ys : List<&2, U32>},
  yz: {List.append(&2, U32, q, ys) == zs : List<&2, U32>}) ->
  {List.append(&2, U32, q, List.append(&2, U32, p, xs)) == zs : List<&2, U32>}:
  %Equal.sym(List<&2, U32>, List.append(&2, U32, p, xs), ys, xy) :
    {List.append(&2, U32, q, _) == zs : List<&2, U32>}
  yz

def utf8_proof.suffix_trans.split(+xs: List<&2, U32>, +ys: List<&2, U32>, +zs: List<&2, U32>,
  +p: List<&2, U32>, xy: {List.append(&2, U32, p, xs) == ys : List<&2, U32>},
  yz: utf8_proof.Suffix(ys, zs)) -> utf8_proof.Suffix(xs, zs):
  (+q, e) = yz
  (List.append(&2, U32, q, p),
    Equal.trans(List<&2, U32>, List.append(&2, U32, List.append(&2, U32, q, p), xs),
      List.append(&2, U32, q, List.append(&2, U32, p, xs)), zs,
      utf8_proof.append_assoc(q, p, xs),
      utf8_proof.suffix_trans.regroup(q, p, xs, ys, zs, xy, e)))

def utf8_proof.suffix_trans(+xs: List<&2, U32>, +ys: List<&2, U32>, +zs: List<&2, U32>,
  xy: utf8_proof.Suffix(xs, ys), yz: utf8_proof.Suffix(ys, zs)) -> utf8_proof.Suffix(xs, zs):
  (+p, e) = xy
  utf8_proof.suffix_trans.split(xs, ys, zs, p, e, yz)

# The scalars for `b1 <> more`, given the first result and the scalars
# for what follows it.
def utf8_proof.decodes_cons(+bytes: List<&2, U32>, +cp: U32, +rest: List<&2, U32>,
  decoded: Laws.decodes_first(bytes, Some{(cp, rest)}),
  tail: Exists(String, text => Laws.decodes.go(text, rest))) ->
  Exists(String, text => Laws.decodes.go(text, bytes)):
  (+more, decoded_rest) = tail
  (SCon{Chr{cp}, more}, (rest, (decoded, decoded_rest)))

def utf8_proof.decodes_exists.pair(+fs: List<&2, U32>, +b1: U32, +more: List<&2, U32>,
  more_fs: utf8_proof.Suffix(more, fs), p: U32 & List<&2, U32>,
  decoded: Laws.decodes_first(b1 <> more, Some{p}),
  progress: utf8_proof.Progress.pair(more, p),
  recurse: @rest: List<&2, U32> -> utf8_proof.Suffix(rest, fs) ->
    Exists(String, text => Laws.decodes.go(text, rest))) ->
  Exists(String, text => Laws.decodes.go(text, b1 <> more)):
  (+cp, +rest) = p
  utf8_proof.decodes_cons(b1 <> more, cp, rest, decoded,
    recurse(rest, utf8_proof.suffix_trans(rest, more, fs, progress, more_fs)))

def utf8_proof.decodes_exists.result(+fs: List<&2, U32>, +b1: U32, +more: List<&2, U32>,
  more_fs: utf8_proof.Suffix(more, fs), result: Maybe<&1, U32 & List<&2, U32>>,
  decoded: Laws.decodes_first(b1 <> more, result),
  progress: utf8_proof.Progress(more, result),
  recurse: @rest: List<&2, U32> -> utf8_proof.Suffix(rest, fs) ->
    Exists(String, text => Laws.decodes.go(text, rest))) ->
  Exists(String, text => Laws.decodes.go(text, b1 <> more)):
  match result:
    case None{}:
      (SNil{}, decoded)
    case Some{p}:
      utf8_proof.decodes_exists.pair(fs, b1, more, more_fs, p, decoded, progress, recurse)

def utf8_proof.decodes_exists.step(+fs: List<&2, U32>, +b1: U32, +more: List<&2, U32>,
  more_fs: utf8_proof.Suffix(more, fs),
  first: Exists(Maybe<&1, U32 & List<&2, U32>>, result =>
    Laws.decodes_first(b1 <> more, result) & utf8_proof.Progress(more, result)),
  recurse: @rest: List<&2, U32> -> utf8_proof.Suffix(rest, fs) ->
    Exists(String, text => Laws.decodes.go(text, rest))) ->
  Exists(String, text => Laws.decodes.go(text, b1 <> more)):
  (result, both) = first
  (decoded, progress) = both
  utf8_proof.decodes_exists.result(fs, b1, more, more_fs, result, decoded, progress, recurse)

def utf8_proof.decodes_exists.go(+fuel: List<&2, U32>, +bytes: List<&2, U32>,
  suffix: utf8_proof.Suffix(bytes, fuel)) ->
  Exists(String, text => Laws.decodes.go(text, bytes)):
  match fuel bytes:
    case _ Nil{}:
      (SNil{}, {==})
    case Nil{} +b1 <> +more:
      Empty.absurd(Exists(String, text => Laws.decodes.go(text, b1 <> more)),
        utf8_proof.suffix_nil_absurd(b1, more, suffix))
    case +f <> +fs +b1 <> +more:
      utf8_proof.decodes_exists.step(fs, b1, more,
        utf8_proof.suffix_tail(f, fs, b1, more, suffix),
        utf8_proof.first_exists(b1, more),
        rest => sfx => utf8_proof.decodes_exists.go(fs, rest, sfx))

def Laws.decodes_exists(bytes):
  utf8_proof.decodes_exists.go(bytes, bytes, (Nil{}, {==}))

# Uniqueness: by induction on the two lists, using `decodes_first_unique`
# at each step.

def utf8_proof.first_of(d: U32, result: Maybe<&1, U32 & List<&2, U32>>) -> U32:
  match result:
    case None{}: d
    case Some{p}: Pair.fst(U32, List<&2, U32>, p)

def utf8_proof.rest_of(d: List<&2, U32>, result: Maybe<&1, U32 & List<&2, U32>>) -> List<&2, U32>:
  match result:
    case None{}: d
    case Some{p}: Pair.snd(U32, List<&2, U32>, p)

def utf8_proof.some_first(+c1: U32, +c2: U32, +r1: List<&2, U32>, +r2: List<&2, U32>,
  e: {Some{(c1, r1)} == Some{(c2, r2)} : Maybe<&1, U32 & List<&2, U32>>}) -> {c1 == c2 : U32}:
  Equal.cong(Maybe<&1, U32 & List<&2, U32>>, U32, m => utf8_proof.first_of(c1, m),
    Some{(c1, r1)}, Some{(c2, r2)}, e)

def utf8_proof.some_rest(+c1: U32, +c2: U32, +r1: List<&2, U32>, +r2: List<&2, U32>,
  e: {Some{(c1, r1)} == Some{(c2, r2)} : Maybe<&1, U32 & List<&2, U32>>}) -> {r1 == r2 : List<&2, U32>}:
  Equal.cong(Maybe<&1, U32 & List<&2, U32>>, List<&2, U32>, m => utf8_proof.rest_of(r1, m),
    Some{(c1, r1)}, Some{(c2, r2)}, e)

def utf8_proof.none_some(+c: U32, +r: List<&2, U32>,
  e: {None{} == Some{(c, r)} : Maybe<&1, U32 & List<&2, U32>>}) -> Empty:
  H.hex_u32.false_true(Equal.cong(Maybe<&1, U32 & List<&2, U32>>, Bool,
    m => Maybe.is_some(&1, U32 & List<&2, U32>, m), None{}, Some{(c, r)}, e))

def utf8_proof.decodes_at(+text: String, +from: List<&2, U32>, +to: List<&2, U32>,
  same: {from == to : List<&2, U32>}, decoded: Laws.decodes.go(text, from)) ->
  Laws.decodes.go(text, to):
  %same : Laws.decodes.go(text, _)
  decoded

def utf8_proof.scon_eq(+c1: U32, +c2: U32, +t1: String, +t2: String,
  ec: {c1 == c2 : U32}, et: {t1 == t2 : String}) ->
  {SCon{Chr{c1}, t1} == SCon{Chr{c2}, t2} : String}:
  %ec : {SCon{Chr{c1}, t1} == SCon{Chr{_}, t2} : String}
  %et : {SCon{Chr{c1}, t1} == SCon{Chr{c1}, _} : String}
  {==}

def utf8_proof.decodes_unique.cons(+c1: U32, +c2: U32, +t1: String, +t2: String,
  +r1: List<&2, U32>, +r2: List<&2, U32>,
  +e: {Some{(c1, r1)} == Some{(c2, r2)} : Maybe<&1, U32 & List<&2, U32>>},
  g2: Laws.decodes.go(t2, r2),
  tails: Laws.decodes.go(t2, r1) -> {t1 == t2 : String}) ->
  {SCon{Chr{c1}, t1} == SCon{Chr{c2}, t2} : String}:
  utf8_proof.scon_eq(c1, c2, t1, t2, utf8_proof.some_first(c1, c2, r1, r2, e),
    tails(utf8_proof.decodes_at(t2, r2, r1,
      Equal.sym(List<&2, U32>, r1, r2, utf8_proof.some_rest(c1, c2, r1, r2, e)), g2)))

def utf8_proof.decodes_unique.go(+t1: String, +t2: String, +bytes: List<&2, U32>,
  d1: Laws.decodes.go(t1, bytes), d2: Laws.decodes.go(t2, bytes)) -> {t1 == t2 : String}:
  match t1 t2:
    case SNil{} SNil{}:
      {==}
    case SNil{} SCon{Chr{+c}, +cs}:
      (+rest, facts) = d2
      (first, others) = facts
      Empty.absurd({SNil{} == SCon{Chr{c}, cs} : String},
        utf8_proof.none_some(c, rest,
          Laws.decodes_first_unique(bytes, None{}, Some{(c, rest)}, d1, first)))
    case SCon{Chr{+c}, +cs} SNil{}:
      (+rest, facts) = d1
      (first, others) = facts
      Empty.absurd({SCon{Chr{c}, cs} == SNil{} : String},
        utf8_proof.none_some(c, rest,
          Laws.decodes_first_unique(bytes, None{}, Some{(c, rest)}, d2, first)))
    case SCon{Chr{+c1}, +m1} SCon{Chr{+c2}, +m2}:
      (+r1, facts1) = d1
      (first1, g1) = facts1
      (+r2, facts2) = d2
      (first2, g2) = facts2
      utf8_proof.decodes_unique.cons(c1, c2, m1, m2, r1, r2,
        Laws.decodes_first_unique(bytes, Some{(c1, r1)}, Some{(c2, r2)}, first1, first2), g2,
        g => utf8_proof.decodes_unique.go(m1, m2, r1, g1, g))

def Laws.decodes_unique(bytes, t1, t2, d1, d2):
  utf8_proof.decodes_unique.go(t1, t2, bytes, d1, d2)

# Each example gives, for each scalar, the bytes left after it; for a
# replaced scalar, also the maximal subpart and its proof.
def Laws.decodes_examples():
  ({==},
  (([66], ({==}, ([], ({==}, {==})))),
  (([], ({==}, {==})),
  (([65], (([194], ([65], ((([65], {==}), ({==}, {==})), ({==}, {==})))),
    ([], ({==}, {==})))),
  (([128], (([192], ([128], ({==}, ({==}, {==})))),
    ([], (([128], ([], ({==}, ({==}, {==})))), {==})))),
  (([], (([194], ([], ((([], {==}), ({==}, Unit{})), ({==}, {==})))), {==})),
  (([194, 169], (([194], ([194, 169], ((([194, 169], {==}), ({==}, {==})), ({==}, {==})))),
    ([], ({==}, {==})))),
  ([194, 169, 255], ({==},
    ([255], ({==},
      ([], (([255], ([], ({==}, ({==}, {==})))), {==})))))))))))))

# Running the decoder satisfies `decodes`
# ---------------------------------------
#
# The decoder's byte loop, `UTF8.decode_buffer.bytes`, keeps pending
# either nothing or one byte that begins a valid sequence without being
# one.  Each step turns a decoding of what follows into a decoding of
# the whole input; at the end, a pending byte is replaced.

def utf8_proof.Pending(pending: List<&2, U32>) -> Type:
  match pending:
    case Nil{}:
      Unit
    case +p <> Nil{}:
      {UTF8.begins_valid_sequence([p]) == True{} : Bool} &
      {UTF8.sequence_scalar([p]) == None{} : Maybe<&2, U32>}
    case _:
      Empty

# After a step from `pending` on byte `b`, with `rest` still to come:
# the new pending bytes keep the invariant, and the step's text followed
# by any decoding of what remains is a decoding of everything.
def utf8_proof.StepOK(+pending: List<&2, U32>, +b: U32, +rest: List<&2, U32>,
  stepped: UTF8.decode_buffer.Step()) -> Type:
  (text, +next) = stepped
  utf8_proof.Pending(next) &
  (@after: String -> Laws.decodes(List.append(&2, U32, next, rest), after) ->
    Laws.decodes(List.append(&2, U32, pending, b <> rest), text ++ after))

def utf8_proof.final_text(step: UTF8.decode_buffer.Step()) -> String:
  (text, pending) = step
  text ++ UTF8.decode_done(pending)

# The implementation's scalar is the reference definition's.
def utf8_proof.one_scalar_is(+b1: U32, -m: Maybe<&2, U32>,
  e: {UTF8.sequence_scalar([b1]) == m : Maybe<&2, U32>}) ->
  {Laws.one_byte_scalar(b1) == m : Maybe<&2, U32>}:
  Equal.trans(Maybe<&2, U32>, Laws.one_byte_scalar(b1), UTF8.sequence_scalar([b1]), m,
    Equal.sym(Maybe<&2, U32>, UTF8.sequence_scalar([b1]), Laws.one_byte_scalar(b1),
      utf8_proof.one_scalar_agrees(b1, UTF8.valid_one_byte(b1), {==},
        UTF8.valid_one_byte(b1), {==}, {==})), e)

def utf8_proof.two_scalar_is(+b1: U32, +b2: U32, -m: Maybe<&2, U32>,
  e: {UTF8.sequence_scalar([b1, b2]) == m : Maybe<&2, U32>}) ->
  {Laws.two_byte_scalar(b1, b2) == m : Maybe<&2, U32>}:
  Equal.trans(Maybe<&2, U32>, Laws.two_byte_scalar(b1, b2), UTF8.sequence_scalar([b1, b2]), m,
    Equal.sym(Maybe<&2, U32>, UTF8.sequence_scalar([b1, b2]), Laws.two_byte_scalar(b1, b2),
      utf8_proof.two_scalar_agrees(b1, b2, UTF8.valid_two_bytes(b1, b2), {==},
        UTF8.valid_two_bytes(b1, b2), {==}, {==})), e)

def utf8_proof.begins_contra(+b: U32,
  begins: {UTF8.begins_valid_sequence([b]) == True{} : Bool},
  not_begins: {UTF8.begins_valid_sequence([b]) == False{} : Bool}) -> Empty:
  utf8_proof.true_false(Equal.trans(Bool, True{}, UTF8.begins_valid_sequence([b]), False{},
    Equal.sym(Bool, UTF8.begins_valid_sequence([b]), True{}, begins), not_begins))

# A reference scalar is None when its validity test cannot be True.
def utf8_proof.one_scalar_none(+byte: U32, valid: Bool,
  -checked: {UTF8.valid_one_byte(byte) == valid : Bool},
  invalid: {valid == True{} : Bool} -> Empty) ->
  {Laws.one_byte_scalar.if(byte, valid, checked) == None{} : Maybe<&2, U32>}:
  match valid:
    case False{}: {==}
    case True{}: Empty.absurd({Laws.one_byte_scalar.if(byte, True{}, checked) == None{} : Maybe<&2, U32>}, invalid({==}))

def utf8_proof.two_scalar_none(+b1: U32, +b2: U32, valid: Bool,
  -checked: {UTF8.valid_two_bytes(b1, b2) == valid : Bool},
  invalid: {valid == True{} : Bool} -> Empty) ->
  {Laws.two_byte_scalar.if(b1, b2, valid, checked) == None{} : Maybe<&2, U32>}:
  match valid:
    case False{}: {==}
    case True{}: Empty.absurd({Laws.two_byte_scalar.if(b1, b2, True{}, checked) == None{} : Maybe<&2, U32>}, invalid({==}))

# A byte that begins no valid sequence is not one, nor the start of a
# two-byte one.
def utf8_proof.not_one(+b: U32, +not_begins: {UTF8.begins_valid_sequence([b]) == False{} : Bool}) ->
  {Laws.one_byte_scalar(b) == None{} : Maybe<&2, U32>}:
  utf8_proof.one_scalar_none(b, UTF8.valid_one_byte(b), {==},
    valid => utf8_proof.begins_contra(b, utf8_proof.begins_from([b], Nil{}, valid), not_begins))

def utf8_proof.not_two(+b: U32, +b2: U32,
  +not_begins: {UTF8.begins_valid_sequence([b]) == False{} : Bool}) ->
  {Laws.two_byte_scalar(b, b2) == None{} : Maybe<&2, U32>}:
  utf8_proof.two_scalar_none(b, b2, UTF8.valid_two_bytes(b, b2), {==},
    valid => utf8_proof.begins_contra(b, utf8_proof.begins_from([b], [b2], valid), not_begins))

def utf8_proof.two_none_all(+b: U32, +rest: List<&2, U32>,
  none: @b2: U32 -> {Laws.two_byte_scalar(b, b2) == None{} : Maybe<&2, U32>}) ->
  {Laws.next_scalar.two(b, rest) == None{} : Maybe<&1, U32 & List<&2, U32>>}:
  match rest:
    case Nil{}: {==}
    case +b2 <> +after:
      %Equal.sym(Maybe<&2, U32>, Laws.two_byte_scalar(b, b2), None{}, none(b2)) :
        {Laws.next_scalar.found(_, after, r => None{}) == None{} : Maybe<&1, U32 & List<&2, U32>>}
      {==}

def utf8_proof.two_none_at(+p: U32, +b: U32, +rest: List<&2, U32>,
  none: {Laws.two_byte_scalar(p, b) == None{} : Maybe<&2, U32>}) ->
  {Laws.next_scalar.two(p, b <> rest) == None{} : Maybe<&1, U32 & List<&2, U32>>}:
  %Equal.sym(Maybe<&2, U32>, Laws.two_byte_scalar(p, b), None{}, none) :
    {Laws.next_scalar.found(_, rest, r => None{}) == None{} : Maybe<&1, U32 & List<&2, U32>>}
  {==}

def utf8_proof.next_none(+b: U32, +rest: List<&2, U32>,
  one: {Laws.one_byte_scalar(b) == None{} : Maybe<&2, U32>},
  two: {Laws.next_scalar.two(b, rest) == None{} : Maybe<&1, U32 & List<&2, U32>>}) ->
  {Laws.next_scalar(b <> rest) == None{} : Maybe<&1, U32 & List<&2, U32>>}:
  %Equal.sym(Maybe<&2, U32>, Laws.one_byte_scalar(b), None{}, one) :
    {Laws.next_scalar.found(_, rest, r => Laws.next_scalar.two(b, r)) == None{} : Maybe<&1, U32 & List<&2, U32>>}
  two

def utf8_proof.next_one(+b: U32, +rest: List<&2, U32>, +cp: U32,
  one: {Laws.one_byte_scalar(b) == Some{cp} : Maybe<&2, U32>}) ->
  {Laws.next_scalar(b <> rest) == Some{(cp, rest)} : Maybe<&1, U32 & List<&2, U32>>}:
  %Equal.sym(Maybe<&2, U32>, Laws.one_byte_scalar(b), Some{cp}, one) :
    {Laws.next_scalar.found(_, rest, r => Laws.next_scalar.two(b, r)) == Some{(cp, rest)} : Maybe<&1, U32 & List<&2, U32>>}
  {==}

def utf8_proof.next_two(+p: U32, +b: U32, +rest: List<&2, U32>, +cp: U32,
  one: {Laws.one_byte_scalar(p) == None{} : Maybe<&2, U32>},
  two: {Laws.two_byte_scalar(p, b) == Some{cp} : Maybe<&2, U32>}) ->
  {Laws.next_scalar(p <> b <> rest) == Some{(cp, rest)} : Maybe<&1, U32 & List<&2, U32>>}:
  %Equal.sym(Maybe<&2, U32>, Laws.one_byte_scalar(p), None{}, one) :
    {Laws.next_scalar.found(_, b <> rest, r => Laws.next_scalar.two(p, r)) == Some{(cp, rest)} : Maybe<&1, U32 & List<&2, U32>>}
  %Equal.sym(Maybe<&2, U32>, Laws.two_byte_scalar(p, b), Some{cp}, two) :
    {Laws.next_scalar.found(_, rest, r => None{}) == Some{(cp, rest)} : Maybe<&1, U32 & List<&2, U32>>}
  {==}

# A byte that begins no valid sequence is its own maximal subpart.
def utf8_proof.single_subpart.if(+b1: U32, +more: List<&2, U32>, begins: Bool,
  checked: {UTF8.begins_valid_sequence([b1]) == begins : Bool},
  not_begins: {UTF8.begins_valid_sequence([b1]) == False{} : Bool}) ->
  Laws.maximal_subpart.if(b1, more, begins, checked, [b1]):
  match begins:
    case False{}: {==}
    case True{}:
      Empty.absurd(Laws.maximal_subpart.sequence_prefix(b1, more, checked, [b1]),
        utf8_proof.begins_contra(b1, checked, not_begins))

def utf8_proof.single_subpart(+b1: U32, +more: List<&2, U32>,
  not_begins: {UTF8.begins_valid_sequence([b1]) == False{} : Bool}) ->
  Laws.maximal_subpart(b1, more, [b1]):
  utf8_proof.single_subpart.if(b1, more, UTF8.begins_valid_sequence([b1]), {==}, not_begins)

# A byte that begins a valid sequence, which the next byte (if any)
# cannot continue, is its own maximal subpart.
def utf8_proof.lead_subpart.if(+p: U32, +more: List<&2, U32>, begins: Bool,
  checked: {UTF8.begins_valid_sequence([p]) == begins : Bool},
  lead: {UTF8.begins_valid_sequence([p]) == True{} : Bool},
  longest: Laws.maximal_subpart.longest([p], Laws.next_byte_after(p <> more, [p]))) ->
  Laws.maximal_subpart.if(p, more, begins, checked, [p]):
  match begins:
    case True{}: ((more, {==}), (lead, longest))
    case False{}:
      Empty.absurd(Laws.maximal_subpart.single_byte(p, more, checked, [p]),
        utf8_proof.begins_contra(p, lead, checked))

def utf8_proof.lead_subpart(+p: U32, +more: List<&2, U32>,
  lead: {UTF8.begins_valid_sequence([p]) == True{} : Bool},
  longest: Laws.maximal_subpart.longest([p], Laws.next_byte_after(p <> more, [p]))) ->
  Laws.maximal_subpart(p, more, [p]):
  utf8_proof.lead_subpart.if(p, more, UTF8.begins_valid_sequence([p]), {==}, lead, longest)

def utf8_proof.first_found(+b1: U32, +more: List<&2, U32>, -x: U32 & List<&2, U32>,
  e: {Laws.next_scalar(b1 <> more) == Some{x} : Maybe<&1, U32 & List<&2, U32>>}) ->
  Laws.decodes_first(b1 <> more, Some{x}):
  %Equal.sym(Maybe<&1, U32 & List<&2, U32>>, Laws.next_scalar(b1 <> more), Some{x}, e) :
    Laws.decodes_first.found(b1, more, _, Some{x})
  {==}

def utf8_proof.first_replaced(+b1: U32, +more: List<&2, U32>, +sub: List<&2, U32>,
  +rest: List<&2, U32>,
  e: {Laws.next_scalar(b1 <> more) == None{} : Maybe<&1, U32 & List<&2, U32>>},
  maximal: Laws.maximal_subpart(b1, more, sub),
  split: {List.append(&2, U32, sub, rest) == b1 <> more : List<&2, U32>}) ->
  Laws.decodes_first(b1 <> more, Some{(Laws.replacement_char(), rest)}):
  %Equal.sym(Maybe<&1, U32 & List<&2, U32>>, Laws.next_scalar(b1 <> more), None{}, e) :
    Laws.decodes_first.found(b1, more, _, Some{(Laws.replacement_char(), rest)})
  (sub, (rest, (maximal, (split, {==}))))

# A step with nothing pending.
def utf8_proof.start_ok.if(+b: U32, +rest: List<&2, U32>, scalar: Maybe<&2, U32>,
  scalar_is: {UTF8.sequence_scalar([b]) == scalar : Maybe<&2, U32>}, begins: Bool,
  +begins_is: {UTF8.begins_valid_sequence([b]) == begins : Bool}) ->
  utf8_proof.StepOK(Nil{}, b, rest, UTF8.decode_buffer.advance([b], scalar, begins,
    u => (UTF8.replacement_char_string(), Nil{}))):
  match scalar begins:
    case Some{+cp} _:
      (Unit{}, after => d =>
        (rest, (utf8_proof.first_found(b, rest, (cp, rest),
          utf8_proof.next_one(b, rest, cp, utf8_proof.one_scalar_is(b, Some{cp}, scalar_is))), d)))
    case None{} True{}:
      ((begins_is, scalar_is), after => d => d)
    case None{} False{}:
      (Unit{}, after => d =>
        (rest, (utf8_proof.first_replaced(b, rest, [b], rest,
          utf8_proof.next_none(b, rest, utf8_proof.not_one(b, begins_is),
            utf8_proof.two_none_all(b, rest, b2 => utf8_proof.not_two(b, b2, begins_is))),
          utf8_proof.single_subpart(b, rest, begins_is), {==}), d)))

def utf8_proof.start_ok(+b: U32, +rest: List<&2, U32>) ->
  utf8_proof.StepOK(Nil{}, b, rest, UTF8.decode_buffer.start(b)):
  utf8_proof.start_ok.if(b, rest, UTF8.sequence_scalar([b]), {==},
    UTF8.begins_valid_sequence([b]), {==})

# The pending byte cannot be continued: it is replaced, and the new byte
# starts afresh.
def utf8_proof.extend_fail(+p: U32, +b: U32, +rest: List<&2, U32>,
  s: UTF8.decode_buffer.Step(), started: utf8_proof.StepOK(Nil{}, b, rest, s),
  lead: {UTF8.begins_valid_sequence([p]) == True{} : Bool},
  one: {Laws.one_byte_scalar(p) == None{} : Maybe<&2, U32>},
  not_begins: {UTF8.begins_valid_sequence([p, b]) == False{} : Bool},
  two: {Laws.two_byte_scalar(p, b) == None{} : Maybe<&2, U32>}) ->
  utf8_proof.StepOK([p], b, rest,
    UTF8.decode_buffer.prepend(UTF8.replacement_char_string(), s)):
  (+t, +q) = s
  (pending_q, continue) = started
  (pending_q, after => d =>
    (b <> rest, (utf8_proof.first_replaced(p, b <> rest, [p], b <> rest,
      utf8_proof.next_none(p, b <> rest, one, utf8_proof.two_none_at(p, b, rest, two)),
      utf8_proof.lead_subpart(p, b <> rest, lead, not_begins), {==}),
      continue(after, d))))

def utf8_proof.two_valid_some(+p: U32, +b: U32, valid: Bool,
  -checked: {UTF8.valid_two_bytes(p, b) == valid : Bool},
  none: {UTF8.two_byte_scalar.if(p, b, valid, checked) == None{} : Maybe<&2, U32>},
  is_true: {valid == True{} : Bool}) -> Empty:
  match valid:
    case False{}: H.hex_u32.false_true(is_true)
    case True{}:
      utf8_proof.true_false(Equal.cong(Maybe<&2, U32>, Bool, m => Maybe.is_some(&2, U32, m),
        UTF8.two_byte_scalar.if(p, b, True{}, checked), None{}, none))

# A step with one byte pending.
def utf8_proof.extend_ok.if(+p: U32, +b: U32, +rest: List<&2, U32>, scalar: Maybe<&2, U32>,
  scalar_is: {UTF8.sequence_scalar([p, b]) == scalar : Maybe<&2, U32>}, begins: Bool,
  begins_is: {UTF8.begins_valid_sequence([p, b]) == begins : Bool},
  pending: utf8_proof.Pending([p])) ->
  utf8_proof.StepOK([p], b, rest, UTF8.decode_buffer.advance([p, b], scalar, begins,
    u => UTF8.decode_buffer.prepend(UTF8.replacement_char_string(), UTF8.decode_buffer.start(b)))):
  match scalar begins:
    case Some{+cp} _:
      (lead, alone) = pending
      (Unit{}, after => d =>
        (rest, (utf8_proof.first_found(p, b <> rest, (cp, rest),
          utf8_proof.next_two(p, b, rest, cp, utf8_proof.one_scalar_is(p, None{}, alone),
            utf8_proof.two_scalar_is(p, b, Some{cp}, scalar_is))), d)))
    case None{} True{}:
      Empty.absurd(utf8_proof.StepOK([p], b, rest, ("", [p, b])),
        utf8_proof.two_valid_some(p, b, UTF8.valid_two_bytes(p, b), {==}, scalar_is, begins_is))
    case None{} False{}:
      (lead, alone) = pending
      utf8_proof.extend_fail(p, b, rest, UTF8.decode_buffer.start(b), utf8_proof.start_ok(b, rest),
        lead, utf8_proof.one_scalar_is(p, None{}, alone), begins_is,
        utf8_proof.two_scalar_is(p, b, None{}, scalar_is))

def utf8_proof.step_ok(+pending: List<&2, U32>, +b: U32, +rest: List<&2, U32>,
  invariant: utf8_proof.Pending(pending)) ->
  utf8_proof.StepOK(pending, b, rest, UTF8.decode_buffer.step(pending, b)):
  match pending:
    case Nil{}:
      utf8_proof.start_ok(b, rest)
    case +p <> Nil{}:
      utf8_proof.extend_ok.if(p, b, rest, UTF8.sequence_scalar([p, b]), {==},
        UTF8.begins_valid_sequence([p, b]), {==}, invariant)
    case p <> q <> more:
      Empty.absurd(utf8_proof.StepOK(p <> q <> more, b, rest, UTF8.decode_buffer.step(p <> q <> more, b)),
        invariant)

# At the end of the input, a pending byte is replaced.
def utf8_proof.done_ok(+pending: List<&2, U32>, invariant: utf8_proof.Pending(pending)) ->
  Laws.decodes(List.append(&2, U32, pending, Nil{}), UTF8.decode_done(pending)):
  match pending:
    case Nil{}:
      {==}
    case +p <> Nil{}:
      (lead, alone) = invariant
      (Nil{}, (utf8_proof.first_replaced(p, Nil{}, [p], Nil{},
        utf8_proof.next_none(p, Nil{}, utf8_proof.one_scalar_is(p, None{}, alone), {==}),
        utf8_proof.lead_subpart(p, Nil{}, lead, Unit{}), {==}), {==}))
    case p <> q <> more:
      Empty.absurd(Laws.decodes(List.append(&2, U32, p <> q <> more, Nil{}), UTF8.decode_done(p <> q <> more)),
        invariant)

def utf8_proof.final_prepend(+t: String, s: UTF8.decode_buffer.Step()) ->
  {utf8_proof.final_text(UTF8.decode_buffer.prepend(t, s)) == t ++ utf8_proof.final_text(s) : String}:
  (+more, +q) = s
  utf8_proof.string_assoc(t, more, UTF8.decode_done(q))

def utf8_proof.bytes_ok.then(+pending: List<&2, U32>, +b: U32, +rest: List<&2, U32>,
  stepped: UTF8.decode_buffer.Step(), ok: utf8_proof.StepOK(pending, b, rest, stepped),
  recurse: @q: List<&2, U32> -> utf8_proof.Pending(q) ->
    Laws.decodes(List.append(&2, U32, q, rest), utf8_proof.final_text(UTF8.decode_buffer.bytes(rest, q)))) ->
  Laws.decodes(List.append(&2, U32, pending, b <> rest),
    utf8_proof.final_text(UTF8.decode_buffer.then(stepped, q => UTF8.decode_buffer.bytes(rest, q)))):
  (+t, +q) = stepped
  (pending_q, continue) = ok
  %Equal.sym(String, utf8_proof.final_text(UTF8.decode_buffer.prepend(t, UTF8.decode_buffer.bytes(rest, q))),
      t ++ utf8_proof.final_text(UTF8.decode_buffer.bytes(rest, q)),
      utf8_proof.final_prepend(t, UTF8.decode_buffer.bytes(rest, q))) :
    Laws.decodes(List.append(&2, U32, pending, b <> rest), _)
  continue(utf8_proof.final_text(UTF8.decode_buffer.bytes(rest, q)), recurse(q, pending_q))

# Decoding `bytes` from `pending`, then finishing, decodes `pending`
# followed by `bytes`.
def utf8_proof.bytes_ok(+bytes: List<&2, U32>, +pending: List<&2, U32>,
  invariant: utf8_proof.Pending(pending)) ->
  Laws.decodes(List.append(&2, U32, pending, bytes),
    utf8_proof.final_text(UTF8.decode_buffer.bytes(bytes, pending))):
  match bytes:
    case Nil{}:
      utf8_proof.done_ok(pending, invariant)
    case +b <> +rest:
      utf8_proof.bytes_ok.then(pending, b, rest, UTF8.decode_buffer.step(pending, b),
        utf8_proof.step_ok(pending, b, rest, invariant),
        q => q_ok => utf8_proof.bytes_ok(rest, q, q_ok))

def utf8_proof.decodes_result(ok: Bool, +bytes: List<&2, U32>, step: UTF8.decode_buffer.Step(),
  decoded: Laws.decodes(bytes, utf8_proof.final_text(step))) ->
  Laws.decodes_result.if(ok, bytes, Laws.decoded.text(utf8_proof.expected_fed(ok, step))):
  match ok:
    case False{}:
      {==}
    case True{}:
      (+text, +pending) = step
      (text ++ UTF8.decode_done(pending), ({==}, decoded))

def Laws.utf8_decodes(buffers):
  +bytes = List.concat(&2, U32, buffers)
  %Equal.sym(Laws.Fed(), Laws.feed(buffers, Nil{}),
      utf8_proof.expected_fed(Laws.all_bytes(bytes), UTF8.decode_buffer.bytes(bytes, Nil{})),
      utf8_proof.feed_agrees(buffers, Nil{})) :
    Laws.decodes_result.if(Laws.all_bytes(bytes), bytes, Laws.decoded.text(_))
  utf8_proof.decodes_result(Laws.all_bytes(bytes), bytes, UTF8.decode_buffer.bytes(bytes, Nil{}),
    utf8_proof.bytes_ok(bytes, Nil{}, Unit{}))

# Safe and prompt
# ---------------

def utf8_proof.step_text(step: UTF8.decode_buffer.Step()) -> String:
  (text, pending) = step
  text

def utf8_proof.step_pending(step: UTF8.decode_buffer.Step()) -> List<&2, U32>:
  (text, pending) = step
  pending

def utf8_proof.final_then(step: UTF8.decode_buffer.Step(), +ys: List<&2, U32>) ->
  {utf8_proof.final_text(UTF8.decode_buffer.then(step, q => UTF8.decode_buffer.bytes(ys, q))) ==
    utf8_proof.step_text(step) ++
      utf8_proof.final_text(UTF8.decode_buffer.bytes(ys, utf8_proof.step_pending(step))) : String}:
  (+t, +q) = step
  utf8_proof.final_prepend(t, UTF8.decode_buffer.bytes(ys, q))

# Decoding `xs ++ ys` from scratch gives the text so far for `xs`, then
# what finishing with `ys` gives.
def utf8_proof.decodes_split(+xs: List<&2, U32>, +ys: List<&2, U32>) ->
  Laws.decodes(List.append(&2, U32, xs, ys),
    utf8_proof.step_text(UTF8.decode_buffer.bytes(xs, Nil{})) ++
    utf8_proof.final_text(UTF8.decode_buffer.bytes(ys,
      utf8_proof.step_pending(UTF8.decode_buffer.bytes(xs, Nil{}))))):
  %utf8_proof.final_then(UTF8.decode_buffer.bytes(xs, Nil{}), ys) :
    Laws.decodes(List.append(&2, U32, xs, ys), _)
  %utf8_proof.go_append(xs, ys, Nil{}) :
    Laws.decodes(List.append(&2, U32, xs, ys), utf8_proof.final_text(_))
  utf8_proof.bytes_ok(List.append(&2, U32, xs, ys), Nil{}, Unit{})

# The decoder's pending bytes keep the invariant.
def utf8_proof.pending_prepend(+t: String, s: UTF8.decode_buffer.Step()) ->
  {utf8_proof.step_pending(UTF8.decode_buffer.prepend(t, s)) == utf8_proof.step_pending(s) : List<&2, U32>}:
  (+more, +q) = s
  {==}

def utf8_proof.pending_ok.then(+pending: List<&2, U32>, +b: U32, +rest: List<&2, U32>,
  stepped: UTF8.decode_buffer.Step(), ok: utf8_proof.StepOK(pending, b, rest, stepped),
  recurse: @q: List<&2, U32> -> utf8_proof.Pending(q) ->
    utf8_proof.Pending(utf8_proof.step_pending(UTF8.decode_buffer.bytes(rest, q)))) ->
  utf8_proof.Pending(utf8_proof.step_pending(
    UTF8.decode_buffer.then(stepped, q => UTF8.decode_buffer.bytes(rest, q)))):
  (+t, +q) = stepped
  (pending_q, continue) = ok
  %Equal.sym(List<&2, U32>,
      utf8_proof.step_pending(UTF8.decode_buffer.prepend(t, UTF8.decode_buffer.bytes(rest, q))),
      utf8_proof.step_pending(UTF8.decode_buffer.bytes(rest, q)),
      utf8_proof.pending_prepend(t, UTF8.decode_buffer.bytes(rest, q))) :
    utf8_proof.Pending(_)
  recurse(q, pending_q)

def utf8_proof.pending_ok(+bytes: List<&2, U32>, +pending: List<&2, U32>,
  invariant: utf8_proof.Pending(pending)) ->
  utf8_proof.Pending(utf8_proof.step_pending(UTF8.decode_buffer.bytes(bytes, pending))):
  match bytes:
    case Nil{}:
      invariant
    case +b <> +rest:
      utf8_proof.pending_ok.then(pending, b, rest, UTF8.decode_buffer.step(pending, b),
        utf8_proof.step_ok(pending, b, rest, invariant),
        q => q_ok => utf8_proof.pending_ok(rest, q, q_ok))

# The text so far is the text of the byte loop's result.
def utf8_proof.string_or(d: String, m: Maybe<&2, String>) -> String:
  match m:
    case None{}: d
    case Some{x}: x

def utf8_proof.text_so_far(ok: Bool, step: UTF8.decode_buffer.Step(), +text: String,
  e: {Laws.decoded_so_far.text(utf8_proof.expected_fed(ok, step)) == Some{text} : Maybe<&2, String>}) ->
  {utf8_proof.step_text(step) == text : String}:
  match ok:
    case False{}:
      Empty.absurd({utf8_proof.step_text(step) == text : String},
        H.hex_u32.false_true(Equal.cong(Maybe<&2, String>, Bool, m => Maybe.is_some(&2, String, m),
          None{}, Some{text}, e)))
    case True{}:
      (+t, +q) = step
      Equal.cong(Maybe<&2, String>, String, m => utf8_proof.string_or(t, m), Some{t}, Some{text}, e)

def utf8_proof.so_far_at(+buffers: List<&2, List<&2, U32>>, +text: String,
  so_far: {Laws.decoded_so_far(buffers) == Some{text} : Maybe<&2, String>}) ->
  {Laws.decoded_so_far.text(utf8_proof.expected_fed(Laws.all_bytes(List.concat(&2, U32, buffers)),
    UTF8.decode_buffer.bytes(List.concat(&2, U32, buffers), Nil{}))) == Some{text} : Maybe<&2, String>}:
  %utf8_proof.feed_agrees(buffers, Nil{}) :
    {Laws.decoded_so_far.text(_) == Some{text} : Maybe<&2, String>}
  so_far

# Safe.
def utf8_proof.prefix_from.eq(+t: String, +text: String, +more: String, +full: String,
  same_text: {t == text : String}, same_full: {full == t ++ more : String}) ->
  {text ++ more == full : String}:
  %same_text : {_ ++ more == full : String}
  Equal.sym(String, full, t ++ more, same_full)

def utf8_proof.prefix_from(+t: String, +text: String, +more: String, +full: String,
  same_text: {t == text : String}, same_full: {full == t ++ more : String}) ->
  Laws.is_text_prefix(text, full):
  (more, utf8_proof.prefix_from.eq(t, text, more, full, same_text, same_full))

def utf8_proof.safe.step(+bytes: List<&2, U32>, +rest: List<&2, U32>, +text: String, +full: String,
  step: UTF8.decode_buffer.Step(),
  text_is: {utf8_proof.step_text(step) == text : String},
  split: Laws.decodes(List.append(&2, U32, bytes, rest),
    utf8_proof.step_text(step) ++
    utf8_proof.final_text(UTF8.decode_buffer.bytes(rest, utf8_proof.step_pending(step)))),
  decoded: Laws.decodes(List.append(&2, U32, bytes, rest), full)) ->
  Laws.is_text_prefix(text, full):
  (+t, +q) = step
  utf8_proof.prefix_from(t, text, utf8_proof.final_text(UTF8.decode_buffer.bytes(rest, q)), full, text_is,
    Laws.decodes_unique(List.append(&2, U32, bytes, rest), full,
      t ++ utf8_proof.final_text(UTF8.decode_buffer.bytes(rest, q)), decoded, split))

def Laws.utf8_decode_buffer_safe(buffers, text, so_far, rest, full, decoded):
  utf8_proof.safe.step(List.concat(&2, U32, buffers), rest, text, full,
    UTF8.decode_buffer.bytes(List.concat(&2, U32, buffers), Nil{}),
    utf8_proof.text_so_far(Laws.all_bytes(List.concat(&2, U32, buffers)),
      UTF8.decode_buffer.bytes(List.concat(&2, U32, buffers), Nil{}), text,
      utf8_proof.so_far_at(buffers, text, so_far)),
    utf8_proof.decodes_split(List.concat(&2, U32, buffers), rest), decoded)

# Prompt.
def utf8_proof.PromptGoal(+bytes: List<&2, U32>, +text: String, +c: U32) -> Type:
  Exists(List<&2, U32>, rest =>
    {Laws.all_bytes(rest) == True{} : Bool} &
    Exists(String, full =>
      Laws.decodes(List.append(&2, U32, bytes, rest), full) &
      (Laws.is_text_prefix(text ++ Laws.code_point_to_string(c), full) -> Empty)))

def utf8_proof.string_tail(s: String) -> String:
  match s:
    case SNil{}: SNil{}
    case SCon{h, t}: t

def utf8_proof.string_is_cons(s: String) -> Bool:
  match s:
    case SNil{}: False{}
    case SCon{h, t}: True{}

def utf8_proof.char_of(d: U32, s: String) -> U32:
  match s:
    case SNil{}: d
    case SCon{Chr{x}, t}: x

def utf8_proof.string_cancel(+t: String, +a: String, +b: String, +e: {t ++ a == t ++ b : String}) ->
  {a == b : String}:
  match t:
    case SNil{}: e
    case SCon{+h, +tt}:
      utf8_proof.string_cancel(tt, a, b,
        Equal.cong(String, String, utf8_proof.string_tail, SCon{h, tt ++ a}, SCon{h, tt ++ b}, e))

def utf8_proof.not_prefix.regroup(+text: String, +t: String, +c: U32, +more: String, +rest: String,
  +same: {t == text : String},
  e: {(text ++ SCon{Chr{c}, SNil{}}) ++ more == t ++ rest : String}) ->
  {text ++ SCon{Chr{c}, more} == text ++ rest : String}:
  Equal.trans(String, text ++ SCon{Chr{c}, more}, (text ++ SCon{Chr{c}, SNil{}}) ++ more, text ++ rest,
    Equal.sym(String, (text ++ SCon{Chr{c}, SNil{}}) ++ more, text ++ SCon{Chr{c}, more},
      utf8_proof.string_assoc(text, SCon{Chr{c}, SNil{}}, more)),
    Equal.trans(String, (text ++ SCon{Chr{c}, SNil{}}) ++ more, t ++ rest, text ++ rest, e,
      Equal.cong(String, String, x => x ++ rest, t, text, same)))

# Text that continues `t ++ rest` after `text` (which is `t`) with `c`
# would make `rest` begin with `c`.
def utf8_proof.not_prefix(+text: String, +t: String, +c: U32, +rest: String, +same: {t == text : String},
  prefix: Laws.is_text_prefix(text ++ SCon{Chr{c}, SNil{}}, t ++ rest),
  differs: @more: String -> {SCon{Chr{c}, more} == rest : String} -> Empty) -> Empty:
  (+more, e) = prefix
  differs(more, utf8_proof.string_cancel(text, SCon{Chr{c}, more}, rest,
    utf8_proof.not_prefix.regroup(text, t, c, more, rest, same, e)))

def utf8_proof.head_eq(+c1: U32, +c2: U32, +m1: String, +m2: String,
  e: {SCon{Chr{c1}, m1} == SCon{Chr{c2}, m2} : String}) -> {c1 == c2 : U32}:
  Equal.cong(String, U32, s => utf8_proof.char_of(c1, s), SCon{Chr{c1}, m1}, SCon{Chr{c2}, m2}, e)

def utf8_proof.le_at(+x: U32, +y: U32, e: {x == y : U32},
  le: {U32.is_le(x, 2047) == True{} : Bool}) -> {U32.is_le(y, 2047) == True{} : Bool}:
  %e : {U32.is_le(_, 2047) == True{} : Bool}
  le

def utf8_proof.ends_here(+c: U32, +more: String, e: {SCon{Chr{c}, more} == SNil{} : String}) -> Empty:
  utf8_proof.true_false(Equal.cong(String, Bool, utf8_proof.string_is_cons, SCon{Chr{c}, more}, SNil{}, e))

def utf8_proof.not_replacement(+c: U32, +more: String,
  small: {U32.is_le(c, 2047) == True{} : Bool},
  e: {SCon{Chr{c}, more} == SCon{Chr{65533}, SNil{}} : String}) -> Empty:
  H.hex_u32.false_true(utf8_proof.le_at(c, 65533, utf8_proof.head_eq(c, 65533, more, SNil{}, e), small))

def utf8_proof.not_two_byte(+c: U32, +cp: U32, +more: String, +rest: String,
  large: {U32.is_le(c, 2047) == False{} : Bool},
  rest_is: {rest == SCon{Chr{cp}, SNil{}} : String},
  bound: {U32.is_le(cp, 2047) == True{} : Bool},
  e: {SCon{Chr{c}, more} == rest : String}) -> Empty:
  utf8_proof.true_false(Equal.trans(Bool, True{}, U32.is_le(c, 2047), False{},
    Equal.sym(Bool, U32.is_le(c, 2047), True{},
      utf8_proof.le_at(cp, c, Equal.sym(U32, c, cp,
        utf8_proof.head_eq(c, cp, more, SNil{},
          Equal.trans(String, SCon{Chr{c}, more}, rest, SCon{Chr{cp}, SNil{}}, e, rest_is))), bound)),
    large))

# A pending byte begins a two-byte sequence, which 0x80 completes.
def utf8_proof.lead_two.if(+p: U32, one: Bool, -checked: {UTF8.valid_one_byte(p) == one : Bool},
  lead: {(one || UTF8.valid_two_bytes(p, 128)) == True{} : Bool},
  alone: {UTF8.one_byte_scalar.if(p, one, checked) == None{} : Maybe<&2, U32>}) ->
  {UTF8.valid_two_bytes(p, 128) == True{} : Bool}:
  match one:
    case False{}: lead
    case True{}:
      Empty.absurd({UTF8.valid_two_bytes(p, 128) == True{} : Bool},
        utf8_proof.true_false(Equal.cong(Maybe<&2, U32>, Bool, m => Maybe.is_some(&2, U32, m),
          UTF8.one_byte_scalar.if(p, True{}, checked), None{}, alone)))

def utf8_proof.lead_two(+p: U32,
  lead: {UTF8.begins_valid_sequence([p]) == True{} : Bool},
  alone: {UTF8.sequence_scalar([p]) == None{} : Maybe<&2, U32>}) ->
  {UTF8.valid_two_bytes(p, 128) == True{} : Bool}:
  utf8_proof.lead_two.if(p, UTF8.valid_one_byte(p), {==}, lead, alone)

def utf8_proof.TwoAfter(+p: U32, step: UTF8.decode_buffer.Step()) -> Type:
  Exists(U32, cp =>
    {utf8_proof.final_text(UTF8.decode_buffer.then(step, q => UTF8.decode_buffer.bytes(Nil{}, q))) ==
      SCon{Chr{cp}, SNil{}} : String} &
    {U32.is_le(cp, 2047) == True{} : Bool})

def utf8_proof.two_after.if(+p: U32, valid: Bool, +checked: {UTF8.valid_two_bytes(p, 128) == valid : Bool},
  is_true: {valid == True{} : Bool}) ->
  utf8_proof.TwoAfter(p, UTF8.decode_buffer.advance([p, 128], UTF8.two_byte_scalar.if(p, 128, valid, checked), valid,
    u => UTF8.decode_buffer.prepend(UTF8.replacement_char_string(), UTF8.decode_buffer.start(128)))):
  match valid:
    case True{}:
      (UTF8.decode_two_bytes(p, 128, UTF8.valid_two_bytes.has_shape(p, 128, checked)),
        ({==}, utf8_proof.exists_witness(
          {UTF8.can_encode_as_two_bytes(UTF8.decode_two_bytes(p, 128,
            UTF8.valid_two_bytes.has_shape(p, 128, checked))) == True{} : Bool},
          accepted => {UTF8.encode_as_two_bytes(UTF8.decode_two_bytes(p, 128,
            UTF8.valid_two_bytes.has_shape(p, 128, checked)), accepted) == (p, 128) : U32 & U32},
          utf8_proof.two_encode_decode((p, 128), UTF8.valid_two_bytes.has_shape(p, 128, checked)))))
    case False{}:
      Empty.absurd(utf8_proof.TwoAfter(p, UTF8.decode_buffer.advance([p, 128],
          UTF8.two_byte_scalar.if(p, 128, False{}, checked), False{},
          u => UTF8.decode_buffer.prepend(UTF8.replacement_char_string(), UTF8.decode_buffer.start(128)))),
        H.hex_u32.false_true(is_true))

# With `p` pending, the continuation 0x80 gives one character, at most
# 2047.
def utf8_proof.two_after(+p: U32,
  lead: {UTF8.begins_valid_sequence([p]) == True{} : Bool},
  alone: {UTF8.sequence_scalar([p]) == None{} : Maybe<&2, U32>}) ->
  Exists(U32, cp =>
    {utf8_proof.final_text(UTF8.decode_buffer.bytes([128], [p])) == SCon{Chr{cp}, SNil{}} : String} &
    {U32.is_le(cp, 2047) == True{} : Bool}):
  utf8_proof.two_after.if(p, UTF8.valid_two_bytes(p, 128), {==}, utf8_proof.lead_two(p, lead, alone))

def utf8_proof.prompt.large2(+bytes: List<&2, U32>, +text: String, +c: U32, +t: String, +p: U32,
  +same: {t == text : String},
  split: @rest: List<&2, U32> -> Laws.decodes(List.append(&2, U32, bytes, rest),
    t ++ utf8_proof.final_text(UTF8.decode_buffer.bytes(rest, [p]))),
  +large: {U32.is_le(c, 2047) == False{} : Bool}, +cp: U32,
  +rest_is: {utf8_proof.final_text(UTF8.decode_buffer.bytes([128], [p])) == SCon{Chr{cp}, SNil{}} : String},
  +bound: {U32.is_le(cp, 2047) == True{} : Bool}) ->
  utf8_proof.PromptGoal(bytes, text, c):
  ([128], ({==}, (t ++ utf8_proof.final_text(UTF8.decode_buffer.bytes([128], [p])),
    (split([128]), prefix => utf8_proof.not_prefix(text, t, c,
      utf8_proof.final_text(UTF8.decode_buffer.bytes([128], [p])), same, prefix,
      more => e => utf8_proof.not_two_byte(c, cp, more,
        utf8_proof.final_text(UTF8.decode_buffer.bytes([128], [p])), large, rest_is, bound, e))))))

def utf8_proof.prompt.large(+bytes: List<&2, U32>, +text: String, +c: U32, +t: String, +p: U32,
  +same: {t == text : String},
  split: @rest: List<&2, U32> -> Laws.decodes(List.append(&2, U32, bytes, rest),
    t ++ utf8_proof.final_text(UTF8.decode_buffer.bytes(rest, [p]))),
  +large: {U32.is_le(c, 2047) == False{} : Bool},
  after: Exists(U32, cp =>
    {utf8_proof.final_text(UTF8.decode_buffer.bytes([128], [p])) == SCon{Chr{cp}, SNil{}} : String} &
    {U32.is_le(cp, 2047) == True{} : Bool})) ->
  utf8_proof.PromptGoal(bytes, text, c):
  (+cp, facts) = after
  (rest_is, bound) = facts
  utf8_proof.prompt.large2(bytes, text, c, t, p, same, split, large, cp, rest_is, bound)

def utf8_proof.prompt.lead(+bytes: List<&2, U32>, +text: String, +c: U32, +t: String, +p: U32,
  +same: {t == text : String},
  lead: {UTF8.begins_valid_sequence([p]) == True{} : Bool},
  alone: {UTF8.sequence_scalar([p]) == None{} : Maybe<&2, U32>},
  split: @rest: List<&2, U32> -> Laws.decodes(List.append(&2, U32, bytes, rest),
    t ++ utf8_proof.final_text(UTF8.decode_buffer.bytes(rest, [p]))),
  small: Bool, +small_is: {U32.is_le(c, 2047) == small : Bool}) ->
  utf8_proof.PromptGoal(bytes, text, c):
  match small:
    case True{}:
      (Nil{}, ({==}, (t ++ utf8_proof.final_text(UTF8.decode_buffer.bytes(Nil{}, [p])),
        (split(Nil{}), prefix => utf8_proof.not_prefix(text, t, c, SCon{Chr{65533}, SNil{}}, same, prefix,
          more => e => utf8_proof.not_replacement(c, more, small_is, e))))))
    case False{}:
      utf8_proof.prompt.large(bytes, text, c, t, p, same, split, small_is,
        utf8_proof.two_after(p, lead, alone))

def utf8_proof.prompt.pending(+bytes: List<&2, U32>, +text: String, +c: U32, +t: String,
  +q: List<&2, U32>, +same: {t == text : String}, pending: utf8_proof.Pending(q),
  split: @rest: List<&2, U32> -> Laws.decodes(List.append(&2, U32, bytes, rest),
    t ++ utf8_proof.final_text(UTF8.decode_buffer.bytes(rest, q)))) ->
  utf8_proof.PromptGoal(bytes, text, c):
  match q:
    case Nil{}:
      (Nil{}, ({==}, (t ++ utf8_proof.final_text(UTF8.decode_buffer.bytes(Nil{}, Nil{})),
        (split(Nil{}), prefix => utf8_proof.not_prefix(text, t, c, SNil{}, same, prefix,
          more => e => utf8_proof.ends_here(c, more, e))))))
    case +p <> Nil{}:
      (lead, alone) = pending
      utf8_proof.prompt.lead(bytes, text, c, t, p, same, lead, alone, split, U32.is_le(c, 2047), {==})
    case p <> r <> more:
      Empty.absurd(utf8_proof.PromptGoal(bytes, text, c), pending)

def utf8_proof.prompt.step(+bytes: List<&2, U32>, +text: String, +c: U32,
  step: UTF8.decode_buffer.Step(),
  text_is: {utf8_proof.step_text(step) == text : String},
  pending: utf8_proof.Pending(utf8_proof.step_pending(step)),
  split: @rest: List<&2, U32> -> Laws.decodes(List.append(&2, U32, bytes, rest),
    utf8_proof.step_text(step) ++
    utf8_proof.final_text(UTF8.decode_buffer.bytes(rest, utf8_proof.step_pending(step))))) ->
  utf8_proof.PromptGoal(bytes, text, c):
  (+t, +q) = step
  utf8_proof.prompt.pending(bytes, text, c, t, q, text_is, pending, split)

def Laws.utf8_decode_buffer_prompt(buffers, text, so_far, c):
  utf8_proof.prompt.step(List.concat(&2, U32, buffers), text, c,
    UTF8.decode_buffer.bytes(List.concat(&2, U32, buffers), Nil{}),
    utf8_proof.text_so_far(Laws.all_bytes(List.concat(&2, U32, buffers)),
      UTF8.decode_buffer.bytes(List.concat(&2, U32, buffers), Nil{}), text,
      utf8_proof.so_far_at(buffers, text, so_far)),
    utf8_proof.pending_ok(List.concat(&2, U32, buffers), Nil{}, Unit{}),
    rest => utf8_proof.decodes_split(List.concat(&2, U32, buffers), rest))
