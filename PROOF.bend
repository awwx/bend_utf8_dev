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

def utf8_proof.capacity_bits(+b10: Bool, +b9: Bool, +b8: Bool, +b7: Bool, +b6: Bool, +b5: Bool, +b4: Bool, +b3: Bool, +b2: Bool, +b1: Bool, +b0: Bool) -> {UTF8.can_encode_two(UTF8.codepoint11(WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WNil{}}}}}}}}}}}})) == True{} : Bool}:
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
  {UTF8.can_encode_two(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))) == Maybe.is_some(&1, U32 & U32, Laws.two_byte_shape(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0)))) : Bool}:
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

def Laws.utf8_can_encode_two(cp):
  match cp:
    case U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      utf8_proof.capacity_model_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0)

def utf8_proof.one_capacity_model_bits(+b31: Bool, +b30: Bool, +b29: Bool, +b28: Bool, +b27: Bool, +b26: Bool, +b25: Bool, +b24: Bool, +b23: Bool, +b22: Bool, +b21: Bool, +b20: Bool, +b19: Bool, +b18: Bool, +b17: Bool, +b16: Bool, +b15: Bool, +b14: Bool, +b13: Bool, +b12: Bool, +b11: Bool, +b10: Bool, +b9: Bool, +b8: Bool, +b7: Bool, +b6: Bool, +b5: Bool, +b4: Bool, +b3: Bool, +b2: Bool, +b1: Bool, +b0: Bool) ->
  {UTF8.can_encode_one(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))) == Maybe.is_some(&2, U32, Laws.one_byte_shape(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0)))) : Bool}:
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

def Laws.utf8_can_encode_one(cp):
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
def DecodeSpec(+c: Char, +valid: {H.is_hex_digit(c) == True{} : Bool}) -> Type:
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

def HexU32Spec(+s: String, valid: {H.is_valid_hex_u32(s) == True{} : Bool}) -> Type:
  {H.hex_u32(s, valid) == HexLaws.hex_u32_spec(s) : U32}

def hex_u32.reference_values(+c1: Char, +c2: Char, +c3: Char, +c4: Char, +c5: Char, +c6: Char, +c7: Char, +c8: Char,
  valid: {H.is_valid_hex_u32(SCon{c1, SCon{c2, SCon{c3, SCon{c4, SCon{c5, SCon{c6, SCon{c7, SCon{c8, SNil{}}}}}}}}}) == True{} : Bool},
  proofs: {H.is_hex_digit(c1) == True{} : Bool} & {H.is_hex_digit(c2) == True{} : Bool} & {H.is_hex_digit(c3) == True{} : Bool} & {H.is_hex_digit(c4) == True{} : Bool} & {H.is_hex_digit(c5) == True{} : Bool} & {H.is_hex_digit(c6) == True{} : Bool} & {H.is_hex_digit(c7) == True{} : Bool} & {H.is_hex_digit(c8) == True{} : Bool}) ->
  {H.hex_u32(SCon{c1, SCon{c2, SCon{c3, SCon{c4, SCon{c5, SCon{c6, SCon{c7, SCon{c8, SNil{}}}}}}}}}, valid) == HexLaws.nibble_list_value([HexLaws.decode_value_spec(c1), HexLaws.decode_value_spec(c2), HexLaws.decode_value_spec(c3), HexLaws.decode_value_spec(c4), HexLaws.decode_value_spec(c5), HexLaws.decode_value_spec(c6), HexLaws.decode_value_spec(c7), HexLaws.decode_value_spec(c8)]) : U32}:
  match proofs:
    case (p1, p2, p3, p4, p5, p6, p7, p8):
      %decode_value_agrees(c1, p1) : {H.hex_u32(SCon{c1, SCon{c2, SCon{c3, SCon{c4, SCon{c5, SCon{c6, SCon{c7, SCon{c8, SNil{}}}}}}}}}, valid) == HexLaws.nibble_list_value([_, HexLaws.decode_value_spec(c2), HexLaws.decode_value_spec(c3), HexLaws.decode_value_spec(c4), HexLaws.decode_value_spec(c5), HexLaws.decode_value_spec(c6), HexLaws.decode_value_spec(c7), HexLaws.decode_value_spec(c8)]) : U32}
      %decode_value_agrees(c2, p2) : {H.hex_u32(SCon{c1, SCon{c2, SCon{c3, SCon{c4, SCon{c5, SCon{c6, SCon{c7, SCon{c8, SNil{}}}}}}}}}, valid) == HexLaws.nibble_list_value([H.decode(H.HexDigitChar{c1, p1}), _, HexLaws.decode_value_spec(c3), HexLaws.decode_value_spec(c4), HexLaws.decode_value_spec(c5), HexLaws.decode_value_spec(c6), HexLaws.decode_value_spec(c7), HexLaws.decode_value_spec(c8)]) : U32}
      %decode_value_agrees(c3, p3) : {H.hex_u32(SCon{c1, SCon{c2, SCon{c3, SCon{c4, SCon{c5, SCon{c6, SCon{c7, SCon{c8, SNil{}}}}}}}}}, valid) == HexLaws.nibble_list_value([H.decode(H.HexDigitChar{c1, p1}), H.decode(H.HexDigitChar{c2, p2}), _, HexLaws.decode_value_spec(c4), HexLaws.decode_value_spec(c5), HexLaws.decode_value_spec(c6), HexLaws.decode_value_spec(c7), HexLaws.decode_value_spec(c8)]) : U32}
      %decode_value_agrees(c4, p4) : {H.hex_u32(SCon{c1, SCon{c2, SCon{c3, SCon{c4, SCon{c5, SCon{c6, SCon{c7, SCon{c8, SNil{}}}}}}}}}, valid) == HexLaws.nibble_list_value([H.decode(H.HexDigitChar{c1, p1}), H.decode(H.HexDigitChar{c2, p2}), H.decode(H.HexDigitChar{c3, p3}), _, HexLaws.decode_value_spec(c5), HexLaws.decode_value_spec(c6), HexLaws.decode_value_spec(c7), HexLaws.decode_value_spec(c8)]) : U32}
      %decode_value_agrees(c5, p5) : {H.hex_u32(SCon{c1, SCon{c2, SCon{c3, SCon{c4, SCon{c5, SCon{c6, SCon{c7, SCon{c8, SNil{}}}}}}}}}, valid) == HexLaws.nibble_list_value([H.decode(H.HexDigitChar{c1, p1}), H.decode(H.HexDigitChar{c2, p2}), H.decode(H.HexDigitChar{c3, p3}), H.decode(H.HexDigitChar{c4, p4}), _, HexLaws.decode_value_spec(c6), HexLaws.decode_value_spec(c7), HexLaws.decode_value_spec(c8)]) : U32}
      %decode_value_agrees(c6, p6) : {H.hex_u32(SCon{c1, SCon{c2, SCon{c3, SCon{c4, SCon{c5, SCon{c6, SCon{c7, SCon{c8, SNil{}}}}}}}}}, valid) == HexLaws.nibble_list_value([H.decode(H.HexDigitChar{c1, p1}), H.decode(H.HexDigitChar{c2, p2}), H.decode(H.HexDigitChar{c3, p3}), H.decode(H.HexDigitChar{c4, p4}), H.decode(H.HexDigitChar{c5, p5}), _, HexLaws.decode_value_spec(c7), HexLaws.decode_value_spec(c8)]) : U32}
      %decode_value_agrees(c7, p7) : {H.hex_u32(SCon{c1, SCon{c2, SCon{c3, SCon{c4, SCon{c5, SCon{c6, SCon{c7, SCon{c8, SNil{}}}}}}}}}, valid) == HexLaws.nibble_list_value([H.decode(H.HexDigitChar{c1, p1}), H.decode(H.HexDigitChar{c2, p2}), H.decode(H.HexDigitChar{c3, p3}), H.decode(H.HexDigitChar{c4, p4}), H.decode(H.HexDigitChar{c5, p5}), H.decode(H.HexDigitChar{c6, p6}), _, HexLaws.decode_value_spec(c8)]) : U32}
      %decode_value_agrees(c8, p8) : {H.hex_u32(SCon{c1, SCon{c2, SCon{c3, SCon{c4, SCon{c5, SCon{c6, SCon{c7, SCon{c8, SNil{}}}}}}}}}, valid) == HexLaws.nibble_list_value([H.decode(H.HexDigitChar{c1, p1}), H.decode(H.HexDigitChar{c2, p2}), H.decode(H.HexDigitChar{c3, p3}), H.decode(H.HexDigitChar{c4, p4}), H.decode(H.HexDigitChar{c5, p5}), H.decode(H.HexDigitChar{c6, p6}), H.decode(H.HexDigitChar{c7, p7}), _]) : U32}
      {==}

def hex_u32_complete(
  +c1: Char, +c2: Char, +c3: Char, +c4: Char, +c5: Char, +c6: Char, +c7: Char, +c8: Char,
  +valid: {H.is_valid_hex_u32(SCon{c1, SCon{c2, SCon{c3, SCon{c4, SCon{c5, SCon{c6, SCon{c7, SCon{c8, SNil{}}}}}}}}}) == True{} : Bool},
  proofs: {H.is_hex_digit(c1) == True{} : Bool} & {H.is_hex_digit(c2) == True{} : Bool} & {H.is_hex_digit(c3) == True{} : Bool} & {H.is_hex_digit(c4) == True{} : Bool} & {H.is_hex_digit(c5) == True{} : Bool} & {H.is_hex_digit(c6) == True{} : Bool} & {H.is_hex_digit(c7) == True{} : Bool} & {H.is_hex_digit(c8) == True{} : Bool}
) -> HexU32Spec(SCon{c1, SCon{c2, SCon{c3, SCon{c4, SCon{c5, SCon{c6, SCon{c7, SCon{c8, SNil{}}}}}}}}}, valid):
  hex_u32.reference_values(c1, c2, c3, c4, c5, c6, c7, c8, valid, proofs)

def hex_u32_agrees(+s: String, valid: {H.is_valid_hex_u32(s) == True{} : Bool}) -> HexU32Spec(s, valid):
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

def HexLaws.example_zero():
  {==}

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
  valid: {B.is_valid_byte_mask(mask) == True{} : Bool}) -> Type:
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
  valid: {UTF8.can_encode_one(cp) == True{} : Bool}) -> Type:
  {Some{UTF8.encode_one(cp, valid)} == Laws.one_byte_shape(cp) : Maybe<&2, U32>}

def utf8_proof.encode_one_bits(+b31: Bool, +b30: Bool, +b29: Bool, +b28: Bool, +b27: Bool, +b26: Bool, +b25: Bool, +b24: Bool, +b23: Bool, +b22: Bool, +b21: Bool, +b20: Bool, +b19: Bool, +b18: Bool, +b17: Bool, +b16: Bool, +b15: Bool, +b14: Bool, +b13: Bool, +b12: Bool, +b11: Bool, +b10: Bool, +b9: Bool, +b8: Bool, +b7: Bool, +b6: Bool, +b5: Bool, +b4: Bool, +b3: Bool, +b2: Bool, +b1: Bool, +b0: Bool,
  valid: {UTF8.can_encode_one(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))) == True{} : Bool}
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

def Laws.utf8_encode_one(cp, valid):
  match cp:
    case U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      utf8_proof.encode_one_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0, valid)


# A one-byte encoding preserves the code point, so the byte itself is a witness.
def Utf8OneShapeRepresentation(+byte: U32) -> Type:
  Exists(U32, cp => {Laws.one_byte_shape(cp) == Some{byte} : Maybe<&2, U32>})

def utf8_proof.one_shape_witness(+byte: U32,
  accepted: {UTF8.has_one_byte_shape(byte) == True{} : Bool}) -> Utf8OneShapeRepresentation(byte):
  (byte, Equal.sym(Maybe<&2, U32>, Some{byte}, Laws.one_byte_shape(byte),
    Laws.utf8_encode_one(byte, accepted)))

# Reuse the capacity and encoding proofs to recover the produced byte's value.
def utf8_proof.one_model_byte_accepted(+cp: U32, +byte: U32,
  +produced: {Laws.one_byte_shape(cp) == Some{byte} : Maybe<&2, U32>}) ->
  {UTF8.has_one_byte_shape(byte) == True{} : Bool}:
  +accepted = Equal.trans(Bool, UTF8.can_encode_one(cp), Laws.can_encode_as_one_byte(cp), True{},
    Laws.utf8_can_encode_one(cp),
    Equal.cong(Maybe<&2, U32>, Bool, shape => Maybe.is_some(&2, U32, shape),
      Laws.one_byte_shape(cp), Some{byte}, produced))
  equal = Equal.cong(Maybe<&2, U32>, U32, shape => Maybe.default(&2, U32, shape, 0),
    Some{cp}, Some{byte},
    Equal.trans(Maybe<&2, U32>, Some{cp}, Laws.one_byte_shape(cp), Some{byte},
      Laws.utf8_encode_one(cp, accepted), produced))
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

def Laws.utf8_overlong_two(b1, b2):
  {==}

def Laws.utf8_valid_two(b1, b2):
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
  valid: {UTF8.can_encode_two(utf8_proof.codepoint(low, high)) == True{} : Bool}) ->
  {UTF8.first(UTF8.encode_two(utf8_proof.codepoint(low, high), valid)) == utf8_proof.first_byte(high) : U32}:
  match low high:
    case WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WNil{}}}}}}} WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WNil{}}}}}}:
      Equal.cong(Word(32n), U32, x => U32{x},
        Word.add(32n, word_join(5n, Word.zero(5n), 27n, WCon{False{}, WCon{True{}, WCon{True{}, Word.zero(24n)}}}), word_join(5n, high, 27n, Word.zero(27n))),
        word_join(5n, high, 27n, WCon{False{}, WCon{True{}, WCon{True{}, Word.zero(24n)}}}),
        word_add_fields(5n, high, 27n, WCon{False{}, WCon{True{}, WCon{True{}, Word.zero(24n)}}}))

def utf8_proof.encode_second(+low: Word(6n), +high: Word(5n),
  valid: {UTF8.can_encode_two(utf8_proof.codepoint(low, high)) == True{} : Bool}) ->
  {UTF8.second(UTF8.encode_two(utf8_proof.codepoint(low, high), valid)) == utf8_proof.second_byte(low) : U32}:
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

def utf8_proof.decode_fields(+low: Word(6n), +high: Word(5n)) ->
  {UTF8.decode_two(utf8_proof.first_byte(high), utf8_proof.second_byte(low)) == utf8_proof.codepoint(low, high) : U32}:
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

# Compare high bits first; inspect the low bits only at the 127/128 boundary.
def utf8_proof.threshold_bits(+b10: Bool, +b9: Bool, +b8: Bool, +b7: Bool, +b6: Bool, +b5: Bool, +b4: Bool, +b3: Bool, +b2: Bool, +b1: Bool, +b0: Bool) ->
  {UTF8.can_encode_one(utf8_proof.codepoint(WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WNil{}}}}}}}, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WNil{}}}}}})) == utf8_proof.fits_one_byte(WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WNil{}}}}}}) : Bool} &
  {Bool.not(UTF8.can_encode_one(utf8_proof.codepoint(WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WNil{}}}}}}}, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WNil{}}}}}}))) == U32.is_ge(utf8_proof.codepoint(WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WNil{}}}}}}}, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WNil{}}}}}}), 128) : Bool}:
  match b10 b9 b8 b7 b6 b5 b4 b3 b2 b1 b0:
    case True{} _ _ _ _ _ _ _ _ _ _: ({==}, {==})
    case False{} True{} _ _ _ _ _ _ _ _ _: ({==}, {==})
    case False{} False{} True{} _ _ _ _ _ _ _ _: ({==}, {==})
    case False{} False{} False{} True{} True{} _ _ _ _ _ _: ({==}, {==})
    case False{} False{} False{} True{} False{} True{} _ _ _ _ _: ({==}, {==})
    case False{} False{} False{} True{} False{} False{} True{} _ _ _ _: ({==}, {==})
    case False{} False{} False{} True{} False{} False{} False{} True{} _ _ _: ({==}, {==})
    case False{} False{} False{} True{} False{} False{} False{} False{} True{} _ _: ({==}, {==})
    case False{} False{} False{} True{} False{} False{} False{} False{} False{} True{} _: ({==}, {==})
    case False{} False{} False{} True{} False{} False{} False{} False{} False{} False{} True{}: ({==}, {==})
    case False{} False{} False{} True{} False{} False{} False{} False{} False{} False{} False{}: ({==}, {==})
    case False{} False{} False{} False{} False{} _ _ _ _ _ _: ({==}, {==})
    case False{} False{} False{} False{} True{} False{} _ _ _ _ _: ({==}, {==})
    case False{} False{} False{} False{} True{} True{} False{} _ _ _ _: ({==}, {==})
    case False{} False{} False{} False{} True{} True{} True{} False{} _ _ _: ({==}, {==})
    case False{} False{} False{} False{} True{} True{} True{} True{} False{} _ _: ({==}, {==})
    case False{} False{} False{} False{} True{} True{} True{} True{} True{} False{} _: ({==}, {==})
    case False{} False{} False{} False{} True{} True{} True{} True{} True{} True{} False{}: ({==}, {==})
    case False{} False{} False{} False{} True{} True{} True{} True{} True{} True{} True{}: ({==}, {==})

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

def utf8_proof.overlong_from_facts(+cp: U32, +b1: U32, +b2: U32,
  shape: {UTF8.has_two_byte_shape(b1, b2) == True{} : Bool},
  decoded: {UTF8.decode_two(b1, b2) == cp : U32}) ->
  {UTF8.overlong_two(b1, b2) == UTF8.can_encode_one(cp) : Bool}:
  %decoded : {UTF8.overlong_two(b1, b2) == UTF8.can_encode_one(_) : Bool}
  %shape : {UTF8.overlong_two(b1, b2) == (_ && UTF8.can_encode_one(UTF8.decode_two(b1, b2))) : Bool}
  {==}

def utf8_proof.valid_from_facts(+cp: U32, +b1: U32, +b2: U32,
  shape: {UTF8.has_two_byte_shape(b1, b2) == True{} : Bool},
  overlong: {UTF8.overlong_two(b1, b2) == UTF8.can_encode_one(cp) : Bool}) ->
  {UTF8.valid_two(b1, b2) == Bool.not(UTF8.can_encode_one(cp)) : Bool}:
  %overlong : {UTF8.valid_two(b1, b2) == Bool.not(_) : Bool}
  %shape : {UTF8.valid_two(b1, b2) == (_ && Bool.not(UTF8.overlong_two(b1, b2))) : Bool}
  {==}

def utf8_proof.range_from_facts(+low: Word(6n), +high: Word(5n),
  first: {(U32.is_ge(utf8_proof.first_byte(high), 194) && U32.is_le(utf8_proof.first_byte(high), 223)) == Bool.not(utf8_proof.fits_one_byte(high)) : Bool},
  second: {(U32.is_ge(utf8_proof.second_byte(low), 128) && U32.is_le(utf8_proof.second_byte(low), 191)) == True{} : Bool},
  small: {UTF8.can_encode_one(utf8_proof.codepoint(low, high)) == utf8_proof.fits_one_byte(high) : Bool}) ->
  {Bool.not(UTF8.can_encode_one(utf8_proof.codepoint(low, high))) ==
    ((U32.is_ge(utf8_proof.first_byte(high), 194) && U32.is_le(utf8_proof.first_byte(high), 223)) &&
     (U32.is_ge(utf8_proof.second_byte(low), 128) && U32.is_le(utf8_proof.second_byte(low), 191))) : Bool}:
  Equal.trans(Bool,
    Bool.not(UTF8.can_encode_one(utf8_proof.codepoint(low, high))), Bool.not(utf8_proof.fits_one_byte(high)),
    ((U32.is_ge(utf8_proof.first_byte(high), 194) && U32.is_le(utf8_proof.first_byte(high), 223)) &&
     (U32.is_ge(utf8_proof.second_byte(low), 128) && U32.is_le(utf8_proof.second_byte(low), 191))),
    Equal.cong(Bool, Bool, Bool.not, UTF8.can_encode_one(utf8_proof.codepoint(low, high)), utf8_proof.fits_one_byte(high), small),
    Equal.sym(Bool,
      ((U32.is_ge(utf8_proof.first_byte(high), 194) && U32.is_le(utf8_proof.first_byte(high), 223)) &&
       (U32.is_ge(utf8_proof.second_byte(low), 128) && U32.is_le(utf8_proof.second_byte(low), 191))), Bool.not(utf8_proof.fits_one_byte(high)),
      Equal.trans(Bool,
        ((U32.is_ge(utf8_proof.first_byte(high), 194) && U32.is_le(utf8_proof.first_byte(high), 223)) &&
         (U32.is_ge(utf8_proof.second_byte(low), 128) && U32.is_le(utf8_proof.second_byte(low), 191))),
        (Bool.not(utf8_proof.fits_one_byte(high)) && True{}), Bool.not(utf8_proof.fits_one_byte(high)),
        bool_and_equal(
          (U32.is_ge(utf8_proof.first_byte(high), 194) && U32.is_le(utf8_proof.first_byte(high), 223)),
          (U32.is_ge(utf8_proof.second_byte(low), 128) && U32.is_le(utf8_proof.second_byte(low), 191)),
          Bool.not(utf8_proof.fits_one_byte(high)), True{}, first, second), bool_and_true(Bool.not(utf8_proof.fits_one_byte(high))))))

def Utf8RoundtripSpec(+cp: U32, +b1: U32, +b2: U32) -> Type:
  {UTF8.decode_two(b1, b2) == cp : U32} &
  {UTF8.has_two_byte_shape(b1, b2) == True{} : Bool} &
  {UTF8.overlong_two(b1, b2) == UTF8.can_encode_one(cp) : Bool} &
  {UTF8.valid_two(b1, b2) == U32.is_ge(cp, 128) : Bool} &
  {UTF8.valid_two(b1, b2) ==
    ((U32.is_ge(b1, 194) && U32.is_le(b1, 223)) &&
     (U32.is_ge(b2, 128) && U32.is_le(b2, 191))) : Bool}

def utf8_proof.fields_from_facts(+low: Word(6n), +high: Word(5n),
  first: {B.byte_mask("110xxxxx", utf8_proof.first_byte(high), {==}) == True{} : Bool} &
    {(U32.is_ge(utf8_proof.first_byte(high), 194) && U32.is_le(utf8_proof.first_byte(high), 223)) == Bool.not(utf8_proof.fits_one_byte(high)) : Bool},
  second: {B.byte_mask("10xxxxxx", utf8_proof.second_byte(low), {==}) == True{} : Bool} &
    {(U32.is_ge(utf8_proof.second_byte(low), 128) && U32.is_le(utf8_proof.second_byte(low), 191)) == True{} : Bool},
  threshold: {UTF8.can_encode_one(utf8_proof.codepoint(low, high)) == utf8_proof.fits_one_byte(high) : Bool} &
    {Bool.not(UTF8.can_encode_one(utf8_proof.codepoint(low, high))) == U32.is_ge(utf8_proof.codepoint(low, high), 128) : Bool}) ->
  Utf8RoundtripSpec(utf8_proof.codepoint(low, high), utf8_proof.first_byte(high), utf8_proof.second_byte(low)):
  (shape1, range1) = first
  (shape2, range2) = second
  (small, large) = threshold
  +decoded = utf8_proof.decode_fields(low, high)
  +shape = utf8_proof.shape_from_masks(utf8_proof.first_byte(high), utf8_proof.second_byte(low), shape1, shape2)
  +overlong = utf8_proof.overlong_from_facts(utf8_proof.codepoint(low, high), utf8_proof.first_byte(high), utf8_proof.second_byte(low), shape, decoded)
  +valid = utf8_proof.valid_from_facts(utf8_proof.codepoint(low, high), utf8_proof.first_byte(high), utf8_proof.second_byte(low), shape, overlong)
  range = utf8_proof.range_from_facts(low, high, range1, range2, small)
  (decoded, shape, overlong,
   Equal.trans(Bool, UTF8.valid_two(utf8_proof.first_byte(high), utf8_proof.second_byte(low)), Bool.not(UTF8.can_encode_one(utf8_proof.codepoint(low, high))), U32.is_ge(utf8_proof.codepoint(low, high), 128), valid, large),
   Equal.trans(Bool, UTF8.valid_two(utf8_proof.first_byte(high), utf8_proof.second_byte(low)), Bool.not(UTF8.can_encode_one(utf8_proof.codepoint(low, high))),
     ((U32.is_ge(utf8_proof.first_byte(high), 194) && U32.is_le(utf8_proof.first_byte(high), 223)) &&
      (U32.is_ge(utf8_proof.second_byte(low), 128) && U32.is_le(utf8_proof.second_byte(low), 191))), valid, range))

def utf8_proof.fields_roundtrip(+low: Word(6n), +high: Word(5n)) ->
  Utf8RoundtripSpec(utf8_proof.codepoint(low, high), utf8_proof.first_byte(high), utf8_proof.second_byte(low)):
  match low high:
    case WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WNil{}}}}}}} WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WNil{}}}}}}:
      utf8_proof.fields_from_facts(low, high, utf8_proof.first_byte_facts(high), utf8_proof.second_byte_facts(low), utf8_proof.threshold_bits(b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))

# The first zero below the all-ones maximum determines the comparison.
# This needs twelve cases, regardless of the remaining lower bits.
def Laws.utf8_two_capacity(bits):
  match bits:
    case WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WNil{}}}}}}}}}}}}:
      {==}

def Laws.utf8_two_roundtrip(bits):
  match bits:
    case WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WNil{}}}}}}}}}}}}:
      +low = {WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WNil{}}}}}}} : Word(6n)}
      +high = {WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WNil{}}}}}} : Word(5n)}
      %Equal.sym(U32,
        UTF8.first(UTF8.encode_two(utf8_proof.codepoint(low, high), utf8_proof.capacity_bits(b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))), utf8_proof.first_byte(high),
        utf8_proof.encode_first(low, high, utf8_proof.capacity_bits(b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))) :
        Utf8RoundtripSpec(utf8_proof.codepoint(low, high), _, UTF8.second(UTF8.encode_two(utf8_proof.codepoint(low, high), utf8_proof.capacity_bits(b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))))
      %Equal.sym(U32,
        UTF8.second(UTF8.encode_two(utf8_proof.codepoint(low, high), utf8_proof.capacity_bits(b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))), utf8_proof.second_byte(low),
        utf8_proof.encode_second(low, high, utf8_proof.capacity_bits(b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))) :
        Utf8RoundtripSpec(utf8_proof.codepoint(low, high), utf8_proof.first_byte(high), _)
      utf8_proof.fields_roundtrip(low, high)

def Laws.utf8_encoding_examples():
  ({==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==})

def BinaryLaws.bit8(byte, valid):
  {==}

def BinaryLaws.bit8_examples():
  ({==}, {==}, {==})

def Bit8ValueRoundtripSpec(+byte: U32,
  valid: {U32.is_le(byte, 255) == True{} : Bool}) -> Type:
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
  +valid: {U32.is_le(value, 65535) == True{} : Bool}) -> Type:
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
  valid: {UTF8.can_encode_two(cp) == True{} : Bool}) -> Type:
  {Some{UTF8.encode_two(cp, valid)} == Laws.two_byte_shape(cp) : Maybe<&1, U32 & U32>}

def utf8_proof.table_pair(+low: Word(6n), +high: Word(5n),
  +valid: {UTF8.can_encode_two(utf8_proof.codepoint(low, high)) == True{} : Bool}) ->
  {UTF8.encode_two(utf8_proof.codepoint(low, high), valid) ==
    (utf8_proof.first_byte(high), utf8_proof.second_byte(low)) : U32 & U32}:
  match low high:
    case WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WNil{}}}}}}} WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WNil{}}}}}}:
      %utf8_proof.encode_first(low, high, valid) :
        {UTF8.encode_two(utf8_proof.codepoint(low, high), valid) == (_, utf8_proof.second_byte(low)) : U32 & U32}
      %utf8_proof.encode_second(low, high, valid) :
        {UTF8.encode_two(utf8_proof.codepoint(low, high), valid) == (UTF8.first(UTF8.encode_two(utf8_proof.codepoint(low, high), valid)), _) : U32 & U32}
      {==}

def utf8_proof.encode_two_bits(+b31: Bool, +b30: Bool, +b29: Bool, +b28: Bool, +b27: Bool, +b26: Bool, +b25: Bool, +b24: Bool, +b23: Bool, +b22: Bool, +b21: Bool, +b20: Bool, +b19: Bool, +b18: Bool, +b17: Bool, +b16: Bool, +b15: Bool, +b14: Bool, +b13: Bool, +b12: Bool, +b11: Bool, +b10: Bool, +b9: Bool, +b8: Bool, +b7: Bool, +b6: Bool, +b5: Bool, +b4: Bool, +b3: Bool, +b2: Bool, +b1: Bool, +b0: Bool,
  valid: {UTF8.can_encode_two(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))) == True{} : Bool}) -> Utf8EncodeTwoSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0)), valid):
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
        UTF8.encode_two(utf8_proof.codepoint(WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WNil{}}}}}}}, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WNil{}}}}}}), utf8_proof.capacity_bits(b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0)),
        (utf8_proof.first_byte(WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WNil{}}}}}}), utf8_proof.second_byte(WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WNil{}}}}}}})),
        utf8_proof.table_pair(WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WNil{}}}}}}}, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WNil{}}}}}}, utf8_proof.capacity_bits(b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0)))

def Laws.utf8_encode_two(cp, valid):
  match cp:
    case U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      utf8_proof.encode_two_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0, valid)

def Laws.two_byte_shape_examples():
  ({==}, {==}, {==}, {==}, {==}, {==}, {==})

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

def Laws.utf8_decode_two(b1, b2):
  {==}

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
  valid: {B.valid_byte_string(s) == True{} : Bool}) -> Type:
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
