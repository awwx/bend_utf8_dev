import Base
import ./LAWS.bend as Laws
import ./utf8.bend as UTF8

# Bool forms of validity and of the maximal subpart, built from the
# `utf8.bend` helpers.  `LAWS.bend` states these as types and refers
# only to the decoder's public functions; most proofs below work with
# these Bool forms and the `utf8_proof.impl.*` lemmas about the
# helpers, and the section "From the `utf8.bend` tests to the
# `LAWS.bend` definitions" converts between the two.

def utf8_proof.bool.overlong_one_byte(b1: U32) -> Bool:
  False{}

def utf8_proof.bool.valid_one_byte.if(+byte: U32, shape: Bool,
  -checked: {UTF8.has_one_byte_shape(byte) == shape : Bool}) -> Bool:
  match shape:
    case False{}:
      False{}
    case True{}:
      Bool.not(utf8_proof.bool.overlong_one_byte(byte)) &&
      Laws.is_unicode_scalar(UTF8.decode_one_byte(byte, checked))

def utf8_proof.bool.valid_two_bytes.if(+b1: U32, +b2: U32, shape: Bool,
  -checked: {UTF8.has_two_byte_shape(b1, b2) == shape : Bool}) -> Bool:
  match shape:
    case False{}:
      False{}
    case True{}:
      Bool.not(UTF8.overlong_two_bytes(b1, b2, checked)) &&
      Laws.is_unicode_scalar(UTF8.decode_two_bytes(b1, b2, checked))

def utf8_proof.bool.is_valid_sequence(seq: List<&2, U32>) -> Bool:
  match seq:
    case +b1 <> Nil{}:
      UTF8.valid_one_byte(b1)
    case +b1 <> +b2 <> Nil{}:
      UTF8.valid_two_bytes(b1, b2)
    case +b1 <> +b2 <> +b3 <> Nil{}:
      UTF8.valid_three_bytes(b1, b2, b3)
    case +b1 <> +b2 <> +b3 <> +b4 <> Nil{}:
      UTF8.valid_four_bytes(b1, b2, b3, b4)
    case _:
      False{}

def utf8_proof.bool.maximal_subpart.longer_not_valid_prefix(subpart: List<&2, U32>, bytes: List<&2, U32>) -> Type:
  @c: U32 -> @extra: List<&2, U32> ->
    Laws.is_prefix(List.append(&2, U32, subpart, c <> extra), bytes) ->
    {UTF8.is_valid_sequence_prefix(List.append(&2, U32, subpart, c <> extra)) == False{} : Bool}

def utf8_proof.bool.maximal_subpart.sequence_prefix(+b1: U32, +more: List<&2, U32>,
  +subpart: List<&2, U32>) -> Type:
  Laws.is_prefix(subpart, b1 <> more) &
  {UTF8.is_valid_sequence_prefix(subpart) == True{} : Bool} &
  utf8_proof.bool.maximal_subpart.longer_not_valid_prefix(subpart, b1 <> more)

def utf8_proof.bool.maximal_subpart.single_byte(+b1: U32, +subpart: List<&2, U32>) -> Type:
  {subpart == [b1] : List<&2, U32>}

def utf8_proof.bool.maximal_subpart.if(+b1: U32, +more: List<&2, U32>, begins: Bool,
  +subpart: List<&2, U32>) -> Type:
  match begins:
    case True{}:
      utf8_proof.bool.maximal_subpart.sequence_prefix(b1, more, subpart)
    case False{}:
      utf8_proof.bool.maximal_subpart.single_byte(b1, subpart)

def utf8_proof.bool.maximal_subpart(+b1: U32, +more: List<&2, U32>,
  +subpart: List<&2, U32>) -> Type:
  utf8_proof.bool.maximal_subpart.if(b1, more, UTF8.is_valid_sequence_prefix([b1]), subpart)


# The bytes of a two-byte encoding.
def utf8_proof.two_bytes.first(p: U32 & U32) -> U32:
  (a, b) = p
  a

def utf8_proof.two_bytes.second(p: U32 & U32) -> U32:
  (a, b) = p
  b

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

def utf8_proof.impl.can_encode_as_two_bytes(+cp: U32) ->
  {UTF8.can_encode_as_two_bytes(cp) == Maybe.is_some(&1, U32 & U32, Laws.two_byte_shape(cp)) : Bool}:
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

def utf8_proof.impl.can_encode_as_one_byte(+cp: U32) ->
  {UTF8.can_encode_as_one_byte(cp) == Maybe.is_some(&2, U32, Laws.one_byte_shape(cp)) : Bool}:
  match cp:
    case U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      utf8_proof.one_capacity_model_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0)


def Utf8EncodeOneSpec(+cp: U32,
  -valid: {UTF8.can_encode_as_one_byte(cp) == True{} : Bool}) -> Type:
  {Some{UTF8.encode_as_one_byte(cp, valid)} == Laws.one_byte_shape(cp) : Maybe<&2, U32>}

def utf8_proof.encode_as_one_byte_bits(+b31: Bool, +b30: Bool, +b29: Bool, +b28: Bool, +b27: Bool, +b26: Bool, +b25: Bool, +b24: Bool, +b23: Bool, +b22: Bool, +b21: Bool, +b20: Bool, +b19: Bool, +b18: Bool, +b17: Bool, +b16: Bool, +b15: Bool, +b14: Bool, +b13: Bool, +b12: Bool, +b11: Bool, +b10: Bool, +b9: Bool, +b8: Bool, +b7: Bool, +b6: Bool, +b5: Bool, +b4: Bool, +b3: Bool, +b2: Bool, +b1: Bool, +b0: Bool,
  valid: {UTF8.can_encode_as_one_byte(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))) == True{} : Bool}
) -> Utf8EncodeOneSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0)), valid):
  match b31 b30 b29 b28 b27 b26 b25 b24 b23 b22 b21 b20 b19 b18 b17 b16 b15 b14 b13 b12 b11 b10 b9 b8 b7:
    case True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(Utf8EncodeOneSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0)), valid), UTF8.false_true(valid))
    case False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(Utf8EncodeOneSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0)), valid), UTF8.false_true(valid))
    case False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(Utf8EncodeOneSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0)), valid), UTF8.false_true(valid))
    case False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(Utf8EncodeOneSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0)), valid), UTF8.false_true(valid))
    case False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(Utf8EncodeOneSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0)), valid), UTF8.false_true(valid))
    case False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(Utf8EncodeOneSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0)), valid), UTF8.false_true(valid))
    case False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(Utf8EncodeOneSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0)), valid), UTF8.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(Utf8EncodeOneSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0)), valid), UTF8.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(Utf8EncodeOneSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0)), valid), UTF8.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(Utf8EncodeOneSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0)), valid), UTF8.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(Utf8EncodeOneSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0)), valid), UTF8.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(Utf8EncodeOneSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0)), valid), UTF8.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(Utf8EncodeOneSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0)), valid), UTF8.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(Utf8EncodeOneSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0)), valid), UTF8.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(Utf8EncodeOneSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0)), valid), UTF8.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _:
      Empty.absurd(Utf8EncodeOneSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0)), valid), UTF8.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _:
      Empty.absurd(Utf8EncodeOneSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0)), valid), UTF8.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _:
      Empty.absurd(Utf8EncodeOneSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0)), valid), UTF8.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _:
      Empty.absurd(Utf8EncodeOneSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0)), valid), UTF8.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _:
      Empty.absurd(Utf8EncodeOneSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0)), valid), UTF8.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _:
      Empty.absurd(Utf8EncodeOneSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0)), valid), UTF8.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _:
      Empty.absurd(Utf8EncodeOneSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0)), valid), UTF8.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _:
      Empty.absurd(Utf8EncodeOneSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0)), valid), UTF8.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _:
      Empty.absurd(Utf8EncodeOneSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0)), valid), UTF8.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{}:
      Empty.absurd(Utf8EncodeOneSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0)), valid), UTF8.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{}: {==}

def utf8_proof.impl.encode_as_one_byte(+cp: U32, valid: {UTF8.can_encode_as_one_byte(cp) == True{} : Bool}) ->
  {Some{UTF8.encode_as_one_byte(cp, valid)} == Laws.one_byte_shape(cp) : Maybe<&2, U32>}:
  match cp:
    case U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      utf8_proof.encode_as_one_byte_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0, valid)


# Validity reduces to shape once the shape fixes the high 25 bits to zero.
def Utf8ValidOneSpec(+cp: U32) -> Type:
  {UTF8.valid_one_byte(cp) ==
    (Bool.not(utf8_proof.bool.overlong_one_byte(cp)) && Laws.is_unicode_scalar(cp)) : Bool}

# A set high bit contradicts the shape.  Otherwise the low seven bits are
# split until the scalar range check computes, leaving the shape proof.
def utf8_proof.valid_one_byte_bits(+b31: Bool, +b30: Bool, +b29: Bool, +b28: Bool, +b27: Bool, +b26: Bool, +b25: Bool, +b24: Bool, +b23: Bool, +b22: Bool, +b21: Bool, +b20: Bool, +b19: Bool, +b18: Bool, +b17: Bool, +b16: Bool, +b15: Bool, +b14: Bool, +b13: Bool, +b12: Bool, +b11: Bool, +b10: Bool, +b9: Bool, +b8: Bool, +b7: Bool, +b6: Bool, +b5: Bool, +b4: Bool, +b3: Bool, +b2: Bool, +b1: Bool, +b0: Bool,
  valid: {UTF8.has_one_byte_shape(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))) == True{} : Bool}) -> Utf8ValidOneSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))):
  match b31 b30 b29 b28 b27 b26 b25 b24 b23 b22 b21 b20 b19 b18 b17 b16 b15 b14 b13 b12 b11 b10 b9 b8 b7:
    case True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(Utf8ValidOneSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))), UTF8.false_true(valid))
    case False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(Utf8ValidOneSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))), UTF8.false_true(valid))
    case False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(Utf8ValidOneSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))), UTF8.false_true(valid))
    case False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(Utf8ValidOneSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))), UTF8.false_true(valid))
    case False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(Utf8ValidOneSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))), UTF8.false_true(valid))
    case False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(Utf8ValidOneSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))), UTF8.false_true(valid))
    case False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(Utf8ValidOneSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))), UTF8.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(Utf8ValidOneSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))), UTF8.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(Utf8ValidOneSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))), UTF8.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(Utf8ValidOneSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))), UTF8.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(Utf8ValidOneSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))), UTF8.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(Utf8ValidOneSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))), UTF8.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(Utf8ValidOneSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))), UTF8.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(Utf8ValidOneSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))), UTF8.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(Utf8ValidOneSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))), UTF8.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _:
      Empty.absurd(Utf8ValidOneSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))), UTF8.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _:
      Empty.absurd(Utf8ValidOneSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))), UTF8.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _:
      Empty.absurd(Utf8ValidOneSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))), UTF8.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _:
      Empty.absurd(Utf8ValidOneSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))), UTF8.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _:
      Empty.absurd(Utf8ValidOneSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))), UTF8.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _:
      Empty.absurd(Utf8ValidOneSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))), UTF8.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _:
      Empty.absurd(Utf8ValidOneSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))), UTF8.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _:
      Empty.absurd(Utf8ValidOneSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))), UTF8.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _:
      Empty.absurd(Utf8ValidOneSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))), UTF8.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{}:
      Empty.absurd(Utf8ValidOneSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))), UTF8.false_true(valid))
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
  {UTF8.valid_one_byte(byte) == utf8_proof.bool.valid_one_byte.if(byte, shape, checked) : Bool}:
  match shape:
    case False{}:
      checked
    case True{}:
      utf8_proof.valid_one_byte(byte, checked)

def utf8_proof.impl.valid_one_byte(+byte: U32) ->
  {UTF8.valid_one_byte(byte) == utf8_proof.bool.valid_one_byte.if(byte, UTF8.has_one_byte_shape(byte), {==}) : Bool}:
  utf8_proof.valid_one_byte_if(byte, UTF8.has_one_byte_shape(byte), {==})

def utf8_proof.impl.overlong_two_bytes(+b1: U32, +b2: U32, -valid: {UTF8.has_two_byte_shape(b1, b2) == True{} : Bool}) ->
  {UTF8.overlong_two_bytes(b1, b2, valid) ==
    UTF8.can_encode_as_one_byte(UTF8.decode_two_bytes(b1, b2, valid)) : Bool}:
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
  {utf8_proof.two_bytes.first(UTF8.encode_as_two_bytes(utf8_proof.codepoint(low, high), valid)) == utf8_proof.first_byte(high) : U32}:
  match low high:
    case WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WNil{}}}}}}} WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WNil{}}}}}}:
      Equal.cong(Word(32n), U32, x => U32{x},
        Word.add(32n, word_join(5n, Word.zero(5n), 27n, WCon{False{}, WCon{True{}, WCon{True{}, Word.zero(24n)}}}), word_join(5n, high, 27n, Word.zero(27n))),
        word_join(5n, high, 27n, WCon{False{}, WCon{True{}, WCon{True{}, Word.zero(24n)}}}),
        word_add_fields(5n, high, 27n, WCon{False{}, WCon{True{}, WCon{True{}, Word.zero(24n)}}}))

def utf8_proof.encode_second(+low: Word(6n), +high: Word(5n),
  -valid: {UTF8.can_encode_as_two_bytes(utf8_proof.codepoint(low, high)) == True{} : Bool}) ->
  {utf8_proof.two_bytes.second(UTF8.encode_as_two_bytes(utf8_proof.codepoint(low, high), valid)) == utf8_proof.second_byte(low) : U32}:
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
  {UTF8.is_two_byte_lead(utf8_proof.first_byte(high)) == True{} : Bool} &
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
  {UTF8.is_continuation_byte(utf8_proof.second_byte(low)) == True{} : Bool} &
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
  first: {UTF8.is_two_byte_lead(b1) == True{} : Bool},
  second: {UTF8.is_continuation_byte(b2) == True{} : Bool}) ->
  {UTF8.has_two_byte_shape(b1, b2) == True{} : Bool}:
  bool_and_equal(UTF8.is_two_byte_lead(b1), UTF8.is_continuation_byte(b2), True{}, True{}, first, second)

def Laws.is_surrogate_code_point_examples():
  ({==}, {==}, {==}, {==}, {==}, {==})

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
        {UTF8.encode_as_two_bytes(utf8_proof.codepoint(low, high), valid) == (utf8_proof.two_bytes.first(UTF8.encode_as_two_bytes(utf8_proof.codepoint(low, high), valid)), _) : U32 & U32}
      {==}

def utf8_proof.encode_as_two_bytes_bits(+b31: Bool, +b30: Bool, +b29: Bool, +b28: Bool, +b27: Bool, +b26: Bool, +b25: Bool, +b24: Bool, +b23: Bool, +b22: Bool, +b21: Bool, +b20: Bool, +b19: Bool, +b18: Bool, +b17: Bool, +b16: Bool, +b15: Bool, +b14: Bool, +b13: Bool, +b12: Bool, +b11: Bool, +b10: Bool, +b9: Bool, +b8: Bool, +b7: Bool, +b6: Bool, +b5: Bool, +b4: Bool, +b3: Bool, +b2: Bool, +b1: Bool, +b0: Bool,
  valid: {UTF8.can_encode_as_two_bytes(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))) == True{} : Bool}) -> Utf8EncodeTwoSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0)), valid):
  match b31 b30 b29 b28 b27 b26 b25 b24 b23 b22 b21 b20 b19 b18 b17 b16 b15 b14 b13 b12 b11:
    case True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(Utf8EncodeTwoSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0)), valid), UTF8.false_true(valid))
    case False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(Utf8EncodeTwoSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0)), valid), UTF8.false_true(valid))
    case False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(Utf8EncodeTwoSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0)), valid), UTF8.false_true(valid))
    case False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(Utf8EncodeTwoSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0)), valid), UTF8.false_true(valid))
    case False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(Utf8EncodeTwoSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0)), valid), UTF8.false_true(valid))
    case False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(Utf8EncodeTwoSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0)), valid), UTF8.false_true(valid))
    case False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(Utf8EncodeTwoSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0)), valid), UTF8.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(Utf8EncodeTwoSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0)), valid), UTF8.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(Utf8EncodeTwoSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0)), valid), UTF8.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(Utf8EncodeTwoSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0)), valid), UTF8.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(Utf8EncodeTwoSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0)), valid), UTF8.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _:
      Empty.absurd(Utf8EncodeTwoSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0)), valid), UTF8.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _:
      Empty.absurd(Utf8EncodeTwoSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0)), valid), UTF8.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _:
      Empty.absurd(Utf8EncodeTwoSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0)), valid), UTF8.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _:
      Empty.absurd(Utf8EncodeTwoSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0)), valid), UTF8.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _:
      Empty.absurd(Utf8EncodeTwoSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0)), valid), UTF8.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _:
      Empty.absurd(Utf8EncodeTwoSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0)), valid), UTF8.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _:
      Empty.absurd(Utf8EncodeTwoSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0)), valid), UTF8.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _:
      Empty.absurd(Utf8EncodeTwoSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0)), valid), UTF8.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _:
      Empty.absurd(Utf8EncodeTwoSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0)), valid), UTF8.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{}:
      Empty.absurd(Utf8EncodeTwoSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0)), valid), UTF8.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{}:
      Equal.cong(U32 & U32, Maybe<&1, U32 & U32>, bytes => Some{bytes},
        UTF8.encode_as_two_bytes(utf8_proof.codepoint(WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WNil{}}}}}}}, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WNil{}}}}}}), utf8_proof.capacity_bits(b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0)),
        (utf8_proof.first_byte(WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WNil{}}}}}}), utf8_proof.second_byte(WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WNil{}}}}}}})),
        utf8_proof.table_pair(WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WNil{}}}}}}}, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WNil{}}}}}}, utf8_proof.capacity_bits(b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0)))

def utf8_proof.impl.encode_as_two_bytes(+cp: U32, valid: {UTF8.can_encode_as_two_bytes(cp) == True{} : Bool}) ->
  {Some{UTF8.encode_as_two_bytes(cp, valid)} == Laws.two_byte_shape(cp) : Maybe<&1, U32 & U32>}:
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
    case False{}: Empty.absurd({right == True{} : Bool}, UTF8.false_true(valid))
    case True{}: valid

# A byte that passes `UTF8.is_two_byte_lead` is
# `utf8_proof.first_byte` of its low 5 bits.
def utf8_proof.first_payload.Payload(+byte: U32) -> Type:
  Exists(Word(5n), payload => {byte == utf8_proof.first_byte(payload) : U32})

# Split on the bits from the top: the first bit that differs from the
# pattern makes the test False, contradicting `valid`.
def utf8_proof.first_payload.bits(+b31: Bool, +b30: Bool, +b29: Bool, +b28: Bool, +b27: Bool, +b26: Bool, +b25: Bool, +b24: Bool, +b23: Bool, +b22: Bool, +b21: Bool, +b20: Bool, +b19: Bool, +b18: Bool, +b17: Bool, +b16: Bool, +b15: Bool, +b14: Bool, +b13: Bool, +b12: Bool, +b11: Bool, +b10: Bool, +b9: Bool, +b8: Bool, +b7: Bool, +b6: Bool, +b5: Bool, +b4: Bool, +b3: Bool, +b2: Bool, +b1: Bool, +b0: Bool,
  valid: {UTF8.is_two_byte_lead(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))) == True{} : Bool}) ->
  utf8_proof.first_payload.Payload(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))):
  match b31 b30 b29 b28 b27 b26 b25 b24 b23 b22 b21 b20 b19 b18 b17 b16 b15 b14 b13 b12 b11 b10 b9 b8 b7 b6 b5:
    case True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(utf8_proof.first_payload.Payload(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))), UTF8.false_true(valid))
    case False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(utf8_proof.first_payload.Payload(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))), UTF8.false_true(valid))
    case False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(utf8_proof.first_payload.Payload(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))), UTF8.false_true(valid))
    case False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(utf8_proof.first_payload.Payload(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))), UTF8.false_true(valid))
    case False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(utf8_proof.first_payload.Payload(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))), UTF8.false_true(valid))
    case False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(utf8_proof.first_payload.Payload(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))), UTF8.false_true(valid))
    case False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(utf8_proof.first_payload.Payload(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))), UTF8.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(utf8_proof.first_payload.Payload(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))), UTF8.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(utf8_proof.first_payload.Payload(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))), UTF8.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(utf8_proof.first_payload.Payload(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))), UTF8.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(utf8_proof.first_payload.Payload(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))), UTF8.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(utf8_proof.first_payload.Payload(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))), UTF8.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(utf8_proof.first_payload.Payload(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))), UTF8.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(utf8_proof.first_payload.Payload(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))), UTF8.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(utf8_proof.first_payload.Payload(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))), UTF8.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(utf8_proof.first_payload.Payload(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))), UTF8.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(utf8_proof.first_payload.Payload(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))), UTF8.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _:
      Empty.absurd(utf8_proof.first_payload.Payload(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))), UTF8.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _:
      Empty.absurd(utf8_proof.first_payload.Payload(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))), UTF8.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _:
      Empty.absurd(utf8_proof.first_payload.Payload(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))), UTF8.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _:
      Empty.absurd(utf8_proof.first_payload.Payload(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))), UTF8.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _:
      Empty.absurd(utf8_proof.first_payload.Payload(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))), UTF8.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _:
      Empty.absurd(utf8_proof.first_payload.Payload(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))), UTF8.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _:
      Empty.absurd(utf8_proof.first_payload.Payload(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))), UTF8.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} _ _:
      Empty.absurd(utf8_proof.first_payload.Payload(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))), UTF8.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} False{} _:
      Empty.absurd(utf8_proof.first_payload.Payload(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))), UTF8.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} True{} True{}:
      Empty.absurd(utf8_proof.first_payload.Payload(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))), UTF8.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} True{} False{}:
      (WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WNil{}}}}}}, {==})

def utf8_proof.first_payload(+byte: U32,
  +valid: {UTF8.is_two_byte_lead(byte) == True{} : Bool}) ->
  Exists(Word(5n), payload => {byte == utf8_proof.first_byte(payload) : U32}):
  match byte:
    case U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      utf8_proof.first_payload.bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0, valid)

# A byte that passes `UTF8.is_continuation_byte` is
# `utf8_proof.second_byte` of its low 6 bits.
def utf8_proof.second_payload.Payload(+byte: U32) -> Type:
  Exists(Word(6n), payload => {byte == utf8_proof.second_byte(payload) : U32})

# Split on the bits from the top: the first bit that differs from the
# pattern makes the test False, contradicting `valid`.
def utf8_proof.second_payload.bits(+b31: Bool, +b30: Bool, +b29: Bool, +b28: Bool, +b27: Bool, +b26: Bool, +b25: Bool, +b24: Bool, +b23: Bool, +b22: Bool, +b21: Bool, +b20: Bool, +b19: Bool, +b18: Bool, +b17: Bool, +b16: Bool, +b15: Bool, +b14: Bool, +b13: Bool, +b12: Bool, +b11: Bool, +b10: Bool, +b9: Bool, +b8: Bool, +b7: Bool, +b6: Bool, +b5: Bool, +b4: Bool, +b3: Bool, +b2: Bool, +b1: Bool, +b0: Bool,
  valid: {UTF8.is_continuation_byte(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))) == True{} : Bool}) ->
  utf8_proof.second_payload.Payload(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))):
  match b31 b30 b29 b28 b27 b26 b25 b24 b23 b22 b21 b20 b19 b18 b17 b16 b15 b14 b13 b12 b11 b10 b9 b8 b7 b6:
    case True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(utf8_proof.second_payload.Payload(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))), UTF8.false_true(valid))
    case False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(utf8_proof.second_payload.Payload(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))), UTF8.false_true(valid))
    case False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(utf8_proof.second_payload.Payload(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))), UTF8.false_true(valid))
    case False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(utf8_proof.second_payload.Payload(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))), UTF8.false_true(valid))
    case False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(utf8_proof.second_payload.Payload(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))), UTF8.false_true(valid))
    case False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(utf8_proof.second_payload.Payload(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))), UTF8.false_true(valid))
    case False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(utf8_proof.second_payload.Payload(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))), UTF8.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(utf8_proof.second_payload.Payload(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))), UTF8.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(utf8_proof.second_payload.Payload(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))), UTF8.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(utf8_proof.second_payload.Payload(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))), UTF8.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(utf8_proof.second_payload.Payload(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))), UTF8.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(utf8_proof.second_payload.Payload(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))), UTF8.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(utf8_proof.second_payload.Payload(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))), UTF8.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(utf8_proof.second_payload.Payload(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))), UTF8.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(utf8_proof.second_payload.Payload(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))), UTF8.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(utf8_proof.second_payload.Payload(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))), UTF8.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _:
      Empty.absurd(utf8_proof.second_payload.Payload(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))), UTF8.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _:
      Empty.absurd(utf8_proof.second_payload.Payload(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))), UTF8.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _:
      Empty.absurd(utf8_proof.second_payload.Payload(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))), UTF8.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _:
      Empty.absurd(utf8_proof.second_payload.Payload(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))), UTF8.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _:
      Empty.absurd(utf8_proof.second_payload.Payload(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))), UTF8.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _:
      Empty.absurd(utf8_proof.second_payload.Payload(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))), UTF8.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _:
      Empty.absurd(utf8_proof.second_payload.Payload(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))), UTF8.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _:
      Empty.absurd(utf8_proof.second_payload.Payload(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))), UTF8.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} _:
      Empty.absurd(utf8_proof.second_payload.Payload(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))), UTF8.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} True{}:
      Empty.absurd(utf8_proof.second_payload.Payload(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))), UTF8.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} False{}:
      (WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WNil{}}}}}}}, {==})

def utf8_proof.second_payload(+byte: U32,
  +valid: {UTF8.is_continuation_byte(byte) == True{} : Bool}) ->
  Exists(Word(6n), payload => {byte == utf8_proof.second_byte(payload) : U32}):
  match byte:
    case U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      utf8_proof.second_payload.bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0, valid)

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
    utf8_proof.first_payload(b1, bool_and_left_true(UTF8.is_two_byte_lead(b1), UTF8.is_continuation_byte(b2), accepted)),
    utf8_proof.second_payload(b2, bool_and_right_true(UTF8.is_two_byte_lead(b1), UTF8.is_continuation_byte(b2), accepted)))

# Every Some produced by the table has an accepted pair.
def utf8_proof.model_shape_accepted(shape: Maybe<&1, U32 & U32>) -> Bool:
  match shape:
    case None{}: False{}
    case Some{(b1, b2)}: UTF8.has_two_byte_shape(b1, b2)

def utf8_proof.model_fields(+low: Word(6n), +high: Word(5n),
  first_facts: {UTF8.is_two_byte_lead(utf8_proof.first_byte(high)) == True{} : Bool} &
  {(U32.is_ge(utf8_proof.first_byte(high), 194) && U32.is_le(utf8_proof.first_byte(high), 223)) == Bool.not(utf8_proof.fits_one_byte(high)) : Bool},
  second_facts: {UTF8.is_continuation_byte(utf8_proof.second_byte(low)) == True{} : Bool} &
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
      Empty.absurd(Utf8ModelDecodeSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))), UTF8.false_true(accepted))
    case False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(Utf8ModelDecodeSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))), UTF8.false_true(accepted))
    case False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(Utf8ModelDecodeSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))), UTF8.false_true(accepted))
    case False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(Utf8ModelDecodeSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))), UTF8.false_true(accepted))
    case False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(Utf8ModelDecodeSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))), UTF8.false_true(accepted))
    case False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(Utf8ModelDecodeSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))), UTF8.false_true(accepted))
    case False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(Utf8ModelDecodeSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))), UTF8.false_true(accepted))
    case False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(Utf8ModelDecodeSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))), UTF8.false_true(accepted))
    case False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(Utf8ModelDecodeSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))), UTF8.false_true(accepted))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(Utf8ModelDecodeSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))), UTF8.false_true(accepted))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(Utf8ModelDecodeSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))), UTF8.false_true(accepted))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _:
      Empty.absurd(Utf8ModelDecodeSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))), UTF8.false_true(accepted))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _:
      Empty.absurd(Utf8ModelDecodeSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))), UTF8.false_true(accepted))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _:
      Empty.absurd(Utf8ModelDecodeSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))), UTF8.false_true(accepted))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _:
      Empty.absurd(Utf8ModelDecodeSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))), UTF8.false_true(accepted))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _:
      Empty.absurd(Utf8ModelDecodeSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))), UTF8.false_true(accepted))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _:
      Empty.absurd(Utf8ModelDecodeSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))), UTF8.false_true(accepted))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _:
      Empty.absurd(Utf8ModelDecodeSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))), UTF8.false_true(accepted))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _:
      Empty.absurd(Utf8ModelDecodeSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))), UTF8.false_true(accepted))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _:
      Empty.absurd(Utf8ModelDecodeSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))), UTF8.false_true(accepted))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{}:
      Empty.absurd(Utf8ModelDecodeSpec(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))), UTF8.false_true(accepted))
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
    Maybe.is_some(&1, U32 & U32, Laws.two_byte_shape(cp)), True{}, utf8_proof.impl.can_encode_as_two_bytes(cp),
    Equal.cong(Maybe<&1, U32 & U32>, Bool, shape => Maybe.is_some(&1, U32 & U32, shape),
      Laws.two_byte_shape(cp), Some{(b1, b2)}, produced))
  Equal.trans(U32, UTF8.decode_two_bytes(b1, b2, valid),
    utf8_proof.decode_model_result(Laws.two_byte_shape(cp)), cp,
    Equal.sym(U32, utf8_proof.decode_model_result(Laws.two_byte_shape(cp)), UTF8.decode_two_bytes(b1, b2, valid),
      Equal.cong(Maybe<&1, U32 & U32>, U32, shape => utf8_proof.decode_model_result(shape),
        Laws.two_byte_shape(cp), Some{(b1, b2)}, produced)),
    utf8_proof.decode_model(cp, accepted))

# `utf8_proof.impl.has_two_byte_shape` supplies existence; the inverse
# calculation identifies its witness.
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

def utf8_proof.encode_decoded(+b1: U32, +b2: U32,
  -valid: {UTF8.has_two_byte_shape(b1, b2) == True{} : Bool},
  +produced: {Laws.two_byte_shape(UTF8.decode_two_bytes(b1, b2, valid)) == Some{(b1, b2)} : Maybe<&1, U32 & U32>}) ->
  Exists({UTF8.can_encode_as_two_bytes(UTF8.decode_two_bytes(b1, b2, valid)) == True{} : Bool}, accepted =>
    {UTF8.encode_as_two_bytes(UTF8.decode_two_bytes(b1, b2, valid), accepted) == (b1, b2) : U32 & U32}):
  +cp = UTF8.decode_two_bytes(b1, b2, valid)
  +accepted = Equal.trans(Bool, UTF8.can_encode_as_two_bytes(cp),
    Maybe.is_some(&1, U32 & U32, Laws.two_byte_shape(cp)), True{}, utf8_proof.impl.can_encode_as_two_bytes(cp),
    Equal.cong(Maybe<&1, U32 & U32>, Bool, shape => Maybe.is_some(&1, U32 & U32, shape),
      Laws.two_byte_shape(cp), Some{(b1, b2)}, produced))
  (accepted, Equal.cong(Maybe<&1, U32 & U32>, U32 & U32,
    shape => Maybe.default(&1, U32 & U32, shape, (0, 0)),
    Some{UTF8.encode_as_two_bytes(cp, accepted)}, Some{(b1, b2)},
    Equal.trans(Maybe<&1, U32 & U32>, Some{UTF8.encode_as_two_bytes(cp, accepted)},
      Laws.two_byte_shape(cp), Some{(b1, b2)}, utf8_proof.impl.encode_as_two_bytes(cp, accepted), produced)))

# Matching the pair exposes its bytes to the two-byte lemmas.
def utf8_proof.two_encode_decode(p: U32 & U32,
  +valid: {UTF8.has_two_byte_shape(utf8_proof.two_bytes.first(p), utf8_proof.two_bytes.second(p)) == True{} : Bool}) ->
  Exists({UTF8.can_encode_as_two_bytes(UTF8.decode_two_bytes(utf8_proof.two_bytes.first(p), utf8_proof.two_bytes.second(p), valid)) == True{} : Bool}, accepted =>
    {UTF8.encode_as_two_bytes(UTF8.decode_two_bytes(utf8_proof.two_bytes.first(p), utf8_proof.two_bytes.second(p), valid), accepted) == p : U32 & U32}):
  match p:
    case (+b1, +b2):
      utf8_proof.encode_decoded(b1, b2, valid,
        utf8_proof.decode_result_representation(b1, b2, valid, utf8_proof.shape_witness(b1, b2, valid)))

# Code points up to 2047 are scalars.  A set high bit contradicts the
# bound.  Otherwise the low eleven bits are split until the range check
# computes.
def utf8_proof.two_capacity_scalar_bits(+b31: Bool, +b30: Bool, +b29: Bool, +b28: Bool, +b27: Bool, +b26: Bool, +b25: Bool, +b24: Bool, +b23: Bool, +b22: Bool, +b21: Bool, +b20: Bool, +b19: Bool, +b18: Bool, +b17: Bool, +b16: Bool, +b15: Bool, +b14: Bool, +b13: Bool, +b12: Bool, +b11: Bool, +b10: Bool, +b9: Bool, +b8: Bool, +b7: Bool, +b6: Bool, +b5: Bool, +b4: Bool, +b3: Bool, +b2: Bool, +b1: Bool, +b0: Bool,
  accepted: {UTF8.can_encode_as_two_bytes(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))) == True{} : Bool}) ->
  {Laws.is_unicode_scalar(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))) == True{} : Bool}:
  match b31 b30 b29 b28 b27 b26 b25 b24 b23 b22 b21 b20 b19 b18 b17 b16 b15 b14 b13 b12 b11:
    case True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd({Laws.is_unicode_scalar(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))) == True{} : Bool}, UTF8.false_true(accepted))
    case False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd({Laws.is_unicode_scalar(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))) == True{} : Bool}, UTF8.false_true(accepted))
    case False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd({Laws.is_unicode_scalar(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))) == True{} : Bool}, UTF8.false_true(accepted))
    case False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd({Laws.is_unicode_scalar(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))) == True{} : Bool}, UTF8.false_true(accepted))
    case False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd({Laws.is_unicode_scalar(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))) == True{} : Bool}, UTF8.false_true(accepted))
    case False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd({Laws.is_unicode_scalar(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))) == True{} : Bool}, UTF8.false_true(accepted))
    case False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd({Laws.is_unicode_scalar(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))) == True{} : Bool}, UTF8.false_true(accepted))
    case False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd({Laws.is_unicode_scalar(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))) == True{} : Bool}, UTF8.false_true(accepted))
    case False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd({Laws.is_unicode_scalar(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))) == True{} : Bool}, UTF8.false_true(accepted))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd({Laws.is_unicode_scalar(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))) == True{} : Bool}, UTF8.false_true(accepted))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _:
      Empty.absurd({Laws.is_unicode_scalar(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))) == True{} : Bool}, UTF8.false_true(accepted))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _:
      Empty.absurd({Laws.is_unicode_scalar(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))) == True{} : Bool}, UTF8.false_true(accepted))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _:
      Empty.absurd({Laws.is_unicode_scalar(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))) == True{} : Bool}, UTF8.false_true(accepted))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _:
      Empty.absurd({Laws.is_unicode_scalar(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))) == True{} : Bool}, UTF8.false_true(accepted))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _:
      Empty.absurd({Laws.is_unicode_scalar(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))) == True{} : Bool}, UTF8.false_true(accepted))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _:
      Empty.absurd({Laws.is_unicode_scalar(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))) == True{} : Bool}, UTF8.false_true(accepted))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _:
      Empty.absurd({Laws.is_unicode_scalar(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))) == True{} : Bool}, UTF8.false_true(accepted))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _:
      Empty.absurd({Laws.is_unicode_scalar(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))) == True{} : Bool}, UTF8.false_true(accepted))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _:
      Empty.absurd({Laws.is_unicode_scalar(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))) == True{} : Bool}, UTF8.false_true(accepted))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _:
      Empty.absurd({Laws.is_unicode_scalar(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))) == True{} : Bool}, UTF8.false_true(accepted))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{}:
      Empty.absurd({Laws.is_unicode_scalar(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))) == True{} : Bool}, UTF8.false_true(accepted))
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

# Re-encoding the decoded value gives the same bytes, so the value is
# encodable, and so it is at most 2047.
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
    utf8_proof.bool.valid_two_bytes.if(b1, b2, shape, checked) : Bool}:
  match shape:
    case False{}: {==}
    case True{}: utf8_proof.valid_two_bytes_true(b1, b2, checked)

def utf8_proof.impl.valid_two_bytes(+b1: U32, +b2: U32) ->
  {UTF8.valid_two_bytes(b1, b2) == utf8_proof.bool.valid_two_bytes.if(b1, b2, UTF8.has_two_byte_shape(b1, b2), {==}) : Bool}:
  utf8_proof.valid_two_bytes_if(b1, b2, UTF8.has_two_byte_shape(b1, b2), {==})

def Laws.u32_byte4_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0):
  {==}

# The law's sum, added from the most significant bit down: after the
# bits above k are added, the sum is those bits in place with zeros
# below.  Adding bit k fills its place, by `word_add_fields`, without
# cases on the other bits.
def bit8_value.top(+b7: Bool) -> {U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{b7, Word.zero(24n)}}}}}}}}} == (Bool.to_u32(b7) * 128 : U32) : U32}:
  match b7:
    case False{}: {==}
    case True{}: {==}

def bit8_value.add6(+b7: Bool, +b6: Bool) ->
  {U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{b6, WCon{b7, Word.zero(24n)}}}}}}}}} == U32.add(U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{b7, Word.zero(24n)}}}}}}}}}, U32.mul(Bool.to_u32(b6), 64)) : U32}:
  match b6:
    case False{}:
      Equal.cong(Word(32n), U32, w => U32{w}, word_join(7n, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}, 25n, WCon{b7, Word.zero(24n)}),
        Word.add(32n, word_join(7n, Word.zero(7n), 25n, WCon{b7, Word.zero(24n)}), word_join(7n, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}, 25n, Word.zero(25n))),
        Equal.sym(Word(32n), Word.add(32n, word_join(7n, Word.zero(7n), 25n, WCon{b7, Word.zero(24n)}), word_join(7n, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}, 25n, Word.zero(25n))), word_join(7n, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}, 25n, WCon{b7, Word.zero(24n)}),
          word_add_fields(7n, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}, 25n, WCon{b7, Word.zero(24n)})))
    case True{}:
      Equal.cong(Word(32n), U32, w => U32{w}, word_join(7n, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}, 25n, WCon{b7, Word.zero(24n)}),
        Word.add(32n, word_join(7n, Word.zero(7n), 25n, WCon{b7, Word.zero(24n)}), word_join(7n, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}, 25n, Word.zero(25n))),
        Equal.sym(Word(32n), Word.add(32n, word_join(7n, Word.zero(7n), 25n, WCon{b7, Word.zero(24n)}), word_join(7n, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}, 25n, Word.zero(25n))), word_join(7n, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}, 25n, WCon{b7, Word.zero(24n)}),
          word_add_fields(7n, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}, 25n, WCon{b7, Word.zero(24n)})))

def bit8_value.add5(+b7: Bool, +b6: Bool, +b5: Bool) ->
  {U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{b5, WCon{b6, WCon{b7, Word.zero(24n)}}}}}}}}} == U32.add(U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{b6, WCon{b7, Word.zero(24n)}}}}}}}}}, U32.mul(Bool.to_u32(b5), 32)) : U32}:
  match b5:
    case False{}:
      Equal.cong(Word(32n), U32, w => U32{w}, word_join(6n, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}, 26n, WCon{b6, WCon{b7, Word.zero(24n)}}),
        Word.add(32n, word_join(6n, Word.zero(6n), 26n, WCon{b6, WCon{b7, Word.zero(24n)}}), word_join(6n, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}, 26n, Word.zero(26n))),
        Equal.sym(Word(32n), Word.add(32n, word_join(6n, Word.zero(6n), 26n, WCon{b6, WCon{b7, Word.zero(24n)}}), word_join(6n, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}, 26n, Word.zero(26n))), word_join(6n, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}, 26n, WCon{b6, WCon{b7, Word.zero(24n)}}),
          word_add_fields(6n, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}, 26n, WCon{b6, WCon{b7, Word.zero(24n)}})))
    case True{}:
      Equal.cong(Word(32n), U32, w => U32{w}, word_join(6n, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}, 26n, WCon{b6, WCon{b7, Word.zero(24n)}}),
        Word.add(32n, word_join(6n, Word.zero(6n), 26n, WCon{b6, WCon{b7, Word.zero(24n)}}), word_join(6n, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}, 26n, Word.zero(26n))),
        Equal.sym(Word(32n), Word.add(32n, word_join(6n, Word.zero(6n), 26n, WCon{b6, WCon{b7, Word.zero(24n)}}), word_join(6n, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}, 26n, Word.zero(26n))), word_join(6n, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}, 26n, WCon{b6, WCon{b7, Word.zero(24n)}}),
          word_add_fields(6n, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}, 26n, WCon{b6, WCon{b7, Word.zero(24n)}})))

def bit8_value.add4(+b7: Bool, +b6: Bool, +b5: Bool, +b4: Bool) ->
  {U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{b4, WCon{b5, WCon{b6, WCon{b7, Word.zero(24n)}}}}}}}}} == U32.add(U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{b5, WCon{b6, WCon{b7, Word.zero(24n)}}}}}}}}}, U32.mul(Bool.to_u32(b4), 16)) : U32}:
  match b4:
    case False{}:
      Equal.cong(Word(32n), U32, w => U32{w}, word_join(5n, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}, 27n, WCon{b5, WCon{b6, WCon{b7, Word.zero(24n)}}}),
        Word.add(32n, word_join(5n, Word.zero(5n), 27n, WCon{b5, WCon{b6, WCon{b7, Word.zero(24n)}}}), word_join(5n, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}, 27n, Word.zero(27n))),
        Equal.sym(Word(32n), Word.add(32n, word_join(5n, Word.zero(5n), 27n, WCon{b5, WCon{b6, WCon{b7, Word.zero(24n)}}}), word_join(5n, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}, 27n, Word.zero(27n))), word_join(5n, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}, 27n, WCon{b5, WCon{b6, WCon{b7, Word.zero(24n)}}}),
          word_add_fields(5n, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}, 27n, WCon{b5, WCon{b6, WCon{b7, Word.zero(24n)}}})))
    case True{}:
      Equal.cong(Word(32n), U32, w => U32{w}, word_join(5n, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}}, 27n, WCon{b5, WCon{b6, WCon{b7, Word.zero(24n)}}}),
        Word.add(32n, word_join(5n, Word.zero(5n), 27n, WCon{b5, WCon{b6, WCon{b7, Word.zero(24n)}}}), word_join(5n, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}}, 27n, Word.zero(27n))),
        Equal.sym(Word(32n), Word.add(32n, word_join(5n, Word.zero(5n), 27n, WCon{b5, WCon{b6, WCon{b7, Word.zero(24n)}}}), word_join(5n, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}}, 27n, Word.zero(27n))), word_join(5n, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}}, 27n, WCon{b5, WCon{b6, WCon{b7, Word.zero(24n)}}}),
          word_add_fields(5n, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}}, 27n, WCon{b5, WCon{b6, WCon{b7, Word.zero(24n)}}})))

def bit8_value.add3(+b7: Bool, +b6: Bool, +b5: Bool, +b4: Bool, +b3: Bool) ->
  {U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, Word.zero(24n)}}}}}}}}} == U32.add(U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{b4, WCon{b5, WCon{b6, WCon{b7, Word.zero(24n)}}}}}}}}}, U32.mul(Bool.to_u32(b3), 8)) : U32}:
  match b3:
    case False{}:
      Equal.cong(Word(32n), U32, w => U32{w}, word_join(4n, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}, 28n, WCon{b4, WCon{b5, WCon{b6, WCon{b7, Word.zero(24n)}}}}),
        Word.add(32n, word_join(4n, Word.zero(4n), 28n, WCon{b4, WCon{b5, WCon{b6, WCon{b7, Word.zero(24n)}}}}), word_join(4n, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}, 28n, Word.zero(28n))),
        Equal.sym(Word(32n), Word.add(32n, word_join(4n, Word.zero(4n), 28n, WCon{b4, WCon{b5, WCon{b6, WCon{b7, Word.zero(24n)}}}}), word_join(4n, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}, 28n, Word.zero(28n))), word_join(4n, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}, 28n, WCon{b4, WCon{b5, WCon{b6, WCon{b7, Word.zero(24n)}}}}),
          word_add_fields(4n, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}, 28n, WCon{b4, WCon{b5, WCon{b6, WCon{b7, Word.zero(24n)}}}})))
    case True{}:
      Equal.cong(Word(32n), U32, w => U32{w}, word_join(4n, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}, 28n, WCon{b4, WCon{b5, WCon{b6, WCon{b7, Word.zero(24n)}}}}),
        Word.add(32n, word_join(4n, Word.zero(4n), 28n, WCon{b4, WCon{b5, WCon{b6, WCon{b7, Word.zero(24n)}}}}), word_join(4n, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}, 28n, Word.zero(28n))),
        Equal.sym(Word(32n), Word.add(32n, word_join(4n, Word.zero(4n), 28n, WCon{b4, WCon{b5, WCon{b6, WCon{b7, Word.zero(24n)}}}}), word_join(4n, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}, 28n, Word.zero(28n))), word_join(4n, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}, 28n, WCon{b4, WCon{b5, WCon{b6, WCon{b7, Word.zero(24n)}}}}),
          word_add_fields(4n, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}, 28n, WCon{b4, WCon{b5, WCon{b6, WCon{b7, Word.zero(24n)}}}})))

def bit8_value.add2(+b7: Bool, +b6: Bool, +b5: Bool, +b4: Bool, +b3: Bool, +b2: Bool) ->
  {U32{WCon{False{}, WCon{False{}, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, Word.zero(24n)}}}}}}}}} == U32.add(U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, Word.zero(24n)}}}}}}}}}, U32.mul(Bool.to_u32(b2), 4)) : U32}:
  match b2:
    case False{}:
      Equal.cong(Word(32n), U32, w => U32{w}, word_join(3n, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}, 29n, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, Word.zero(24n)}}}}}),
        Word.add(32n, word_join(3n, Word.zero(3n), 29n, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, Word.zero(24n)}}}}}), word_join(3n, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}, 29n, Word.zero(29n))),
        Equal.sym(Word(32n), Word.add(32n, word_join(3n, Word.zero(3n), 29n, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, Word.zero(24n)}}}}}), word_join(3n, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}, 29n, Word.zero(29n))), word_join(3n, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}, 29n, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, Word.zero(24n)}}}}}),
          word_add_fields(3n, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}, 29n, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, Word.zero(24n)}}}}})))
    case True{}:
      Equal.cong(Word(32n), U32, w => U32{w}, word_join(3n, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}, 29n, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, Word.zero(24n)}}}}}),
        Word.add(32n, word_join(3n, Word.zero(3n), 29n, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, Word.zero(24n)}}}}}), word_join(3n, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}, 29n, Word.zero(29n))),
        Equal.sym(Word(32n), Word.add(32n, word_join(3n, Word.zero(3n), 29n, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, Word.zero(24n)}}}}}), word_join(3n, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}, 29n, Word.zero(29n))), word_join(3n, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}, 29n, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, Word.zero(24n)}}}}}),
          word_add_fields(3n, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}, 29n, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, Word.zero(24n)}}}}})))

def bit8_value.add1(+b7: Bool, +b6: Bool, +b5: Bool, +b4: Bool, +b3: Bool, +b2: Bool, +b1: Bool) ->
  {U32{WCon{False{}, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, Word.zero(24n)}}}}}}}}} == U32.add(U32{WCon{False{}, WCon{False{}, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, Word.zero(24n)}}}}}}}}}, U32.mul(Bool.to_u32(b1), 2)) : U32}:
  match b1:
    case False{}:
      Equal.cong(Word(32n), U32, w => U32{w}, word_join(2n, WCon{False{}, WCon{False{}, WNil{}}}, 30n, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, Word.zero(24n)}}}}}}),
        Word.add(32n, word_join(2n, Word.zero(2n), 30n, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, Word.zero(24n)}}}}}}), word_join(2n, WCon{False{}, WCon{False{}, WNil{}}}, 30n, Word.zero(30n))),
        Equal.sym(Word(32n), Word.add(32n, word_join(2n, Word.zero(2n), 30n, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, Word.zero(24n)}}}}}}), word_join(2n, WCon{False{}, WCon{False{}, WNil{}}}, 30n, Word.zero(30n))), word_join(2n, WCon{False{}, WCon{False{}, WNil{}}}, 30n, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, Word.zero(24n)}}}}}}),
          word_add_fields(2n, WCon{False{}, WCon{False{}, WNil{}}}, 30n, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, Word.zero(24n)}}}}}})))
    case True{}:
      Equal.cong(Word(32n), U32, w => U32{w}, word_join(2n, WCon{False{}, WCon{True{}, WNil{}}}, 30n, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, Word.zero(24n)}}}}}}),
        Word.add(32n, word_join(2n, Word.zero(2n), 30n, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, Word.zero(24n)}}}}}}), word_join(2n, WCon{False{}, WCon{True{}, WNil{}}}, 30n, Word.zero(30n))),
        Equal.sym(Word(32n), Word.add(32n, word_join(2n, Word.zero(2n), 30n, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, Word.zero(24n)}}}}}}), word_join(2n, WCon{False{}, WCon{True{}, WNil{}}}, 30n, Word.zero(30n))), word_join(2n, WCon{False{}, WCon{True{}, WNil{}}}, 30n, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, Word.zero(24n)}}}}}}),
          word_add_fields(2n, WCon{False{}, WCon{True{}, WNil{}}}, 30n, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, Word.zero(24n)}}}}}})))

def bit8_value.add0(+b7: Bool, +b6: Bool, +b5: Bool, +b4: Bool, +b3: Bool, +b2: Bool, +b1: Bool, +b0: Bool) ->
  {U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, Word.zero(24n)}}}}}}}}} == U32.add(U32{WCon{False{}, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, Word.zero(24n)}}}}}}}}}, U32.mul(Bool.to_u32(b0), 1)) : U32}:
  match b0:
    case False{}:
      Equal.cong(Word(32n), U32, w => U32{w}, word_join(1n, WCon{False{}, WNil{}}, 31n, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, Word.zero(24n)}}}}}}}),
        Word.add(32n, word_join(1n, Word.zero(1n), 31n, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, Word.zero(24n)}}}}}}}), word_join(1n, WCon{False{}, WNil{}}, 31n, Word.zero(31n))),
        Equal.sym(Word(32n), Word.add(32n, word_join(1n, Word.zero(1n), 31n, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, Word.zero(24n)}}}}}}}), word_join(1n, WCon{False{}, WNil{}}, 31n, Word.zero(31n))), word_join(1n, WCon{False{}, WNil{}}, 31n, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, Word.zero(24n)}}}}}}}),
          word_add_fields(1n, WCon{False{}, WNil{}}, 31n, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, Word.zero(24n)}}}}}}})))
    case True{}:
      Equal.cong(Word(32n), U32, w => U32{w}, word_join(1n, WCon{True{}, WNil{}}, 31n, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, Word.zero(24n)}}}}}}}),
        Word.add(32n, word_join(1n, Word.zero(1n), 31n, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, Word.zero(24n)}}}}}}}), word_join(1n, WCon{True{}, WNil{}}, 31n, Word.zero(31n))),
        Equal.sym(Word(32n), Word.add(32n, word_join(1n, Word.zero(1n), 31n, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, Word.zero(24n)}}}}}}}), word_join(1n, WCon{True{}, WNil{}}, 31n, Word.zero(31n))), word_join(1n, WCon{True{}, WNil{}}, 31n, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, Word.zero(24n)}}}}}}}),
          word_add_fields(1n, WCon{True{}, WNil{}}, 31n, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, Word.zero(24n)}}}}}}})))

def Laws.bit8_value_sum(b7, b6, b5, b4, b3, b2, b1, b0):
  %bit8_value.top(b7) :
    {Laws.bit8_value((b7, b6, b5, b4, b3, b2, b1, b0)) ==
      U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(_, U32.mul(Bool.to_u32(b6), 64)), U32.mul(Bool.to_u32(b5), 32)), U32.mul(Bool.to_u32(b4), 16)), U32.mul(Bool.to_u32(b3), 8)), U32.mul(Bool.to_u32(b2), 4)), U32.mul(Bool.to_u32(b1), 2)), U32.mul(Bool.to_u32(b0), 1)) : U32}
  %bit8_value.add6(b7, b6) :
    {Laws.bit8_value((b7, b6, b5, b4, b3, b2, b1, b0)) ==
      U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(_, U32.mul(Bool.to_u32(b5), 32)), U32.mul(Bool.to_u32(b4), 16)), U32.mul(Bool.to_u32(b3), 8)), U32.mul(Bool.to_u32(b2), 4)), U32.mul(Bool.to_u32(b1), 2)), U32.mul(Bool.to_u32(b0), 1)) : U32}
  %bit8_value.add5(b7, b6, b5) :
    {Laws.bit8_value((b7, b6, b5, b4, b3, b2, b1, b0)) ==
      U32.add(U32.add(U32.add(U32.add(U32.add(_, U32.mul(Bool.to_u32(b4), 16)), U32.mul(Bool.to_u32(b3), 8)), U32.mul(Bool.to_u32(b2), 4)), U32.mul(Bool.to_u32(b1), 2)), U32.mul(Bool.to_u32(b0), 1)) : U32}
  %bit8_value.add4(b7, b6, b5, b4) :
    {Laws.bit8_value((b7, b6, b5, b4, b3, b2, b1, b0)) ==
      U32.add(U32.add(U32.add(U32.add(_, U32.mul(Bool.to_u32(b3), 8)), U32.mul(Bool.to_u32(b2), 4)), U32.mul(Bool.to_u32(b1), 2)), U32.mul(Bool.to_u32(b0), 1)) : U32}
  %bit8_value.add3(b7, b6, b5, b4, b3) :
    {Laws.bit8_value((b7, b6, b5, b4, b3, b2, b1, b0)) ==
      U32.add(U32.add(U32.add(_, U32.mul(Bool.to_u32(b2), 4)), U32.mul(Bool.to_u32(b1), 2)), U32.mul(Bool.to_u32(b0), 1)) : U32}
  %bit8_value.add2(b7, b6, b5, b4, b3, b2) :
    {Laws.bit8_value((b7, b6, b5, b4, b3, b2, b1, b0)) ==
      U32.add(U32.add(_, U32.mul(Bool.to_u32(b1), 2)), U32.mul(Bool.to_u32(b0), 1)) : U32}
  %bit8_value.add1(b7, b6, b5, b4, b3, b2, b1) :
    {Laws.bit8_value((b7, b6, b5, b4, b3, b2, b1, b0)) ==
      U32.add(_, U32.mul(Bool.to_u32(b0), 1)) : U32}
  %bit8_value.add0(b7, b6, b5, b4, b3, b2, b1, b0) :
    {Laws.bit8_value((b7, b6, b5, b4, b3, b2, b1, b0)) ==
      _ : U32}
  {==}

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

def Laws.bit8_value_word(b7, b6, b5, b4, b3, b2, b1, b0):
  word = {WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WNil{}}}}}}}}} : Word(8n)}
  Equal.sym(U32, U32.from_nat(Word.to_nat(8n, word)), word_to_u32(8n, word),
    word_to_u32_from_nat(8n, word))

# Split on the shape: when the shape test fails, `valid_one_byte.if` is
# False, contradicting `valid`.
def utf8_proof.valid_one_byte_has_shape.if(+byte: U32, shape: Bool,
  checked: {UTF8.has_one_byte_shape(byte) == shape : Bool},
  valid: {utf8_proof.bool.valid_one_byte.if(byte, shape, checked) == True{} : Bool}) ->
  {UTF8.has_one_byte_shape(byte) == True{} : Bool}:
  match shape:
    case False{}:
      Empty.absurd({UTF8.has_one_byte_shape(byte) == True{} : Bool},
        UTF8.false_true(valid))
    case True{}:
      checked

# A valid one-byte sequence has the one-byte shape.
def utf8_proof.valid_one_byte_has_shape(+byte: U32,
  valid: {UTF8.valid_one_byte(byte) == True{} : Bool}) ->
  {UTF8.has_one_byte_shape(byte) == True{} : Bool}:
  +shape = UTF8.has_one_byte_shape(byte)
  utf8_proof.valid_one_byte_has_shape.if(byte, shape, {==},
    Equal.trans(Bool, utf8_proof.bool.valid_one_byte.if(byte, shape, {==}), UTF8.valid_one_byte(byte), True{},
      Equal.sym(Bool, UTF8.valid_one_byte(byte), utf8_proof.bool.valid_one_byte.if(byte, shape, {==}),
        utf8_proof.impl.valid_one_byte(byte)),
      valid))

# The same split, for two bytes.
def utf8_proof.valid_two_bytes_has_shape.if(+b1: U32, +b2: U32, shape: Bool,
  checked: {UTF8.has_two_byte_shape(b1, b2) == shape : Bool},
  valid: {utf8_proof.bool.valid_two_bytes.if(b1, b2, shape, checked) == True{} : Bool}) ->
  {UTF8.has_two_byte_shape(b1, b2) == True{} : Bool}:
  match shape:
    case False{}:
      Empty.absurd({UTF8.has_two_byte_shape(b1, b2) == True{} : Bool},
        UTF8.false_true(valid))
    case True{}:
      checked

# A valid two-byte sequence has the two-byte shape.
def utf8_proof.valid_two_bytes_has_shape(+b1: U32, +b2: U32,
  valid: {UTF8.valid_two_bytes(b1, b2) == True{} : Bool}) ->
  {UTF8.has_two_byte_shape(b1, b2) == True{} : Bool}:
  +shape = UTF8.has_two_byte_shape(b1, b2)
  utf8_proof.valid_two_bytes_has_shape.if(b1, b2, shape, {==},
    Equal.trans(Bool, utf8_proof.bool.valid_two_bytes.if(b1, b2, shape, {==}), UTF8.valid_two_bytes(b1, b2), True{},
      Equal.sym(Bool, UTF8.valid_two_bytes(b1, b2), utf8_proof.bool.valid_two_bytes.if(b1, b2, shape, {==}),
        utf8_proof.impl.valid_two_bytes(b1, b2)),
      valid))

# Three-byte and four-byte sequences
# ==================================
#
# These proofs work with symbolic payload fields rather than enumerating
# code points.  Comparisons against a constant whose low bits are all ones
# or all zeros depend only on the high bits, whatever the low bits are.

def utf8_proof.fin_le_ones(+ab: Bool, t: Cmp) ->
  {Cmp.is_le(Word.cmp.fin(ab, True{}, t)) == Cmp.is_le(t) : Bool}:
  match ab t:
    case False{} LT{}: {==}
    case False{} EQ{}: {==}
    case False{} GT{}: {==}
    case True{} LT{}: {==}
    case True{} EQ{}: {==}
    case True{} GT{}: {==}

def utf8_proof.fin_ge_zero(+ab: Bool, t: Cmp) ->
  {Cmp.is_ge(Word.cmp.fin(ab, False{}, t)) == Cmp.is_ge(t) : Bool}:
  match ab t:
    case False{} LT{}: {==}
    case False{} EQ{}: {==}
    case False{} GT{}: {==}
    case True{} LT{}: {==}
    case True{} EQ{}: {==}
    case True{} GT{}: {==}

def utf8_proof.word_le_ones(+n: Nat, +low: Word(n), +m: Nat, +high: Word(m), +other: Word(m)) ->
  {Cmp.is_le(Word.cmp(Nat.add(n, m), word_join(n, low, m, high), word_join(n, word_ones(n), m, other))) ==
    Cmp.is_le(Word.cmp(m, high, other)) : Bool}:
  match n:
    case 0n: {==}
    case 1n+p:
      match low:
        case WCon{+b, +rest}:
          Equal.trans(Bool,
            Cmp.is_le(Word.cmp.fin(b, True{}, Word.cmp(Nat.add(p, m), word_join(p, rest, m, high), word_join(p, word_ones(p), m, other)))),
            Cmp.is_le(Word.cmp(Nat.add(p, m), word_join(p, rest, m, high), word_join(p, word_ones(p), m, other))),
            Cmp.is_le(Word.cmp(m, high, other)),
            utf8_proof.fin_le_ones(b, Word.cmp(Nat.add(p, m), word_join(p, rest, m, high), word_join(p, word_ones(p), m, other))),
            utf8_proof.word_le_ones(p, rest, m, high, other))

def utf8_proof.word_ge_zeros(+n: Nat, +low: Word(n), +m: Nat, +high: Word(m), +other: Word(m)) ->
  {Cmp.is_ge(Word.cmp(Nat.add(n, m), word_join(n, low, m, high), word_join(n, Word.zero(n), m, other))) ==
    Cmp.is_ge(Word.cmp(m, high, other)) : Bool}:
  match n:
    case 0n: {==}
    case 1n+p:
      match low:
        case WCon{+b, +rest}:
          Equal.trans(Bool,
            Cmp.is_ge(Word.cmp.fin(b, False{}, Word.cmp(Nat.add(p, m), word_join(p, rest, m, high), word_join(p, Word.zero(p), m, other)))),
            Cmp.is_ge(Word.cmp(Nat.add(p, m), word_join(p, rest, m, high), word_join(p, Word.zero(p), m, other))),
            Cmp.is_ge(Word.cmp(m, high, other)),
            utf8_proof.fin_ge_zero(b, Word.cmp(Nat.add(p, m), word_join(p, rest, m, high), word_join(p, Word.zero(p), m, other))),
            utf8_proof.word_ge_zeros(p, rest, m, high, other))

def utf8_proof.word_ge_zero(+n: Nat, +w: Word(n)) ->
  {Cmp.is_ge(Word.cmp(n, w, Word.zero(n))) == True{} : Bool}:
  match n:
    case 0n: {==}
    case 1n+p:
      match w:
        case WCon{+b, +rest}:
          Equal.trans(Bool,
            Cmp.is_ge(Word.cmp.fin(b, False{}, Word.cmp(p, rest, Word.zero(p)))),
            Cmp.is_ge(Word.cmp(p, rest, Word.zero(p))), True{},
            utf8_proof.fin_ge_zero(b, Word.cmp(p, rest, Word.zero(p))),
            utf8_proof.word_ge_zero(p, rest))

def utf8_proof.u32_ge_zero(+cp: U32) -> {U32.is_ge(cp, 0) == True{} : Bool}:
  match cp:
    case U32{+w}: utf8_proof.word_ge_zero(32n, w)

# The implementation's scalar test is the specification's.
def utf8_proof.scalar_agrees(+cp: U32) -> {UTF8.is_scalar(cp) == Laws.is_unicode_scalar(cp) : Bool}:
  %Equal.sym(Bool, U32.is_ge(cp, 0), True{}, utf8_proof.u32_ge_zero(cp)) :
    {UTF8.is_scalar(cp) == Bool.and(Bool.and(_, U32.is_le(cp, 1114111)), Bool.not(Laws.is_surrogate_code_point(cp))) : Bool}
  {==}

# Shifting in a continuation byte.
def utf8_proof.append_eq(+acc: U32, +y: Word(6n), +hi: Word(26n),
  e: {U32.shln(acc, 6n) == U32{word_join(6n, Word.zero(6n), 26n, hi)} : U32}) ->
  {UTF8.append_continuation(acc, utf8_proof.second_byte(y)) == U32{word_join(6n, y, 26n, hi)} : U32}:
  %Equal.sym(U32, U32.shln(acc, 6n), U32{word_join(6n, Word.zero(6n), 26n, hi)}, e) :
    {(_ + U32.and(utf8_proof.second_byte(y), 63) : U32) == U32{word_join(6n, y, 26n, hi)} : U32}
  %Equal.sym(U32, U32.and(utf8_proof.second_byte(y), 63), U32{word_join(6n, y, 26n, Word.zero(26n))}, utf8_proof.mask_second(y)) :
    {(U32{word_join(6n, Word.zero(6n), 26n, hi)} + _ : U32) == U32{word_join(6n, y, 26n, hi)} : U32}
  Equal.cong(Word(32n), U32, x => U32{x},
    Word.add(32n, word_join(6n, Word.zero(6n), 26n, hi), word_join(6n, y, 26n, Word.zero(26n))),
    word_join(6n, y, 26n, hi), word_add_fields(6n, y, 26n, hi))

def utf8_proof.cont_mask.first(+c: U32,
  facts: {UTF8.is_continuation_byte(c) == True{} : Bool} &
    {(U32.is_ge(c, 128) && U32.is_le(c, 191)) == True{} : Bool}) ->
  {UTF8.is_continuation_byte(c) == True{} : Bool}:
  (m, r) = facts
  m

def utf8_proof.cont_mask(+y: Word(6n)) ->
  {UTF8.is_continuation_byte(utf8_proof.second_byte(y)) == True{} : Bool}:
  utf8_proof.cont_mask.first(utf8_proof.second_byte(y), utf8_proof.second_byte_facts(y))

def utf8_proof.bit4(y: Word(6n)) -> Bool:
  match y:
    case WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WNil{}}}}}}}: b4

def utf8_proof.bit5(y: Word(6n)) -> Bool:
  match y:
    case WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WNil{}}}}}}}: b5

# Three-byte sequences
# ------------------

def utf8_proof.cp3(+z: Word(6n), +y: Word(6n), +t: Word(4n)) -> U32:
  U32{word_join(6n, z, 26n, word_join(6n, y, 20n, word_join(4n, t, 16n, Word.zero(16n))))}

def utf8_proof.lead3(t: Word(4n)) -> U32:
  U32{word_join(4n, t, 28n, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, Word.zero(24n)}}}})}

# A byte that passes `UTF8.is_three_byte_lead` is
# `utf8_proof.lead3` of its low 4 bits.
def utf8_proof.lead3_payload.Payload(+byte: U32) -> Type:
  Exists(Word(4n), payload => {byte == utf8_proof.lead3(payload) : U32})

# Split on the bits from the top: the first bit that differs from the
# pattern makes the test False, contradicting `valid`.
def utf8_proof.lead3_payload.bits(+b31: Bool, +b30: Bool, +b29: Bool, +b28: Bool, +b27: Bool, +b26: Bool, +b25: Bool, +b24: Bool, +b23: Bool, +b22: Bool, +b21: Bool, +b20: Bool, +b19: Bool, +b18: Bool, +b17: Bool, +b16: Bool, +b15: Bool, +b14: Bool, +b13: Bool, +b12: Bool, +b11: Bool, +b10: Bool, +b9: Bool, +b8: Bool, +b7: Bool, +b6: Bool, +b5: Bool, +b4: Bool, +b3: Bool, +b2: Bool, +b1: Bool, +b0: Bool,
  valid: {UTF8.is_three_byte_lead(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))) == True{} : Bool}) ->
  utf8_proof.lead3_payload.Payload(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))):
  match b31 b30 b29 b28 b27 b26 b25 b24 b23 b22 b21 b20 b19 b18 b17 b16 b15 b14 b13 b12 b11 b10 b9 b8 b7 b6 b5 b4:
    case True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(utf8_proof.lead3_payload.Payload(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))), UTF8.false_true(valid))
    case False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(utf8_proof.lead3_payload.Payload(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))), UTF8.false_true(valid))
    case False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(utf8_proof.lead3_payload.Payload(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))), UTF8.false_true(valid))
    case False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(utf8_proof.lead3_payload.Payload(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))), UTF8.false_true(valid))
    case False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(utf8_proof.lead3_payload.Payload(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))), UTF8.false_true(valid))
    case False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(utf8_proof.lead3_payload.Payload(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))), UTF8.false_true(valid))
    case False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(utf8_proof.lead3_payload.Payload(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))), UTF8.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(utf8_proof.lead3_payload.Payload(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))), UTF8.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(utf8_proof.lead3_payload.Payload(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))), UTF8.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(utf8_proof.lead3_payload.Payload(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))), UTF8.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(utf8_proof.lead3_payload.Payload(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))), UTF8.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(utf8_proof.lead3_payload.Payload(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))), UTF8.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(utf8_proof.lead3_payload.Payload(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))), UTF8.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(utf8_proof.lead3_payload.Payload(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))), UTF8.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(utf8_proof.lead3_payload.Payload(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))), UTF8.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(utf8_proof.lead3_payload.Payload(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))), UTF8.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(utf8_proof.lead3_payload.Payload(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))), UTF8.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(utf8_proof.lead3_payload.Payload(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))), UTF8.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _:
      Empty.absurd(utf8_proof.lead3_payload.Payload(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))), UTF8.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _:
      Empty.absurd(utf8_proof.lead3_payload.Payload(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))), UTF8.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _:
      Empty.absurd(utf8_proof.lead3_payload.Payload(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))), UTF8.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _:
      Empty.absurd(utf8_proof.lead3_payload.Payload(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))), UTF8.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _:
      Empty.absurd(utf8_proof.lead3_payload.Payload(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))), UTF8.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _:
      Empty.absurd(utf8_proof.lead3_payload.Payload(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))), UTF8.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} _ _ _:
      Empty.absurd(utf8_proof.lead3_payload.Payload(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))), UTF8.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} False{} _ _:
      Empty.absurd(utf8_proof.lead3_payload.Payload(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))), UTF8.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} True{} False{} _:
      Empty.absurd(utf8_proof.lead3_payload.Payload(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))), UTF8.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} True{} True{} True{}:
      Empty.absurd(utf8_proof.lead3_payload.Payload(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))), UTF8.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} True{} True{} False{}:
      (WCon{b0, WCon{b1, WCon{b2, WCon{b3, WNil{}}}}}, {==})

def utf8_proof.lead3_payload(+byte: U32,
  +valid: {UTF8.is_three_byte_lead(byte) == True{} : Bool}) ->
  Exists(Word(4n), payload => {byte == utf8_proof.lead3(payload) : U32}):
  match byte:
    case U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      utf8_proof.lead3_payload.bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0, valid)

def utf8_proof.dec3(+b1: U32, +b2: U32, +b3: U32) -> U32:
  UTF8.append_continuation(UTF8.append_continuation(U32.and(b1, 15), b2), b3)

def utf8_proof.mask_lead3(+t: Word(4n)) ->
  {U32.and(utf8_proof.lead3(t), 15) == U32{word_join(4n, t, 28n, Word.zero(28n))} : U32}:
  Equal.cong(Word(32n), U32, x => U32{x},
    Word.and(32n, word_join(4n, t, 28n, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, Word.zero(24n)}}}}), word_join(4n, word_ones(4n), 28n, Word.zero(28n))),
    word_join(4n, t, 28n, Word.zero(28n)), word_mask_fields(4n, t, 28n, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, Word.zero(24n)}}}}))

def utf8_proof.dec3_fields(+z: Word(6n), +y: Word(6n), +t: Word(4n)) ->
  {utf8_proof.dec3(utf8_proof.lead3(t), utf8_proof.second_byte(y), utf8_proof.second_byte(z)) == utf8_proof.cp3(z, y, t) : U32}:
  match z y t:
    case WCon{z0, WCon{z1, WCon{z2, WCon{z3, WCon{z4, WCon{z5, WNil{}}}}}}} WCon{y0, WCon{y1, WCon{y2, WCon{y3, WCon{y4, WCon{y5, WNil{}}}}}}} WCon{t0, WCon{t1, WCon{t2, WCon{t3, WNil{}}}}}:
      %Equal.sym(U32, U32.and(utf8_proof.lead3(t), 15), U32{word_join(4n, t, 28n, Word.zero(28n))}, utf8_proof.mask_lead3(t)) :
        {UTF8.append_continuation(UTF8.append_continuation(_, utf8_proof.second_byte(y)), utf8_proof.second_byte(z)) == utf8_proof.cp3(z, y, t) : U32}
      %Equal.sym(U32, UTF8.append_continuation(U32{word_join(4n, t, 28n, Word.zero(28n))}, utf8_proof.second_byte(y)), U32{word_join(6n, y, 26n, word_join(4n, t, 22n, Word.zero(22n)))},
          utf8_proof.append_eq(U32{word_join(4n, t, 28n, Word.zero(28n))}, y, word_join(4n, t, 22n, Word.zero(22n)), {==})) :
        {UTF8.append_continuation(_, utf8_proof.second_byte(z)) == utf8_proof.cp3(z, y, t) : U32}
      utf8_proof.append_eq(U32{word_join(6n, y, 26n, word_join(4n, t, 22n, Word.zero(22n)))}, z, word_join(6n, y, 20n, word_join(4n, t, 16n, Word.zero(16n))), {==})

def utf8_proof.table3(+z: Word(6n), +y: Word(6n), +t: Word(4n)) ->
  {Laws.three_byte_shape(utf8_proof.cp3(z, y, t)) == Some{(utf8_proof.lead3(t), utf8_proof.second_byte(y), utf8_proof.second_byte(z))} : Maybe<&1, U32 & U32 & U32>}:
  match z y t:
    case WCon{z0, WCon{z1, WCon{z2, WCon{z3, WCon{z4, WCon{z5, WNil{}}}}}}} WCon{y0, WCon{y1, WCon{y2, WCon{y3, WCon{y4, WCon{y5, WNil{}}}}}}} WCon{t0, WCon{t1, WCon{t2, WCon{t3, WNil{}}}}}: {==}

def utf8_proof.View3(+cp: U32) -> Type:
  Exists(Word(6n), z => Exists(Word(6n), y => Exists(Word(4n), t => {cp == utf8_proof.cp3(z, y, t) : U32})))

def utf8_proof.view3_bits(+b31: Bool, +b30: Bool, +b29: Bool, +b28: Bool, +b27: Bool, +b26: Bool, +b25: Bool, +b24: Bool, +b23: Bool, +b22: Bool, +b21: Bool, +b20: Bool, +b19: Bool, +b18: Bool, +b17: Bool, +b16: Bool, +b15: Bool, +b14: Bool, +b13: Bool, +b12: Bool, +b11: Bool, +b10: Bool, +b9: Bool, +b8: Bool, +b7: Bool, +b6: Bool, +b5: Bool, +b4: Bool, +b3: Bool, +b2: Bool, +b1: Bool, +b0: Bool,
  valid: {UTF8.can_encode_as_three_bytes(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}) == True{} : Bool}) -> utf8_proof.View3(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}):
  match b31 b30 b29 b28 b27 b26 b25 b24 b23 b22 b21 b20 b19 b18 b17 b16:
    case True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(utf8_proof.View3(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}), UTF8.false_true(valid))
    case False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(utf8_proof.View3(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}), UTF8.false_true(valid))
    case False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(utf8_proof.View3(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}), UTF8.false_true(valid))
    case False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(utf8_proof.View3(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}), UTF8.false_true(valid))
    case False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(utf8_proof.View3(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}), UTF8.false_true(valid))
    case False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(utf8_proof.View3(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}), UTF8.false_true(valid))
    case False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _:
      Empty.absurd(utf8_proof.View3(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}), UTF8.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _:
      Empty.absurd(utf8_proof.View3(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}), UTF8.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _:
      Empty.absurd(utf8_proof.View3(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}), UTF8.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _:
      Empty.absurd(utf8_proof.View3(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}), UTF8.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _:
      Empty.absurd(utf8_proof.View3(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}), UTF8.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _:
      Empty.absurd(utf8_proof.View3(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}), UTF8.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _:
      Empty.absurd(utf8_proof.View3(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}), UTF8.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _:
      Empty.absurd(utf8_proof.View3(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}), UTF8.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _:
      Empty.absurd(utf8_proof.View3(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}), UTF8.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{}:
      Empty.absurd(utf8_proof.View3(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}), UTF8.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{}:
      (WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WNil{}}}}}}}, (WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WNil{}}}}}}}, (WCon{b12, WCon{b13, WCon{b14, WCon{b15, WNil{}}}}}, {==})))

def utf8_proof.view3(+cp: U32, valid: {UTF8.can_encode_as_three_bytes(cp) == True{} : Bool}) -> utf8_proof.View3(cp):
  match cp:
    case U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      utf8_proof.view3_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0, valid)

def utf8_proof.can3_bits(+b31: Bool, +b30: Bool, +b29: Bool, +b28: Bool, +b27: Bool, +b26: Bool, +b25: Bool, +b24: Bool, +b23: Bool, +b22: Bool, +b21: Bool, +b20: Bool, +b19: Bool, +b18: Bool, +b17: Bool, +b16: Bool, +b15: Bool, +b14: Bool, +b13: Bool, +b12: Bool, +b11: Bool, +b10: Bool, +b9: Bool, +b8: Bool, +b7: Bool, +b6: Bool, +b5: Bool, +b4: Bool, +b3: Bool, +b2: Bool, +b1: Bool, +b0: Bool) ->
  {UTF8.can_encode_as_three_bytes(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}) == Maybe.is_some(&1, U32 & U32 & U32, Laws.three_byte_shape(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}})) : Bool}:
  match b31 b30 b29 b28 b27 b26 b25 b24 b23 b22 b21 b20 b19 b18 b17 b16:
    case True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _: {==}
    case False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _: {==}
    case False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _: {==}
    case False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _: {==}
    case False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _: {==}
    case False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _: {==}
    case False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _: {==}
    case False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _: {==}
    case False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _: {==}
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _: {==}
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _: {==}
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _: {==}
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _: {==}
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _: {==}
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _: {==}
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{}: {==}
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{}:
      utf8_proof.word_le_ones(16n, WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WNil{}}}}}}}}}}}}}}}}}, 16n, Word.zero(16n), Word.zero(16n))

def utf8_proof.impl.can_encode_as_three_bytes(+cp: U32) ->
  {UTF8.can_encode_as_three_bytes(cp) == Maybe.is_some(&1, U32 & U32 & U32, Laws.three_byte_shape(cp)) : Bool}:
  match cp:
    case U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      utf8_proof.can3_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0)

def utf8_proof.lead3_mask(+t: Word(4n)) ->
  {UTF8.is_three_byte_lead(utf8_proof.lead3(t)) == True{} : Bool}:
  match t:
    case WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}: {==}
    case WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}: {==}
    case WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WNil{}}}}}: {==}
    case WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WNil{}}}}}: {==}
    case WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WNil{}}}}}: {==}
    case WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WNil{}}}}}: {==}
    case WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WNil{}}}}}: {==}
    case WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WNil{}}}}}: {==}
    case WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}: {==}
    case WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}: {==}
    case WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WNil{}}}}}: {==}
    case WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WNil{}}}}}: {==}
    case WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WNil{}}}}}: {==}
    case WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WNil{}}}}}: {==}
    case WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WNil{}}}}}: {==}
    case WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WNil{}}}}}: {==}

def utf8_proof.has3_fields(+z: Word(6n), +y: Word(6n), +t: Word(4n)) ->
  {UTF8.has_three_byte_shape(utf8_proof.lead3(t), utf8_proof.second_byte(y), utf8_proof.second_byte(z)) == True{} : Bool}:
  %Equal.sym(Bool, UTF8.is_three_byte_lead(utf8_proof.lead3(t)), True{}, utf8_proof.lead3_mask(t)) :
    {Bool.and(Bool.and(_, UTF8.is_continuation_byte(utf8_proof.second_byte(y))), UTF8.is_continuation_byte(utf8_proof.second_byte(z))) == True{} : Bool}
  %Equal.sym(Bool, UTF8.is_continuation_byte(utf8_proof.second_byte(y)), True{}, utf8_proof.cont_mask(y)) :
    {Bool.and(Bool.and(True{}, _), UTF8.is_continuation_byte(utf8_proof.second_byte(z))) == True{} : Bool}
  %Equal.sym(Bool, UTF8.is_continuation_byte(utf8_proof.second_byte(z)), True{}, utf8_proof.cont_mask(z)) :
    {Bool.and(Bool.and(True{}, True{}), _) == True{} : Bool}
  {==}

def utf8_proof.Fields3(+b1: U32, +b2: U32, +b3: U32) -> Type:
  Exists(Word(6n), z => Exists(Word(6n), y => Exists(Word(4n), t => {b1 == utf8_proof.lead3(t) : U32} & {b2 == utf8_proof.second_byte(y) : U32} & {b3 == utf8_proof.second_byte(z) : U32})))

def utf8_proof.fields3.of(+b1: U32, +b2: U32, +b3: U32, pt: Exists(Word(4n), t => {b1 == utf8_proof.lead3(t) : U32}), py: Exists(Word(6n), y => {b2 == utf8_proof.second_byte(y) : U32}), pz: Exists(Word(6n), z => {b3 == utf8_proof.second_byte(z) : U32})) -> utf8_proof.Fields3(b1, b2, b3):
  (+t, et) = pt
  (+y, ey) = py
  (+z, ez) = pz
  (z, (y, (t, (et, (ey, ez)))))

def utf8_proof.fields3(+b1: U32, +b2: U32, +b3: U32, +accepted: {UTF8.has_three_byte_shape(b1, b2, b3) == True{} : Bool}) -> utf8_proof.Fields3(b1, b2, b3):
  utf8_proof.fields3.of(b1, b2, b3, utf8_proof.lead3_payload(b1, bool_and_left_true(UTF8.is_three_byte_lead(b1), UTF8.is_continuation_byte(b2), bool_and_left_true(Bool.and(UTF8.is_three_byte_lead(b1), UTF8.is_continuation_byte(b2)), UTF8.is_continuation_byte(b3), accepted))), utf8_proof.second_payload(b2, bool_and_right_true(UTF8.is_three_byte_lead(b1), UTF8.is_continuation_byte(b2), bool_and_left_true(Bool.and(UTF8.is_three_byte_lead(b1), UTF8.is_continuation_byte(b2)), UTF8.is_continuation_byte(b3), accepted))), utf8_proof.second_payload(b3, bool_and_right_true(Bool.and(UTF8.is_three_byte_lead(b1), UTF8.is_continuation_byte(b2)), UTF8.is_continuation_byte(b3), accepted)))

def utf8_proof.produced3_at(+z: Word(6n), +y: Word(6n), +t: Word(4n), +b1: U32, +b2: U32, +b3: U32, et: {b1 == utf8_proof.lead3(t) : U32}, ey: {b2 == utf8_proof.second_byte(y) : U32}, ez: {b3 == utf8_proof.second_byte(z) : U32}) ->
  {Laws.three_byte_shape(utf8_proof.cp3(z, y, t)) == Some{(b1, b2, b3)} : Maybe<&1, U32 & U32 & U32>}:
  %Equal.sym(U32, b1, utf8_proof.lead3(t), et) : {Laws.three_byte_shape(utf8_proof.cp3(z, y, t)) == Some{(_, b2, b3)} : Maybe<&1, U32 & U32 & U32>}
  %Equal.sym(U32, b2, utf8_proof.second_byte(y), ey) : {Laws.three_byte_shape(utf8_proof.cp3(z, y, t)) == Some{(utf8_proof.lead3(t), _, b3)} : Maybe<&1, U32 & U32 & U32>}
  %Equal.sym(U32, b3, utf8_proof.second_byte(z), ez) : {Laws.three_byte_shape(utf8_proof.cp3(z, y, t)) == Some{(utf8_proof.lead3(t), utf8_proof.second_byte(y), _)} : Maybe<&1, U32 & U32 & U32>}
  utf8_proof.table3(z, y, t)

def utf8_proof.dec3_at(+z: Word(6n), +y: Word(6n), +t: Word(4n), +b1: U32, +b2: U32, +b3: U32, et: {b1 == utf8_proof.lead3(t) : U32}, ey: {b2 == utf8_proof.second_byte(y) : U32}, ez: {b3 == utf8_proof.second_byte(z) : U32}) ->
  {utf8_proof.dec3(b1, b2, b3) == utf8_proof.cp3(z, y, t) : U32}:
  %Equal.sym(U32, b1, utf8_proof.lead3(t), et) : {utf8_proof.dec3(_, b2, b3) == utf8_proof.cp3(z, y, t) : U32}
  %Equal.sym(U32, b2, utf8_proof.second_byte(y), ey) : {utf8_proof.dec3(utf8_proof.lead3(t), _, b3) == utf8_proof.cp3(z, y, t) : U32}
  %Equal.sym(U32, b3, utf8_proof.second_byte(z), ez) : {utf8_proof.dec3(utf8_proof.lead3(t), utf8_proof.second_byte(y), _) == utf8_proof.cp3(z, y, t) : U32}
  utf8_proof.dec3_fields(z, y, t)

def utf8_proof.accepted3(m: Maybe<&1, U32 & U32 & U32>) -> Bool:
  match m:
    case None{}: False{}
    case Some{(x0, x1, x2)}: UTF8.has_three_byte_shape(x0, x1, x2)

def utf8_proof.dec_of3(m: Maybe<&1, U32 & U32 & U32>) -> U32:
  match m:
    case None{}: 0
    case Some{(x0, x1, x2)}: utf8_proof.dec3(x0, x1, x2)

def utf8_proof.Produced3(+cp: U32, +b1: U32, +b2: U32, +b3: U32) -> Type:
  {UTF8.has_three_byte_shape(b1, b2, b3) == True{} : Bool} & {utf8_proof.dec3(b1, b2, b3) == cp : U32}

def utf8_proof.produced3.at(+z: Word(6n), +y: Word(6n), +t: Word(4n), +cp: U32, +b1: U32, +b2: U32, +b3: U32, +e: {cp == utf8_proof.cp3(z, y, t) : U32},
  +produced: {Laws.three_byte_shape(cp) == Some{(b1, b2, b3)} : Maybe<&1, U32 & U32 & U32>}) -> utf8_proof.Produced3(cp, b1, b2, b3):
  +same = Equal.trans(Maybe<&1, U32 & U32 & U32>, Some{(utf8_proof.lead3(t), utf8_proof.second_byte(y), utf8_proof.second_byte(z))}, Laws.three_byte_shape(utf8_proof.cp3(z, y, t)), Some{(b1, b2, b3)},
    Equal.sym(Maybe<&1, U32 & U32 & U32>, Laws.three_byte_shape(utf8_proof.cp3(z, y, t)), Some{(utf8_proof.lead3(t), utf8_proof.second_byte(y), utf8_proof.second_byte(z))}, utf8_proof.table3(z, y, t)),
    Equal.trans(Maybe<&1, U32 & U32 & U32>, Laws.three_byte_shape(utf8_proof.cp3(z, y, t)), Laws.three_byte_shape(cp), Some{(b1, b2, b3)},
      Equal.cong(U32, Maybe<&1, U32 & U32 & U32>, v => Laws.three_byte_shape(v), utf8_proof.cp3(z, y, t), cp, Equal.sym(U32, cp, utf8_proof.cp3(z, y, t), e)), produced))
  (Equal.trans(Bool, utf8_proof.accepted3(Some{(b1, b2, b3)}), utf8_proof.accepted3(Some{(utf8_proof.lead3(t), utf8_proof.second_byte(y), utf8_proof.second_byte(z))}), True{},
     Equal.cong(Maybe<&1, U32 & U32 & U32>, Bool, m => utf8_proof.accepted3(m), Some{(b1, b2, b3)}, Some{(utf8_proof.lead3(t), utf8_proof.second_byte(y), utf8_proof.second_byte(z))}, Equal.sym(Maybe<&1, U32 & U32 & U32>, Some{(utf8_proof.lead3(t), utf8_proof.second_byte(y), utf8_proof.second_byte(z))}, Some{(b1, b2, b3)}, same)),
     utf8_proof.has3_fields(z, y, t)),
   Equal.trans(U32, utf8_proof.dec_of3(Some{(b1, b2, b3)}), utf8_proof.dec_of3(Some{(utf8_proof.lead3(t), utf8_proof.second_byte(y), utf8_proof.second_byte(z))}), cp,
     Equal.cong(Maybe<&1, U32 & U32 & U32>, U32, m => utf8_proof.dec_of3(m), Some{(b1, b2, b3)}, Some{(utf8_proof.lead3(t), utf8_proof.second_byte(y), utf8_proof.second_byte(z))}, Equal.sym(Maybe<&1, U32 & U32 & U32>, Some{(utf8_proof.lead3(t), utf8_proof.second_byte(y), utf8_proof.second_byte(z))}, Some{(b1, b2, b3)}, same)),
     Equal.trans(U32, utf8_proof.dec3(utf8_proof.lead3(t), utf8_proof.second_byte(y), utf8_proof.second_byte(z)), utf8_proof.cp3(z, y, t), cp, utf8_proof.dec3_fields(z, y, t), Equal.sym(U32, cp, utf8_proof.cp3(z, y, t), e))))

def utf8_proof.produced3.view(+cp: U32, +b1: U32, +b2: U32, +b3: U32,
  +produced: {Laws.three_byte_shape(cp) == Some{(b1, b2, b3)} : Maybe<&1, U32 & U32 & U32>}, v: utf8_proof.View3(cp)) -> utf8_proof.Produced3(cp, b1, b2, b3):
  (+z, r0) = v
  (+y, r1) = r0
  (+t, e) = r1
  utf8_proof.produced3.at(z, y, t, cp, b1, b2, b3, e, produced)

def utf8_proof.produced3(+cp: U32, +b1: U32, +b2: U32, +b3: U32,
  +produced: {Laws.three_byte_shape(cp) == Some{(b1, b2, b3)} : Maybe<&1, U32 & U32 & U32>}) -> utf8_proof.Produced3(cp, b1, b2, b3):
  +accepted = Equal.trans(Bool, UTF8.can_encode_as_three_bytes(cp), Maybe.is_some(&1, U32 & U32 & U32, Laws.three_byte_shape(cp)), True{},
    utf8_proof.impl.can_encode_as_three_bytes(cp),
    Equal.cong(Maybe<&1, U32 & U32 & U32>, Bool, m => Maybe.is_some(&1, U32 & U32 & U32, m), Laws.three_byte_shape(cp), Some{(b1, b2, b3)}, produced))
  utf8_proof.produced3.view(cp, b1, b2, b3, produced, utf8_proof.view3(cp, accepted))

def utf8_proof.dec_produces3.eqs(+z: Word(6n), +y: Word(6n), +t: Word(4n), +b1: U32, +b2: U32, +b3: U32, +et: {b1 == utf8_proof.lead3(t) : U32}, +ey: {b2 == utf8_proof.second_byte(y) : U32}, +ez: {b3 == utf8_proof.second_byte(z) : U32}) ->
  {Laws.three_byte_shape(utf8_proof.dec3(b1, b2, b3)) == Some{(b1, b2, b3)} : Maybe<&1, U32 & U32 & U32>}:
  Equal.trans(Maybe<&1, U32 & U32 & U32>, Laws.three_byte_shape(utf8_proof.dec3(b1, b2, b3)), Laws.three_byte_shape(utf8_proof.cp3(z, y, t)), Some{(b1, b2, b3)},
    Equal.cong(U32, Maybe<&1, U32 & U32 & U32>, v => Laws.three_byte_shape(v), utf8_proof.dec3(b1, b2, b3), utf8_proof.cp3(z, y, t), utf8_proof.dec3_at(z, y, t, b1, b2, b3, et, ey, ez)),
    utf8_proof.produced3_at(z, y, t, b1, b2, b3, et, ey, ez))

def utf8_proof.dec_produces3(+b1: U32, +b2: U32, +b3: U32, f: utf8_proof.Fields3(b1, b2, b3)) ->
  {Laws.three_byte_shape(utf8_proof.dec3(b1, b2, b3)) == Some{(b1, b2, b3)} : Maybe<&1, U32 & U32 & U32>}:
  (+z, f0) = f
  (+y, f1) = f0
  (+t, f2) = f1
  (et, g0) = f2
  (ey, g1) = g0
  utf8_proof.dec_produces3.eqs(z, y, t, b1, b2, b3, et, ey, g1)


def utf8_proof.value3(+cp: U32) -> Bool:
  Bool.and(Bool.not(UTF8.can_encode_as_two_bytes(cp)), UTF8.is_scalar(cp))

def utf8_proof.valid3_if(+b1: U32, +b2: U32, +b3: U32, shape: Bool,
  -checked: {UTF8.has_three_byte_shape(b1, b2, b3) == shape : Bool}, is_true: {shape == True{} : Bool}) ->
  {UTF8.valid_three_bytes.if(b1, b2, b3, shape, checked) == utf8_proof.value3(utf8_proof.dec3(b1, b2, b3)) : Bool}:
  match shape:
    case False{}:
      Empty.absurd({False{} == utf8_proof.value3(utf8_proof.dec3(b1, b2, b3)) : Bool}, UTF8.false_true(is_true))
    case True{}: {==}

def utf8_proof.valid3_value(+b1: U32, +b2: U32, +b3: U32, +accepted: {UTF8.has_three_byte_shape(b1, b2, b3) == True{} : Bool}) ->
  {UTF8.valid_three_bytes(b1, b2, b3) == utf8_proof.value3(utf8_proof.dec3(b1, b2, b3)) : Bool}:
  utf8_proof.valid3_if(b1, b2, b3, UTF8.has_three_byte_shape(b1, b2, b3), {==}, accepted)

def utf8_proof.valid3_fields(+z: Word(6n), +y: Word(6n), +t: Word(4n)) ->
  {UTF8.valid_three_bytes(utf8_proof.lead3(t), utf8_proof.second_byte(y), utf8_proof.second_byte(z)) == utf8_proof.value3(utf8_proof.cp3(z, y, t)) : Bool}:
  %utf8_proof.dec3_fields(z, y, t) : {UTF8.valid_three_bytes(utf8_proof.lead3(t), utf8_proof.second_byte(y), utf8_proof.second_byte(z)) == utf8_proof.value3(_) : Bool}
  utf8_proof.valid3_value(utf8_proof.lead3(t), utf8_proof.second_byte(y), utf8_proof.second_byte(z), utf8_proof.has3_fields(z, y, t))


# Four-byte sequences
# ------------------

def utf8_proof.cp4(+z: Word(6n), +y: Word(6n), +x: Word(6n), +t: Word(3n)) -> U32:
  U32{word_join(6n, z, 26n, word_join(6n, y, 20n, word_join(6n, x, 14n, word_join(3n, t, 11n, Word.zero(11n)))))}

def utf8_proof.lead4(t: Word(3n)) -> U32:
  U32{word_join(3n, t, 29n, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, Word.zero(24n)}}}}})}

# A byte that passes `UTF8.is_four_byte_lead` is
# `utf8_proof.lead4` of its low 3 bits.
def utf8_proof.lead4_payload.Payload(+byte: U32) -> Type:
  Exists(Word(3n), payload => {byte == utf8_proof.lead4(payload) : U32})

# Split on the bits from the top: the first bit that differs from the
# pattern makes the test False, contradicting `valid`.
def utf8_proof.lead4_payload.bits(+b31: Bool, +b30: Bool, +b29: Bool, +b28: Bool, +b27: Bool, +b26: Bool, +b25: Bool, +b24: Bool, +b23: Bool, +b22: Bool, +b21: Bool, +b20: Bool, +b19: Bool, +b18: Bool, +b17: Bool, +b16: Bool, +b15: Bool, +b14: Bool, +b13: Bool, +b12: Bool, +b11: Bool, +b10: Bool, +b9: Bool, +b8: Bool, +b7: Bool, +b6: Bool, +b5: Bool, +b4: Bool, +b3: Bool, +b2: Bool, +b1: Bool, +b0: Bool,
  valid: {UTF8.is_four_byte_lead(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))) == True{} : Bool}) ->
  utf8_proof.lead4_payload.Payload(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))):
  match b31 b30 b29 b28 b27 b26 b25 b24 b23 b22 b21 b20 b19 b18 b17 b16 b15 b14 b13 b12 b11 b10 b9 b8 b7 b6 b5 b4 b3:
    case True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(utf8_proof.lead4_payload.Payload(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))), UTF8.false_true(valid))
    case False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(utf8_proof.lead4_payload.Payload(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))), UTF8.false_true(valid))
    case False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(utf8_proof.lead4_payload.Payload(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))), UTF8.false_true(valid))
    case False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(utf8_proof.lead4_payload.Payload(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))), UTF8.false_true(valid))
    case False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(utf8_proof.lead4_payload.Payload(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))), UTF8.false_true(valid))
    case False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(utf8_proof.lead4_payload.Payload(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))), UTF8.false_true(valid))
    case False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(utf8_proof.lead4_payload.Payload(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))), UTF8.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(utf8_proof.lead4_payload.Payload(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))), UTF8.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(utf8_proof.lead4_payload.Payload(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))), UTF8.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(utf8_proof.lead4_payload.Payload(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))), UTF8.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(utf8_proof.lead4_payload.Payload(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))), UTF8.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(utf8_proof.lead4_payload.Payload(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))), UTF8.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(utf8_proof.lead4_payload.Payload(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))), UTF8.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(utf8_proof.lead4_payload.Payload(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))), UTF8.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(utf8_proof.lead4_payload.Payload(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))), UTF8.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(utf8_proof.lead4_payload.Payload(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))), UTF8.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(utf8_proof.lead4_payload.Payload(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))), UTF8.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(utf8_proof.lead4_payload.Payload(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))), UTF8.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(utf8_proof.lead4_payload.Payload(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))), UTF8.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _:
      Empty.absurd(utf8_proof.lead4_payload.Payload(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))), UTF8.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _:
      Empty.absurd(utf8_proof.lead4_payload.Payload(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))), UTF8.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _:
      Empty.absurd(utf8_proof.lead4_payload.Payload(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))), UTF8.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _:
      Empty.absurd(utf8_proof.lead4_payload.Payload(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))), UTF8.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _:
      Empty.absurd(utf8_proof.lead4_payload.Payload(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))), UTF8.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} _ _ _ _:
      Empty.absurd(utf8_proof.lead4_payload.Payload(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))), UTF8.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} False{} _ _ _:
      Empty.absurd(utf8_proof.lead4_payload.Payload(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))), UTF8.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} True{} False{} _ _:
      Empty.absurd(utf8_proof.lead4_payload.Payload(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))), UTF8.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} True{} True{} False{} _:
      Empty.absurd(utf8_proof.lead4_payload.Payload(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))), UTF8.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} True{} True{} True{} True{}:
      Empty.absurd(utf8_proof.lead4_payload.Payload(Char.to_u32(char_from_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0))), UTF8.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} True{} True{} True{} False{}:
      (WCon{b0, WCon{b1, WCon{b2, WNil{}}}}, {==})

def utf8_proof.lead4_payload(+byte: U32,
  +valid: {UTF8.is_four_byte_lead(byte) == True{} : Bool}) ->
  Exists(Word(3n), payload => {byte == utf8_proof.lead4(payload) : U32}):
  match byte:
    case U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      utf8_proof.lead4_payload.bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0, valid)

def utf8_proof.dec4(+b1: U32, +b2: U32, +b3: U32, +b4: U32) -> U32:
  UTF8.append_continuation(UTF8.append_continuation(UTF8.append_continuation(U32.and(b1, 7), b2), b3), b4)

def utf8_proof.mask_lead4(+t: Word(3n)) ->
  {U32.and(utf8_proof.lead4(t), 7) == U32{word_join(3n, t, 29n, Word.zero(29n))} : U32}:
  Equal.cong(Word(32n), U32, x => U32{x},
    Word.and(32n, word_join(3n, t, 29n, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, Word.zero(24n)}}}}}), word_join(3n, word_ones(3n), 29n, Word.zero(29n))),
    word_join(3n, t, 29n, Word.zero(29n)), word_mask_fields(3n, t, 29n, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, Word.zero(24n)}}}}}))

def utf8_proof.dec4_fields(+z: Word(6n), +y: Word(6n), +x: Word(6n), +t: Word(3n)) ->
  {utf8_proof.dec4(utf8_proof.lead4(t), utf8_proof.second_byte(x), utf8_proof.second_byte(y), utf8_proof.second_byte(z)) == utf8_proof.cp4(z, y, x, t) : U32}:
  match z y x t:
    case WCon{z0, WCon{z1, WCon{z2, WCon{z3, WCon{z4, WCon{z5, WNil{}}}}}}} WCon{y0, WCon{y1, WCon{y2, WCon{y3, WCon{y4, WCon{y5, WNil{}}}}}}} WCon{x0, WCon{x1, WCon{x2, WCon{x3, WCon{x4, WCon{x5, WNil{}}}}}}} WCon{t0, WCon{t1, WCon{t2, WNil{}}}}:
      %Equal.sym(U32, U32.and(utf8_proof.lead4(t), 7), U32{word_join(3n, t, 29n, Word.zero(29n))}, utf8_proof.mask_lead4(t)) :
        {UTF8.append_continuation(UTF8.append_continuation(UTF8.append_continuation(_, utf8_proof.second_byte(x)), utf8_proof.second_byte(y)), utf8_proof.second_byte(z)) == utf8_proof.cp4(z, y, x, t) : U32}
      %Equal.sym(U32, UTF8.append_continuation(U32{word_join(3n, t, 29n, Word.zero(29n))}, utf8_proof.second_byte(x)), U32{word_join(6n, x, 26n, word_join(3n, t, 23n, Word.zero(23n)))},
          utf8_proof.append_eq(U32{word_join(3n, t, 29n, Word.zero(29n))}, x, word_join(3n, t, 23n, Word.zero(23n)), {==})) :
        {UTF8.append_continuation(UTF8.append_continuation(_, utf8_proof.second_byte(y)), utf8_proof.second_byte(z)) == utf8_proof.cp4(z, y, x, t) : U32}
      %Equal.sym(U32, UTF8.append_continuation(U32{word_join(6n, x, 26n, word_join(3n, t, 23n, Word.zero(23n)))}, utf8_proof.second_byte(y)), U32{word_join(6n, y, 26n, word_join(6n, x, 20n, word_join(3n, t, 17n, Word.zero(17n))))},
          utf8_proof.append_eq(U32{word_join(6n, x, 26n, word_join(3n, t, 23n, Word.zero(23n)))}, y, word_join(6n, x, 20n, word_join(3n, t, 17n, Word.zero(17n))), {==})) :
        {UTF8.append_continuation(_, utf8_proof.second_byte(z)) == utf8_proof.cp4(z, y, x, t) : U32}
      utf8_proof.append_eq(U32{word_join(6n, y, 26n, word_join(6n, x, 20n, word_join(3n, t, 17n, Word.zero(17n))))}, z, word_join(6n, y, 20n, word_join(6n, x, 14n, word_join(3n, t, 11n, Word.zero(11n)))), {==})

def utf8_proof.table4(+z: Word(6n), +y: Word(6n), +x: Word(6n), +t: Word(3n)) ->
  {Laws.four_byte_shape(utf8_proof.cp4(z, y, x, t)) == Some{(utf8_proof.lead4(t), utf8_proof.second_byte(x), utf8_proof.second_byte(y), utf8_proof.second_byte(z))} : Maybe<&1, U32 & U32 & U32 & U32>}:
  match z y x t:
    case WCon{z0, WCon{z1, WCon{z2, WCon{z3, WCon{z4, WCon{z5, WNil{}}}}}}} WCon{y0, WCon{y1, WCon{y2, WCon{y3, WCon{y4, WCon{y5, WNil{}}}}}}} WCon{x0, WCon{x1, WCon{x2, WCon{x3, WCon{x4, WCon{x5, WNil{}}}}}}} WCon{t0, WCon{t1, WCon{t2, WNil{}}}}: {==}

def utf8_proof.View4(+cp: U32) -> Type:
  Exists(Word(6n), z => Exists(Word(6n), y => Exists(Word(6n), x => Exists(Word(3n), t => {cp == utf8_proof.cp4(z, y, x, t) : U32}))))

def utf8_proof.view4_bits(+b31: Bool, +b30: Bool, +b29: Bool, +b28: Bool, +b27: Bool, +b26: Bool, +b25: Bool, +b24: Bool, +b23: Bool, +b22: Bool, +b21: Bool, +b20: Bool, +b19: Bool, +b18: Bool, +b17: Bool, +b16: Bool, +b15: Bool, +b14: Bool, +b13: Bool, +b12: Bool, +b11: Bool, +b10: Bool, +b9: Bool, +b8: Bool, +b7: Bool, +b6: Bool, +b5: Bool, +b4: Bool, +b3: Bool, +b2: Bool, +b1: Bool, +b0: Bool,
  valid: {UTF8.can_encode_as_four_bytes(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}) == True{} : Bool}) -> utf8_proof.View4(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}):
  match b31 b30 b29 b28 b27 b26 b25 b24 b23 b22 b21:
    case True{} _ _ _ _ _ _ _ _ _ _:
      Empty.absurd(utf8_proof.View4(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}), UTF8.false_true(valid))
    case False{} True{} _ _ _ _ _ _ _ _ _:
      Empty.absurd(utf8_proof.View4(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}), UTF8.false_true(valid))
    case False{} False{} True{} _ _ _ _ _ _ _ _:
      Empty.absurd(utf8_proof.View4(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}), UTF8.false_true(valid))
    case False{} False{} False{} True{} _ _ _ _ _ _ _:
      Empty.absurd(utf8_proof.View4(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}), UTF8.false_true(valid))
    case False{} False{} False{} False{} True{} _ _ _ _ _ _:
      Empty.absurd(utf8_proof.View4(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}), UTF8.false_true(valid))
    case False{} False{} False{} False{} False{} True{} _ _ _ _ _:
      Empty.absurd(utf8_proof.View4(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}), UTF8.false_true(valid))
    case False{} False{} False{} False{} False{} False{} True{} _ _ _ _:
      Empty.absurd(utf8_proof.View4(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}), UTF8.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} True{} _ _ _:
      Empty.absurd(utf8_proof.View4(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}), UTF8.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _:
      Empty.absurd(utf8_proof.View4(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}), UTF8.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _:
      Empty.absurd(utf8_proof.View4(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}), UTF8.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{}:
      Empty.absurd(utf8_proof.View4(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}), UTF8.false_true(valid))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{}:
      (WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WNil{}}}}}}}, (WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WNil{}}}}}}}, (WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WNil{}}}}}}}, (WCon{b18, WCon{b19, WCon{b20, WNil{}}}}, {==}))))

def utf8_proof.view4(+cp: U32, valid: {UTF8.can_encode_as_four_bytes(cp) == True{} : Bool}) -> utf8_proof.View4(cp):
  match cp:
    case U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      utf8_proof.view4_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0, valid)

def utf8_proof.can4_bits(+b31: Bool, +b30: Bool, +b29: Bool, +b28: Bool, +b27: Bool, +b26: Bool, +b25: Bool, +b24: Bool, +b23: Bool, +b22: Bool, +b21: Bool, +b20: Bool, +b19: Bool, +b18: Bool, +b17: Bool, +b16: Bool, +b15: Bool, +b14: Bool, +b13: Bool, +b12: Bool, +b11: Bool, +b10: Bool, +b9: Bool, +b8: Bool, +b7: Bool, +b6: Bool, +b5: Bool, +b4: Bool, +b3: Bool, +b2: Bool, +b1: Bool, +b0: Bool) ->
  {UTF8.can_encode_as_four_bytes(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}) == Maybe.is_some(&1, U32 & U32 & U32 & U32, Laws.four_byte_shape(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}})) : Bool}:
  match b31 b30 b29 b28 b27 b26 b25 b24 b23 b22 b21:
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
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{}:
      utf8_proof.word_le_ones(21n, WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WNil{}}}}}}}}}}}}}}}}}}}}}}, 11n, Word.zero(11n), Word.zero(11n))

def utf8_proof.impl.can_encode_as_four_bytes(+cp: U32) ->
  {UTF8.can_encode_as_four_bytes(cp) == Maybe.is_some(&1, U32 & U32 & U32 & U32, Laws.four_byte_shape(cp)) : Bool}:
  match cp:
    case U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      utf8_proof.can4_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0)

def utf8_proof.lead4_mask(+t: Word(3n)) ->
  {UTF8.is_four_byte_lead(utf8_proof.lead4(t)) == True{} : Bool}:
  match t:
    case WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}: {==}
    case WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}: {==}
    case WCon{False{}, WCon{True{}, WCon{False{}, WNil{}}}}: {==}
    case WCon{False{}, WCon{True{}, WCon{True{}, WNil{}}}}: {==}
    case WCon{True{}, WCon{False{}, WCon{False{}, WNil{}}}}: {==}
    case WCon{True{}, WCon{False{}, WCon{True{}, WNil{}}}}: {==}
    case WCon{True{}, WCon{True{}, WCon{False{}, WNil{}}}}: {==}
    case WCon{True{}, WCon{True{}, WCon{True{}, WNil{}}}}: {==}

def utf8_proof.has4_fields(+z: Word(6n), +y: Word(6n), +x: Word(6n), +t: Word(3n)) ->
  {UTF8.has_four_byte_shape(utf8_proof.lead4(t), utf8_proof.second_byte(x), utf8_proof.second_byte(y), utf8_proof.second_byte(z)) == True{} : Bool}:
  %Equal.sym(Bool, UTF8.is_four_byte_lead(utf8_proof.lead4(t)), True{}, utf8_proof.lead4_mask(t)) :
    {Bool.and(Bool.and(Bool.and(_, UTF8.is_continuation_byte(utf8_proof.second_byte(x))), UTF8.is_continuation_byte(utf8_proof.second_byte(y))), UTF8.is_continuation_byte(utf8_proof.second_byte(z))) == True{} : Bool}
  %Equal.sym(Bool, UTF8.is_continuation_byte(utf8_proof.second_byte(x)), True{}, utf8_proof.cont_mask(x)) :
    {Bool.and(Bool.and(Bool.and(True{}, _), UTF8.is_continuation_byte(utf8_proof.second_byte(y))), UTF8.is_continuation_byte(utf8_proof.second_byte(z))) == True{} : Bool}
  %Equal.sym(Bool, UTF8.is_continuation_byte(utf8_proof.second_byte(y)), True{}, utf8_proof.cont_mask(y)) :
    {Bool.and(Bool.and(Bool.and(True{}, True{}), _), UTF8.is_continuation_byte(utf8_proof.second_byte(z))) == True{} : Bool}
  %Equal.sym(Bool, UTF8.is_continuation_byte(utf8_proof.second_byte(z)), True{}, utf8_proof.cont_mask(z)) :
    {Bool.and(Bool.and(Bool.and(True{}, True{}), True{}), _) == True{} : Bool}
  {==}

def utf8_proof.Fields4(+b1: U32, +b2: U32, +b3: U32, +b4: U32) -> Type:
  Exists(Word(6n), z => Exists(Word(6n), y => Exists(Word(6n), x => Exists(Word(3n), t => {b1 == utf8_proof.lead4(t) : U32} & {b2 == utf8_proof.second_byte(x) : U32} & {b3 == utf8_proof.second_byte(y) : U32} & {b4 == utf8_proof.second_byte(z) : U32}))))

def utf8_proof.fields4.of(+b1: U32, +b2: U32, +b3: U32, +b4: U32, pt: Exists(Word(3n), t => {b1 == utf8_proof.lead4(t) : U32}), px: Exists(Word(6n), x => {b2 == utf8_proof.second_byte(x) : U32}), py: Exists(Word(6n), y => {b3 == utf8_proof.second_byte(y) : U32}), pz: Exists(Word(6n), z => {b4 == utf8_proof.second_byte(z) : U32})) -> utf8_proof.Fields4(b1, b2, b3, b4):
  (+t, et) = pt
  (+x, ex) = px
  (+y, ey) = py
  (+z, ez) = pz
  (z, (y, (x, (t, (et, (ex, (ey, ez)))))))

def utf8_proof.fields4(+b1: U32, +b2: U32, +b3: U32, +b4: U32, +accepted: {UTF8.has_four_byte_shape(b1, b2, b3, b4) == True{} : Bool}) -> utf8_proof.Fields4(b1, b2, b3, b4):
  utf8_proof.fields4.of(b1, b2, b3, b4, utf8_proof.lead4_payload(b1, bool_and_left_true(UTF8.is_four_byte_lead(b1), UTF8.is_continuation_byte(b2), bool_and_left_true(Bool.and(UTF8.is_four_byte_lead(b1), UTF8.is_continuation_byte(b2)), UTF8.is_continuation_byte(b3), bool_and_left_true(Bool.and(Bool.and(UTF8.is_four_byte_lead(b1), UTF8.is_continuation_byte(b2)), UTF8.is_continuation_byte(b3)), UTF8.is_continuation_byte(b4), accepted)))), utf8_proof.second_payload(b2, bool_and_right_true(UTF8.is_four_byte_lead(b1), UTF8.is_continuation_byte(b2), bool_and_left_true(Bool.and(UTF8.is_four_byte_lead(b1), UTF8.is_continuation_byte(b2)), UTF8.is_continuation_byte(b3), bool_and_left_true(Bool.and(Bool.and(UTF8.is_four_byte_lead(b1), UTF8.is_continuation_byte(b2)), UTF8.is_continuation_byte(b3)), UTF8.is_continuation_byte(b4), accepted)))), utf8_proof.second_payload(b3, bool_and_right_true(Bool.and(UTF8.is_four_byte_lead(b1), UTF8.is_continuation_byte(b2)), UTF8.is_continuation_byte(b3), bool_and_left_true(Bool.and(Bool.and(UTF8.is_four_byte_lead(b1), UTF8.is_continuation_byte(b2)), UTF8.is_continuation_byte(b3)), UTF8.is_continuation_byte(b4), accepted))), utf8_proof.second_payload(b4, bool_and_right_true(Bool.and(Bool.and(UTF8.is_four_byte_lead(b1), UTF8.is_continuation_byte(b2)), UTF8.is_continuation_byte(b3)), UTF8.is_continuation_byte(b4), accepted)))

def utf8_proof.produced4_at(+z: Word(6n), +y: Word(6n), +x: Word(6n), +t: Word(3n), +b1: U32, +b2: U32, +b3: U32, +b4: U32, et: {b1 == utf8_proof.lead4(t) : U32}, ex: {b2 == utf8_proof.second_byte(x) : U32}, ey: {b3 == utf8_proof.second_byte(y) : U32}, ez: {b4 == utf8_proof.second_byte(z) : U32}) ->
  {Laws.four_byte_shape(utf8_proof.cp4(z, y, x, t)) == Some{(b1, b2, b3, b4)} : Maybe<&1, U32 & U32 & U32 & U32>}:
  %Equal.sym(U32, b1, utf8_proof.lead4(t), et) : {Laws.four_byte_shape(utf8_proof.cp4(z, y, x, t)) == Some{(_, b2, b3, b4)} : Maybe<&1, U32 & U32 & U32 & U32>}
  %Equal.sym(U32, b2, utf8_proof.second_byte(x), ex) : {Laws.four_byte_shape(utf8_proof.cp4(z, y, x, t)) == Some{(utf8_proof.lead4(t), _, b3, b4)} : Maybe<&1, U32 & U32 & U32 & U32>}
  %Equal.sym(U32, b3, utf8_proof.second_byte(y), ey) : {Laws.four_byte_shape(utf8_proof.cp4(z, y, x, t)) == Some{(utf8_proof.lead4(t), utf8_proof.second_byte(x), _, b4)} : Maybe<&1, U32 & U32 & U32 & U32>}
  %Equal.sym(U32, b4, utf8_proof.second_byte(z), ez) : {Laws.four_byte_shape(utf8_proof.cp4(z, y, x, t)) == Some{(utf8_proof.lead4(t), utf8_proof.second_byte(x), utf8_proof.second_byte(y), _)} : Maybe<&1, U32 & U32 & U32 & U32>}
  utf8_proof.table4(z, y, x, t)

def utf8_proof.dec4_at(+z: Word(6n), +y: Word(6n), +x: Word(6n), +t: Word(3n), +b1: U32, +b2: U32, +b3: U32, +b4: U32, et: {b1 == utf8_proof.lead4(t) : U32}, ex: {b2 == utf8_proof.second_byte(x) : U32}, ey: {b3 == utf8_proof.second_byte(y) : U32}, ez: {b4 == utf8_proof.second_byte(z) : U32}) ->
  {utf8_proof.dec4(b1, b2, b3, b4) == utf8_proof.cp4(z, y, x, t) : U32}:
  %Equal.sym(U32, b1, utf8_proof.lead4(t), et) : {utf8_proof.dec4(_, b2, b3, b4) == utf8_proof.cp4(z, y, x, t) : U32}
  %Equal.sym(U32, b2, utf8_proof.second_byte(x), ex) : {utf8_proof.dec4(utf8_proof.lead4(t), _, b3, b4) == utf8_proof.cp4(z, y, x, t) : U32}
  %Equal.sym(U32, b3, utf8_proof.second_byte(y), ey) : {utf8_proof.dec4(utf8_proof.lead4(t), utf8_proof.second_byte(x), _, b4) == utf8_proof.cp4(z, y, x, t) : U32}
  %Equal.sym(U32, b4, utf8_proof.second_byte(z), ez) : {utf8_proof.dec4(utf8_proof.lead4(t), utf8_proof.second_byte(x), utf8_proof.second_byte(y), _) == utf8_proof.cp4(z, y, x, t) : U32}
  utf8_proof.dec4_fields(z, y, x, t)

def utf8_proof.accepted4(m: Maybe<&1, U32 & U32 & U32 & U32>) -> Bool:
  match m:
    case None{}: False{}
    case Some{(x0, x1, x2, x3)}: UTF8.has_four_byte_shape(x0, x1, x2, x3)

def utf8_proof.dec_of4(m: Maybe<&1, U32 & U32 & U32 & U32>) -> U32:
  match m:
    case None{}: 0
    case Some{(x0, x1, x2, x3)}: utf8_proof.dec4(x0, x1, x2, x3)

def utf8_proof.Produced4(+cp: U32, +b1: U32, +b2: U32, +b3: U32, +b4: U32) -> Type:
  {UTF8.has_four_byte_shape(b1, b2, b3, b4) == True{} : Bool} & {utf8_proof.dec4(b1, b2, b3, b4) == cp : U32}

def utf8_proof.produced4.at(+z: Word(6n), +y: Word(6n), +x: Word(6n), +t: Word(3n), +cp: U32, +b1: U32, +b2: U32, +b3: U32, +b4: U32, +e: {cp == utf8_proof.cp4(z, y, x, t) : U32},
  +produced: {Laws.four_byte_shape(cp) == Some{(b1, b2, b3, b4)} : Maybe<&1, U32 & U32 & U32 & U32>}) -> utf8_proof.Produced4(cp, b1, b2, b3, b4):
  +same = Equal.trans(Maybe<&1, U32 & U32 & U32 & U32>, Some{(utf8_proof.lead4(t), utf8_proof.second_byte(x), utf8_proof.second_byte(y), utf8_proof.second_byte(z))}, Laws.four_byte_shape(utf8_proof.cp4(z, y, x, t)), Some{(b1, b2, b3, b4)},
    Equal.sym(Maybe<&1, U32 & U32 & U32 & U32>, Laws.four_byte_shape(utf8_proof.cp4(z, y, x, t)), Some{(utf8_proof.lead4(t), utf8_proof.second_byte(x), utf8_proof.second_byte(y), utf8_proof.second_byte(z))}, utf8_proof.table4(z, y, x, t)),
    Equal.trans(Maybe<&1, U32 & U32 & U32 & U32>, Laws.four_byte_shape(utf8_proof.cp4(z, y, x, t)), Laws.four_byte_shape(cp), Some{(b1, b2, b3, b4)},
      Equal.cong(U32, Maybe<&1, U32 & U32 & U32 & U32>, v => Laws.four_byte_shape(v), utf8_proof.cp4(z, y, x, t), cp, Equal.sym(U32, cp, utf8_proof.cp4(z, y, x, t), e)), produced))
  (Equal.trans(Bool, utf8_proof.accepted4(Some{(b1, b2, b3, b4)}), utf8_proof.accepted4(Some{(utf8_proof.lead4(t), utf8_proof.second_byte(x), utf8_proof.second_byte(y), utf8_proof.second_byte(z))}), True{},
     Equal.cong(Maybe<&1, U32 & U32 & U32 & U32>, Bool, m => utf8_proof.accepted4(m), Some{(b1, b2, b3, b4)}, Some{(utf8_proof.lead4(t), utf8_proof.second_byte(x), utf8_proof.second_byte(y), utf8_proof.second_byte(z))}, Equal.sym(Maybe<&1, U32 & U32 & U32 & U32>, Some{(utf8_proof.lead4(t), utf8_proof.second_byte(x), utf8_proof.second_byte(y), utf8_proof.second_byte(z))}, Some{(b1, b2, b3, b4)}, same)),
     utf8_proof.has4_fields(z, y, x, t)),
   Equal.trans(U32, utf8_proof.dec_of4(Some{(b1, b2, b3, b4)}), utf8_proof.dec_of4(Some{(utf8_proof.lead4(t), utf8_proof.second_byte(x), utf8_proof.second_byte(y), utf8_proof.second_byte(z))}), cp,
     Equal.cong(Maybe<&1, U32 & U32 & U32 & U32>, U32, m => utf8_proof.dec_of4(m), Some{(b1, b2, b3, b4)}, Some{(utf8_proof.lead4(t), utf8_proof.second_byte(x), utf8_proof.second_byte(y), utf8_proof.second_byte(z))}, Equal.sym(Maybe<&1, U32 & U32 & U32 & U32>, Some{(utf8_proof.lead4(t), utf8_proof.second_byte(x), utf8_proof.second_byte(y), utf8_proof.second_byte(z))}, Some{(b1, b2, b3, b4)}, same)),
     Equal.trans(U32, utf8_proof.dec4(utf8_proof.lead4(t), utf8_proof.second_byte(x), utf8_proof.second_byte(y), utf8_proof.second_byte(z)), utf8_proof.cp4(z, y, x, t), cp, utf8_proof.dec4_fields(z, y, x, t), Equal.sym(U32, cp, utf8_proof.cp4(z, y, x, t), e))))

def utf8_proof.produced4.view(+cp: U32, +b1: U32, +b2: U32, +b3: U32, +b4: U32,
  +produced: {Laws.four_byte_shape(cp) == Some{(b1, b2, b3, b4)} : Maybe<&1, U32 & U32 & U32 & U32>}, v: utf8_proof.View4(cp)) -> utf8_proof.Produced4(cp, b1, b2, b3, b4):
  (+z, r0) = v
  (+y, r1) = r0
  (+x, r2) = r1
  (+t, e) = r2
  utf8_proof.produced4.at(z, y, x, t, cp, b1, b2, b3, b4, e, produced)

def utf8_proof.produced4(+cp: U32, +b1: U32, +b2: U32, +b3: U32, +b4: U32,
  +produced: {Laws.four_byte_shape(cp) == Some{(b1, b2, b3, b4)} : Maybe<&1, U32 & U32 & U32 & U32>}) -> utf8_proof.Produced4(cp, b1, b2, b3, b4):
  +accepted = Equal.trans(Bool, UTF8.can_encode_as_four_bytes(cp), Maybe.is_some(&1, U32 & U32 & U32 & U32, Laws.four_byte_shape(cp)), True{},
    utf8_proof.impl.can_encode_as_four_bytes(cp),
    Equal.cong(Maybe<&1, U32 & U32 & U32 & U32>, Bool, m => Maybe.is_some(&1, U32 & U32 & U32 & U32, m), Laws.four_byte_shape(cp), Some{(b1, b2, b3, b4)}, produced))
  utf8_proof.produced4.view(cp, b1, b2, b3, b4, produced, utf8_proof.view4(cp, accepted))

def utf8_proof.dec_produces4.eqs(+z: Word(6n), +y: Word(6n), +x: Word(6n), +t: Word(3n), +b1: U32, +b2: U32, +b3: U32, +b4: U32, +et: {b1 == utf8_proof.lead4(t) : U32}, +ex: {b2 == utf8_proof.second_byte(x) : U32}, +ey: {b3 == utf8_proof.second_byte(y) : U32}, +ez: {b4 == utf8_proof.second_byte(z) : U32}) ->
  {Laws.four_byte_shape(utf8_proof.dec4(b1, b2, b3, b4)) == Some{(b1, b2, b3, b4)} : Maybe<&1, U32 & U32 & U32 & U32>}:
  Equal.trans(Maybe<&1, U32 & U32 & U32 & U32>, Laws.four_byte_shape(utf8_proof.dec4(b1, b2, b3, b4)), Laws.four_byte_shape(utf8_proof.cp4(z, y, x, t)), Some{(b1, b2, b3, b4)},
    Equal.cong(U32, Maybe<&1, U32 & U32 & U32 & U32>, v => Laws.four_byte_shape(v), utf8_proof.dec4(b1, b2, b3, b4), utf8_proof.cp4(z, y, x, t), utf8_proof.dec4_at(z, y, x, t, b1, b2, b3, b4, et, ex, ey, ez)),
    utf8_proof.produced4_at(z, y, x, t, b1, b2, b3, b4, et, ex, ey, ez))

def utf8_proof.dec_produces4(+b1: U32, +b2: U32, +b3: U32, +b4: U32, f: utf8_proof.Fields4(b1, b2, b3, b4)) ->
  {Laws.four_byte_shape(utf8_proof.dec4(b1, b2, b3, b4)) == Some{(b1, b2, b3, b4)} : Maybe<&1, U32 & U32 & U32 & U32>}:
  (+z, f0) = f
  (+y, f1) = f0
  (+x, f2) = f1
  (+t, f3) = f2
  (et, g0) = f3
  (ex, g1) = g0
  (ey, g2) = g1
  utf8_proof.dec_produces4.eqs(z, y, x, t, b1, b2, b3, b4, et, ex, ey, g2)


def utf8_proof.value4(+cp: U32) -> Bool:
  Bool.and(Bool.not(UTF8.can_encode_as_three_bytes(cp)), UTF8.is_scalar(cp))

def utf8_proof.valid4_if(+b1: U32, +b2: U32, +b3: U32, +b4: U32, shape: Bool,
  -checked: {UTF8.has_four_byte_shape(b1, b2, b3, b4) == shape : Bool}, is_true: {shape == True{} : Bool}) ->
  {UTF8.valid_four_bytes.if(b1, b2, b3, b4, shape, checked) == utf8_proof.value4(utf8_proof.dec4(b1, b2, b3, b4)) : Bool}:
  match shape:
    case False{}:
      Empty.absurd({False{} == utf8_proof.value4(utf8_proof.dec4(b1, b2, b3, b4)) : Bool}, UTF8.false_true(is_true))
    case True{}: {==}

def utf8_proof.valid4_value(+b1: U32, +b2: U32, +b3: U32, +b4: U32, +accepted: {UTF8.has_four_byte_shape(b1, b2, b3, b4) == True{} : Bool}) ->
  {UTF8.valid_four_bytes(b1, b2, b3, b4) == utf8_proof.value4(utf8_proof.dec4(b1, b2, b3, b4)) : Bool}:
  utf8_proof.valid4_if(b1, b2, b3, b4, UTF8.has_four_byte_shape(b1, b2, b3, b4), {==}, accepted)

def utf8_proof.valid4_fields(+z: Word(6n), +y: Word(6n), +x: Word(6n), +t: Word(3n)) ->
  {UTF8.valid_four_bytes(utf8_proof.lead4(t), utf8_proof.second_byte(x), utf8_proof.second_byte(y), utf8_proof.second_byte(z)) == utf8_proof.value4(utf8_proof.cp4(z, y, x, t)) : Bool}:
  %utf8_proof.dec4_fields(z, y, x, t) : {UTF8.valid_four_bytes(utf8_proof.lead4(t), utf8_proof.second_byte(x), utf8_proof.second_byte(y), utf8_proof.second_byte(z)) == utf8_proof.value4(_) : Bool}
  utf8_proof.valid4_value(utf8_proof.lead4(t), utf8_proof.second_byte(x), utf8_proof.second_byte(y), utf8_proof.second_byte(z), utf8_proof.has4_fields(z, y, x, t))


# What validity depends on
# -----------------------
#
# A three-byte sequence's validity depends only on the lead byte's
# payload and the top bit of the second byte's payload.  For four bytes
# it depends on the lead byte's payload and the second byte's top two
# payload bits.

def utf8_proof.H3(bit: Bool, t: Word(4n)) -> Word(21n):
  WCon{bit, word_join(4n, t, 16n, Word.zero(16n))}

def utf8_proof.model3(+bit: Bool, +t: Word(4n)) -> Bool:
  Bool.and(Bool.not(Cmp.is_le(Word.cmp(21n, utf8_proof.H3(bit, t), Word.zero(21n)))),
    Bool.not(Bool.and(Cmp.is_ge(Word.cmp(21n, utf8_proof.H3(bit, t), WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, Word.zero(16n)}}}}})), Cmp.is_le(Word.cmp(21n, utf8_proof.H3(bit, t), WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, Word.zero(16n)}}}}})))))

def utf8_proof.H4(x4: Bool, x5: Bool, t: Word(3n)) -> Word(16n):
  WCon{x4, WCon{x5, word_join(3n, t, 11n, Word.zero(11n))}}

def utf8_proof.model4(+x4: Bool, +x5: Bool, +t: Word(3n)) -> Bool:
  Bool.and(Bool.not(Cmp.is_le(Word.cmp(16n, utf8_proof.H4(x4, x5, t), Word.zero(16n)))),
    Cmp.is_le(Word.cmp(16n, utf8_proof.H4(x4, x5, t), WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, Word.zero(11n)}}}}})))

def utf8_proof.value3_model(+z: Word(6n), +y: Word(6n), +t: Word(4n)) ->
  {utf8_proof.value3(utf8_proof.cp3(z, y, t)) == utf8_proof.model3(utf8_proof.bit5(y), t) : Bool}:
  match z y t:
    case WCon{z0, WCon{z1, WCon{z2, WCon{z3, WCon{z4, WCon{z5, WNil{}}}}}}} WCon{y0, WCon{y1, WCon{y2, WCon{y3, WCon{y4, WCon{y5, WNil{}}}}}}} WCon{t0, WCon{t1, WCon{t2, WCon{t3, WNil{}}}}}:
      %Equal.sym(Bool, Cmp.is_le(Word.cmp(32n, word_join(11n, WCon{z0, WCon{z1, WCon{z2, WCon{z3, WCon{z4, WCon{z5, WCon{y0, WCon{y1, WCon{y2, WCon{y3, WCon{y4, WNil{}}}}}}}}}}}}, 21n, utf8_proof.H3(y5, t)), word_join(11n, word_ones(11n), 21n, Word.zero(21n)))), Cmp.is_le(Word.cmp(21n, utf8_proof.H3(y5, t), Word.zero(21n))), utf8_proof.word_le_ones(11n, WCon{z0, WCon{z1, WCon{z2, WCon{z3, WCon{z4, WCon{z5, WCon{y0, WCon{y1, WCon{y2, WCon{y3, WCon{y4, WNil{}}}}}}}}}}}}, 21n, utf8_proof.H3(y5, t), Word.zero(21n))) :
        {Bool.and(Bool.not(_), UTF8.is_scalar(utf8_proof.cp3(z, y, t))) == utf8_proof.model3(utf8_proof.bit5(y), t) : Bool}
      %Equal.sym(Bool, Cmp.is_ge(Word.cmp(32n, word_join(11n, WCon{z0, WCon{z1, WCon{z2, WCon{z3, WCon{z4, WCon{z5, WCon{y0, WCon{y1, WCon{y2, WCon{y3, WCon{y4, WNil{}}}}}}}}}}}}, 21n, utf8_proof.H3(y5, t)), word_join(11n, Word.zero(11n), 21n, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, Word.zero(16n)}}}}}))), Cmp.is_ge(Word.cmp(21n, utf8_proof.H3(y5, t), WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, Word.zero(16n)}}}}})), utf8_proof.word_ge_zeros(11n, WCon{z0, WCon{z1, WCon{z2, WCon{z3, WCon{z4, WCon{z5, WCon{y0, WCon{y1, WCon{y2, WCon{y3, WCon{y4, WNil{}}}}}}}}}}}}, 21n, utf8_proof.H3(y5, t), WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, Word.zero(16n)}}}}})) :
        {Bool.and(Bool.not(Cmp.is_le(Word.cmp(21n, utf8_proof.H3(y5, t), Word.zero(21n)))), Bool.and(U32.is_le(utf8_proof.cp3(z, y, t), 1114111), Bool.not(Bool.and(_, U32.is_le(utf8_proof.cp3(z, y, t), 57343))))) == utf8_proof.model3(utf8_proof.bit5(y), t) : Bool}
      %Equal.sym(Bool, Cmp.is_le(Word.cmp(32n, word_join(11n, WCon{z0, WCon{z1, WCon{z2, WCon{z3, WCon{z4, WCon{z5, WCon{y0, WCon{y1, WCon{y2, WCon{y3, WCon{y4, WNil{}}}}}}}}}}}}, 21n, utf8_proof.H3(y5, t)), word_join(11n, word_ones(11n), 21n, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, Word.zero(16n)}}}}}))), Cmp.is_le(Word.cmp(21n, utf8_proof.H3(y5, t), WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, Word.zero(16n)}}}}})), utf8_proof.word_le_ones(11n, WCon{z0, WCon{z1, WCon{z2, WCon{z3, WCon{z4, WCon{z5, WCon{y0, WCon{y1, WCon{y2, WCon{y3, WCon{y4, WNil{}}}}}}}}}}}}, 21n, utf8_proof.H3(y5, t), WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, Word.zero(16n)}}}}})) :
        {Bool.and(Bool.not(Cmp.is_le(Word.cmp(21n, utf8_proof.H3(y5, t), Word.zero(21n)))), Bool.and(U32.is_le(utf8_proof.cp3(z, y, t), 1114111), Bool.not(Bool.and(Cmp.is_ge(Word.cmp(21n, utf8_proof.H3(y5, t), WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, Word.zero(16n)}}}}})), _)))) == utf8_proof.model3(utf8_proof.bit5(y), t) : Bool}
      {==}

def utf8_proof.valid3_eq(+z: Word(6n), +y: Word(6n), +t: Word(4n)) ->
  {UTF8.valid_three_bytes(utf8_proof.lead3(t), utf8_proof.second_byte(y), utf8_proof.second_byte(z)) == utf8_proof.model3(utf8_proof.bit5(y), t) : Bool}:
  Equal.trans(Bool, UTF8.valid_three_bytes(utf8_proof.lead3(t), utf8_proof.second_byte(y), utf8_proof.second_byte(z)), utf8_proof.value3(utf8_proof.cp3(z, y, t)), utf8_proof.model3(utf8_proof.bit5(y), t),
    utf8_proof.valid3_fields(z, y, t), utf8_proof.value3_model(z, y, t))

def utf8_proof.value4_rows(+z0: Bool, +z1: Bool, +z2: Bool, +z3: Bool, +z4: Bool, +z5: Bool, +y0: Bool, +y1: Bool, +y2: Bool, +y3: Bool, +y4: Bool, +y5: Bool, +x0: Bool, +x1: Bool, +x2: Bool, +x3: Bool, +x4: Bool, +x5: Bool, +t0: Bool, +t1: Bool, +t2: Bool) ->
  {Bool.and(Bool.not(Cmp.is_le(Word.cmp(16n, utf8_proof.H4(x4, x5, WCon{t0, WCon{t1, WCon{t2, WNil{}}}}), Word.zero(16n)))), Bool.and(Cmp.is_le(Word.cmp(16n, utf8_proof.H4(x4, x5, WCon{t0, WCon{t1, WCon{t2, WNil{}}}}), WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, Word.zero(11n)}}}}})), Bool.not(Bool.and(U32.is_ge(utf8_proof.cp4(WCon{z0, WCon{z1, WCon{z2, WCon{z3, WCon{z4, WCon{z5, WNil{}}}}}}}, WCon{y0, WCon{y1, WCon{y2, WCon{y3, WCon{y4, WCon{y5, WNil{}}}}}}}, WCon{x0, WCon{x1, WCon{x2, WCon{x3, WCon{x4, WCon{x5, WNil{}}}}}}}, WCon{t0, WCon{t1, WCon{t2, WNil{}}}}), 55296), U32.is_le(utf8_proof.cp4(WCon{z0, WCon{z1, WCon{z2, WCon{z3, WCon{z4, WCon{z5, WNil{}}}}}}}, WCon{y0, WCon{y1, WCon{y2, WCon{y3, WCon{y4, WCon{y5, WNil{}}}}}}}, WCon{x0, WCon{x1, WCon{x2, WCon{x3, WCon{x4, WCon{x5, WNil{}}}}}}}, WCon{t0, WCon{t1, WCon{t2, WNil{}}}}), 57343))))) ==
    utf8_proof.model4(x4, x5, WCon{t0, WCon{t1, WCon{t2, WNil{}}}}) : Bool}:
  match x4 x5 t0 t1 t2:
    case False{} False{} False{} False{} False{}: {==}
    case False{} False{} False{} False{} True{}: {==}
    case False{} False{} False{} True{} False{}: {==}
    case False{} False{} False{} True{} True{}: {==}
    case False{} False{} True{} False{} False{}: {==}
    case False{} False{} True{} False{} True{}: {==}
    case False{} False{} True{} True{} False{}: {==}
    case False{} False{} True{} True{} True{}: {==}
    case False{} True{} False{} False{} False{}: {==}
    case False{} True{} False{} False{} True{}: {==}
    case False{} True{} False{} True{} False{}: {==}
    case False{} True{} False{} True{} True{}: {==}
    case False{} True{} True{} False{} False{}: {==}
    case False{} True{} True{} False{} True{}: {==}
    case False{} True{} True{} True{} False{}: {==}
    case False{} True{} True{} True{} True{}: {==}
    case True{} False{} False{} False{} False{}: {==}
    case True{} False{} False{} False{} True{}: {==}
    case True{} False{} False{} True{} False{}: {==}
    case True{} False{} False{} True{} True{}: {==}
    case True{} False{} True{} False{} False{}: {==}
    case True{} False{} True{} False{} True{}: {==}
    case True{} False{} True{} True{} False{}: {==}
    case True{} False{} True{} True{} True{}: {==}
    case True{} True{} False{} False{} False{}: {==}
    case True{} True{} False{} False{} True{}: {==}
    case True{} True{} False{} True{} False{}: {==}
    case True{} True{} False{} True{} True{}: {==}
    case True{} True{} True{} False{} False{}: {==}
    case True{} True{} True{} False{} True{}: {==}
    case True{} True{} True{} True{} False{}: {==}
    case True{} True{} True{} True{} True{}: {==}

def utf8_proof.value4_model(+z: Word(6n), +y: Word(6n), +x: Word(6n), +t: Word(3n)) ->
  {utf8_proof.value4(utf8_proof.cp4(z, y, x, t)) == utf8_proof.model4(utf8_proof.bit4(x), utf8_proof.bit5(x), t) : Bool}:
  match z y x t:
    case WCon{z0, WCon{z1, WCon{z2, WCon{z3, WCon{z4, WCon{z5, WNil{}}}}}}} WCon{y0, WCon{y1, WCon{y2, WCon{y3, WCon{y4, WCon{y5, WNil{}}}}}}} WCon{x0, WCon{x1, WCon{x2, WCon{x3, WCon{x4, WCon{x5, WNil{}}}}}}} WCon{t0, WCon{t1, WCon{t2, WNil{}}}}:
      %Equal.sym(Bool, Cmp.is_le(Word.cmp(32n, word_join(16n, WCon{z0, WCon{z1, WCon{z2, WCon{z3, WCon{z4, WCon{z5, WCon{y0, WCon{y1, WCon{y2, WCon{y3, WCon{y4, WCon{y5, WCon{x0, WCon{x1, WCon{x2, WCon{x3, WNil{}}}}}}}}}}}}}}}}}, 16n, utf8_proof.H4(x4, x5, WCon{t0, WCon{t1, WCon{t2, WNil{}}}})), word_join(16n, word_ones(16n), 16n, Word.zero(16n)))), Cmp.is_le(Word.cmp(16n, utf8_proof.H4(x4, x5, WCon{t0, WCon{t1, WCon{t2, WNil{}}}}), Word.zero(16n))), utf8_proof.word_le_ones(16n, WCon{z0, WCon{z1, WCon{z2, WCon{z3, WCon{z4, WCon{z5, WCon{y0, WCon{y1, WCon{y2, WCon{y3, WCon{y4, WCon{y5, WCon{x0, WCon{x1, WCon{x2, WCon{x3, WNil{}}}}}}}}}}}}}}}}}, 16n, utf8_proof.H4(x4, x5, WCon{t0, WCon{t1, WCon{t2, WNil{}}}}), Word.zero(16n))) :
        {Bool.and(Bool.not(_), UTF8.is_scalar(utf8_proof.cp4(WCon{z0, WCon{z1, WCon{z2, WCon{z3, WCon{z4, WCon{z5, WNil{}}}}}}}, WCon{y0, WCon{y1, WCon{y2, WCon{y3, WCon{y4, WCon{y5, WNil{}}}}}}}, WCon{x0, WCon{x1, WCon{x2, WCon{x3, WCon{x4, WCon{x5, WNil{}}}}}}}, WCon{t0, WCon{t1, WCon{t2, WNil{}}}}))) == utf8_proof.model4(x4, x5, WCon{t0, WCon{t1, WCon{t2, WNil{}}}}) : Bool}
      %Equal.sym(Bool, Cmp.is_le(Word.cmp(32n, word_join(16n, WCon{z0, WCon{z1, WCon{z2, WCon{z3, WCon{z4, WCon{z5, WCon{y0, WCon{y1, WCon{y2, WCon{y3, WCon{y4, WCon{y5, WCon{x0, WCon{x1, WCon{x2, WCon{x3, WNil{}}}}}}}}}}}}}}}}}, 16n, utf8_proof.H4(x4, x5, WCon{t0, WCon{t1, WCon{t2, WNil{}}}})), word_join(16n, word_ones(16n), 16n, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, Word.zero(11n)}}}}}))), Cmp.is_le(Word.cmp(16n, utf8_proof.H4(x4, x5, WCon{t0, WCon{t1, WCon{t2, WNil{}}}}), WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, Word.zero(11n)}}}}})), utf8_proof.word_le_ones(16n, WCon{z0, WCon{z1, WCon{z2, WCon{z3, WCon{z4, WCon{z5, WCon{y0, WCon{y1, WCon{y2, WCon{y3, WCon{y4, WCon{y5, WCon{x0, WCon{x1, WCon{x2, WCon{x3, WNil{}}}}}}}}}}}}}}}}}, 16n, utf8_proof.H4(x4, x5, WCon{t0, WCon{t1, WCon{t2, WNil{}}}}), WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, Word.zero(11n)}}}}})) :
        {Bool.and(Bool.not(Cmp.is_le(Word.cmp(16n, utf8_proof.H4(x4, x5, WCon{t0, WCon{t1, WCon{t2, WNil{}}}}), Word.zero(16n)))), Bool.and(_, Bool.not(UTF8.is_surrogate(utf8_proof.cp4(WCon{z0, WCon{z1, WCon{z2, WCon{z3, WCon{z4, WCon{z5, WNil{}}}}}}}, WCon{y0, WCon{y1, WCon{y2, WCon{y3, WCon{y4, WCon{y5, WNil{}}}}}}}, WCon{x0, WCon{x1, WCon{x2, WCon{x3, WCon{x4, WCon{x5, WNil{}}}}}}}, WCon{t0, WCon{t1, WCon{t2, WNil{}}}}))))) == utf8_proof.model4(x4, x5, WCon{t0, WCon{t1, WCon{t2, WNil{}}}}) : Bool}
      utf8_proof.value4_rows(z0, z1, z2, z3, z4, z5, y0, y1, y2, y3, y4, y5, x0, x1, x2, x3, x4, x5, t0, t1, t2)

def utf8_proof.valid4_eq(+z: Word(6n), +y: Word(6n), +x: Word(6n), +t: Word(3n)) ->
  {UTF8.valid_four_bytes(utf8_proof.lead4(t), utf8_proof.second_byte(x), utf8_proof.second_byte(y), utf8_proof.second_byte(z)) == utf8_proof.model4(utf8_proof.bit4(x), utf8_proof.bit5(x), t) : Bool}:
  Equal.trans(Bool, UTF8.valid_four_bytes(utf8_proof.lead4(t), utf8_proof.second_byte(x), utf8_proof.second_byte(y), utf8_proof.second_byte(z)), utf8_proof.value4(utf8_proof.cp4(z, y, x, t)), utf8_proof.model4(utf8_proof.bit4(x), utf8_proof.bit5(x), t),
    utf8_proof.valid4_fields(z, y, x, t), utf8_proof.value4_model(z, y, x, t))

def utf8_proof.any3_last.at(+z: Word(6n), +y: Word(6n), +t: Word(4n), v: {UTF8.valid_three_bytes(utf8_proof.lead3(t), utf8_proof.second_byte(y), utf8_proof.second_byte(z)) == True{} : Bool}) -> {UTF8.valid_three_bytes(utf8_proof.lead3(t), utf8_proof.second_byte(y), 128) == True{} : Bool}:
  Equal.trans(Bool, UTF8.valid_three_bytes(utf8_proof.lead3(t), utf8_proof.second_byte(y), 128), utf8_proof.model3(utf8_proof.bit5(y), t), True{}, utf8_proof.valid3_eq(WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}, y, t),
    Equal.trans(Bool, utf8_proof.model3(utf8_proof.bit5(y), t), UTF8.valid_three_bytes(utf8_proof.lead3(t), utf8_proof.second_byte(y), utf8_proof.second_byte(z)), True{},
      Equal.sym(Bool, UTF8.valid_three_bytes(utf8_proof.lead3(t), utf8_proof.second_byte(y), utf8_proof.second_byte(z)), utf8_proof.model3(utf8_proof.bit5(y), t), utf8_proof.valid3_eq(z, y, t)), v))

def utf8_proof.any3_last.eqs(+z: Word(6n), +y: Word(6n), +t: Word(4n), +b1: U32, +b2: U32, +b3: U32, +et: {b1 == utf8_proof.lead3(t) : U32}, +ey: {b2 == utf8_proof.second_byte(y) : U32}, +ez: {b3 == utf8_proof.second_byte(z) : U32}) -> {UTF8.valid_three_bytes(b1, b2, b3) == True{} : Bool} -> {UTF8.valid_three_bytes(b1, b2, 128) == True{} : Bool}:
  %Equal.sym(U32, b1, utf8_proof.lead3(t), et) : {UTF8.valid_three_bytes(_, b2, b3) == True{} : Bool} -> {UTF8.valid_three_bytes(_, b2, 128) == True{} : Bool}
  %Equal.sym(U32, b2, utf8_proof.second_byte(y), ey) : {UTF8.valid_three_bytes(utf8_proof.lead3(t), _, b3) == True{} : Bool} -> {UTF8.valid_three_bytes(utf8_proof.lead3(t), _, 128) == True{} : Bool}
  %Equal.sym(U32, b3, utf8_proof.second_byte(z), ez) : {UTF8.valid_three_bytes(utf8_proof.lead3(t), utf8_proof.second_byte(y), _) == True{} : Bool} -> {UTF8.valid_three_bytes(utf8_proof.lead3(t), utf8_proof.second_byte(y), 128) == True{} : Bool}
  v => utf8_proof.any3_last.at(z, y, t, v)


def utf8_proof.any3_last.fields(+b1: U32, +b2: U32, +b3: U32, f: utf8_proof.Fields3(b1, b2, b3)) -> {UTF8.valid_three_bytes(b1, b2, b3) == True{} : Bool} -> {UTF8.valid_three_bytes(b1, b2, 128) == True{} : Bool}:
  (+z, f0) = f
  (+y, f1) = f0
  (+t, f2) = f1
  (et, g0) = f2
  (ey, g1) = g0
  utf8_proof.any3_last.eqs(z, y, t, b1, b2, b3, et, ey, g1)

def utf8_proof.any3_last(+b1: U32, +b2: U32, +b3: U32, +valid: {UTF8.valid_three_bytes(b1, b2, b3) == True{} : Bool}) -> {UTF8.valid_three_bytes(b1, b2, 128) == True{} : Bool}:
  utf8_proof.any3_last.fields(b1, b2, b3, utf8_proof.fields3(b1, b2, b3, UTF8.valid_three_bytes.has_shape(b1, b2, b3, valid)), valid)

def utf8_proof.any3_mid.case(bit: Bool, +t: Word(4n), m: {utf8_proof.model3(bit, t) == True{} : Bool}) -> Or({UTF8.valid_three_bytes(utf8_proof.lead3(t), 128, 128) == True{} : Bool}, {UTF8.valid_three_bytes(utf8_proof.lead3(t), 191, 128) == True{} : Bool}):
  match bit:
    case False{}: Inl{Equal.trans(Bool, UTF8.valid_three_bytes(utf8_proof.lead3(t), 128, 128), utf8_proof.model3(False{}, t), True{}, utf8_proof.valid3_eq(WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}, t), m)}
    case True{}: Inr{Equal.trans(Bool, UTF8.valid_three_bytes(utf8_proof.lead3(t), 191, 128), utf8_proof.model3(True{}, t), True{}, utf8_proof.valid3_eq(WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}, t), m)}

def utf8_proof.any3_mid.at(+z: Word(6n), +y: Word(6n), +t: Word(4n), v: {UTF8.valid_three_bytes(utf8_proof.lead3(t), utf8_proof.second_byte(y), utf8_proof.second_byte(z)) == True{} : Bool}) -> Or({UTF8.valid_three_bytes(utf8_proof.lead3(t), 128, 128) == True{} : Bool}, {UTF8.valid_three_bytes(utf8_proof.lead3(t), 191, 128) == True{} : Bool}):
  utf8_proof.any3_mid.case(utf8_proof.bit5(y), t,
    Equal.trans(Bool, utf8_proof.model3(utf8_proof.bit5(y), t), UTF8.valid_three_bytes(utf8_proof.lead3(t), utf8_proof.second_byte(y), utf8_proof.second_byte(z)), True{},
      Equal.sym(Bool, UTF8.valid_three_bytes(utf8_proof.lead3(t), utf8_proof.second_byte(y), utf8_proof.second_byte(z)), utf8_proof.model3(utf8_proof.bit5(y), t), utf8_proof.valid3_eq(z, y, t)), v))

def utf8_proof.any3_mid.eqs(+z: Word(6n), +y: Word(6n), +t: Word(4n), +b1: U32, +b2: U32, +b3: U32, +et: {b1 == utf8_proof.lead3(t) : U32}, +ey: {b2 == utf8_proof.second_byte(y) : U32}, +ez: {b3 == utf8_proof.second_byte(z) : U32}) -> {UTF8.valid_three_bytes(b1, b2, b3) == True{} : Bool} -> Or({UTF8.valid_three_bytes(b1, 128, 128) == True{} : Bool}, {UTF8.valid_three_bytes(b1, 191, 128) == True{} : Bool}):
  %Equal.sym(U32, b1, utf8_proof.lead3(t), et) : {UTF8.valid_three_bytes(_, b2, b3) == True{} : Bool} -> Or({UTF8.valid_three_bytes(_, 128, 128) == True{} : Bool}, {UTF8.valid_three_bytes(_, 191, 128) == True{} : Bool})
  %Equal.sym(U32, b2, utf8_proof.second_byte(y), ey) : {UTF8.valid_three_bytes(utf8_proof.lead3(t), _, b3) == True{} : Bool} -> Or({UTF8.valid_three_bytes(utf8_proof.lead3(t), 128, 128) == True{} : Bool}, {UTF8.valid_three_bytes(utf8_proof.lead3(t), 191, 128) == True{} : Bool})
  %Equal.sym(U32, b3, utf8_proof.second_byte(z), ez) : {UTF8.valid_three_bytes(utf8_proof.lead3(t), utf8_proof.second_byte(y), _) == True{} : Bool} -> Or({UTF8.valid_three_bytes(utf8_proof.lead3(t), 128, 128) == True{} : Bool}, {UTF8.valid_three_bytes(utf8_proof.lead3(t), 191, 128) == True{} : Bool})
  v => utf8_proof.any3_mid.at(z, y, t, v)


def utf8_proof.any3_mid.fields(+b1: U32, +b2: U32, +b3: U32, f: utf8_proof.Fields3(b1, b2, b3)) -> {UTF8.valid_three_bytes(b1, b2, b3) == True{} : Bool} -> Or({UTF8.valid_three_bytes(b1, 128, 128) == True{} : Bool}, {UTF8.valid_three_bytes(b1, 191, 128) == True{} : Bool}):
  (+z, f0) = f
  (+y, f1) = f0
  (+t, f2) = f1
  (et, g0) = f2
  (ey, g1) = g0
  utf8_proof.any3_mid.eqs(z, y, t, b1, b2, b3, et, ey, g1)

def utf8_proof.any3_mid(+b1: U32, +b2: U32, +b3: U32, +valid: {UTF8.valid_three_bytes(b1, b2, b3) == True{} : Bool}) -> Or({UTF8.valid_three_bytes(b1, 128, 128) == True{} : Bool}, {UTF8.valid_three_bytes(b1, 191, 128) == True{} : Bool}):
  utf8_proof.any3_mid.fields(b1, b2, b3, utf8_proof.fields3(b1, b2, b3, UTF8.valid_three_bytes.has_shape(b1, b2, b3, valid)), valid)

def utf8_proof.any4_last.at(+z: Word(6n), +y: Word(6n), +x: Word(6n), +t: Word(3n), v: {UTF8.valid_four_bytes(utf8_proof.lead4(t), utf8_proof.second_byte(x), utf8_proof.second_byte(y), utf8_proof.second_byte(z)) == True{} : Bool}) -> {UTF8.valid_four_bytes(utf8_proof.lead4(t), utf8_proof.second_byte(x), utf8_proof.second_byte(y), 128) == True{} : Bool}:
  Equal.trans(Bool, UTF8.valid_four_bytes(utf8_proof.lead4(t), utf8_proof.second_byte(x), utf8_proof.second_byte(y), 128), utf8_proof.model4(utf8_proof.bit4(x), utf8_proof.bit5(x), t), True{}, utf8_proof.valid4_eq(WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}, y, x, t),
    Equal.trans(Bool, utf8_proof.model4(utf8_proof.bit4(x), utf8_proof.bit5(x), t), UTF8.valid_four_bytes(utf8_proof.lead4(t), utf8_proof.second_byte(x), utf8_proof.second_byte(y), utf8_proof.second_byte(z)), True{},
      Equal.sym(Bool, UTF8.valid_four_bytes(utf8_proof.lead4(t), utf8_proof.second_byte(x), utf8_proof.second_byte(y), utf8_proof.second_byte(z)), utf8_proof.model4(utf8_proof.bit4(x), utf8_proof.bit5(x), t), utf8_proof.valid4_eq(z, y, x, t)), v))

def utf8_proof.any4_last.eqs(+z: Word(6n), +y: Word(6n), +x: Word(6n), +t: Word(3n), +b1: U32, +b2: U32, +b3: U32, +b4: U32, +et: {b1 == utf8_proof.lead4(t) : U32}, +ex: {b2 == utf8_proof.second_byte(x) : U32}, +ey: {b3 == utf8_proof.second_byte(y) : U32}, +ez: {b4 == utf8_proof.second_byte(z) : U32}) -> {UTF8.valid_four_bytes(b1, b2, b3, b4) == True{} : Bool} -> {UTF8.valid_four_bytes(b1, b2, b3, 128) == True{} : Bool}:
  %Equal.sym(U32, b1, utf8_proof.lead4(t), et) : {UTF8.valid_four_bytes(_, b2, b3, b4) == True{} : Bool} -> {UTF8.valid_four_bytes(_, b2, b3, 128) == True{} : Bool}
  %Equal.sym(U32, b2, utf8_proof.second_byte(x), ex) : {UTF8.valid_four_bytes(utf8_proof.lead4(t), _, b3, b4) == True{} : Bool} -> {UTF8.valid_four_bytes(utf8_proof.lead4(t), _, b3, 128) == True{} : Bool}
  %Equal.sym(U32, b3, utf8_proof.second_byte(y), ey) : {UTF8.valid_four_bytes(utf8_proof.lead4(t), utf8_proof.second_byte(x), _, b4) == True{} : Bool} -> {UTF8.valid_four_bytes(utf8_proof.lead4(t), utf8_proof.second_byte(x), _, 128) == True{} : Bool}
  %Equal.sym(U32, b4, utf8_proof.second_byte(z), ez) : {UTF8.valid_four_bytes(utf8_proof.lead4(t), utf8_proof.second_byte(x), utf8_proof.second_byte(y), _) == True{} : Bool} -> {UTF8.valid_four_bytes(utf8_proof.lead4(t), utf8_proof.second_byte(x), utf8_proof.second_byte(y), 128) == True{} : Bool}
  v => utf8_proof.any4_last.at(z, y, x, t, v)


def utf8_proof.any4_last.fields(+b1: U32, +b2: U32, +b3: U32, +b4: U32, f: utf8_proof.Fields4(b1, b2, b3, b4)) -> {UTF8.valid_four_bytes(b1, b2, b3, b4) == True{} : Bool} -> {UTF8.valid_four_bytes(b1, b2, b3, 128) == True{} : Bool}:
  (+z, f0) = f
  (+y, f1) = f0
  (+x, f2) = f1
  (+t, f3) = f2
  (et, g0) = f3
  (ex, g1) = g0
  (ey, g2) = g1
  utf8_proof.any4_last.eqs(z, y, x, t, b1, b2, b3, b4, et, ex, ey, g2)

def utf8_proof.any4_last(+b1: U32, +b2: U32, +b3: U32, +b4: U32, +valid: {UTF8.valid_four_bytes(b1, b2, b3, b4) == True{} : Bool}) -> {UTF8.valid_four_bytes(b1, b2, b3, 128) == True{} : Bool}:
  utf8_proof.any4_last.fields(b1, b2, b3, b4, utf8_proof.fields4(b1, b2, b3, b4, UTF8.valid_four_bytes.has_shape(b1, b2, b3, b4, valid)), valid)

def utf8_proof.any4_third.at(+z: Word(6n), +y: Word(6n), +x: Word(6n), +t: Word(3n), v: {UTF8.valid_four_bytes(utf8_proof.lead4(t), utf8_proof.second_byte(x), utf8_proof.second_byte(y), utf8_proof.second_byte(z)) == True{} : Bool}) -> {UTF8.valid_four_bytes(utf8_proof.lead4(t), utf8_proof.second_byte(x), 128, 128) == True{} : Bool}:
  Equal.trans(Bool, UTF8.valid_four_bytes(utf8_proof.lead4(t), utf8_proof.second_byte(x), 128, 128), utf8_proof.model4(utf8_proof.bit4(x), utf8_proof.bit5(x), t), True{}, utf8_proof.valid4_eq(WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}, x, t),
    Equal.trans(Bool, utf8_proof.model4(utf8_proof.bit4(x), utf8_proof.bit5(x), t), UTF8.valid_four_bytes(utf8_proof.lead4(t), utf8_proof.second_byte(x), utf8_proof.second_byte(y), utf8_proof.second_byte(z)), True{},
      Equal.sym(Bool, UTF8.valid_four_bytes(utf8_proof.lead4(t), utf8_proof.second_byte(x), utf8_proof.second_byte(y), utf8_proof.second_byte(z)), utf8_proof.model4(utf8_proof.bit4(x), utf8_proof.bit5(x), t), utf8_proof.valid4_eq(z, y, x, t)), v))

def utf8_proof.any4_third.eqs(+z: Word(6n), +y: Word(6n), +x: Word(6n), +t: Word(3n), +b1: U32, +b2: U32, +b3: U32, +b4: U32, +et: {b1 == utf8_proof.lead4(t) : U32}, +ex: {b2 == utf8_proof.second_byte(x) : U32}, +ey: {b3 == utf8_proof.second_byte(y) : U32}, +ez: {b4 == utf8_proof.second_byte(z) : U32}) -> {UTF8.valid_four_bytes(b1, b2, b3, b4) == True{} : Bool} -> {UTF8.valid_four_bytes(b1, b2, 128, 128) == True{} : Bool}:
  %Equal.sym(U32, b1, utf8_proof.lead4(t), et) : {UTF8.valid_four_bytes(_, b2, b3, b4) == True{} : Bool} -> {UTF8.valid_four_bytes(_, b2, 128, 128) == True{} : Bool}
  %Equal.sym(U32, b2, utf8_proof.second_byte(x), ex) : {UTF8.valid_four_bytes(utf8_proof.lead4(t), _, b3, b4) == True{} : Bool} -> {UTF8.valid_four_bytes(utf8_proof.lead4(t), _, 128, 128) == True{} : Bool}
  %Equal.sym(U32, b3, utf8_proof.second_byte(y), ey) : {UTF8.valid_four_bytes(utf8_proof.lead4(t), utf8_proof.second_byte(x), _, b4) == True{} : Bool} -> {UTF8.valid_four_bytes(utf8_proof.lead4(t), utf8_proof.second_byte(x), 128, 128) == True{} : Bool}
  %Equal.sym(U32, b4, utf8_proof.second_byte(z), ez) : {UTF8.valid_four_bytes(utf8_proof.lead4(t), utf8_proof.second_byte(x), utf8_proof.second_byte(y), _) == True{} : Bool} -> {UTF8.valid_four_bytes(utf8_proof.lead4(t), utf8_proof.second_byte(x), 128, 128) == True{} : Bool}
  v => utf8_proof.any4_third.at(z, y, x, t, v)


def utf8_proof.any4_third.fields(+b1: U32, +b2: U32, +b3: U32, +b4: U32, f: utf8_proof.Fields4(b1, b2, b3, b4)) -> {UTF8.valid_four_bytes(b1, b2, b3, b4) == True{} : Bool} -> {UTF8.valid_four_bytes(b1, b2, 128, 128) == True{} : Bool}:
  (+z, f0) = f
  (+y, f1) = f0
  (+x, f2) = f1
  (+t, f3) = f2
  (et, g0) = f3
  (ex, g1) = g0
  (ey, g2) = g1
  utf8_proof.any4_third.eqs(z, y, x, t, b1, b2, b3, b4, et, ex, ey, g2)

def utf8_proof.any4_third(+b1: U32, +b2: U32, +b3: U32, +b4: U32, +valid: {UTF8.valid_four_bytes(b1, b2, b3, b4) == True{} : Bool}) -> {UTF8.valid_four_bytes(b1, b2, 128, 128) == True{} : Bool}:
  utf8_proof.any4_third.fields(b1, b2, b3, b4, utf8_proof.fields4(b1, b2, b3, b4, UTF8.valid_four_bytes.has_shape(b1, b2, b3, b4, valid)), valid)

def utf8_proof.any4_mid.Or(+t: Word(3n)) -> Type:
  Or({utf8_proof.model4(False{}, False{}, t) == True{} : Bool}, {utf8_proof.model4(True{}, True{}, t) == True{} : Bool})

def utf8_proof.any4_mid.rows(+x4: Bool, +x5: Bool, +t0: Bool, +t1: Bool, +t2: Bool,
  v: {utf8_proof.model4(x4, x5, WCon{t0, WCon{t1, WCon{t2, WNil{}}}}) == True{} : Bool}) -> utf8_proof.any4_mid.Or(WCon{t0, WCon{t1, WCon{t2, WNil{}}}}):
  match x4 x5 t0 t1 t2:
    case False{} False{} False{} False{} False{}: Empty.absurd(utf8_proof.any4_mid.Or(WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}), UTF8.false_true(v))
    case False{} False{} False{} False{} True{}: Inl{{==}}
    case False{} False{} False{} True{} False{}: Inl{{==}}
    case False{} False{} False{} True{} True{}: Empty.absurd(utf8_proof.any4_mid.Or(WCon{False{}, WCon{True{}, WCon{True{}, WNil{}}}}), UTF8.false_true(v))
    case False{} False{} True{} False{} False{}: Inl{{==}}
    case False{} False{} True{} False{} True{}: Empty.absurd(utf8_proof.any4_mid.Or(WCon{True{}, WCon{False{}, WCon{True{}, WNil{}}}}), UTF8.false_true(v))
    case False{} False{} True{} True{} False{}: Inl{{==}}
    case False{} False{} True{} True{} True{}: Empty.absurd(utf8_proof.any4_mid.Or(WCon{True{}, WCon{True{}, WCon{True{}, WNil{}}}}), UTF8.false_true(v))
    case False{} True{} False{} False{} False{}: Inr{{==}}
    case False{} True{} False{} False{} True{}: Empty.absurd(utf8_proof.any4_mid.Or(WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}), UTF8.false_true(v))
    case False{} True{} False{} True{} False{}: Inl{{==}}
    case False{} True{} False{} True{} True{}: Empty.absurd(utf8_proof.any4_mid.Or(WCon{False{}, WCon{True{}, WCon{True{}, WNil{}}}}), UTF8.false_true(v))
    case False{} True{} True{} False{} False{}: Inl{{==}}
    case False{} True{} True{} False{} True{}: Empty.absurd(utf8_proof.any4_mid.Or(WCon{True{}, WCon{False{}, WCon{True{}, WNil{}}}}), UTF8.false_true(v))
    case False{} True{} True{} True{} False{}: Inl{{==}}
    case False{} True{} True{} True{} True{}: Empty.absurd(utf8_proof.any4_mid.Or(WCon{True{}, WCon{True{}, WCon{True{}, WNil{}}}}), UTF8.false_true(v))
    case True{} False{} False{} False{} False{}: Inr{{==}}
    case True{} False{} False{} False{} True{}: Empty.absurd(utf8_proof.any4_mid.Or(WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}), UTF8.false_true(v))
    case True{} False{} False{} True{} False{}: Inl{{==}}
    case True{} False{} False{} True{} True{}: Empty.absurd(utf8_proof.any4_mid.Or(WCon{False{}, WCon{True{}, WCon{True{}, WNil{}}}}), UTF8.false_true(v))
    case True{} False{} True{} False{} False{}: Inl{{==}}
    case True{} False{} True{} False{} True{}: Empty.absurd(utf8_proof.any4_mid.Or(WCon{True{}, WCon{False{}, WCon{True{}, WNil{}}}}), UTF8.false_true(v))
    case True{} False{} True{} True{} False{}: Inl{{==}}
    case True{} False{} True{} True{} True{}: Empty.absurd(utf8_proof.any4_mid.Or(WCon{True{}, WCon{True{}, WCon{True{}, WNil{}}}}), UTF8.false_true(v))
    case True{} True{} False{} False{} False{}: Inr{{==}}
    case True{} True{} False{} False{} True{}: Empty.absurd(utf8_proof.any4_mid.Or(WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}), UTF8.false_true(v))
    case True{} True{} False{} True{} False{}: Inl{{==}}
    case True{} True{} False{} True{} True{}: Empty.absurd(utf8_proof.any4_mid.Or(WCon{False{}, WCon{True{}, WCon{True{}, WNil{}}}}), UTF8.false_true(v))
    case True{} True{} True{} False{} False{}: Inl{{==}}
    case True{} True{} True{} False{} True{}: Empty.absurd(utf8_proof.any4_mid.Or(WCon{True{}, WCon{False{}, WCon{True{}, WNil{}}}}), UTF8.false_true(v))
    case True{} True{} True{} True{} False{}: Inl{{==}}
    case True{} True{} True{} True{} True{}: Empty.absurd(utf8_proof.any4_mid.Or(WCon{True{}, WCon{True{}, WCon{True{}, WNil{}}}}), UTF8.false_true(v))

def utf8_proof.any4_mid.split(+x: Word(6n), +t: Word(3n), v: {utf8_proof.model4(utf8_proof.bit4(x), utf8_proof.bit5(x), t) == True{} : Bool}) -> utf8_proof.any4_mid.Or(t):
  match x t:
    case WCon{x0, WCon{x1, WCon{x2, WCon{x3, WCon{x4, WCon{x5, WNil{}}}}}}} WCon{t0, WCon{t1, WCon{t2, WNil{}}}}:
      utf8_proof.any4_mid.rows(x4, x5, t0, t1, t2, v)

def utf8_proof.any4_mid.pick(+t: Word(3n), o: utf8_proof.any4_mid.Or(t)) ->
  Or({UTF8.valid_four_bytes(utf8_proof.lead4(t), 128, 128, 128) == True{} : Bool}, {UTF8.valid_four_bytes(utf8_proof.lead4(t), 191, 128, 128) == True{} : Bool}):
  match o:
    case Inl{m}: Inl{Equal.trans(Bool, UTF8.valid_four_bytes(utf8_proof.lead4(t), 128, 128, 128), utf8_proof.model4(False{}, False{}, t), True{}, utf8_proof.valid4_eq(WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}, t), m)}
    case Inr{m}: Inr{Equal.trans(Bool, UTF8.valid_four_bytes(utf8_proof.lead4(t), 191, 128, 128), utf8_proof.model4(True{}, True{}, t), True{}, utf8_proof.valid4_eq(WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}, t), m)}


def utf8_proof.any4_mid.at(+z: Word(6n), +y: Word(6n), +x: Word(6n), +t: Word(3n), v: {UTF8.valid_four_bytes(utf8_proof.lead4(t), utf8_proof.second_byte(x), utf8_proof.second_byte(y), utf8_proof.second_byte(z)) == True{} : Bool}) -> Or({UTF8.valid_four_bytes(utf8_proof.lead4(t), 128, 128, 128) == True{} : Bool}, {UTF8.valid_four_bytes(utf8_proof.lead4(t), 191, 128, 128) == True{} : Bool}):
  utf8_proof.any4_mid.pick(t, utf8_proof.any4_mid.split(x, t, Equal.trans(Bool, utf8_proof.model4(utf8_proof.bit4(x), utf8_proof.bit5(x), t), UTF8.valid_four_bytes(utf8_proof.lead4(t), utf8_proof.second_byte(x), utf8_proof.second_byte(y), utf8_proof.second_byte(z)), True{},
      Equal.sym(Bool, UTF8.valid_four_bytes(utf8_proof.lead4(t), utf8_proof.second_byte(x), utf8_proof.second_byte(y), utf8_proof.second_byte(z)), utf8_proof.model4(utf8_proof.bit4(x), utf8_proof.bit5(x), t), utf8_proof.valid4_eq(z, y, x, t)), v)))

def utf8_proof.any4_mid.eqs(+z: Word(6n), +y: Word(6n), +x: Word(6n), +t: Word(3n), +b1: U32, +b2: U32, +b3: U32, +b4: U32, +et: {b1 == utf8_proof.lead4(t) : U32}, +ex: {b2 == utf8_proof.second_byte(x) : U32}, +ey: {b3 == utf8_proof.second_byte(y) : U32}, +ez: {b4 == utf8_proof.second_byte(z) : U32}) -> {UTF8.valid_four_bytes(b1, b2, b3, b4) == True{} : Bool} -> Or({UTF8.valid_four_bytes(b1, 128, 128, 128) == True{} : Bool}, {UTF8.valid_four_bytes(b1, 191, 128, 128) == True{} : Bool}):
  %Equal.sym(U32, b1, utf8_proof.lead4(t), et) : {UTF8.valid_four_bytes(_, b2, b3, b4) == True{} : Bool} -> Or({UTF8.valid_four_bytes(_, 128, 128, 128) == True{} : Bool}, {UTF8.valid_four_bytes(_, 191, 128, 128) == True{} : Bool})
  %Equal.sym(U32, b2, utf8_proof.second_byte(x), ex) : {UTF8.valid_four_bytes(utf8_proof.lead4(t), _, b3, b4) == True{} : Bool} -> Or({UTF8.valid_four_bytes(utf8_proof.lead4(t), 128, 128, 128) == True{} : Bool}, {UTF8.valid_four_bytes(utf8_proof.lead4(t), 191, 128, 128) == True{} : Bool})
  %Equal.sym(U32, b3, utf8_proof.second_byte(y), ey) : {UTF8.valid_four_bytes(utf8_proof.lead4(t), utf8_proof.second_byte(x), _, b4) == True{} : Bool} -> Or({UTF8.valid_four_bytes(utf8_proof.lead4(t), 128, 128, 128) == True{} : Bool}, {UTF8.valid_four_bytes(utf8_proof.lead4(t), 191, 128, 128) == True{} : Bool})
  %Equal.sym(U32, b4, utf8_proof.second_byte(z), ez) : {UTF8.valid_four_bytes(utf8_proof.lead4(t), utf8_proof.second_byte(x), utf8_proof.second_byte(y), _) == True{} : Bool} -> Or({UTF8.valid_four_bytes(utf8_proof.lead4(t), 128, 128, 128) == True{} : Bool}, {UTF8.valid_four_bytes(utf8_proof.lead4(t), 191, 128, 128) == True{} : Bool})
  v => utf8_proof.any4_mid.at(z, y, x, t, v)


def utf8_proof.any4_mid.fields(+b1: U32, +b2: U32, +b3: U32, +b4: U32, f: utf8_proof.Fields4(b1, b2, b3, b4)) -> {UTF8.valid_four_bytes(b1, b2, b3, b4) == True{} : Bool} -> Or({UTF8.valid_four_bytes(b1, 128, 128, 128) == True{} : Bool}, {UTF8.valid_four_bytes(b1, 191, 128, 128) == True{} : Bool}):
  (+z, f0) = f
  (+y, f1) = f0
  (+x, f2) = f1
  (+t, f3) = f2
  (et, g0) = f3
  (ex, g1) = g0
  (ey, g2) = g1
  utf8_proof.any4_mid.eqs(z, y, x, t, b1, b2, b3, b4, et, ex, ey, g2)

def utf8_proof.any4_mid(+b1: U32, +b2: U32, +b3: U32, +b4: U32, +valid: {UTF8.valid_four_bytes(b1, b2, b3, b4) == True{} : Bool}) -> Or({UTF8.valid_four_bytes(b1, 128, 128, 128) == True{} : Bool}, {UTF8.valid_four_bytes(b1, 191, 128, 128) == True{} : Bool}):
  utf8_proof.any4_mid.fields(b1, b2, b3, b4, utf8_proof.fields4(b1, b2, b3, b4, UTF8.valid_four_bytes.has_shape(b1, b2, b3, b4, valid)), valid)

def utf8_proof.mono12_bits(+b31: Bool, +b30: Bool, +b29: Bool, +b28: Bool, +b27: Bool, +b26: Bool, +b25: Bool, +b24: Bool, +b23: Bool, +b22: Bool, +b21: Bool, +b20: Bool, +b19: Bool, +b18: Bool, +b17: Bool, +b16: Bool, +b15: Bool, +b14: Bool, +b13: Bool, +b12: Bool, +b11: Bool, +b10: Bool, +b9: Bool, +b8: Bool, +b7: Bool, +b6: Bool, +b5: Bool, +b4: Bool, +b3: Bool, +b2: Bool, +b1: Bool, +b0: Bool, v: {U32.is_le(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 127) == True{} : Bool}) -> {U32.is_le(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 2047) == True{} : Bool}:
  match b31 b30 b29 b28 b27 b26 b25 b24 b23 b22 b21 b20 b19 b18 b17 b16 b15 b14 b13 b12 b11:
    case True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _: Empty.absurd({U32.is_le(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 2047) == True{} : Bool}, UTF8.false_true(v))
    case False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _: Empty.absurd({U32.is_le(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 2047) == True{} : Bool}, UTF8.false_true(v))
    case False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _: Empty.absurd({U32.is_le(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 2047) == True{} : Bool}, UTF8.false_true(v))
    case False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _: Empty.absurd({U32.is_le(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 2047) == True{} : Bool}, UTF8.false_true(v))
    case False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _: Empty.absurd({U32.is_le(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 2047) == True{} : Bool}, UTF8.false_true(v))
    case False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _: Empty.absurd({U32.is_le(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 2047) == True{} : Bool}, UTF8.false_true(v))
    case False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _: Empty.absurd({U32.is_le(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 2047) == True{} : Bool}, UTF8.false_true(v))
    case False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _: Empty.absurd({U32.is_le(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 2047) == True{} : Bool}, UTF8.false_true(v))
    case False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _: Empty.absurd({U32.is_le(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 2047) == True{} : Bool}, UTF8.false_true(v))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _: Empty.absurd({U32.is_le(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 2047) == True{} : Bool}, UTF8.false_true(v))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _: Empty.absurd({U32.is_le(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 2047) == True{} : Bool}, UTF8.false_true(v))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _: Empty.absurd({U32.is_le(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 2047) == True{} : Bool}, UTF8.false_true(v))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _: Empty.absurd({U32.is_le(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 2047) == True{} : Bool}, UTF8.false_true(v))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _: Empty.absurd({U32.is_le(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 2047) == True{} : Bool}, UTF8.false_true(v))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _: Empty.absurd({U32.is_le(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 2047) == True{} : Bool}, UTF8.false_true(v))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _: Empty.absurd({U32.is_le(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 2047) == True{} : Bool}, UTF8.false_true(v))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _: Empty.absurd({U32.is_le(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 2047) == True{} : Bool}, UTF8.false_true(v))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _: Empty.absurd({U32.is_le(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 2047) == True{} : Bool}, UTF8.false_true(v))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _: Empty.absurd({U32.is_le(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 2047) == True{} : Bool}, UTF8.false_true(v))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _: Empty.absurd({U32.is_le(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 2047) == True{} : Bool}, UTF8.false_true(v))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{}: Empty.absurd({U32.is_le(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 2047) == True{} : Bool}, UTF8.false_true(v))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{}:
      utf8_proof.word_le_ones(11n, WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WNil{}}}}}}}}}}}}, 21n, Word.zero(21n), Word.zero(21n))

def utf8_proof.mono12(+cp: U32, v: {U32.is_le(cp, 127) == True{} : Bool}) -> {U32.is_le(cp, 2047) == True{} : Bool}:
  match cp:
    case U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      utf8_proof.mono12_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0, v)

def utf8_proof.mono23_bits(+b31: Bool, +b30: Bool, +b29: Bool, +b28: Bool, +b27: Bool, +b26: Bool, +b25: Bool, +b24: Bool, +b23: Bool, +b22: Bool, +b21: Bool, +b20: Bool, +b19: Bool, +b18: Bool, +b17: Bool, +b16: Bool, +b15: Bool, +b14: Bool, +b13: Bool, +b12: Bool, +b11: Bool, +b10: Bool, +b9: Bool, +b8: Bool, +b7: Bool, +b6: Bool, +b5: Bool, +b4: Bool, +b3: Bool, +b2: Bool, +b1: Bool, +b0: Bool, v: {U32.is_le(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 2047) == True{} : Bool}) -> {U32.is_le(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 65535) == True{} : Bool}:
  match b31 b30 b29 b28 b27 b26 b25 b24 b23 b22 b21 b20 b19 b18 b17 b16:
    case True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _: Empty.absurd({U32.is_le(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 65535) == True{} : Bool}, UTF8.false_true(v))
    case False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _ _: Empty.absurd({U32.is_le(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 65535) == True{} : Bool}, UTF8.false_true(v))
    case False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _ _: Empty.absurd({U32.is_le(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 65535) == True{} : Bool}, UTF8.false_true(v))
    case False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _ _: Empty.absurd({U32.is_le(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 65535) == True{} : Bool}, UTF8.false_true(v))
    case False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _ _: Empty.absurd({U32.is_le(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 65535) == True{} : Bool}, UTF8.false_true(v))
    case False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _ _: Empty.absurd({U32.is_le(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 65535) == True{} : Bool}, UTF8.false_true(v))
    case False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _ _: Empty.absurd({U32.is_le(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 65535) == True{} : Bool}, UTF8.false_true(v))
    case False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _ _: Empty.absurd({U32.is_le(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 65535) == True{} : Bool}, UTF8.false_true(v))
    case False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _ _: Empty.absurd({U32.is_le(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 65535) == True{} : Bool}, UTF8.false_true(v))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _ _: Empty.absurd({U32.is_le(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 65535) == True{} : Bool}, UTF8.false_true(v))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _ _: Empty.absurd({U32.is_le(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 65535) == True{} : Bool}, UTF8.false_true(v))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _ _: Empty.absurd({U32.is_le(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 65535) == True{} : Bool}, UTF8.false_true(v))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _ _: Empty.absurd({U32.is_le(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 65535) == True{} : Bool}, UTF8.false_true(v))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _ _: Empty.absurd({U32.is_le(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 65535) == True{} : Bool}, UTF8.false_true(v))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{} _: Empty.absurd({U32.is_le(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 65535) == True{} : Bool}, UTF8.false_true(v))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} True{}: Empty.absurd({U32.is_le(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 65535) == True{} : Bool}, UTF8.false_true(v))
    case False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{} False{}:
      utf8_proof.word_le_ones(16n, WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WNil{}}}}}}}}}}}}}}}}}, 16n, Word.zero(16n), Word.zero(16n))

def utf8_proof.mono23(+cp: U32, v: {U32.is_le(cp, 2047) == True{} : Bool}) -> {U32.is_le(cp, 65535) == True{} : Bool}:
  match cp:
    case U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      utf8_proof.mono23_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0, v)

# Which sequence length a lead byte belongs to
# --------------------------------------------

def utf8_proof.kind.if(t: Bool, yes: Nat, no: Nat) -> Nat:
  match t:
    case True{}: yes
    case False{}: no

def utf8_proof.kind(+b: U32) -> Nat:
  utf8_proof.kind.if(U32.is_le(b, 127), 1n, utf8_proof.kind.if(UTF8.is_two_byte_lead(b), 2n, utf8_proof.kind.if(UTF8.is_three_byte_lead(b), 3n, 4n)))

def utf8_proof.kind_lead2(+t: Word(5n)) -> {utf8_proof.kind(utf8_proof.first_byte(t)) == 2n : Nat}:
  match t:
    case WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}: {==}
    case WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}}: {==}
    case WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WNil{}}}}}}: {==}
    case WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WNil{}}}}}}: {==}
    case WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WNil{}}}}}}: {==}
    case WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WNil{}}}}}}: {==}
    case WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WNil{}}}}}}: {==}
    case WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WNil{}}}}}}: {==}
    case WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}: {==}
    case WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}}: {==}
    case WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WNil{}}}}}}: {==}
    case WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WNil{}}}}}}: {==}
    case WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WNil{}}}}}}: {==}
    case WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WNil{}}}}}}: {==}
    case WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WNil{}}}}}}: {==}
    case WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WNil{}}}}}}: {==}
    case WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}: {==}
    case WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}}: {==}
    case WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WNil{}}}}}}: {==}
    case WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WNil{}}}}}}: {==}
    case WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WNil{}}}}}}: {==}
    case WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WNil{}}}}}}: {==}
    case WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WNil{}}}}}}: {==}
    case WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WNil{}}}}}}: {==}
    case WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}: {==}
    case WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}}: {==}
    case WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WNil{}}}}}}: {==}
    case WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WNil{}}}}}}: {==}
    case WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WNil{}}}}}}: {==}
    case WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WNil{}}}}}}: {==}
    case WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WNil{}}}}}}: {==}
    case WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WNil{}}}}}}: {==}

def utf8_proof.kind_lead3(+t: Word(4n)) -> {utf8_proof.kind(utf8_proof.lead3(t)) == 3n : Nat}:
  match t:
    case WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}: {==}
    case WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}: {==}
    case WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WNil{}}}}}: {==}
    case WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WNil{}}}}}: {==}
    case WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WNil{}}}}}: {==}
    case WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WNil{}}}}}: {==}
    case WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WNil{}}}}}: {==}
    case WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WNil{}}}}}: {==}
    case WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}: {==}
    case WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}: {==}
    case WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WNil{}}}}}: {==}
    case WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WNil{}}}}}: {==}
    case WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WNil{}}}}}: {==}
    case WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WNil{}}}}}: {==}
    case WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WNil{}}}}}: {==}
    case WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WNil{}}}}}: {==}

def utf8_proof.kind_lead4(+t: Word(3n)) -> {utf8_proof.kind(utf8_proof.lead4(t)) == 4n : Nat}:
  match t:
    case WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}: {==}
    case WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}: {==}
    case WCon{False{}, WCon{True{}, WCon{False{}, WNil{}}}}: {==}
    case WCon{False{}, WCon{True{}, WCon{True{}, WNil{}}}}: {==}
    case WCon{True{}, WCon{False{}, WCon{False{}, WNil{}}}}: {==}
    case WCon{True{}, WCon{False{}, WCon{True{}, WNil{}}}}: {==}
    case WCon{True{}, WCon{True{}, WCon{False{}, WNil{}}}}: {==}
    case WCon{True{}, WCon{True{}, WCon{True{}, WNil{}}}}: {==}

def utf8_proof.valid_kind1(+b: U32, v: {UTF8.valid_one_byte(b) == True{} : Bool}) -> {utf8_proof.kind(b) == 1n : Nat}:
  %Equal.sym(Bool, U32.is_le(b, 127), True{}, v) :
    {utf8_proof.kind.if(_, 1n, utf8_proof.kind.if(UTF8.is_two_byte_lead(b), 2n, utf8_proof.kind.if(UTF8.is_three_byte_lead(b), 3n, 4n))) == 1n : Nat}
  {==}

def utf8_proof.valid_kind2.pay(+b1: U32, p: Exists(Word(5n), high => {b1 == utf8_proof.first_byte(high) : U32})) -> {utf8_proof.kind(b1) == 2n : Nat}:
  (+high, e) = p
  %Equal.sym(U32, b1, utf8_proof.first_byte(high), e) : {utf8_proof.kind(_) == 2n : Nat}
  utf8_proof.kind_lead2(high)

def utf8_proof.valid_kind2(+b1: U32, +b2: U32, +v: {UTF8.valid_two_bytes(b1, b2) == True{} : Bool}) -> {utf8_proof.kind(b1) == 2n : Nat}:
  utf8_proof.valid_kind2.pay(b1, utf8_proof.first_payload(b1, bool_and_left_true(UTF8.is_two_byte_lead(b1), UTF8.is_continuation_byte(b2),
    UTF8.valid_two_bytes.has_shape(b1, b2, v))))

def utf8_proof.valid_kind3.at(+b1: U32, +b2: U32, +b3: U32, +t: Word(4n), +et: {b1 == utf8_proof.lead3(t) : U32}) -> {utf8_proof.kind(b1) == 3n : Nat}:
  %Equal.sym(U32, b1, utf8_proof.lead3(t), et) : {utf8_proof.kind(_) == 3n : Nat}
  utf8_proof.kind_lead3(t)

def utf8_proof.valid_kind3.fields(+b1: U32, +b2: U32, +b3: U32, f: utf8_proof.Fields3(b1, b2, b3)) -> {utf8_proof.kind(b1) == 3n : Nat}:
  (z, f0) = f
  (y, f1) = f0
  (+t, f2) = f1
  (et, g0) = f2
  utf8_proof.valid_kind3.at(b1, b2, b3, t, et)

def utf8_proof.valid_kind3(+b1: U32, +b2: U32, +b3: U32, +v: {UTF8.valid_three_bytes(b1, b2, b3) == True{} : Bool}) -> {utf8_proof.kind(b1) == 3n : Nat}:
  utf8_proof.valid_kind3.fields(b1, b2, b3, utf8_proof.fields3(b1, b2, b3, UTF8.valid_three_bytes.has_shape(b1, b2, b3, v)))

def utf8_proof.valid_kind4.at(+b1: U32, +b2: U32, +b3: U32, +b4: U32, +t: Word(3n), +et: {b1 == utf8_proof.lead4(t) : U32}) -> {utf8_proof.kind(b1) == 4n : Nat}:
  %Equal.sym(U32, b1, utf8_proof.lead4(t), et) : {utf8_proof.kind(_) == 4n : Nat}
  utf8_proof.kind_lead4(t)

def utf8_proof.valid_kind4.fields(+b1: U32, +b2: U32, +b3: U32, +b4: U32, f: utf8_proof.Fields4(b1, b2, b3, b4)) -> {utf8_proof.kind(b1) == 4n : Nat}:
  (z, f0) = f
  (y, f1) = f0
  (x, f2) = f1
  (+t, f3) = f2
  (et, g0) = f3
  utf8_proof.valid_kind4.at(b1, b2, b3, b4, t, et)

def utf8_proof.valid_kind4(+b1: U32, +b2: U32, +b3: U32, +b4: U32, +v: {UTF8.valid_four_bytes(b1, b2, b3, b4) == True{} : Bool}) -> {utf8_proof.kind(b1) == 4n : Nat}:
  utf8_proof.valid_kind4.fields(b1, b2, b3, b4, utf8_proof.fields4(b1, b2, b3, b4, UTF8.valid_four_bytes.has_shape(b1, b2, b3, b4, v)))

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
        UTF8.false_true(valid))
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
  first: {UTF8.is_two_byte_lead(utf8_proof.first_byte(high)) == True{} : Bool} &
    {(U32.is_ge(utf8_proof.first_byte(high), 194) && U32.is_le(utf8_proof.first_byte(high), 223)) == Bool.not(utf8_proof.fits_one_byte(high)) : Bool},
  second: {UTF8.is_continuation_byte(utf8_proof.second_byte(low)) == True{} : Bool} &
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
    utf8_proof.first_payload(b1, bool_and_left_true(UTF8.is_two_byte_lead(b1), UTF8.is_continuation_byte(b2), shape)),
    utf8_proof.second_payload(b2, bool_and_right_true(UTF8.is_two_byte_lead(b1), UTF8.is_continuation_byte(b2), shape)),
    valid)

# `Bool.or(a, True)` is True whatever `a` is.
def bool_or_true(+a: Bool) -> {Bool.or(a, True{}) == True{} : Bool}:
  match a:
    case False{}: {==}
    case True{}: {==}

def PrefixCompletion(+seq: List<&2, U32>) -> Type:
  Exists(List<&2, U32>, rest =>
    {utf8_proof.bool.is_valid_sequence(List.append(&2, U32, seq, rest)) == True{} : Bool})

# `||` chains
# -----------

def utf8_proof.or_left(+a: Bool, -b: Bool, e: {a == True{} : Bool}) -> {Bool.or(a, b) == True{} : Bool}:
  %Equal.sym(Bool, a, True{}, e) : {Bool.or(_, b) == True{} : Bool}
  {==}

def utf8_proof.or_right(+a: Bool, +b: Bool, e: {b == True{} : Bool}) -> {Bool.or(a, b) == True{} : Bool}:
  %Equal.sym(Bool, b, True{}, e) : {Bool.or(a, _) == True{} : Bool}
  bool_or_true(a)

def utf8_proof.OrT6(+a0: Bool, +a1: Bool, +a2: Bool, +a3: Bool, +a4: Bool, +a5: Bool) -> Type:
  Or({a0 == True{} : Bool}, Or({a1 == True{} : Bool}, Or({a2 == True{} : Bool}, Or({a3 == True{} : Bool}, Or({a4 == True{} : Bool}, {a5 == True{} : Bool})))))

def utf8_proof.or_split6(+a0: Bool, +a1: Bool, +a2: Bool, +a3: Bool, +a4: Bool, +a5: Bool, e: {Bool.or(Bool.or(Bool.or(Bool.or(Bool.or(a0, a1), a2), a3), a4), a5) == True{} : Bool}) -> utf8_proof.OrT6(a0, a1, a2, a3, a4, a5):
  match a0 a1 a2 a3 a4 a5:
    case True{} _ _ _ _ _: Inl{{==}}
    case False{} True{} _ _ _ _: Inr{Inl{{==}}}
    case False{} False{} True{} _ _ _: Inr{Inr{Inl{{==}}}}
    case False{} False{} False{} True{} _ _: Inr{Inr{Inr{Inl{{==}}}}}
    case False{} False{} False{} False{} True{} _: Inr{Inr{Inr{Inr{Inl{{==}}}}}}
    case False{} False{} False{} False{} False{} True{}: Inr{Inr{Inr{Inr{Inr{{==}}}}}}
    case False{} False{} False{} False{} False{} False{}: Empty.absurd(utf8_proof.OrT6(False{}, False{}, False{}, False{}, False{}, False{}), UTF8.false_true(e))

def utf8_proof.OrT3(+a0: Bool, +a1: Bool, +a2: Bool) -> Type:
  Or({a0 == True{} : Bool}, Or({a1 == True{} : Bool}, {a2 == True{} : Bool}))

def utf8_proof.or_split3(+a0: Bool, +a1: Bool, +a2: Bool, e: {Bool.or(Bool.or(a0, a1), a2) == True{} : Bool}) -> utf8_proof.OrT3(a0, a1, a2):
  match a0 a1 a2:
    case True{} _ _: Inl{{==}}
    case False{} True{} _: Inr{Inl{{==}}}
    case False{} False{} True{}: Inr{Inr{{==}}}
    case False{} False{} False{}: Empty.absurd(utf8_proof.OrT3(False{}, False{}, False{}), UTF8.false_true(e))

def utf8_proof.OrT2(+a0: Bool, +a1: Bool) -> Type:
  Or({a0 == True{} : Bool}, {a1 == True{} : Bool})

def utf8_proof.or_split2(+a0: Bool, +a1: Bool, e: {Bool.or(a0, a1) == True{} : Bool}) -> utf8_proof.OrT2(a0, a1):
  match a0 a1:
    case True{} _: Inl{{==}}
    case False{} True{}: Inr{{==}}
    case False{} False{}: Empty.absurd(utf8_proof.OrT2(False{}, False{}), UTF8.false_true(e))

def utf8_proof.prefix.of1(+b1: U32, o: utf8_proof.OrT6(UTF8.valid_one_byte(b1), UTF8.valid_two_bytes(b1, 128), UTF8.valid_three_bytes(b1, 128, 128), UTF8.valid_three_bytes(b1, 191, 128), UTF8.valid_four_bytes(b1, 128, 128, 128), UTF8.valid_four_bytes(b1, 191, 128, 128))) -> PrefixCompletion([b1]):
  match o:
    case Inl{e}: (Nil{}, e)
    case Inr{Inl{e}}: ([128], e)
    case Inr{Inr{Inl{e}}}: ([128, 128], e)
    case Inr{Inr{Inr{Inl{e}}}}: ([191, 128], e)
    case Inr{Inr{Inr{Inr{Inl{e}}}}}: ([128, 128, 128], e)
    case Inr{Inr{Inr{Inr{Inr{e}}}}}: ([191, 128, 128], e)

def utf8_proof.prefix.of2(+b1: U32, +b2: U32, o: utf8_proof.OrT3(UTF8.valid_two_bytes(b1, b2), UTF8.valid_three_bytes(b1, b2, 128), UTF8.valid_four_bytes(b1, b2, 128, 128))) -> PrefixCompletion([b1, b2]):
  match o:
    case Inl{e}: (Nil{}, e)
    case Inr{Inl{e}}: ([128], e)
    case Inr{Inr{e}}: ([128, 128], e)

def utf8_proof.prefix.of3(+b1: U32, +b2: U32, +b3: U32, o: utf8_proof.OrT2(UTF8.valid_three_bytes(b1, b2, b3), UTF8.valid_four_bytes(b1, b2, b3, 128))) -> PrefixCompletion([b1, b2, b3]):
  match o:
    case Inl{e}: (Nil{}, e)
    case Inr{e}: ([128], e)

# A valid sequence prefix is completed by the bytes that the prefix test tried.
def utf8_proof.prefix_completion(+seq: List<&2, U32>,
  begins: {UTF8.is_valid_sequence_prefix(seq) == True{} : Bool}) -> PrefixCompletion(seq):
  match seq:
    case Nil{}:
      Empty.absurd(PrefixCompletion(Nil{}), UTF8.false_true(begins))
    case +b1 <> Nil{}:
      utf8_proof.prefix.of1(b1, utf8_proof.or_split6(UTF8.valid_one_byte(b1), UTF8.valid_two_bytes(b1, 128), UTF8.valid_three_bytes(b1, 128, 128), UTF8.valid_three_bytes(b1, 191, 128), UTF8.valid_four_bytes(b1, 128, 128, 128), UTF8.valid_four_bytes(b1, 191, 128, 128), begins))
    case +b1 <> +b2 <> Nil{}:
      utf8_proof.prefix.of2(b1, b2, utf8_proof.or_split3(UTF8.valid_two_bytes(b1, b2), UTF8.valid_three_bytes(b1, b2, 128), UTF8.valid_four_bytes(b1, b2, 128, 128), begins))
    case +b1 <> +b2 <> +b3 <> Nil{}:
      utf8_proof.prefix.of3(b1, b2, b3, utf8_proof.or_split2(UTF8.valid_three_bytes(b1, b2, b3), UTF8.valid_four_bytes(b1, b2, b3, 128), begins))
    case +b1 <> +b2 <> +b3 <> +b4 <> Nil{}:
      (Nil{}, begins)
    case b1 <> b2 <> b3 <> b4 <> b5 <> rest:
      Empty.absurd(PrefixCompletion(b1 <> b2 <> b3 <> b4 <> b5 <> rest), UTF8.false_true(begins))

def utf8_proof.prefix.mid3(+b1: U32, o: Or({UTF8.valid_three_bytes(b1, 128, 128) == True{} : Bool}, {UTF8.valid_three_bytes(b1, 191, 128) == True{} : Bool})) -> {UTF8.is_valid_sequence_prefix([b1]) == True{} : Bool}:
  match o:
    case Inl{e}: utf8_proof.or_left(Bool.or(Bool.or(Bool.or(Bool.or(UTF8.valid_one_byte(b1), UTF8.valid_two_bytes(b1, 128)), UTF8.valid_three_bytes(b1, 128, 128)), UTF8.valid_three_bytes(b1, 191, 128)), UTF8.valid_four_bytes(b1, 128, 128, 128)), UTF8.valid_four_bytes(b1, 191, 128, 128), utf8_proof.or_left(Bool.or(Bool.or(Bool.or(UTF8.valid_one_byte(b1), UTF8.valid_two_bytes(b1, 128)), UTF8.valid_three_bytes(b1, 128, 128)), UTF8.valid_three_bytes(b1, 191, 128)), UTF8.valid_four_bytes(b1, 128, 128, 128), utf8_proof.or_left(Bool.or(Bool.or(UTF8.valid_one_byte(b1), UTF8.valid_two_bytes(b1, 128)), UTF8.valid_three_bytes(b1, 128, 128)), UTF8.valid_three_bytes(b1, 191, 128), utf8_proof.or_right(Bool.or(UTF8.valid_one_byte(b1), UTF8.valid_two_bytes(b1, 128)), UTF8.valid_three_bytes(b1, 128, 128), e))))
    case Inr{e}: utf8_proof.or_left(Bool.or(Bool.or(Bool.or(Bool.or(UTF8.valid_one_byte(b1), UTF8.valid_two_bytes(b1, 128)), UTF8.valid_three_bytes(b1, 128, 128)), UTF8.valid_three_bytes(b1, 191, 128)), UTF8.valid_four_bytes(b1, 128, 128, 128)), UTF8.valid_four_bytes(b1, 191, 128, 128), utf8_proof.or_left(Bool.or(Bool.or(Bool.or(UTF8.valid_one_byte(b1), UTF8.valid_two_bytes(b1, 128)), UTF8.valid_three_bytes(b1, 128, 128)), UTF8.valid_three_bytes(b1, 191, 128)), UTF8.valid_four_bytes(b1, 128, 128, 128), utf8_proof.or_right(Bool.or(Bool.or(UTF8.valid_one_byte(b1), UTF8.valid_two_bytes(b1, 128)), UTF8.valid_three_bytes(b1, 128, 128)), UTF8.valid_three_bytes(b1, 191, 128), e)))

def utf8_proof.prefix.mid4(+b1: U32, o: Or({UTF8.valid_four_bytes(b1, 128, 128, 128) == True{} : Bool}, {UTF8.valid_four_bytes(b1, 191, 128, 128) == True{} : Bool})) -> {UTF8.is_valid_sequence_prefix([b1]) == True{} : Bool}:
  match o:
    case Inl{e}: utf8_proof.or_left(Bool.or(Bool.or(Bool.or(Bool.or(UTF8.valid_one_byte(b1), UTF8.valid_two_bytes(b1, 128)), UTF8.valid_three_bytes(b1, 128, 128)), UTF8.valid_three_bytes(b1, 191, 128)), UTF8.valid_four_bytes(b1, 128, 128, 128)), UTF8.valid_four_bytes(b1, 191, 128, 128), utf8_proof.or_right(Bool.or(Bool.or(Bool.or(UTF8.valid_one_byte(b1), UTF8.valid_two_bytes(b1, 128)), UTF8.valid_three_bytes(b1, 128, 128)), UTF8.valid_three_bytes(b1, 191, 128)), UTF8.valid_four_bytes(b1, 128, 128, 128), e))
    case Inr{e}: utf8_proof.or_right(Bool.or(Bool.or(Bool.or(Bool.or(UTF8.valid_one_byte(b1), UTF8.valid_two_bytes(b1, 128)), UTF8.valid_three_bytes(b1, 128, 128)), UTF8.valid_three_bytes(b1, 191, 128)), UTF8.valid_four_bytes(b1, 128, 128, 128)), UTF8.valid_four_bytes(b1, 191, 128, 128), e)

def utf8_proof.prefix_from_valid(+b1: U32, +more: List<&2, U32>, +rest: List<&2, U32>,
  valid: {utf8_proof.bool.is_valid_sequence(List.append(&2, U32, b1 <> more, rest)) == True{} : Bool}) ->
  {UTF8.is_valid_sequence_prefix(b1 <> more) == True{} : Bool}:
  match more rest:
    case Nil{} Nil{}:
      utf8_proof.or_left(Bool.or(Bool.or(Bool.or(Bool.or(UTF8.valid_one_byte(b1), UTF8.valid_two_bytes(b1, 128)), UTF8.valid_three_bytes(b1, 128, 128)), UTF8.valid_three_bytes(b1, 191, 128)), UTF8.valid_four_bytes(b1, 128, 128, 128)), UTF8.valid_four_bytes(b1, 191, 128, 128), utf8_proof.or_left(Bool.or(Bool.or(Bool.or(UTF8.valid_one_byte(b1), UTF8.valid_two_bytes(b1, 128)), UTF8.valid_three_bytes(b1, 128, 128)), UTF8.valid_three_bytes(b1, 191, 128)), UTF8.valid_four_bytes(b1, 128, 128, 128), utf8_proof.or_left(Bool.or(Bool.or(UTF8.valid_one_byte(b1), UTF8.valid_two_bytes(b1, 128)), UTF8.valid_three_bytes(b1, 128, 128)), UTF8.valid_three_bytes(b1, 191, 128), utf8_proof.or_left(Bool.or(UTF8.valid_one_byte(b1), UTF8.valid_two_bytes(b1, 128)), UTF8.valid_three_bytes(b1, 128, 128), utf8_proof.or_left(UTF8.valid_one_byte(b1), UTF8.valid_two_bytes(b1, 128), valid)))))
    case Nil{} +b2 <> Nil{}:
      utf8_proof.or_left(Bool.or(Bool.or(Bool.or(Bool.or(UTF8.valid_one_byte(b1), UTF8.valid_two_bytes(b1, 128)), UTF8.valid_three_bytes(b1, 128, 128)), UTF8.valid_three_bytes(b1, 191, 128)), UTF8.valid_four_bytes(b1, 128, 128, 128)), UTF8.valid_four_bytes(b1, 191, 128, 128), utf8_proof.or_left(Bool.or(Bool.or(Bool.or(UTF8.valid_one_byte(b1), UTF8.valid_two_bytes(b1, 128)), UTF8.valid_three_bytes(b1, 128, 128)), UTF8.valid_three_bytes(b1, 191, 128)), UTF8.valid_four_bytes(b1, 128, 128, 128), utf8_proof.or_left(Bool.or(Bool.or(UTF8.valid_one_byte(b1), UTF8.valid_two_bytes(b1, 128)), UTF8.valid_three_bytes(b1, 128, 128)), UTF8.valid_three_bytes(b1, 191, 128), utf8_proof.or_left(Bool.or(UTF8.valid_one_byte(b1), UTF8.valid_two_bytes(b1, 128)), UTF8.valid_three_bytes(b1, 128, 128), utf8_proof.or_right(UTF8.valid_one_byte(b1), UTF8.valid_two_bytes(b1, 128), utf8_proof.any_continuation(b1, b2, valid))))))
    case Nil{} +b2 <> +b3 <> Nil{}:
      utf8_proof.prefix.mid3(b1, utf8_proof.any3_mid(b1, b2, b3, valid))
    case Nil{} +b2 <> +b3 <> +b4 <> Nil{}:
      utf8_proof.prefix.mid4(b1, utf8_proof.any4_mid(b1, b2, b3, b4, valid))
    case Nil{} b2 <> b3 <> b4 <> b5 <> after:
      Empty.absurd({UTF8.is_valid_sequence_prefix(b1 <> Nil{}) == True{} : Bool}, UTF8.false_true(valid))
    case +b2 <> Nil{} Nil{}:
      utf8_proof.or_left(Bool.or(UTF8.valid_two_bytes(b1, b2), UTF8.valid_three_bytes(b1, b2, 128)), UTF8.valid_four_bytes(b1, b2, 128, 128), utf8_proof.or_left(UTF8.valid_two_bytes(b1, b2), UTF8.valid_three_bytes(b1, b2, 128), valid))
    case +b2 <> Nil{} +b3 <> Nil{}:
      utf8_proof.or_left(Bool.or(UTF8.valid_two_bytes(b1, b2), UTF8.valid_three_bytes(b1, b2, 128)), UTF8.valid_four_bytes(b1, b2, 128, 128), utf8_proof.or_right(UTF8.valid_two_bytes(b1, b2), UTF8.valid_three_bytes(b1, b2, 128), utf8_proof.any3_last(b1, b2, b3, valid)))
    case +b2 <> Nil{} +b3 <> +b4 <> Nil{}:
      utf8_proof.or_right(Bool.or(UTF8.valid_two_bytes(b1, b2), UTF8.valid_three_bytes(b1, b2, 128)), UTF8.valid_four_bytes(b1, b2, 128, 128), utf8_proof.any4_third(b1, b2, b3, b4, valid))
    case +b2 <> Nil{} b3 <> b4 <> b5 <> after:
      Empty.absurd({UTF8.is_valid_sequence_prefix(b1 <> [b2]) == True{} : Bool}, UTF8.false_true(valid))
    case +b2 <> +b3 <> Nil{} Nil{}:
      utf8_proof.or_left(UTF8.valid_three_bytes(b1, b2, b3), UTF8.valid_four_bytes(b1, b2, b3, 128), valid)
    case +b2 <> +b3 <> Nil{} +b4 <> Nil{}:
      utf8_proof.or_right(UTF8.valid_three_bytes(b1, b2, b3), UTF8.valid_four_bytes(b1, b2, b3, 128), utf8_proof.any4_last(b1, b2, b3, b4, valid))
    case +b2 <> +b3 <> Nil{} b4 <> b5 <> after:
      Empty.absurd({UTF8.is_valid_sequence_prefix(b1 <> [b2, b3]) == True{} : Bool}, UTF8.false_true(valid))
    case +b2 <> +b3 <> +b4 <> Nil{} Nil{}:
      valid
    case +b2 <> +b3 <> +b4 <> Nil{} b5 <> after:
      Empty.absurd({UTF8.is_valid_sequence_prefix(b1 <> [b2, b3, b4]) == True{} : Bool}, UTF8.false_true(valid))
    case b2 <> b3 <> b4 <> b5 <> after _:
      Empty.absurd({UTF8.is_valid_sequence_prefix(b1 <> (b2 <> b3 <> b4 <> b5 <> after)) == True{} : Bool}, UTF8.false_true(valid))

def utf8_proof.prefix_from_completion(+b1: U32, +more: List<&2, U32>,
  completion: PrefixCompletion(b1 <> more)) ->
  {UTF8.is_valid_sequence_prefix(b1 <> more) == True{} : Bool}:
  (+rest, valid) = completion
  utf8_proof.prefix_from_valid(b1, more, rest, valid)

def utf8_proof.impl.is_valid_sequence_prefix(+b1: U32, +more: List<&2, U32>) ->
  ({UTF8.is_valid_sequence_prefix(b1 <> more) == True{} : Bool} -> (Exists(List<&2, U32>, rest => {utf8_proof.bool.is_valid_sequence(List.append(&2, U32, b1 <> more, rest)) == True{} : Bool}))) &
  ((Exists(List<&2, U32>, rest => {utf8_proof.bool.is_valid_sequence(List.append(&2, U32, b1 <> more, rest)) == True{} : Bool})) -> {UTF8.is_valid_sequence_prefix(b1 <> more) == True{} : Bool}):
  (begins => utf8_proof.prefix_completion(b1 <> more, begins),
   completion => utf8_proof.prefix_from_completion(b1, more, completion))

def utf8_proof.impl.empty_not_valid_sequence_prefix() ->
  {UTF8.is_valid_sequence_prefix(Nil{}) == False{} : Bool}:
  {==}

# Decoding a valid sequence
# -------------------------
#
# The scalar that a valid one- or two-byte sequence encodes, or None.
# `utf8_proof.next_scalar` computes with these, and `utf8_proof.Decodes`
# relates them to `Laws.encodes`.

def utf8_proof.one_byte_scalar.if(+byte: U32, valid: Bool,
  -checked: {UTF8.valid_one_byte(byte) == valid : Bool}) -> Maybe<&2, U32>:
  match valid:
    case False{}:
      None{}
    case True{}:
      Some{UTF8.decode_one_byte(byte, utf8_proof.valid_one_byte_has_shape(byte, checked))}

def utf8_proof.one_byte_scalar(+byte: U32) -> Maybe<&2, U32>:
  utf8_proof.one_byte_scalar.if(byte, UTF8.valid_one_byte(byte), {==})

def utf8_proof.two_byte_scalar.if(+b1: U32, +b2: U32, valid: Bool,
  -checked: {UTF8.valid_two_bytes(b1, b2) == valid : Bool}) -> Maybe<&2, U32>:
  match valid:
    case False{}:
      None{}
    case True{}:
      Some{UTF8.decode_two_bytes(b1, b2, utf8_proof.valid_two_bytes_has_shape(b1, b2, checked))}

def utf8_proof.two_byte_scalar(+b1: U32, +b2: U32) -> Maybe<&2, U32>:
  utf8_proof.two_byte_scalar.if(b1, b2, UTF8.valid_two_bytes(b1, b2), {==})

# The implementation's scalar functions agree with these
# -------------------------------------------------------

def utf8_proof.true_false(e: {True{} == False{} : Bool}) -> Empty:
  UTF8.false_true(Equal.sym(Bool, True{}, False{}, e))

# Both scalar functions branch on validity tests that the validity laws
# make equal, and decoding does not depend on its proof argument.
def utf8_proof.one_scalar_agrees(+byte: U32, impl: Bool,
  -impl_checked: {UTF8.valid_one_byte(byte) == impl : Bool}, spec: Bool,
  -spec_checked: {UTF8.valid_one_byte(byte) == spec : Bool},
  same: {impl == spec : Bool}) ->
  {UTF8.one_byte_scalar.if(byte, impl, impl_checked) ==
    utf8_proof.one_byte_scalar.if(byte, spec, spec_checked) : Maybe<&2, U32>}:
  match impl spec:
    case False{} False{}: {==}
    case True{} True{}: {==}
    case False{} True{}:
      Empty.absurd({None{} == Some{UTF8.decode_one_byte(byte, utf8_proof.valid_one_byte_has_shape(byte, spec_checked))} : Maybe<&2, U32>},
        UTF8.false_true(same))
    case True{} False{}:
      Empty.absurd({Some{UTF8.decode_one_byte(byte, impl_checked)} == None{} : Maybe<&2, U32>},
        utf8_proof.true_false(same))

def utf8_proof.two_scalar_agrees(+b1: U32, +b2: U32, impl: Bool,
  -impl_checked: {UTF8.valid_two_bytes(b1, b2) == impl : Bool}, spec: Bool,
  -spec_checked: {UTF8.valid_two_bytes(b1, b2) == spec : Bool},
  same: {impl == spec : Bool}) ->
  {UTF8.two_byte_scalar.if(b1, b2, impl, impl_checked) ==
    utf8_proof.two_byte_scalar.if(b1, b2, spec, spec_checked) : Maybe<&2, U32>}:
  match impl spec:
    case False{} False{}: {==}
    case True{} True{}: {==}
    case False{} True{}:
      Empty.absurd({None{} == Some{UTF8.decode_two_bytes(b1, b2, utf8_proof.valid_two_bytes_has_shape(b1, b2, spec_checked))} : Maybe<&2, U32>},
        UTF8.false_true(same))
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

# What feeding should give: the byte loop's state and text.
def utf8_proof.fed_step(step: UTF8.decode_buffer.Step()) -> UTF8.DecodeState() & String:
  UTF8.decode_buffer.result(step)

def utf8_proof.fed_prepend(+text: String, step: UTF8.decode_buffer.Step()) ->
  {Laws.feed.prepend(text, utf8_proof.fed_step(step)) ==
    utf8_proof.fed_step(UTF8.decode_buffer.prepend(text, step)) : UTF8.DecodeState() & String}:
  (more, pending) = step
  {==}

def Laws.utf8_decode_buffer_all_bytes(bytes):
  {==}

def utf8_proof.feed_step(+rest: List<&2, List<&2, U32>>, -valid: Laws.all_buffers_bytes(rest),
  stepped: UTF8.decode_buffer.Step(),
  same: @q: List<&2, U32> ->
    {Laws.feed(rest, valid, q) ==
      utf8_proof.fed_step(UTF8.decode_buffer.bytes(List.concat(&2, U32, rest), q)) : UTF8.DecodeState() & String}) ->
  {Laws.feed.then(UTF8.decode_buffer.result(stepped), s => Laws.feed(rest, valid, s)) ==
    utf8_proof.fed_step(UTF8.decode_buffer.then(stepped,
      q => UTF8.decode_buffer.bytes(List.concat(&2, U32, rest), q))) : UTF8.DecodeState() & String}:
  (+text, +q) = stepped
  %Equal.sym(UTF8.DecodeState() & String, Laws.feed(rest, valid, q),
      utf8_proof.fed_step(UTF8.decode_buffer.bytes(List.concat(&2, U32, rest), q)), same(q)) :
    {Laws.feed.prepend(text, _) ==
      utf8_proof.fed_step(UTF8.decode_buffer.prepend(text, UTF8.decode_buffer.bytes(List.concat(&2, U32, rest), q))) : UTF8.DecodeState() & String}
  utf8_proof.fed_prepend(text, UTF8.decode_buffer.bytes(List.concat(&2, U32, rest), q))

# Feeding any list of buffers gives what the byte loop gives for their
# concatenation.
def utf8_proof.feed_agrees(+buffers: List<&2, List<&2, U32>>, -valid: Laws.all_buffers_bytes(buffers),
  +pending: List<&2, U32>) ->
  {Laws.feed(buffers, valid, pending) ==
    utf8_proof.fed_step(UTF8.decode_buffer.bytes(List.concat(&2, U32, buffers), pending)) : UTF8.DecodeState() & String}:
  match buffers:
    case Nil{}: {==}
    case +buffer <> +rest:
      %Equal.sym(UTF8.decode_buffer.Step(), UTF8.decode_buffer.bytes(List.append(&2, U32, buffer, List.concat(&2, U32, rest)), pending),
          UTF8.decode_buffer.then(UTF8.decode_buffer.bytes(buffer, pending), q => UTF8.decode_buffer.bytes(List.concat(&2, U32, rest), q)),
          utf8_proof.go_append(buffer, List.concat(&2, U32, rest), pending)) :
        {Laws.feed(buffer <> rest, valid, pending) == utf8_proof.fed_step(_) : UTF8.DecodeState() & String}
      utf8_proof.feed_step(rest, Laws.all_buffers_bytes.tail(buffer, rest, valid), UTF8.decode_buffer.bytes(buffer, pending),
        q => utf8_proof.feed_agrees(rest, Laws.all_buffers_bytes.tail(buffer, rest, valid), q))

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

# Every non-empty prefix of a valid sequence prefix is one too, by
# `utf8_proof.impl.is_valid_sequence_prefix`.
def utf8_proof.valid_regroup(+x: List<&2, U32>, +y: List<&2, U32>, +z: List<&2, U32>,
  valid: {utf8_proof.bool.is_valid_sequence(List.append(&2, U32, List.append(&2, U32, x, y), z)) == True{} : Bool}) ->
  {utf8_proof.bool.is_valid_sequence(List.append(&2, U32, x, List.append(&2, U32, y, z))) == True{} : Bool}:
  %utf8_proof.append_assoc(x, y, z) : {utf8_proof.bool.is_valid_sequence(_) == True{} : Bool}
  valid

def utf8_proof.prefix_closed.completion(+x1: U32, +xs: List<&2, U32>, +y: List<&2, U32>,
  completion: PrefixCompletion(List.append(&2, U32, x1 <> xs, y))) ->
  {UTF8.is_valid_sequence_prefix(x1 <> xs) == True{} : Bool}:
  (+rest, valid) = completion
  utf8_proof.prefix_from_completion(x1, xs,
    (List.append(&2, U32, y, rest), utf8_proof.valid_regroup(x1 <> xs, y, rest, valid)))

def utf8_proof.prefix_closed(+x1: U32, +xs: List<&2, U32>, +y: List<&2, U32>,
  begins: {UTF8.is_valid_sequence_prefix(List.append(&2, U32, x1 <> xs, y)) == True{} : Bool}) ->
  {UTF8.is_valid_sequence_prefix(x1 <> xs) == True{} : Bool}:
  utf8_proof.prefix_closed.completion(x1, xs, y,
    utf8_proof.prefix_completion(List.append(&2, U32, x1 <> xs, y), begins))

# The contrapositive of prefix closure.
def utf8_proof.not_prefix_extended.if(+b1: U32, +more: List<&2, U32>, +extra: List<&2, U32>,
  invalid: {UTF8.is_valid_sequence_prefix(b1 <> more) == False{} : Bool}, valid: Bool,
  checked: {UTF8.is_valid_sequence_prefix(List.append(&2, U32, b1 <> more, extra)) == valid : Bool}) ->
  {UTF8.is_valid_sequence_prefix(List.append(&2, U32, b1 <> more, extra)) == False{} : Bool}:
  match valid:
    case False{}:
      checked
    case True{}:
      Empty.absurd({UTF8.is_valid_sequence_prefix(List.append(&2, U32, b1 <> more, extra)) == False{} : Bool},
        utf8_proof.true_false(Equal.trans(Bool, True{}, UTF8.is_valid_sequence_prefix(b1 <> more), False{},
          Equal.sym(Bool, UTF8.is_valid_sequence_prefix(b1 <> more), True{},
            utf8_proof.prefix_closed(b1, more, extra, checked)),
          invalid)))

def utf8_proof.impl.not_valid_sequence_prefix_extended(+b1: U32, +more: List<&2, U32>, +extra: List<&2, U32>, invalid: {UTF8.is_valid_sequence_prefix(b1 <> more) == False{} : Bool}) ->
  {UTF8.is_valid_sequence_prefix(List.append(&2, U32, b1 <> more, extra)) == False{} : Bool}:
  utf8_proof.not_prefix_extended.if(b1, more, extra, invalid,
    UTF8.is_valid_sequence_prefix(List.append(&2, U32, b1 <> more, extra)), {==})

# `a` followed by `c` is non-empty, so prefix closure applies to it.
def utf8_proof.prefix_closed_snoc(+a: List<&2, U32>, +c: U32, +extra: List<&2, U32>,
  begins: {UTF8.is_valid_sequence_prefix(List.append(&2, U32, List.append(&2, U32, a, [c]), extra)) == True{} : Bool}) ->
  {UTF8.is_valid_sequence_prefix(List.append(&2, U32, a, [c])) == True{} : Bool}:
  match a:
    case Nil{}:
      utf8_proof.prefix_closed(c, Nil{}, extra, begins)
    case +h <> +t:
      utf8_proof.prefix_closed(h, List.append(&2, U32, t, [c]), extra, begins)

# The byte that follows `prefix` in `bytes`, or None if there is none.
# Only the length of `prefix` matters.
def utf8_proof.next_byte_after(bytes: List<&2, U32>, prefix: List<&2, U32>) ->
  Maybe<&2, U32>:
  match bytes prefix:
    case Nil{} _:
      None{}
    case b <> rest Nil{}:
      Some{b}
    case b <> rest p <> ps:
      utf8_proof.next_byte_after(rest, ps)

# `subpart` cannot be extended by `next`, the byte after it in the
# input, if any: either there is no next byte, or `subpart` followed by
# `next` is not a valid sequence prefix.  With prefix closure this gives
# `utf8_proof.bool.maximal_subpart.longer_not_valid_prefix`; see
# `utf8_proof.longer_not_valid_from_not_extended`.
def utf8_proof.not_extended_by(subpart: List<&2, U32>, next: Maybe<&2, U32>) -> Type:
  match next:
    case None{}:
      Unit
    case Some{b}:
      {UTF8.is_valid_sequence_prefix(List.append(&2, U32, subpart, [b])) == False{} : Bool}

# `a` is shorter than `b`, both prefixes of `bytes`: `b` is `a` followed
# by `c` and more, and `c` is the byte after `a`.
def utf8_proof.Shorter(+a: List<&2, U32>, +b: List<&2, U32>, +bytes: List<&2, U32>) -> Type:
  Exists(U32, c => Exists(List<&2, U32>, extra =>
    {b == List.append(&2, U32, a, c <> extra) : List<&2, U32>} &
    {utf8_proof.next_byte_after(bytes, a) == Some{c} : Maybe<&2, U32>}))

# Two prefixes of the same bytes are equal or one is shorter.
def utf8_proof.Compared(+s1: List<&2, U32>, +s2: List<&2, U32>, +bytes: List<&2, U32>) -> Type:
  Or({s1 == s2 : List<&2, U32>},
    Or(utf8_proof.Shorter(s1, s2, bytes), utf8_proof.Shorter(s2, s1, bytes)))

def utf8_proof.next_after_nil(+h: U32, +rest: List<&2, U32>, +bytes: List<&2, U32>,
  e: {h <> rest == bytes : List<&2, U32>}) ->
  {utf8_proof.next_byte_after(bytes, Nil{}) == Some{h} : Maybe<&2, U32>}:
  %e : {utf8_proof.next_byte_after(_, Nil{}) == Some{h} : Maybe<&2, U32>}
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
  next: {utf8_proof.next_byte_after(bytes, a) == Some{c} : Maybe<&2, U32>},
  not_extended: utf8_proof.not_extended_by(a, utf8_proof.next_byte_after(bytes, a))) ->
  utf8_proof.not_extended_by(a, Some{c}):
  %next : utf8_proof.not_extended_by(a, _)
  not_extended

def utf8_proof.prefix_regroup(+a: List<&2, U32>, +c: U32, +extra: List<&2, U32>,
  +b: List<&2, U32>, eq: {b == List.append(&2, U32, a, c <> extra) : List<&2, U32>},
  begins: {UTF8.is_valid_sequence_prefix(b) == True{} : Bool}) ->
  {UTF8.is_valid_sequence_prefix(List.append(&2, U32, List.append(&2, U32, a, [c]), extra)) == True{} : Bool}:
  %Equal.sym(List<&2, U32>, List.append(&2, U32, List.append(&2, U32, a, [c]), extra),
      List.append(&2, U32, a, List.append(&2, U32, [c], extra)), utf8_proof.append_assoc(a, [c], extra)) :
    {UTF8.is_valid_sequence_prefix(_) == True{} : Bool}
  %eq : {UTF8.is_valid_sequence_prefix(_) == True{} : Bool}
  begins

def utf8_proof.prefix_along(+x: List<&2, U32>, +y: List<&2, U32>, +bytes: List<&2, U32>,
  eq: {x == y : List<&2, U32>}, prefix: Laws.is_prefix(x, bytes)) -> Laws.is_prefix(y, bytes):
  %eq : Laws.is_prefix(_, bytes)
  prefix

def utf8_proof.valid_prefix_along(+x: List<&2, U32>, +y: List<&2, U32>,
  eq: {x == y : List<&2, U32>},
  begins: {UTF8.is_valid_sequence_prefix(x) == True{} : Bool}) ->
  {UTF8.is_valid_sequence_prefix(y) == True{} : Bool}:
  %eq : {UTF8.is_valid_sequence_prefix(_) == True{} : Bool}
  begins

# A valid sequence prefix of `bytes` longer than `a` contradicts
# `utf8_proof.bool.maximal_subpart.longer_not_valid_prefix(a, bytes)`.
def utf8_proof.longer_contradicts(+a: List<&2, U32>, +b: List<&2, U32>, +bytes: List<&2, U32>,
  prefix_b: Laws.is_prefix(b, bytes),
  begins_b: {UTF8.is_valid_sequence_prefix(b) == True{} : Bool},
  longer_not_valid_a: utf8_proof.bool.maximal_subpart.longer_not_valid_prefix(a, bytes),
  shorter: utf8_proof.Shorter(a, b, bytes)) -> Empty:
  (+c, more) = shorter
  (+extra, facts) = more
  (+eq, next) = facts
  +ac = List.append(&2, U32, a, c <> extra)
  not_begins = longer_not_valid_a(c, extra, utf8_proof.prefix_along(b, ac, bytes, eq, prefix_b))
  begins_ac = utf8_proof.valid_prefix_along(b, ac, eq, begins_b)
  utf8_proof.true_false(Equal.trans(Bool, True{}, UTF8.is_valid_sequence_prefix(ac), False{},
    Equal.sym(Bool, UTF8.is_valid_sequence_prefix(ac), True{}, begins_ac), not_begins))

def utf8_proof.sequence_prefix_unique.compared(+s1: List<&2, U32>, +s2: List<&2, U32>,
  +bytes: List<&2, U32>,
  +r1: List<&2, U32>, +r2: List<&2, U32>,
  +e1: {List.append(&2, U32, s1, r1) == bytes : List<&2, U32>},
  +e2: {List.append(&2, U32, s2, r2) == bytes : List<&2, U32>},
  begins1: {UTF8.is_valid_sequence_prefix(s1) == True{} : Bool},
  begins2: {UTF8.is_valid_sequence_prefix(s2) == True{} : Bool},
  longer_not_valid1: utf8_proof.bool.maximal_subpart.longer_not_valid_prefix(s1, bytes),
  longer_not_valid2: utf8_proof.bool.maximal_subpart.longer_not_valid_prefix(s2, bytes),
  compared: utf8_proof.Compared(s1, s2, bytes)) -> {s1 == s2 : List<&2, U32>}:
  match compared:
    case Inl{same}:
      same
    case Inr{Inl{shorter}}:
      Empty.absurd({s1 == s2 : List<&2, U32>},
        utf8_proof.longer_contradicts(s1, s2, bytes, (r2, e2), begins2, longer_not_valid1, shorter))
    case Inr{Inr{shorter}}:
      Empty.absurd({s1 == s2 : List<&2, U32>},
        utf8_proof.longer_contradicts(s2, s1, bytes, (r1, e1), begins1, longer_not_valid2, shorter))

def utf8_proof.sequence_prefix_unique.split(+s1: List<&2, U32>, +s2: List<&2, U32>,
  +bytes: List<&2, U32>,
  +r1: List<&2, U32>, +r2: List<&2, U32>,
  +e1: {List.append(&2, U32, s1, r1) == bytes : List<&2, U32>},
  +e2: {List.append(&2, U32, s2, r2) == bytes : List<&2, U32>},
  begins1: {UTF8.is_valid_sequence_prefix(s1) == True{} : Bool},
  begins2: {UTF8.is_valid_sequence_prefix(s2) == True{} : Bool},
  longer_not_valid1: utf8_proof.bool.maximal_subpart.longer_not_valid_prefix(s1, bytes),
  longer_not_valid2: utf8_proof.bool.maximal_subpart.longer_not_valid_prefix(s2, bytes)) -> {s1 == s2 : List<&2, U32>}:
  utf8_proof.sequence_prefix_unique.compared(s1, s2, bytes, r1, r2, e1, e2,
    begins1, begins2, longer_not_valid1, longer_not_valid2,
    utf8_proof.compare(s1, s2, bytes, r1, r2, e1, e2))

def utf8_proof.sequence_prefix_unique(+b1: U32, +more: List<&2, U32>,
  -first: {UTF8.is_valid_sequence_prefix([b1]) == True{} : Bool},
  +s1: List<&2, U32>, +s2: List<&2, U32>,
  p1: utf8_proof.bool.maximal_subpart.sequence_prefix(b1, more, s1),
  p2: utf8_proof.bool.maximal_subpart.sequence_prefix(b1, more, s2)) -> {s1 == s2 : List<&2, U32>}:
  (prefix1, facts1) = p1
  (+r1, e1) = prefix1
  (begins1, longer_not_valid1) = facts1
  (prefix2, facts2) = p2
  (+r2, e2) = prefix2
  (begins2, longer_not_valid2) = facts2
  utf8_proof.sequence_prefix_unique.split(s1, s2, b1 <> more, r1, r2, e1, e2,
    begins1, begins2, longer_not_valid1, longer_not_valid2)

def utf8_proof.maximal_subpart_unique.if(+b1: U32, +more: List<&2, U32>, begins: Bool,
  -checked: {UTF8.is_valid_sequence_prefix([b1]) == begins : Bool},
  +s1: List<&2, U32>, +s2: List<&2, U32>,
  p1: utf8_proof.bool.maximal_subpart.if(b1, more, begins, s1),
  p2: utf8_proof.bool.maximal_subpart.if(b1, more, begins, s2)) -> {s1 == s2 : List<&2, U32>}:
  match begins:
    case True{}:
      utf8_proof.sequence_prefix_unique(b1, more, checked, s1, s2, p1, p2)
    case False{}:
      Equal.trans(List<&2, U32>, s1, [b1], s2, p1, Equal.sym(List<&2, U32>, s2, [b1], p2))

def utf8_proof.bool.maximal_subpart_unique(+b1: U32, +more: List<&2, U32>, +s1: List<&2, U32>, +s2: List<&2, U32>, p1: utf8_proof.bool.maximal_subpart(b1, more, s1), p2: utf8_proof.bool.maximal_subpart(b1, more, s2)) ->
  {s1 == s2 : List<&2, U32>}:
  utf8_proof.maximal_subpart_unique.if(b1, more, UTF8.is_valid_sequence_prefix([b1]), {==},
    s1, s2, p1, p2)

# Existence: scan forward from `[b1]`, extending the prefix while it
# is still a valid sequence prefix.

# What the scan finds: a valid sequence prefix at the front of `bytes`
# that the next byte does not extend.
def utf8_proof.Unextended(+bytes: List<&2, U32>) -> Type:
  Exists(List<&2, U32>, sub =>
    Laws.is_prefix(sub, bytes) &
    {UTF8.is_valid_sequence_prefix(sub) == True{} : Bool} &
    utf8_proof.not_extended_by(sub, utf8_proof.next_byte_after(bytes, sub)))

def utf8_proof.next_after_append(+s: List<&2, U32>, +r: List<&2, U32>) ->
  {utf8_proof.next_byte_after(List.append(&2, U32, s, r), s) == List.head(&2, U32, r) : Maybe<&2, U32>}:
  match s:
    case Nil{}:
      match r:
        case Nil{}: {==}
        case x <> xs: {==}
    case +h <> +t:
      utf8_proof.next_after_append(t, r)

def utf8_proof.next_after(+s: List<&2, U32>, +r: List<&2, U32>, +bytes: List<&2, U32>,
  e: {List.append(&2, U32, s, r) == bytes : List<&2, U32>}) ->
  {utf8_proof.next_byte_after(bytes, s) == List.head(&2, U32, r) : Maybe<&2, U32>}:
  %e : {utf8_proof.next_byte_after(_, s) == List.head(&2, U32, r) : Maybe<&2, U32>}
  utf8_proof.next_after_append(s, r)

def utf8_proof.longest_from_next(+s: List<&2, U32>, +bytes: List<&2, U32>,
  -next: Maybe<&2, U32>, same: {next == utf8_proof.next_byte_after(bytes, s) : Maybe<&2, U32>},
  not_extended: utf8_proof.not_extended_by(s, next)) ->
  utf8_proof.not_extended_by(s, utf8_proof.next_byte_after(bytes, s)):
  %same : utf8_proof.not_extended_by(s, _)
  not_extended

# `s` is a valid sequence prefix and `s` followed by `c` is not.
def utf8_proof.longest_stop(+s: List<&2, U32>, +bytes: List<&2, U32>, +c: U32,
  +r: List<&2, U32>, +e: {List.append(&2, U32, s, c <> r) == bytes : List<&2, U32>},
  begins_s: {UTF8.is_valid_sequence_prefix(s) == True{} : Bool},
  not_more: {UTF8.is_valid_sequence_prefix(List.append(&2, U32, s, [c])) == False{} : Bool}) ->
  utf8_proof.Unextended(bytes):
  (s, ((c <> r, e), (begins_s,
    utf8_proof.longest_from_next(s, bytes, Some{c},
      Equal.sym(Maybe<&2, U32>, utf8_proof.next_byte_after(bytes, s), Some{c},
        utf8_proof.next_after(s, c <> r, bytes, e)),
      not_more))))

def utf8_proof.regroup_prefix(+s: List<&2, U32>, +c: U32, +r: List<&2, U32>,
  +bytes: List<&2, U32>, e: {List.append(&2, U32, s, c <> r) == bytes : List<&2, U32>}) ->
  {List.append(&2, U32, List.append(&2, U32, s, [c]), r) == bytes : List<&2, U32>}:
  Equal.trans(List<&2, U32>, List.append(&2, U32, List.append(&2, U32, s, [c]), r),
    List.append(&2, U32, s, c <> r), bytes, utf8_proof.append_assoc(s, [c], r), e)

def utf8_proof.longest_step(+s: List<&2, U32>, +bytes: List<&2, U32>, +c: U32,
  +r: List<&2, U32>, +e: {List.append(&2, U32, s, c <> r) == bytes : List<&2, U32>},
  begins_s: {UTF8.is_valid_sequence_prefix(s) == True{} : Bool}, more: Bool,
  checked: {UTF8.is_valid_sequence_prefix(List.append(&2, U32, s, [c])) == more : Bool},
  longer: {UTF8.is_valid_sequence_prefix(List.append(&2, U32, s, [c])) == True{} : Bool} ->
    utf8_proof.Unextended(bytes)) ->
  utf8_proof.Unextended(bytes):
  match more:
    case False{}: utf8_proof.longest_stop(s, bytes, c, r, e, begins_s, checked)
    case True{}: longer(checked)

# `s` is a valid sequence prefix at the front of `bytes` and `r` is the
# rest; some prefix at least as long is the longest.
def utf8_proof.longest_from(+r: List<&2, U32>, +s: List<&2, U32>, +bytes: List<&2, U32>,
  +e: {List.append(&2, U32, s, r) == bytes : List<&2, U32>},
  begins_s: {UTF8.is_valid_sequence_prefix(s) == True{} : Bool}) ->
  utf8_proof.Unextended(bytes):
  match r:
    case Nil{}:
      (s, ((Nil{}, e), (begins_s,
        utf8_proof.longest_from_next(s, bytes, None{},
          Equal.sym(Maybe<&2, U32>, utf8_proof.next_byte_after(bytes, s), None{},
            utf8_proof.next_after(s, Nil{}, bytes, e)),
          Unit{}))))
    case +c <> +rest:
      utf8_proof.longest_step(s, bytes, c, rest, e, begins_s,
        UTF8.is_valid_sequence_prefix(List.append(&2, U32, s, [c])), {==},
        t => utf8_proof.longest_from(rest, List.append(&2, U32, s, [c]), bytes,
          utf8_proof.regroup_prefix(s, c, rest, bytes, e), t))

# `s` followed by `c` and `extra` is a prefix of `bytes`.  If it were a
# valid sequence prefix, then by prefix closure so would `s` followed by
# `c` be; but `c` is the byte after `s`, which does not extend `s`.
def utf8_proof.longer_not_valid_at.if(+s: List<&2, U32>, +bytes: List<&2, U32>, +c: U32, +extra: List<&2, U32>,
  not_extended: utf8_proof.not_extended_by(s, utf8_proof.next_byte_after(bytes, s)),
  valid: Bool, checked: {UTF8.is_valid_sequence_prefix(List.append(&2, U32, s, c <> extra)) == valid : Bool},
  longer: Laws.is_prefix(List.append(&2, U32, s, c <> extra), bytes)) ->
  {UTF8.is_valid_sequence_prefix(List.append(&2, U32, s, c <> extra)) == False{} : Bool}:
  match valid:
    case False{}:
      checked
    case True{}:
      (+r, e) = longer
      +begins_sc = utf8_proof.prefix_closed_snoc(s, c, extra,
        utf8_proof.prefix_regroup(s, c, extra, List.append(&2, U32, s, c <> extra), {==}, checked))
      next = utf8_proof.next_after(s, c <> List.append(&2, U32, extra, r), bytes,
        Equal.trans(List<&2, U32>, List.append(&2, U32, s, c <> List.append(&2, U32, extra, r)),
          List.append(&2, U32, List.append(&2, U32, s, c <> extra), r), bytes,
          Equal.sym(List<&2, U32>, List.append(&2, U32, List.append(&2, U32, s, c <> extra), r),
            List.append(&2, U32, s, c <> List.append(&2, U32, extra, r)),
            utf8_proof.append_assoc(s, c <> extra, r)),
          e))
      not_more = utf8_proof.longest_next(s, bytes, c, next, not_extended)
      Empty.absurd({UTF8.is_valid_sequence_prefix(List.append(&2, U32, s, c <> extra)) == False{} : Bool},
        utf8_proof.true_false(Equal.trans(Bool, True{}, UTF8.is_valid_sequence_prefix(List.append(&2, U32, s, [c])), False{},
          Equal.sym(Bool, UTF8.is_valid_sequence_prefix(List.append(&2, U32, s, [c])), True{}, begins_sc),
          not_more)))

def utf8_proof.longer_not_valid_at(+s: List<&2, U32>, +bytes: List<&2, U32>, +c: U32, +extra: List<&2, U32>,
  not_extended: utf8_proof.not_extended_by(s, utf8_proof.next_byte_after(bytes, s)),
  longer: Laws.is_prefix(List.append(&2, U32, s, c <> extra), bytes)) ->
  {UTF8.is_valid_sequence_prefix(List.append(&2, U32, s, c <> extra)) == False{} : Bool}:
  utf8_proof.longer_not_valid_at.if(s, bytes, c, extra, not_extended,
    UTF8.is_valid_sequence_prefix(List.append(&2, U32, s, c <> extra)), {==}, longer)

# If the next byte does not extend a prefix, then by prefix closure no
# longer prefix is a valid sequence prefix.
def utf8_proof.longer_not_valid_from_not_extended(+s: List<&2, U32>, +bytes: List<&2, U32>,
  not_extended: utf8_proof.not_extended_by(s, utf8_proof.next_byte_after(bytes, s))) ->
  utf8_proof.bool.maximal_subpart.longer_not_valid_prefix(s, bytes):
  c => extra => longer => utf8_proof.longer_not_valid_at(s, bytes, c, extra, not_extended, longer)

def utf8_proof.longest_found(+bytes: List<&2, U32>, found: utf8_proof.Unextended(bytes)) ->
  Exists(List<&2, U32>, sub =>
    Laws.is_prefix(sub, bytes) &
    {UTF8.is_valid_sequence_prefix(sub) == True{} : Bool} &
    utf8_proof.bool.maximal_subpart.longer_not_valid_prefix(sub, bytes)):
  (+sub, facts) = found
  (prefix, more_facts) = facts
  (begins, not_extended) = more_facts
  (sub, (prefix, (begins, utf8_proof.longer_not_valid_from_not_extended(sub, bytes, not_extended))))

def utf8_proof.maximal_subpart_exists.if(+b1: U32, +more: List<&2, U32>, begins: Bool,
  checked: {UTF8.is_valid_sequence_prefix([b1]) == begins : Bool}) ->
  Exists(List<&2, U32>, s => utf8_proof.bool.maximal_subpart.if(b1, more, begins, s)):
  match begins:
    case True{}: utf8_proof.longest_found(b1 <> more, utf8_proof.longest_from(more, [b1], b1 <> more, {==}, checked))
    case False{}: ([b1], {==})

def utf8_proof.bool.maximal_subpart_exists(+b1: U32, +more: List<&2, U32>, invalid: Laws.no_valid_sequence(b1 <> more)) ->
  Exists(List<&2, U32>, subpart => utf8_proof.bool.maximal_subpart(b1, more, subpart)):
  utf8_proof.maximal_subpart_exists.if(b1, more, UTF8.is_valid_sequence_prefix([b1]), {==})

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

# Computing the first scalar
# --------------------------
#
# `next_scalar` computes what `Laws.begins_with_scalar` describes: the
# scalar of the valid sequence at the front of a buffer and the bytes
# after it, or None if there is no valid sequence there.  The proofs
# about `decodes_first` compute with it, in the form
# `utf8_proof.Decoded.nonempty`; `utf8_proof.to_first` and
# `utf8_proof.from_first` convert between that form and the law's.

def utf8_proof.next_scalar.found(scalar: Maybe<&2, U32>, rest: List<&2, U32>,
  otherwise: List<&2, U32> -> Maybe<&1, U32 & List<&2, U32>>) ->
  Maybe<&1, U32 & List<&2, U32>>:
  match scalar:
    case Some{cp}:
      Some{(cp, rest)}
    case None{}:
      otherwise(rest)

def utf8_proof.next_scalar.four(+b1: U32, +b2: U32, +b3: U32, rest: List<&2, U32>) ->
  Maybe<&1, U32 & List<&2, U32>>:
  match rest:
    case Nil{}:
      None{}
    case +b4 <> after:
      utf8_proof.next_scalar.found(UTF8.four_byte_scalar(b1, b2, b3, b4), after, r => None{})

def utf8_proof.next_scalar.three(+b1: U32, +b2: U32, rest: List<&2, U32>) ->
  Maybe<&1, U32 & List<&2, U32>>:
  match rest:
    case Nil{}:
      None{}
    case +b3 <> after:
      utf8_proof.next_scalar.found(UTF8.three_byte_scalar(b1, b2, b3), after, r => utf8_proof.next_scalar.four(b1, b2, b3, r))

def utf8_proof.next_scalar.two(+b1: U32, rest: List<&2, U32>) ->
  Maybe<&1, U32 & List<&2, U32>>:
  match rest:
    case Nil{}:
      None{}
    case +b2 <> after:
      utf8_proof.next_scalar.found(utf8_proof.two_byte_scalar(b1, b2), after, r => utf8_proof.next_scalar.three(b1, b2, r))

def utf8_proof.next_scalar(bytes: List<&2, U32>) -> Maybe<&1, U32 & List<&2, U32>>:
  match bytes:
    case Nil{}:
      None{}
    case +b1 <> rest:
      utf8_proof.next_scalar.found(utf8_proof.one_byte_scalar(b1), rest,
        r => utf8_proof.next_scalar.two(b1, r))

# `Laws.decodes_first.nonempty`, given `found = next_scalar(b1 <> more)`.
def utf8_proof.Decoded.nonempty(+b1: U32, +more: List<&2, U32>,
  found: Maybe<&1, U32 & List<&2, U32>>,
  result: Maybe<&1, U32 & List<&2, U32>>) -> Type:
  match found:
    case Some{scalar_rest}:
      {result == Some{scalar_rest} : Maybe<&1, U32 & List<&2, U32>>}
    case None{}:
      Laws.decodes_first.replaced(b1, more, result)

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
  UTF8.false_true(Equal.cong(Maybe<&1, U32 & List<&2, U32>>, Bool,
    m => Maybe.is_some(&1, U32 & List<&2, U32>, m), None{}, Some{(c, r)}, e))

def utf8_proof.next_one(+b: U32, +rest: List<&2, U32>, +cp: U32,
  one: {utf8_proof.one_byte_scalar(b) == Some{cp} : Maybe<&2, U32>}) ->
  {utf8_proof.next_scalar(b <> rest) == Some{(cp, rest)} : Maybe<&1, U32 & List<&2, U32>>}:
  %Equal.sym(Maybe<&2, U32>, utf8_proof.one_byte_scalar(b), Some{cp}, one) :
    {utf8_proof.next_scalar.found(_, rest, r => utf8_proof.next_scalar.two(b, r)) == Some{(cp, rest)} : Maybe<&1, U32 & List<&2, U32>>}
  {==}

def utf8_proof.next_two(+p: U32, +b: U32, +rest: List<&2, U32>, +cp: U32,
  one: {utf8_proof.one_byte_scalar(p) == None{} : Maybe<&2, U32>},
  two: {utf8_proof.two_byte_scalar(p, b) == Some{cp} : Maybe<&2, U32>}) ->
  {utf8_proof.next_scalar(p <> b <> rest) == Some{(cp, rest)} : Maybe<&1, U32 & List<&2, U32>>}:
  %Equal.sym(Maybe<&2, U32>, utf8_proof.one_byte_scalar(p), None{}, one) :
    {utf8_proof.next_scalar.found(_, b <> rest, r => utf8_proof.next_scalar.two(p, r)) == Some{(cp, rest)} : Maybe<&1, U32 & List<&2, U32>>}
  %Equal.sym(Maybe<&2, U32>, utf8_proof.two_byte_scalar(p, b), Some{cp}, two) :
    {utf8_proof.next_scalar.found(_, rest, r => utf8_proof.next_scalar.three(p, b, r)) == Some{(cp, rest)} : Maybe<&1, U32 & List<&2, U32>>}
  {==}

def utf8_proof.next_three(+p: U32, +q: U32, +b: U32, +rest: List<&2, U32>, +cp: U32,
  one: {utf8_proof.one_byte_scalar(p) == None{} : Maybe<&2, U32>},
  two: {utf8_proof.two_byte_scalar(p, q) == None{} : Maybe<&2, U32>},
  three: {UTF8.three_byte_scalar(p, q, b) == Some{cp} : Maybe<&2, U32>}) ->
  {utf8_proof.next_scalar(p <> q <> b <> rest) == Some{(cp, rest)} : Maybe<&1, U32 & List<&2, U32>>}:
  %Equal.sym(Maybe<&2, U32>, utf8_proof.one_byte_scalar(p), None{}, one) :
    {utf8_proof.next_scalar.found(_, q <> b <> rest, r => utf8_proof.next_scalar.two(p, r)) == Some{(cp, rest)} : Maybe<&1, U32 & List<&2, U32>>}
  %Equal.sym(Maybe<&2, U32>, utf8_proof.two_byte_scalar(p, q), None{}, two) :
    {utf8_proof.next_scalar.found(_, b <> rest, r => utf8_proof.next_scalar.three(p, q, r)) == Some{(cp, rest)} : Maybe<&1, U32 & List<&2, U32>>}
  %Equal.sym(Maybe<&2, U32>, UTF8.three_byte_scalar(p, q, b), Some{cp}, three) :
    {utf8_proof.next_scalar.found(_, rest, r => utf8_proof.next_scalar.four(p, q, b, r)) == Some{(cp, rest)} : Maybe<&1, U32 & List<&2, U32>>}
  {==}

def utf8_proof.next_four(+p: U32, +q: U32, +r1: U32, +b: U32, +rest: List<&2, U32>, +cp: U32,
  one: {utf8_proof.one_byte_scalar(p) == None{} : Maybe<&2, U32>},
  two: {utf8_proof.two_byte_scalar(p, q) == None{} : Maybe<&2, U32>},
  three: {UTF8.three_byte_scalar(p, q, r1) == None{} : Maybe<&2, U32>},
  four: {UTF8.four_byte_scalar(p, q, r1, b) == Some{cp} : Maybe<&2, U32>}) ->
  {utf8_proof.next_scalar(p <> q <> r1 <> b <> rest) == Some{(cp, rest)} : Maybe<&1, U32 & List<&2, U32>>}:
  %Equal.sym(Maybe<&2, U32>, utf8_proof.one_byte_scalar(p), None{}, one) :
    {utf8_proof.next_scalar.found(_, q <> r1 <> b <> rest, r => utf8_proof.next_scalar.two(p, r)) == Some{(cp, rest)} : Maybe<&1, U32 & List<&2, U32>>}
  %Equal.sym(Maybe<&2, U32>, utf8_proof.two_byte_scalar(p, q), None{}, two) :
    {utf8_proof.next_scalar.found(_, r1 <> b <> rest, r => utf8_proof.next_scalar.three(p, q, r)) == Some{(cp, rest)} : Maybe<&1, U32 & List<&2, U32>>}
  %Equal.sym(Maybe<&2, U32>, UTF8.three_byte_scalar(p, q, r1), None{}, three) :
    {utf8_proof.next_scalar.found(_, b <> rest, r => utf8_proof.next_scalar.four(p, q, r1, r)) == Some{(cp, rest)} : Maybe<&1, U32 & List<&2, U32>>}
  %Equal.sym(Maybe<&2, U32>, UTF8.four_byte_scalar(p, q, r1, b), Some{cp}, four) :
    {utf8_proof.next_scalar.found(_, rest, r => None{}) == Some{(cp, rest)} : Maybe<&1, U32 & List<&2, U32>>}
  {==}

def utf8_proof.two_scalar_valid(+b1: U32, +b2: U32, +cp: U32, valid: Bool,
  checked: {UTF8.valid_two_bytes(b1, b2) == valid : Bool},
  e: {utf8_proof.two_byte_scalar.if(b1, b2, valid, checked) == Some{cp} : Maybe<&2, U32>}) ->
  {UTF8.valid_two_bytes(b1, b2) == True{} : Bool}:
  match valid:
    case False{}:
      Empty.absurd({UTF8.valid_two_bytes(b1, b2) == True{} : Bool},
        UTF8.false_true(Equal.cong(Maybe<&2, U32>, Bool, m => Maybe.is_some(&2, U32, m),
          None{}, Some{cp}, e)))
    case True{}:
      checked

def utf8_proof.one_scalar_none(+byte: U32, valid: Bool,
  -checked: {UTF8.valid_one_byte(byte) == valid : Bool},
  invalid: {valid == True{} : Bool} -> Empty) ->
  {utf8_proof.one_byte_scalar.if(byte, valid, checked) == None{} : Maybe<&2, U32>}:
  match valid:
    case False{}: {==}
    case True{}: Empty.absurd({utf8_proof.one_byte_scalar.if(byte, True{}, checked) == None{} : Maybe<&2, U32>}, invalid({==}))

def utf8_proof.two_scalar_none(+b1: U32, +b2: U32, valid: Bool,
  -checked: {UTF8.valid_two_bytes(b1, b2) == valid : Bool},
  invalid: {valid == True{} : Bool} -> Empty) ->
  {utf8_proof.two_byte_scalar.if(b1, b2, valid, checked) == None{} : Maybe<&2, U32>}:
  match valid:
    case False{}: {==}
    case True{}: Empty.absurd({utf8_proof.two_byte_scalar.if(b1, b2, True{}, checked) == None{} : Maybe<&2, U32>}, invalid({==}))

def utf8_proof.three_scalar_valid(+b1: U32, +b2: U32, +b3: U32, +cp: U32, valid: Bool,
  checked: {UTF8.valid_three_bytes(b1, b2, b3) == valid : Bool},
  e: {UTF8.three_byte_scalar.if(b1, b2, b3, valid, checked) == Some{cp} : Maybe<&2, U32>}) ->
  {UTF8.valid_three_bytes(b1, b2, b3) == True{} : Bool}:
  match valid:
    case False{}:
      Empty.absurd({UTF8.valid_three_bytes(b1, b2, b3) == True{} : Bool},
        UTF8.false_true(Equal.cong(Maybe<&2, U32>, Bool, m => Maybe.is_some(&2, U32, m), None{}, Some{cp}, e)))
    case True{}:
      checked

def utf8_proof.three_scalar_none(+b1: U32, +b2: U32, +b3: U32, valid: Bool,
  -checked: {UTF8.valid_three_bytes(b1, b2, b3) == valid : Bool},
  invalid: {valid == True{} : Bool} -> Empty) ->
  {UTF8.three_byte_scalar.if(b1, b2, b3, valid, checked) == None{} : Maybe<&2, U32>}:
  match valid:
    case False{}: {==}
    case True{}: Empty.absurd({UTF8.three_byte_scalar.if(b1, b2, b3, True{}, checked) == None{} : Maybe<&2, U32>}, invalid({==}))

def utf8_proof.four_scalar_valid(+b1: U32, +b2: U32, +b3: U32, +b4: U32, +cp: U32, valid: Bool,
  checked: {UTF8.valid_four_bytes(b1, b2, b3, b4) == valid : Bool},
  e: {UTF8.four_byte_scalar.if(b1, b2, b3, b4, valid, checked) == Some{cp} : Maybe<&2, U32>}) ->
  {UTF8.valid_four_bytes(b1, b2, b3, b4) == True{} : Bool}:
  match valid:
    case False{}:
      Empty.absurd({UTF8.valid_four_bytes(b1, b2, b3, b4) == True{} : Bool},
        UTF8.false_true(Equal.cong(Maybe<&2, U32>, Bool, m => Maybe.is_some(&2, U32, m), None{}, Some{cp}, e)))
    case True{}:
      checked

def utf8_proof.two_scalar_any_valid(+b1: U32, +b2: U32, +cp: U32,
  two: {utf8_proof.two_byte_scalar(b1, b2) == Some{cp} : Maybe<&2, U32>}) -> {UTF8.valid_two_bytes(b1, b2) == True{} : Bool}:
  utf8_proof.two_scalar_valid(b1, b2, cp, UTF8.valid_two_bytes(b1, b2), {==}, two)

def utf8_proof.next_two_valid(+b1: U32, +b2: U32, +rest: List<&2, U32>, +cp: U32,
  +two: {utf8_proof.two_byte_scalar(b1, b2) == Some{cp} : Maybe<&2, U32>}) ->
  {utf8_proof.next_scalar(b1 <> b2 <> rest) == Some{(cp, rest)} : Maybe<&1, U32 & List<&2, U32>>}:
  +k = utf8_proof.valid_kind2(b1, b2, utf8_proof.two_scalar_any_valid(b1, b2, cp, two))
  utf8_proof.next_two(b1, b2, rest, cp, utf8_proof.one_scalar_none(b1, UTF8.valid_one_byte(b1), {==}, v => UTF8.false_true(Equal.cong(Nat, Bool, m => Nat.is_eq(m, 2n), 1n, 2n, Equal.trans(Nat, 1n, utf8_proof.kind(b1), 2n, Equal.sym(Nat, utf8_proof.kind(b1), 1n, utf8_proof.valid_kind1(b1, v)), k)))), two)

def utf8_proof.next_three_valid(+b1: U32, +b2: U32, +b3: U32, +rest: List<&2, U32>, +cp: U32,
  +three: {UTF8.three_byte_scalar(b1, b2, b3) == Some{cp} : Maybe<&2, U32>}) ->
  {utf8_proof.next_scalar(b1 <> b2 <> b3 <> rest) == Some{(cp, rest)} : Maybe<&1, U32 & List<&2, U32>>}:
  +k = utf8_proof.valid_kind3(b1, b2, b3, utf8_proof.three_scalar_valid(b1, b2, b3, cp, UTF8.valid_three_bytes(b1, b2, b3), {==}, three))
  utf8_proof.next_three(b1, b2, b3, rest, cp, utf8_proof.one_scalar_none(b1, UTF8.valid_one_byte(b1), {==}, v => UTF8.false_true(Equal.cong(Nat, Bool, m => Nat.is_eq(m, 3n), 1n, 3n, Equal.trans(Nat, 1n, utf8_proof.kind(b1), 3n, Equal.sym(Nat, utf8_proof.kind(b1), 1n, utf8_proof.valid_kind1(b1, v)), k)))), utf8_proof.two_scalar_none(b1, b2, UTF8.valid_two_bytes(b1, b2), {==}, v => UTF8.false_true(Equal.cong(Nat, Bool, m => Nat.is_eq(m, 3n), 2n, 3n, Equal.trans(Nat, 2n, utf8_proof.kind(b1), 3n, Equal.sym(Nat, utf8_proof.kind(b1), 2n, utf8_proof.valid_kind2(b1, b2, v)), k)))), three)

def utf8_proof.next_four_valid(+b1: U32, +b2: U32, +b3: U32, +b4: U32, +rest: List<&2, U32>, +cp: U32,
  +four: {UTF8.four_byte_scalar(b1, b2, b3, b4) == Some{cp} : Maybe<&2, U32>}) ->
  {utf8_proof.next_scalar(b1 <> b2 <> b3 <> b4 <> rest) == Some{(cp, rest)} : Maybe<&1, U32 & List<&2, U32>>}:
  +k = utf8_proof.valid_kind4(b1, b2, b3, b4, utf8_proof.four_scalar_valid(b1, b2, b3, b4, cp, UTF8.valid_four_bytes(b1, b2, b3, b4), {==}, four))
  utf8_proof.next_four(b1, b2, b3, b4, rest, cp, utf8_proof.one_scalar_none(b1, UTF8.valid_one_byte(b1), {==}, v => UTF8.false_true(Equal.cong(Nat, Bool, m => Nat.is_eq(m, 4n), 1n, 4n, Equal.trans(Nat, 1n, utf8_proof.kind(b1), 4n, Equal.sym(Nat, utf8_proof.kind(b1), 1n, utf8_proof.valid_kind1(b1, v)), k)))), utf8_proof.two_scalar_none(b1, b2, UTF8.valid_two_bytes(b1, b2), {==}, v => UTF8.false_true(Equal.cong(Nat, Bool, m => Nat.is_eq(m, 4n), 2n, 4n, Equal.trans(Nat, 2n, utf8_proof.kind(b1), 4n, Equal.sym(Nat, utf8_proof.kind(b1), 2n, utf8_proof.valid_kind2(b1, b2, v)), k)))), utf8_proof.three_scalar_none(b1, b2, b3, UTF8.valid_three_bytes(b1, b2, b3), {==}, v => UTF8.false_true(Equal.cong(Nat, Bool, m => Nat.is_eq(m, 4n), 3n, 4n, Equal.trans(Nat, 3n, utf8_proof.kind(b1), 4n, Equal.sym(Nat, utf8_proof.kind(b1), 3n, utf8_proof.valid_kind3(b1, b2, b3, v)), k)))), four)

# The two directions of `Laws.encodes`
# -------------------------------------
#
# `Laws.encodes` says that `seq` is the encoding of `cp`.
# `utf8_proof.Decodes` says the same thing in the decoding direction:
# `seq` is a valid sequence and `cp` is the scalar it
# decodes to.  `utf8_proof.from_old` and `utf8_proof.to_old` convert
# between them.

def utf8_proof.Decodes(seq: List<&2, U32>, cp: U32) -> Type:
  match seq:
    case +b1 <> Nil{}:
      {utf8_proof.one_byte_scalar(b1) == Some{cp} : Maybe<&2, U32>}
    case +b1 <> +b2 <> Nil{}:
      {utf8_proof.two_byte_scalar(b1, b2) == Some{cp} : Maybe<&2, U32>}
    case +b1 <> +b2 <> +b3 <> Nil{}:
      {UTF8.three_byte_scalar(b1, b2, b3) == Some{cp} : Maybe<&2, U32>}
    case +b1 <> +b2 <> +b3 <> +b4 <> Nil{}:
      {UTF8.four_byte_scalar(b1, b2, b3, b4) == Some{cp} : Maybe<&2, U32>}
    case _:
      Empty

def utf8_proof.some_value(+a: U32, +b: U32, e: {Some{a} == Some{b} : Maybe<&2, U32>}) -> {a == b : U32}:
  Equal.cong(Maybe<&2, U32>, U32, m => Maybe.default(&2, U32, m, 0), Some{a}, Some{b}, e)

def utf8_proof.some_list(+a: List<&2, U32>, +b: List<&2, U32>,
  e: {Some{a} == Some{b} : Maybe<&1, List<&2, U32>>}) -> {a == b : List<&2, U32>}:
  Equal.cong(Maybe<&1, List<&2, U32>>, List<&2, U32>, m => Maybe.default(&1, List<&2, U32>, m, Nil{}),
    Some{a}, Some{b}, e)

def utf8_proof.not_true(+x: Bool, e: {Bool.not(x) == True{} : Bool}) -> {x == False{} : Bool}:
  match x:
    case False{}:
      {==}
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, UTF8.false_true(e))

def utf8_proof.none_from_is_some(m: Maybe<&2, U32>,
  e: {Maybe.is_some(&2, U32, m) == False{} : Bool}) -> {m == None{} : Maybe<&2, U32>}:
  match m:
    case None{}:
      {==}
    case Some{x}:
      Empty.absurd({Some{x} == None{} : Maybe<&2, U32>}, utf8_proof.true_false(e))

# Decoding direction to encoding direction, one byte.  A valid byte is a
# scalar, and its one-byte shape is itself.

def utf8_proof.one_encoding(+b: U32, +shape: {UTF8.has_one_byte_shape(b) == True{} : Bool}) ->
  {Laws.encoding(b) == Some{[b]} : Maybe<&1, List<&2, U32>>}:
  %utf8_proof.impl.encode_as_one_byte(b, shape) : {Laws.encoding.if(b, _) == Some{[b]} : Maybe<&1, List<&2, U32>>}
  {==}

def utf8_proof.one_encodes(+b: U32, +valid: {UTF8.valid_one_byte(b) == True{} : Bool}) ->
  Laws.encodes([b], b):
  +shape = utf8_proof.valid_one_byte_has_shape(b, valid)
  (Equal.trans(Bool, Laws.is_unicode_scalar(b), UTF8.valid_one_byte(b), True{},
     Equal.sym(Bool, UTF8.valid_one_byte(b), Laws.is_unicode_scalar(b), utf8_proof.valid_one_byte(b, shape)),
     valid),
   utf8_proof.one_encoding(b, shape))

def utf8_proof.one_encodes.if(+b: U32, valid: Bool, +checked: {UTF8.valid_one_byte(b) == valid : Bool},
  +cp: U32, e: {utf8_proof.one_byte_scalar.if(b, valid, checked) == Some{cp} : Maybe<&2, U32>}) ->
  Laws.encodes([b], cp):
  match valid:
    case False{}:
      Empty.absurd(Laws.encodes([b], cp),
        UTF8.false_true(Equal.cong(Maybe<&2, U32>, Bool, m => Maybe.is_some(&2, U32, m),
          None{}, Some{cp}, e)))
    case True{}:
      %utf8_proof.some_value(b, cp, e) : Laws.encodes([b], _)
      utf8_proof.one_encodes(b, checked)

# Decoding direction to encoding direction, two bytes.  The decoded
# value is a scalar; it has no one-byte shape, since the pair is not
# overlong; and its two-byte shape is the pair.

def utf8_proof.none_of2(m: Maybe<&1, U32 & U32>,
  e: {Maybe.is_some(&1, U32 & U32, m) == False{} : Bool}) -> {m == None{} : Maybe<&1, U32 & U32>}:
  match m:
    case None{}:
      {==}
    case Some{x}:
      Empty.absurd({Some{x} == None{} : Maybe<&1, U32 & U32>}, utf8_proof.true_false(e))

def utf8_proof.none_of3(m: Maybe<&1, U32 & U32 & U32>,
  e: {Maybe.is_some(&1, U32 & U32 & U32, m) == False{} : Bool}) -> {m == None{} : Maybe<&1, U32 & U32 & U32>}:
  match m:
    case None{}:
      {==}
    case Some{x}:
      Empty.absurd({Some{x} == None{} : Maybe<&1, U32 & U32 & U32>}, utf8_proof.true_false(e))

def utf8_proof.false_of(+x: Bool, c: {x == True{} : Bool} -> Empty) -> {x == False{} : Bool}:
  match x:
    case False{}: {==}
    case True{}: Empty.absurd({True{} == False{} : Bool}, c({==}))

def utf8_proof.two_encoding(+cp: U32, +b1: U32, +b2: U32,
  no_one: {Laws.one_byte_shape(cp) == None{} : Maybe<&2, U32>},
  two: {Laws.two_byte_shape(cp) == Some{(b1, b2)} : Maybe<&1, U32 & U32>}) ->
  {Laws.encoding(cp) == Some{[b1, b2]} : Maybe<&1, List<&2, U32>>}:
  %Equal.sym(Maybe<&2, U32>, Laws.one_byte_shape(cp), None{}, no_one) :
    {Laws.encoding.if(cp, _) == Some{[b1, b2]} : Maybe<&1, List<&2, U32>>}
  %Equal.sym(Maybe<&1, U32 & U32>, Laws.two_byte_shape(cp), Some{(b1, b2)}, two) :
    {Laws.encoding.two(cp, _) == Some{[b1, b2]} : Maybe<&1, List<&2, U32>>}
  {==}

def utf8_proof.three_encoding(+cp: U32, +b1: U32, +b2: U32, +b3: U32,
  no_one: {Laws.one_byte_shape(cp) == None{} : Maybe<&2, U32>},
  no_two: {Laws.two_byte_shape(cp) == None{} : Maybe<&1, U32 & U32>},
  three: {Laws.three_byte_shape(cp) == Some{(b1, b2, b3)} : Maybe<&1, U32 & U32 & U32>}) ->
  {Laws.encoding(cp) == Some{[b1, b2, b3]} : Maybe<&1, List<&2, U32>>}:
  %Equal.sym(Maybe<&2, U32>, Laws.one_byte_shape(cp), None{}, no_one) :
    {Laws.encoding.if(cp, _) == Some{[b1, b2, b3]} : Maybe<&1, List<&2, U32>>}
  %Equal.sym(Maybe<&1, U32 & U32>, Laws.two_byte_shape(cp), None{}, no_two) :
    {Laws.encoding.two(cp, _) == Some{[b1, b2, b3]} : Maybe<&1, List<&2, U32>>}
  %Equal.sym(Maybe<&1, U32 & U32 & U32>, Laws.three_byte_shape(cp), Some{(b1, b2, b3)}, three) :
    {Laws.encoding.three(cp, _) == Some{[b1, b2, b3]} : Maybe<&1, List<&2, U32>>}
  {==}

def utf8_proof.four_encoding(+cp: U32, +b1: U32, +b2: U32, +b3: U32, +b4: U32,
  no_one: {Laws.one_byte_shape(cp) == None{} : Maybe<&2, U32>},
  no_two: {Laws.two_byte_shape(cp) == None{} : Maybe<&1, U32 & U32>},
  no_three: {Laws.three_byte_shape(cp) == None{} : Maybe<&1, U32 & U32 & U32>},
  four: {Laws.four_byte_shape(cp) == Some{(b1, b2, b3, b4)} : Maybe<&1, U32 & U32 & U32 & U32>}) ->
  {Laws.encoding(cp) == Some{[b1, b2, b3, b4]} : Maybe<&1, List<&2, U32>>}:
  %Equal.sym(Maybe<&2, U32>, Laws.one_byte_shape(cp), None{}, no_one) :
    {Laws.encoding.if(cp, _) == Some{[b1, b2, b3, b4]} : Maybe<&1, List<&2, U32>>}
  %Equal.sym(Maybe<&1, U32 & U32>, Laws.two_byte_shape(cp), None{}, no_two) :
    {Laws.encoding.two(cp, _) == Some{[b1, b2, b3, b4]} : Maybe<&1, List<&2, U32>>}
  %Equal.sym(Maybe<&1, U32 & U32 & U32>, Laws.three_byte_shape(cp), None{}, no_three) :
    {Laws.encoding.three(cp, _) == Some{[b1, b2, b3, b4]} : Maybe<&1, List<&2, U32>>}
  %Equal.sym(Maybe<&1, U32 & U32 & U32 & U32>, Laws.four_byte_shape(cp), Some{(b1, b2, b3, b4)}, four) :
    {Laws.encoding.four(_) == Some{[b1, b2, b3, b4]} : Maybe<&1, List<&2, U32>>}
  {==}

def utf8_proof.two_encodes(+b1: U32, +b2: U32,
  +shape: {UTF8.has_two_byte_shape(b1, b2) == True{} : Bool},
  valid: {UTF8.valid_two_bytes(b1, b2) == True{} : Bool}) ->
  Laws.encodes([b1, b2], UTF8.decode_two_bytes(b1, b2, shape)):
  +cp = UTF8.decode_two_bytes(b1, b2, shape)
  +fits = Equal.trans(Bool, Bool.not(UTF8.can_encode_as_one_byte(cp)), UTF8.valid_two_bytes(b1, b2), True{},
    Equal.sym(Bool, UTF8.valid_two_bytes(b1, b2), Bool.not(UTF8.can_encode_as_one_byte(cp)),
      utf8_proof.valid_from_facts(cp, b1, b2, shape, utf8_proof.impl.overlong_two_bytes(b1, b2, shape))),
    valid)
  +not_one = utf8_proof.not_true(UTF8.can_encode_as_one_byte(cp), fits)
  +no_one = utf8_proof.none_from_is_some(Laws.one_byte_shape(cp),
    Equal.trans(Bool, Maybe.is_some(&2, U32, Laws.one_byte_shape(cp)), UTF8.can_encode_as_one_byte(cp), False{},
      Equal.sym(Bool, UTF8.can_encode_as_one_byte(cp), Maybe.is_some(&2, U32, Laws.one_byte_shape(cp)),
        utf8_proof.impl.can_encode_as_one_byte(cp)),
      not_one))
  +two = utf8_proof.decode_result_representation(b1, b2, shape, utf8_proof.shape_witness(b1, b2, shape))
  (utf8_proof.two_decoded_scalar(b1, b2, shape), utf8_proof.two_encoding(cp, b1, b2, no_one, two))

def utf8_proof.two_encodes.if(+b1: U32, +b2: U32, valid: Bool,
  +checked: {UTF8.valid_two_bytes(b1, b2) == valid : Bool}, +cp: U32,
  e: {utf8_proof.two_byte_scalar.if(b1, b2, valid, checked) == Some{cp} : Maybe<&2, U32>}) ->
  Laws.encodes([b1, b2], cp):
  match valid:
    case False{}:
      Empty.absurd(Laws.encodes([b1, b2], cp),
        UTF8.false_true(Equal.cong(Maybe<&2, U32>, Bool, m => Maybe.is_some(&2, U32, m),
          None{}, Some{cp}, e)))
    case True{}:
      %utf8_proof.some_value(UTF8.decode_two_bytes(b1, b2, utf8_proof.valid_two_bytes_has_shape(b1, b2, checked)), cp, e) :
        Laws.encodes([b1, b2], _)
      utf8_proof.two_encodes(b1, b2, utf8_proof.valid_two_bytes_has_shape(b1, b2, checked), checked)

def utf8_proof.three_encodes(+b1: U32, +b2: U32, +b3: U32,
  +shape: {UTF8.has_three_byte_shape(b1, b2, b3) == True{} : Bool},
  valid: {UTF8.valid_three_bytes(b1, b2, b3) == True{} : Bool}) ->
  Laws.encodes([b1, b2, b3], UTF8.decode_three_bytes(b1, b2, b3, shape)):
  +cp = UTF8.decode_three_bytes(b1, b2, b3, shape)
  +v = Equal.trans(Bool, utf8_proof.value3(utf8_proof.dec3(b1, b2, b3)), UTF8.valid_three_bytes(b1, b2, b3), True{}, Equal.sym(Bool, UTF8.valid_three_bytes(b1, b2, b3), utf8_proof.value3(utf8_proof.dec3(b1, b2, b3)), utf8_proof.valid3_value(b1, b2, b3, shape)), valid)
  +not2 = utf8_proof.not_true(UTF8.can_encode_as_two_bytes(cp), bool_and_left_true(Bool.not(UTF8.can_encode_as_two_bytes(cp)), UTF8.is_scalar(cp), v))
  +sc = Equal.trans(Bool, Laws.is_unicode_scalar(cp), UTF8.is_scalar(cp), True{}, Equal.sym(Bool, UTF8.is_scalar(cp), Laws.is_unicode_scalar(cp), utf8_proof.scalar_agrees(cp)), bool_and_right_true(Bool.not(UTF8.can_encode_as_two_bytes(cp)), UTF8.is_scalar(cp), v))
  +not1 = utf8_proof.false_of(UTF8.can_encode_as_one_byte(cp), c => utf8_proof.true_false(Equal.trans(Bool, True{}, UTF8.can_encode_as_two_bytes(cp), False{}, Equal.sym(Bool, UTF8.can_encode_as_two_bytes(cp), True{}, utf8_proof.mono12(cp, c)), not2)))
  (sc, utf8_proof.three_encoding(cp, b1, b2, b3, utf8_proof.none_from_is_some(Laws.one_byte_shape(cp), Equal.trans(Bool, Maybe.is_some(&2, U32, Laws.one_byte_shape(cp)), UTF8.can_encode_as_one_byte(cp), False{}, Equal.sym(Bool, UTF8.can_encode_as_one_byte(cp), Maybe.is_some(&2, U32, Laws.one_byte_shape(cp)), utf8_proof.impl.can_encode_as_one_byte(cp)), not1)), utf8_proof.none_of2(Laws.two_byte_shape(cp), Equal.trans(Bool, Maybe.is_some(&1, U32 & U32, Laws.two_byte_shape(cp)), UTF8.can_encode_as_two_bytes(cp), False{}, Equal.sym(Bool, UTF8.can_encode_as_two_bytes(cp), Maybe.is_some(&1, U32 & U32, Laws.two_byte_shape(cp)), utf8_proof.impl.can_encode_as_two_bytes(cp)), not2)), utf8_proof.dec_produces3(b1, b2, b3, utf8_proof.fields3(b1, b2, b3, shape))))

def utf8_proof.three_encodes.if(+b1: U32, +b2: U32, +b3: U32, valid: Bool,
  +checked: {UTF8.valid_three_bytes(b1, b2, b3) == valid : Bool}, +cp: U32,
  e: {UTF8.three_byte_scalar.if(b1, b2, b3, valid, checked) == Some{cp} : Maybe<&2, U32>}) ->
  Laws.encodes([b1, b2, b3], cp):
  match valid:
    case False{}:
      Empty.absurd(Laws.encodes([b1, b2, b3], cp),
        UTF8.false_true(Equal.cong(Maybe<&2, U32>, Bool, m => Maybe.is_some(&2, U32, m), None{}, Some{cp}, e)))
    case True{}:
      %utf8_proof.some_value(UTF8.decode_three_bytes(b1, b2, b3, UTF8.valid_three_bytes.has_shape(b1, b2, b3, checked)), cp, e) : Laws.encodes([b1, b2, b3], _)
      utf8_proof.three_encodes(b1, b2, b3, UTF8.valid_three_bytes.has_shape(b1, b2, b3, checked), checked)

def utf8_proof.four_encodes(+b1: U32, +b2: U32, +b3: U32, +b4: U32,
  +shape: {UTF8.has_four_byte_shape(b1, b2, b3, b4) == True{} : Bool},
  valid: {UTF8.valid_four_bytes(b1, b2, b3, b4) == True{} : Bool}) ->
  Laws.encodes([b1, b2, b3, b4], UTF8.decode_four_bytes(b1, b2, b3, b4, shape)):
  +cp = UTF8.decode_four_bytes(b1, b2, b3, b4, shape)
  +v = Equal.trans(Bool, utf8_proof.value4(utf8_proof.dec4(b1, b2, b3, b4)), UTF8.valid_four_bytes(b1, b2, b3, b4), True{}, Equal.sym(Bool, UTF8.valid_four_bytes(b1, b2, b3, b4), utf8_proof.value4(utf8_proof.dec4(b1, b2, b3, b4)), utf8_proof.valid4_value(b1, b2, b3, b4, shape)), valid)
  +not3 = utf8_proof.not_true(UTF8.can_encode_as_three_bytes(cp), bool_and_left_true(Bool.not(UTF8.can_encode_as_three_bytes(cp)), UTF8.is_scalar(cp), v))
  +sc = Equal.trans(Bool, Laws.is_unicode_scalar(cp), UTF8.is_scalar(cp), True{}, Equal.sym(Bool, UTF8.is_scalar(cp), Laws.is_unicode_scalar(cp), utf8_proof.scalar_agrees(cp)), bool_and_right_true(Bool.not(UTF8.can_encode_as_three_bytes(cp)), UTF8.is_scalar(cp), v))
  +not2 = utf8_proof.false_of(UTF8.can_encode_as_two_bytes(cp), c => utf8_proof.true_false(Equal.trans(Bool, True{}, UTF8.can_encode_as_three_bytes(cp), False{}, Equal.sym(Bool, UTF8.can_encode_as_three_bytes(cp), True{}, utf8_proof.mono23(cp, c)), not3)))
  +not1 = utf8_proof.false_of(UTF8.can_encode_as_one_byte(cp), c => utf8_proof.true_false(Equal.trans(Bool, True{}, UTF8.can_encode_as_two_bytes(cp), False{}, Equal.sym(Bool, UTF8.can_encode_as_two_bytes(cp), True{}, utf8_proof.mono12(cp, c)), not2)))
  (sc, utf8_proof.four_encoding(cp, b1, b2, b3, b4, utf8_proof.none_from_is_some(Laws.one_byte_shape(cp), Equal.trans(Bool, Maybe.is_some(&2, U32, Laws.one_byte_shape(cp)), UTF8.can_encode_as_one_byte(cp), False{}, Equal.sym(Bool, UTF8.can_encode_as_one_byte(cp), Maybe.is_some(&2, U32, Laws.one_byte_shape(cp)), utf8_proof.impl.can_encode_as_one_byte(cp)), not1)), utf8_proof.none_of2(Laws.two_byte_shape(cp), Equal.trans(Bool, Maybe.is_some(&1, U32 & U32, Laws.two_byte_shape(cp)), UTF8.can_encode_as_two_bytes(cp), False{}, Equal.sym(Bool, UTF8.can_encode_as_two_bytes(cp), Maybe.is_some(&1, U32 & U32, Laws.two_byte_shape(cp)), utf8_proof.impl.can_encode_as_two_bytes(cp)), not2)), utf8_proof.none_of3(Laws.three_byte_shape(cp), Equal.trans(Bool, Maybe.is_some(&1, U32 & U32 & U32, Laws.three_byte_shape(cp)), UTF8.can_encode_as_three_bytes(cp), False{}, Equal.sym(Bool, UTF8.can_encode_as_three_bytes(cp), Maybe.is_some(&1, U32 & U32 & U32, Laws.three_byte_shape(cp)), utf8_proof.impl.can_encode_as_three_bytes(cp)), not3)), utf8_proof.dec_produces4(b1, b2, b3, b4, utf8_proof.fields4(b1, b2, b3, b4, shape))))

def utf8_proof.four_encodes.if(+b1: U32, +b2: U32, +b3: U32, +b4: U32, valid: Bool,
  +checked: {UTF8.valid_four_bytes(b1, b2, b3, b4) == valid : Bool}, +cp: U32,
  e: {UTF8.four_byte_scalar.if(b1, b2, b3, b4, valid, checked) == Some{cp} : Maybe<&2, U32>}) ->
  Laws.encodes([b1, b2, b3, b4], cp):
  match valid:
    case False{}:
      Empty.absurd(Laws.encodes([b1, b2, b3, b4], cp),
        UTF8.false_true(Equal.cong(Maybe<&2, U32>, Bool, m => Maybe.is_some(&2, U32, m), None{}, Some{cp}, e)))
    case True{}:
      %utf8_proof.some_value(UTF8.decode_four_bytes(b1, b2, b3, b4, UTF8.valid_four_bytes.has_shape(b1, b2, b3, b4, checked)), cp, e) : Laws.encodes([b1, b2, b3, b4], _)
      utf8_proof.four_encodes(b1, b2, b3, b4, UTF8.valid_four_bytes.has_shape(b1, b2, b3, b4, checked), checked)

def utf8_proof.from_old(+seq: List<&2, U32>, +cp: U32, decoded: utf8_proof.Decodes(seq, cp)) ->
  Laws.encodes(seq, cp):
  match seq:
    case Nil{}:
      Empty.absurd(Laws.encodes(Nil{}, cp), decoded)
    case +x <> Nil{}:
      utf8_proof.one_encodes.if(x, UTF8.valid_one_byte(x), {==}, cp, decoded)
    case +x <> +y <> Nil{}:
      utf8_proof.two_encodes.if(x, y, UTF8.valid_two_bytes(x, y), {==}, cp, decoded)
    case +x <> +y <> +z <> Nil{}:
      utf8_proof.three_encodes.if(x, y, z, UTF8.valid_three_bytes(x, y, z), {==}, cp, decoded)
    case +x <> +y <> +z <> +w <> Nil{}:
      utf8_proof.four_encodes.if(x, y, z, w, UTF8.valid_four_bytes(x, y, z, w), {==}, cp, decoded)
    case x <> y <> z <> w <> v <> rest:
      Empty.absurd(Laws.encodes(x <> y <> z <> w <> v <> rest, cp), decoded)

# Encoding direction to decoding direction.  A one-byte shape is the code
# point itself, which is a valid byte.  A two-byte shape with no
# one-byte shape is a valid pair that decodes to the code point.

def utf8_proof.one_scalar_some(+b: U32, valid: Bool,
  -checked: {UTF8.valid_one_byte(b) == valid : Bool}, is_true: {valid == True{} : Bool}) ->
  {utf8_proof.one_byte_scalar.if(b, valid, checked) == Some{b} : Maybe<&2, U32>}:
  match valid:
    case False{}:
      Empty.absurd({None{} == Some{b} : Maybe<&2, U32>}, UTF8.false_true(is_true))
    case True{}:
      {==}

def utf8_proof.one_decodes(+cp: U32, +b: U32,
  +produced: {Laws.one_byte_shape(cp) == Some{b} : Maybe<&2, U32>}) ->
  {utf8_proof.one_byte_scalar(b) == Some{cp} : Maybe<&2, U32>}:
  +accepted = Equal.trans(Bool, UTF8.can_encode_as_one_byte(cp), Maybe.is_some(&2, U32, Laws.one_byte_shape(cp)), True{},
    utf8_proof.impl.can_encode_as_one_byte(cp),
    Equal.cong(Maybe<&2, U32>, Bool, m => Maybe.is_some(&2, U32, m), Laws.one_byte_shape(cp), Some{b}, produced))
  +same = utf8_proof.some_value(cp, b,
    Equal.trans(Maybe<&2, U32>, Some{cp}, Laws.one_byte_shape(cp), Some{b},
      utf8_proof.impl.encode_as_one_byte(cp, accepted), produced))
  %same : {utf8_proof.one_byte_scalar(_) == Some{cp} : Maybe<&2, U32>}
  utf8_proof.one_scalar_some(cp, UTF8.valid_one_byte(cp), {==}, accepted)

def utf8_proof.two_scalar_some(+b1: U32, +b2: U32, +cp: U32, valid: Bool,
  +checked: {UTF8.valid_two_bytes(b1, b2) == valid : Bool}, is_true: {valid == True{} : Bool},
  +produced: {Laws.two_byte_shape(cp) == Some{(b1, b2)} : Maybe<&1, U32 & U32>}) ->
  {utf8_proof.two_byte_scalar.if(b1, b2, valid, checked) == Some{cp} : Maybe<&2, U32>}:
  match valid:
    case False{}:
      Empty.absurd({None{} == Some{cp} : Maybe<&2, U32>}, UTF8.false_true(is_true))
    case True{}:
      Equal.cong(U32, Maybe<&2, U32>, x => Some{x},
        UTF8.decode_two_bytes(b1, b2, utf8_proof.valid_two_bytes_has_shape(b1, b2, checked)), cp,
        utf8_proof.decode_model_produced(cp, b1, b2, utf8_proof.valid_two_bytes_has_shape(b1, b2, checked), produced))

def utf8_proof.two_decodes(+cp: U32, +b1: U32, +b2: U32,
  +no_one: {Laws.one_byte_shape(cp) == None{} : Maybe<&2, U32>},
  +produced: {Laws.two_byte_shape(cp) == Some{(b1, b2)} : Maybe<&1, U32 & U32>}) ->
  {utf8_proof.two_byte_scalar(b1, b2) == Some{cp} : Maybe<&2, U32>}:
  +shape = utf8_proof.model_pair_accepted(cp, b1, b2, produced)
  +decoded = utf8_proof.decode_model_produced(cp, b1, b2, shape, produced)
  +not_one = Equal.trans(Bool, UTF8.can_encode_as_one_byte(cp), Maybe.is_some(&2, U32, Laws.one_byte_shape(cp)), False{},
    utf8_proof.impl.can_encode_as_one_byte(cp),
    Equal.cong(Maybe<&2, U32>, Bool, m => Maybe.is_some(&2, U32, m), Laws.one_byte_shape(cp), None{}, no_one))
  +overlong = Equal.trans(Bool, UTF8.overlong_two_bytes(b1, b2, shape),
    UTF8.can_encode_as_one_byte(UTF8.decode_two_bytes(b1, b2, shape)), UTF8.can_encode_as_one_byte(cp),
    utf8_proof.impl.overlong_two_bytes(b1, b2, shape),
    Equal.cong(U32, Bool, x => UTF8.can_encode_as_one_byte(x), UTF8.decode_two_bytes(b1, b2, shape), cp, decoded))
  +valid = Equal.trans(Bool, UTF8.valid_two_bytes(b1, b2), Bool.not(UTF8.can_encode_as_one_byte(cp)), True{},
    utf8_proof.valid_from_facts(cp, b1, b2, shape, overlong),
    Equal.cong(Bool, Bool, x => Bool.not(x), UTF8.can_encode_as_one_byte(cp), False{}, not_one))
  utf8_proof.two_scalar_some(b1, b2, cp, UTF8.valid_two_bytes(b1, b2), {==}, valid, produced)

def utf8_proof.three_scalar_some(+b1: U32, +b2: U32, +b3: U32, +cp: U32, valid: Bool,
  +checked: {UTF8.valid_three_bytes(b1, b2, b3) == valid : Bool}, is_true: {valid == True{} : Bool},
  +dec: {utf8_proof.dec3(b1, b2, b3) == cp : U32}) ->
  {UTF8.three_byte_scalar.if(b1, b2, b3, valid, checked) == Some{cp} : Maybe<&2, U32>}:
  match valid:
    case False{}:
      Empty.absurd({None{} == Some{cp} : Maybe<&2, U32>}, UTF8.false_true(is_true))
    case True{}:
      Equal.cong(U32, Maybe<&2, U32>, x => Some{x}, UTF8.decode_three_bytes(b1, b2, b3, UTF8.valid_three_bytes.has_shape(b1, b2, b3, checked)), cp, dec)

def utf8_proof.three_value_true(+b1: U32, +b2: U32, +b3: U32, +cp: U32,
  +dec: {utf8_proof.dec3(b1, b2, b3) == cp : U32},
  +not_prev: {UTF8.can_encode_as_two_bytes(cp) == False{} : Bool},
  +sc: {UTF8.is_scalar(cp) == True{} : Bool}) -> {utf8_proof.value3(utf8_proof.dec3(b1, b2, b3)) == True{} : Bool}:
  %Equal.sym(U32, utf8_proof.dec3(b1, b2, b3), cp, dec) : {utf8_proof.value3(_) == True{} : Bool}
  %Equal.sym(Bool, UTF8.can_encode_as_two_bytes(cp), False{}, not_prev) : {Bool.and(Bool.not(_), UTF8.is_scalar(cp)) == True{} : Bool}
  %Equal.sym(Bool, UTF8.is_scalar(cp), True{}, sc) : {Bool.and(Bool.not(False{}), _) == True{} : Bool}
  {==}

def utf8_proof.three_decodes.p(+b1: U32, +b2: U32, +b3: U32, +cp: U32,
  +sc: {Laws.is_unicode_scalar(cp) == True{} : Bool},
  +no_prev: {Laws.two_byte_shape(cp) == None{} : Maybe<&1, U32 & U32>},
  p: utf8_proof.Produced3(cp, b1, b2, b3)) ->
  {UTF8.three_byte_scalar(b1, b2, b3) == Some{cp} : Maybe<&2, U32>}:
  (+shape, +dec) = p
  +not_prev = Equal.trans(Bool, UTF8.can_encode_as_two_bytes(cp), Maybe.is_some(&1, U32 & U32, Laws.two_byte_shape(cp)), False{}, utf8_proof.impl.can_encode_as_two_bytes(cp),
    Equal.cong(Maybe<&1, U32 & U32>, Bool, m => Maybe.is_some(&1, U32 & U32, m), Laws.two_byte_shape(cp), None{}, no_prev))
  +sc2 = Equal.trans(Bool, UTF8.is_scalar(cp), Laws.is_unicode_scalar(cp), True{}, utf8_proof.scalar_agrees(cp), sc)
  +valid = Equal.trans(Bool, UTF8.valid_three_bytes(b1, b2, b3), utf8_proof.value3(utf8_proof.dec3(b1, b2, b3)), True{}, utf8_proof.valid3_value(b1, b2, b3, shape),
    utf8_proof.three_value_true(b1, b2, b3, cp, dec, not_prev, sc2))
  utf8_proof.three_scalar_some(b1, b2, b3, cp, UTF8.valid_three_bytes(b1, b2, b3), {==}, valid, dec)

def utf8_proof.three_decodes(+cp: U32, +b1: U32, +b2: U32, +b3: U32,
  +sc: {Laws.is_unicode_scalar(cp) == True{} : Bool},
  +no_prev: {Laws.two_byte_shape(cp) == None{} : Maybe<&1, U32 & U32>},
  +produced: {Laws.three_byte_shape(cp) == Some{(b1, b2, b3)} : Maybe<&1, U32 & U32 & U32>}) ->
  {UTF8.three_byte_scalar(b1, b2, b3) == Some{cp} : Maybe<&2, U32>}:
  utf8_proof.three_decodes.p(b1, b2, b3, cp, sc, no_prev, utf8_proof.produced3(cp, b1, b2, b3, produced))

def utf8_proof.four_scalar_some(+b1: U32, +b2: U32, +b3: U32, +b4: U32, +cp: U32, valid: Bool,
  +checked: {UTF8.valid_four_bytes(b1, b2, b3, b4) == valid : Bool}, is_true: {valid == True{} : Bool},
  +dec: {utf8_proof.dec4(b1, b2, b3, b4) == cp : U32}) ->
  {UTF8.four_byte_scalar.if(b1, b2, b3, b4, valid, checked) == Some{cp} : Maybe<&2, U32>}:
  match valid:
    case False{}:
      Empty.absurd({None{} == Some{cp} : Maybe<&2, U32>}, UTF8.false_true(is_true))
    case True{}:
      Equal.cong(U32, Maybe<&2, U32>, x => Some{x}, UTF8.decode_four_bytes(b1, b2, b3, b4, UTF8.valid_four_bytes.has_shape(b1, b2, b3, b4, checked)), cp, dec)

def utf8_proof.four_value_true(+b1: U32, +b2: U32, +b3: U32, +b4: U32, +cp: U32,
  +dec: {utf8_proof.dec4(b1, b2, b3, b4) == cp : U32},
  +not_prev: {UTF8.can_encode_as_three_bytes(cp) == False{} : Bool},
  +sc: {UTF8.is_scalar(cp) == True{} : Bool}) -> {utf8_proof.value4(utf8_proof.dec4(b1, b2, b3, b4)) == True{} : Bool}:
  %Equal.sym(U32, utf8_proof.dec4(b1, b2, b3, b4), cp, dec) : {utf8_proof.value4(_) == True{} : Bool}
  %Equal.sym(Bool, UTF8.can_encode_as_three_bytes(cp), False{}, not_prev) : {Bool.and(Bool.not(_), UTF8.is_scalar(cp)) == True{} : Bool}
  %Equal.sym(Bool, UTF8.is_scalar(cp), True{}, sc) : {Bool.and(Bool.not(False{}), _) == True{} : Bool}
  {==}

def utf8_proof.four_decodes.p(+b1: U32, +b2: U32, +b3: U32, +b4: U32, +cp: U32,
  +sc: {Laws.is_unicode_scalar(cp) == True{} : Bool},
  +no_prev: {Laws.three_byte_shape(cp) == None{} : Maybe<&1, U32 & U32 & U32>},
  p: utf8_proof.Produced4(cp, b1, b2, b3, b4)) ->
  {UTF8.four_byte_scalar(b1, b2, b3, b4) == Some{cp} : Maybe<&2, U32>}:
  (+shape, +dec) = p
  +not_prev = Equal.trans(Bool, UTF8.can_encode_as_three_bytes(cp), Maybe.is_some(&1, U32 & U32 & U32, Laws.three_byte_shape(cp)), False{}, utf8_proof.impl.can_encode_as_three_bytes(cp),
    Equal.cong(Maybe<&1, U32 & U32 & U32>, Bool, m => Maybe.is_some(&1, U32 & U32 & U32, m), Laws.three_byte_shape(cp), None{}, no_prev))
  +sc2 = Equal.trans(Bool, UTF8.is_scalar(cp), Laws.is_unicode_scalar(cp), True{}, utf8_proof.scalar_agrees(cp), sc)
  +valid = Equal.trans(Bool, UTF8.valid_four_bytes(b1, b2, b3, b4), utf8_proof.value4(utf8_proof.dec4(b1, b2, b3, b4)), True{}, utf8_proof.valid4_value(b1, b2, b3, b4, shape),
    utf8_proof.four_value_true(b1, b2, b3, b4, cp, dec, not_prev, sc2))
  utf8_proof.four_scalar_some(b1, b2, b3, b4, cp, UTF8.valid_four_bytes(b1, b2, b3, b4), {==}, valid, dec)

def utf8_proof.four_decodes(+cp: U32, +b1: U32, +b2: U32, +b3: U32, +b4: U32,
  +sc: {Laws.is_unicode_scalar(cp) == True{} : Bool},
  +no_prev: {Laws.three_byte_shape(cp) == None{} : Maybe<&1, U32 & U32 & U32>},
  +produced: {Laws.four_byte_shape(cp) == Some{(b1, b2, b3, b4)} : Maybe<&1, U32 & U32 & U32 & U32>}) ->
  {UTF8.four_byte_scalar(b1, b2, b3, b4) == Some{cp} : Maybe<&2, U32>}:
  utf8_proof.four_decodes.p(b1, b2, b3, b4, cp, sc, no_prev, utf8_proof.produced4(cp, b1, b2, b3, b4, produced))

def utf8_proof.to_old.four.l2(+b1: U32, +b2: U32, r: U32 & U32, +seq: List<&2, U32>, +cp: U32, +sc: {Laws.is_unicode_scalar(cp) == True{} : Bool}, +no3: {Laws.three_byte_shape(cp) == None{} : Maybe<&1, U32 & U32 & U32>}, +checked: {Laws.four_byte_shape(cp) == Some{(b1, b2, r)} : Maybe<&1, U32 & U32 & U32 & U32>}, e: {Laws.encoding.four(Some{(b1, b2, r)}) == Some{seq} : Maybe<&1, List<&2, U32>>}) -> utf8_proof.Decodes(seq, cp):
  match r:
    case (+b3, +b4):
      %utf8_proof.some_list([b1, b2, b3, b4], seq, e) : utf8_proof.Decodes(_, cp)
      utf8_proof.four_decodes(cp, b1, b2, b3, b4, sc, no3, checked)

def utf8_proof.to_old.four.l1(+b1: U32, r: U32 & U32 & U32, +seq: List<&2, U32>, +cp: U32, +sc: {Laws.is_unicode_scalar(cp) == True{} : Bool}, +no3: {Laws.three_byte_shape(cp) == None{} : Maybe<&1, U32 & U32 & U32>}, +checked: {Laws.four_byte_shape(cp) == Some{(b1, r)} : Maybe<&1, U32 & U32 & U32 & U32>}, e: {Laws.encoding.four(Some{(b1, r)}) == Some{seq} : Maybe<&1, List<&2, U32>>}) -> utf8_proof.Decodes(seq, cp):
  match r:
    case (+b2, r2):
      utf8_proof.to_old.four.l2(b1, b2, r2, seq, cp, sc, no3, checked, e)

def utf8_proof.to_old.four.l0(r: U32 & U32 & U32 & U32, +seq: List<&2, U32>, +cp: U32, +sc: {Laws.is_unicode_scalar(cp) == True{} : Bool}, +no3: {Laws.three_byte_shape(cp) == None{} : Maybe<&1, U32 & U32 & U32>}, +checked: {Laws.four_byte_shape(cp) == Some{r} : Maybe<&1, U32 & U32 & U32 & U32>}, e: {Laws.encoding.four(Some{r}) == Some{seq} : Maybe<&1, List<&2, U32>>}) -> utf8_proof.Decodes(seq, cp):
  match r:
    case (+b1, r2):
      utf8_proof.to_old.four.l1(b1, r2, seq, cp, sc, no3, checked, e)

def utf8_proof.to_old.four(+seq: List<&2, U32>, +cp: U32, +sc: {Laws.is_unicode_scalar(cp) == True{} : Bool},
  +no3: {Laws.three_byte_shape(cp) == None{} : Maybe<&1, U32 & U32 & U32>},
  four: Maybe<&1, U32 & U32 & U32 & U32>, +checked: {Laws.four_byte_shape(cp) == four : Maybe<&1, U32 & U32 & U32 & U32>},
  e: {Laws.encoding.four(four) == Some{seq} : Maybe<&1, List<&2, U32>>}) -> utf8_proof.Decodes(seq, cp):
  match four:
    case None{}:
      Empty.absurd(utf8_proof.Decodes(seq, cp), UTF8.false_true(Equal.cong(Maybe<&1, List<&2, U32>>, Bool, m => Maybe.is_some(&1, List<&2, U32>, m), None{}, Some{seq}, e)))
    case Some{p}:
      utf8_proof.to_old.four.l0(p, seq, cp, sc, no3, checked, e)

def utf8_proof.to_old.three.l1(+b1: U32, r: U32 & U32, +seq: List<&2, U32>, +cp: U32, +sc: {Laws.is_unicode_scalar(cp) == True{} : Bool}, +no2: {Laws.two_byte_shape(cp) == None{} : Maybe<&1, U32 & U32>}, +checked: {Laws.three_byte_shape(cp) == Some{(b1, r)} : Maybe<&1, U32 & U32 & U32>}, e: {Laws.encoding.three(cp, Some{(b1, r)}) == Some{seq} : Maybe<&1, List<&2, U32>>}) -> utf8_proof.Decodes(seq, cp):
  match r:
    case (+b2, +b3):
      %utf8_proof.some_list([b1, b2, b3], seq, e) : utf8_proof.Decodes(_, cp)
      utf8_proof.three_decodes(cp, b1, b2, b3, sc, no2, checked)

def utf8_proof.to_old.three.l0(r: U32 & U32 & U32, +seq: List<&2, U32>, +cp: U32, +sc: {Laws.is_unicode_scalar(cp) == True{} : Bool}, +no2: {Laws.two_byte_shape(cp) == None{} : Maybe<&1, U32 & U32>}, +checked: {Laws.three_byte_shape(cp) == Some{r} : Maybe<&1, U32 & U32 & U32>}, e: {Laws.encoding.three(cp, Some{r}) == Some{seq} : Maybe<&1, List<&2, U32>>}) -> utf8_proof.Decodes(seq, cp):
  match r:
    case (+b1, r2):
      utf8_proof.to_old.three.l1(b1, r2, seq, cp, sc, no2, checked, e)

def utf8_proof.to_old.three(+seq: List<&2, U32>, +cp: U32, +sc: {Laws.is_unicode_scalar(cp) == True{} : Bool},
  +no2: {Laws.two_byte_shape(cp) == None{} : Maybe<&1, U32 & U32>},
  three: Maybe<&1, U32 & U32 & U32>, +checked: {Laws.three_byte_shape(cp) == three : Maybe<&1, U32 & U32 & U32>},
  e: {Laws.encoding.three(cp, three) == Some{seq} : Maybe<&1, List<&2, U32>>}) -> utf8_proof.Decodes(seq, cp):
  match three:
    case None{}:
      utf8_proof.to_old.four(seq, cp, sc, checked, Laws.four_byte_shape(cp), {==}, e)
    case Some{p}:
      utf8_proof.to_old.three.l0(p, seq, cp, sc, no2, checked, e)

def utf8_proof.to_old.two(+seq: List<&2, U32>, +cp: U32, +sc: {Laws.is_unicode_scalar(cp) == True{} : Bool},
  +no_one: {Laws.one_byte_shape(cp) == None{} : Maybe<&2, U32>},
  two: Maybe<&1, U32 & U32>, +checked: {Laws.two_byte_shape(cp) == two : Maybe<&1, U32 & U32>},
  e: {Laws.encoding.two(cp, two) == Some{seq} : Maybe<&1, List<&2, U32>>}) -> utf8_proof.Decodes(seq, cp):
  match two:
    case None{}:
      utf8_proof.to_old.three(seq, cp, sc, checked, Laws.three_byte_shape(cp), {==}, e)
    case Some{p}:
      (+b1, +b2) = p
      %utf8_proof.some_list([b1, b2], seq, e) : utf8_proof.Decodes(_, cp)
      utf8_proof.two_decodes(cp, b1, b2, no_one, checked)

def utf8_proof.to_old.one(+seq: List<&2, U32>, +cp: U32, +sc: {Laws.is_unicode_scalar(cp) == True{} : Bool}, one: Maybe<&2, U32>,
  +checked: {Laws.one_byte_shape(cp) == one : Maybe<&2, U32>},
  e: {Laws.encoding.if(cp, one) == Some{seq} : Maybe<&1, List<&2, U32>>}) -> utf8_proof.Decodes(seq, cp):
  match one:
    case Some{+b}:
      %utf8_proof.some_list([b], seq, e) : utf8_proof.Decodes(_, cp)
      utf8_proof.one_decodes(cp, b, checked)
    case None{}:
      utf8_proof.to_old.two(seq, cp, sc, checked, Laws.two_byte_shape(cp), {==}, e)

def utf8_proof.to_old(+seq: List<&2, U32>, +cp: U32, enc: Laws.encodes(seq, cp)) -> utf8_proof.Decodes(seq, cp):
  (scalar, e) = enc
  utf8_proof.to_old.one(seq, cp, scalar, Laws.one_byte_shape(cp), {==}, e)

# The valid sequences are exactly the encodings.

def utf8_proof.one_scalar_valid(+b: U32, +cp: U32, valid: Bool,
  +checked: {UTF8.valid_one_byte(b) == valid : Bool},
  e: {utf8_proof.one_byte_scalar.if(b, valid, checked) == Some{cp} : Maybe<&2, U32>}) ->
  {UTF8.valid_one_byte(b) == True{} : Bool}:
  match valid:
    case False{}:
      Empty.absurd({UTF8.valid_one_byte(b) == True{} : Bool},
        UTF8.false_true(Equal.cong(Maybe<&2, U32>, Bool, m => Maybe.is_some(&2, U32, m),
          None{}, Some{cp}, e)))
    case True{}:
      checked

def utf8_proof.decodes_valid(+seq: List<&2, U32>, +cp: U32, decoded: utf8_proof.Decodes(seq, cp)) ->
  {utf8_proof.bool.is_valid_sequence(seq) == True{} : Bool}:
  match seq:
    case Nil{}:
      Empty.absurd({utf8_proof.bool.is_valid_sequence(Nil{}) == True{} : Bool}, decoded)
    case +x <> Nil{}:
      utf8_proof.one_scalar_valid(x, cp, UTF8.valid_one_byte(x), {==}, decoded)
    case +x <> +y <> Nil{}:
      utf8_proof.two_scalar_valid(x, y, cp, UTF8.valid_two_bytes(x, y), {==}, decoded)
    case +x <> +y <> +z <> Nil{}:
      utf8_proof.three_scalar_valid(x, y, z, cp, UTF8.valid_three_bytes(x, y, z), {==}, decoded)
    case +x <> +y <> +z <> +w <> Nil{}:
      utf8_proof.four_scalar_valid(x, y, z, w, cp, UTF8.valid_four_bytes(x, y, z, w), {==}, decoded)
    case x <> y <> z <> w <> v <> rest:
      Empty.absurd({utf8_proof.bool.is_valid_sequence(x <> y <> z <> w <> v <> rest) == True{} : Bool}, decoded)

def utf8_proof.two_valid_encodes(+x: U32, +y: U32, +valid: {UTF8.valid_two_bytes(x, y) == True{} : Bool}) ->
  Exists(U32, cp => Laws.encodes([x, y], cp)):
  +shape = utf8_proof.valid_two_bytes_has_shape(x, y, valid)
  (UTF8.decode_two_bytes(x, y, shape), utf8_proof.two_encodes(x, y, shape, valid))

def utf8_proof.three_valid_encodes(+x: U32, +y: U32, +z: U32, +valid: {UTF8.valid_three_bytes(x, y, z) == True{} : Bool}) ->
  Exists(U32, cp => Laws.encodes([x, y, z], cp)):
  +shape = UTF8.valid_three_bytes.has_shape(x, y, z, valid)
  (UTF8.decode_three_bytes(x, y, z, shape), utf8_proof.three_encodes(x, y, z, shape, valid))

def utf8_proof.four_valid_encodes(+x: U32, +y: U32, +z: U32, +w: U32, +valid: {UTF8.valid_four_bytes(x, y, z, w) == True{} : Bool}) ->
  Exists(U32, cp => Laws.encodes([x, y, z, w], cp)):
  +shape = UTF8.valid_four_bytes.has_shape(x, y, z, w, valid)
  (UTF8.decode_four_bytes(x, y, z, w, shape), utf8_proof.four_encodes(x, y, z, w, shape, valid))

def utf8_proof.valid_encodes(+seq: List<&2, U32>, valid: {utf8_proof.bool.is_valid_sequence(seq) == True{} : Bool}) ->
  Exists(U32, cp => Laws.encodes(seq, cp)):
  match seq:
    case Nil{}:
      Empty.absurd(Exists(U32, cp => Laws.encodes(Nil{}, cp)), UTF8.false_true(valid))
    case +x <> Nil{}:
      (x, utf8_proof.one_encodes(x, valid))
    case +x <> +y <> Nil{}:
      utf8_proof.two_valid_encodes(x, y, valid)
    case +x <> +y <> +z <> Nil{}:
      utf8_proof.three_valid_encodes(x, y, z, valid)
    case +x <> +y <> +z <> +w <> Nil{}:
      utf8_proof.four_valid_encodes(x, y, z, w, valid)
    case x <> y <> z <> w <> v <> rest:
      Empty.absurd(Exists(U32, cp => Laws.encodes(x <> y <> z <> w <> v <> rest, cp)), UTF8.false_true(valid))

def utf8_proof.encodes_valid(+seq: List<&2, U32>, some: Exists(U32, cp => Laws.encodes(seq, cp))) ->
  {utf8_proof.bool.is_valid_sequence(seq) == True{} : Bool}:
  (+cp, enc) = some
  utf8_proof.decodes_valid(seq, cp, utf8_proof.to_old(seq, cp, enc))

def utf8_proof.bool.valid_sequence_encodes(+seq: List<&2, U32>) ->
  ({utf8_proof.bool.is_valid_sequence(seq) == True{} : Bool} -> (Exists(U32, cp => Laws.encodes(seq, cp)))) &
  ((Exists(U32, cp => Laws.encodes(seq, cp))) -> {utf8_proof.bool.is_valid_sequence(seq) == True{} : Bool}):
  (valid => utf8_proof.valid_encodes(seq, valid),
   some => utf8_proof.encodes_valid(seq, some))

# A valid sequence at the front of the buffer is what `next_scalar` finds.
def utf8_proof.next_of_encodes(+seq: List<&2, U32>, +cp: U32, +rest: List<&2, U32>,
  enc: utf8_proof.Decodes(seq, cp)) ->
  {utf8_proof.next_scalar(List.append(&2, U32, seq, rest)) == Some{(cp, rest)} : Maybe<&1, U32 & List<&2, U32>>}:
  match seq:
    case Nil{}:
      Empty.absurd({utf8_proof.next_scalar(rest) == Some{(cp, rest)} : Maybe<&1, U32 & List<&2, U32>>}, enc)
    case +x <> Nil{}:
      utf8_proof.next_one(x, rest, cp, enc)
    case +x <> +y <> Nil{}:
      utf8_proof.next_two_valid(x, y, rest, cp, enc)
    case +x <> +y <> +z <> Nil{}:
      utf8_proof.next_three_valid(x, y, z, rest, cp, enc)
    case +x <> +y <> +z <> +w <> Nil{}:
      utf8_proof.next_four_valid(x, y, z, w, rest, cp, enc)
    case x <> y <> z <> w <> v <> more:
      Empty.absurd({utf8_proof.next_scalar(List.append(&2, U32, (x <> y <> z <> w <> v <> more), rest)) == Some{(cp, rest)} : Maybe<&1, U32 & List<&2, U32>>}, enc)

def utf8_proof.next_of_begins(+bytes: List<&2, U32>, +cp: U32, +rest: List<&2, U32>,
  begins: Laws.begins_with_scalar(bytes, cp, rest)) ->
  {utf8_proof.next_scalar(bytes) == Some{(cp, rest)} : Maybe<&1, U32 & List<&2, U32>>}:
  (+seq, facts) = begins
  (enc, split) = facts
  %split : {utf8_proof.next_scalar(_) == Some{(cp, rest)} : Maybe<&1, U32 & List<&2, U32>>}
  utf8_proof.next_of_encodes(seq, cp, rest, utf8_proof.to_old(seq, cp, enc))

def Laws.begins_with_scalar_unique(bytes, cp1, rest1, cp2, rest2, first, second):
  +same = Equal.trans(Maybe<&1, U32 & List<&2, U32>>, Some{(cp1, rest1)},
    utf8_proof.next_scalar(bytes), Some{(cp2, rest2)},
    Equal.sym(Maybe<&1, U32 & List<&2, U32>>, utf8_proof.next_scalar(bytes), Some{(cp1, rest1)},
      utf8_proof.next_of_begins(bytes, cp1, rest1, first)),
    utf8_proof.next_of_begins(bytes, cp2, rest2, second))
  (utf8_proof.some_first(cp1, cp2, rest1, rest2, same),
   utf8_proof.some_rest(cp1, cp2, rest1, rest2, same))

def utf8_proof.no_valid_from_none.at(+bytes: List<&2, U32>,
  +none: {utf8_proof.next_scalar(bytes) == None{} : Maybe<&1, U32 & List<&2, U32>>},
  +cp: U32, +rest: List<&2, U32>, begins: Laws.begins_with_scalar(bytes, cp, rest)) -> Empty:
  utf8_proof.none_some(cp, rest,
    Equal.trans(Maybe<&1, U32 & List<&2, U32>>, None{}, utf8_proof.next_scalar(bytes), Some{(cp, rest)},
      Equal.sym(Maybe<&1, U32 & List<&2, U32>>, utf8_proof.next_scalar(bytes), None{}, none),
      utf8_proof.next_of_begins(bytes, cp, rest, begins)))

def utf8_proof.no_valid_from_none(+bytes: List<&2, U32>,
  +none: {utf8_proof.next_scalar(bytes) == None{} : Maybe<&1, U32 & List<&2, U32>>}) ->
  Laws.no_valid_sequence(bytes):
  cp => rest => begins => utf8_proof.no_valid_from_none.at(bytes, none, cp, rest, begins)

# What `next_scalar` finds is a valid sequence at the front.
def utf8_proof.Finds(bytes: List<&2, U32>, found: Maybe<&1, U32 & List<&2, U32>>) -> Type:
  match found:
    case None{}:
      Unit
    case Some{(cp, rest)}:
      Laws.begins_with_scalar(bytes, cp, rest)

def utf8_proof.finds.quad(+b1: U32, +b2: U32, +b3: U32, +b4: U32, +after: List<&2, U32>, m: Maybe<&2, U32>,
  checked: {UTF8.four_byte_scalar(b1, b2, b3, b4) == m : Maybe<&2, U32>}) ->
  utf8_proof.Finds(b1 <> b2 <> b3 <> b4 <> after, utf8_proof.next_scalar.found(m, after, r => None{})):
  match m:
    case None{}:
      Unit{}
    case Some{+c}:
      ([b1, b2, b3, b4], (utf8_proof.from_old([b1, b2, b3, b4], c, checked), {==}))

def utf8_proof.finds.four(+b1: U32, +b2: U32, +b3: U32, +rest: List<&2, U32>) ->
  utf8_proof.Finds(b1 <> b2 <> b3 <> rest, utf8_proof.next_scalar.four(b1, b2, b3, rest)):
  match rest:
    case Nil{}:
      Unit{}
    case +b4 <> +after:
      utf8_proof.finds.quad(b1, b2, b3, b4, after, UTF8.four_byte_scalar(b1, b2, b3, b4), {==})

def utf8_proof.finds.triple(+b1: U32, +b2: U32, +b3: U32, +after: List<&2, U32>, m: Maybe<&2, U32>,
  checked: {UTF8.three_byte_scalar(b1, b2, b3) == m : Maybe<&2, U32>}) ->
  utf8_proof.Finds(b1 <> b2 <> b3 <> after, utf8_proof.next_scalar.found(m, after, r => utf8_proof.next_scalar.four(b1, b2, b3, r))):
  match m:
    case None{}:
      utf8_proof.finds.four(b1, b2, b3, after)
    case Some{+c}:
      ([b1, b2, b3], (utf8_proof.from_old([b1, b2, b3], c, checked), {==}))

def utf8_proof.finds.three(+b1: U32, +b2: U32, +rest: List<&2, U32>) ->
  utf8_proof.Finds(b1 <> b2 <> rest, utf8_proof.next_scalar.three(b1, b2, rest)):
  match rest:
    case Nil{}:
      Unit{}
    case +b3 <> +after:
      utf8_proof.finds.triple(b1, b2, b3, after, UTF8.three_byte_scalar(b1, b2, b3), {==})

def utf8_proof.finds.pair(+b1: U32, +b2: U32, +after: List<&2, U32>, m: Maybe<&2, U32>,
  checked: {utf8_proof.two_byte_scalar(b1, b2) == m : Maybe<&2, U32>}) ->
  utf8_proof.Finds(b1 <> b2 <> after, utf8_proof.next_scalar.found(m, after, r => utf8_proof.next_scalar.three(b1, b2, r))):
  match m:
    case None{}:
      utf8_proof.finds.three(b1, b2, after)
    case Some{+c}:
      ([b1, b2], (utf8_proof.from_old([b1, b2], c, checked), {==}))

def utf8_proof.finds.two(+b1: U32, +rest: List<&2, U32>) ->
  utf8_proof.Finds(b1 <> rest, utf8_proof.next_scalar.two(b1, rest)):
  match rest:
    case Nil{}:
      Unit{}
    case +b2 <> +after:
      utf8_proof.finds.pair(b1, b2, after, utf8_proof.two_byte_scalar(b1, b2), {==})

def utf8_proof.finds.one(+b1: U32, +rest: List<&2, U32>, m: Maybe<&2, U32>,
  checked: {utf8_proof.one_byte_scalar(b1) == m : Maybe<&2, U32>}) ->
  utf8_proof.Finds(b1 <> rest,
    utf8_proof.next_scalar.found(m, rest, r => utf8_proof.next_scalar.two(b1, r))):
  match m:
    case None{}:
      utf8_proof.finds.two(b1, rest)
    case Some{+c}:
      ([b1], (utf8_proof.from_old([b1], c, checked), {==}))

def utf8_proof.finds(+bytes: List<&2, U32>) ->
  utf8_proof.Finds(bytes, utf8_proof.next_scalar(bytes)):
  match bytes:
    case Nil{}:
      Unit{}
    case +b1 <> +rest:
      utf8_proof.finds.one(b1, rest, utf8_proof.one_byte_scalar(b1), {==})

def utf8_proof.finds_at(+bytes: List<&2, U32>, -found: Maybe<&1, U32 & List<&2, U32>>,
  checked: {utf8_proof.next_scalar(bytes) == found : Maybe<&1, U32 & List<&2, U32>>}) ->
  utf8_proof.Finds(bytes, found):
  %checked : utf8_proof.Finds(bytes, _)
  utf8_proof.finds(bytes)

def utf8_proof.to_first.if(+b1: U32, +more: List<&2, U32>,
  found: Maybe<&1, U32 & List<&2, U32>>,
  checked: {utf8_proof.next_scalar(b1 <> more) == found : Maybe<&1, U32 & List<&2, U32>>},
  -result: Maybe<&1, U32 & List<&2, U32>>,
  decoded: utf8_proof.Decoded.nonempty(b1, more, found, result)) ->
  Laws.decodes_first.nonempty(b1, more, result):
  match found:
    case Some{x}:
      (+cp, +rest) = x
      Inl{(cp, (rest, (utf8_proof.finds_at(b1 <> more, Some{(cp, rest)}, checked), decoded)))}
    case None{}:
      Inr{(utf8_proof.no_valid_from_none(b1 <> more, checked), decoded)}

def utf8_proof.to_first(+b1: U32, +more: List<&2, U32>,
  -result: Maybe<&1, U32 & List<&2, U32>>,
  decoded: utf8_proof.Decoded.nonempty(b1, more, utf8_proof.next_scalar(b1 <> more), result)) ->
  Laws.decodes_first(b1 <> more, result):
  utf8_proof.to_first.if(b1, more, utf8_proof.next_scalar(b1 <> more), {==}, result, decoded)

def utf8_proof.from_first.scalar(+b1: U32, +more: List<&2, U32>,
  -result: Maybe<&1, U32 & List<&2, U32>>,
  scalar: Laws.decodes_first.scalar(b1 <> more, result)) ->
  utf8_proof.Decoded.nonempty(b1, more, utf8_proof.next_scalar(b1 <> more), result):
  (+cp, s1) = scalar
  (+rest, s2) = s1
  (begins, produced) = s2
  %Equal.sym(Maybe<&1, U32 & List<&2, U32>>, utf8_proof.next_scalar(b1 <> more), Some{(cp, rest)},
      utf8_proof.next_of_begins(b1 <> more, cp, rest, begins)) :
    utf8_proof.Decoded.nonempty(b1, more, _, result)
  produced

def utf8_proof.from_first.none(+b1: U32, +more: List<&2, U32>,
  found: Maybe<&1, U32 & List<&2, U32>>,
  checked: {utf8_proof.next_scalar(b1 <> more) == found : Maybe<&1, U32 & List<&2, U32>>},
  -result: Maybe<&1, U32 & List<&2, U32>>,
  none: Laws.no_valid_sequence(b1 <> more),
  replaced: Laws.decodes_first.replaced(b1, more, result)) ->
  utf8_proof.Decoded.nonempty(b1, more, found, result):
  match found:
    case None{}:
      replaced
    case Some{x}:
      (+cp, +rest) = x
      Empty.absurd({result == Some{(cp, rest)} : Maybe<&1, U32 & List<&2, U32>>},
        none(cp, rest, utf8_proof.finds_at(b1 <> more, Some{(cp, rest)}, checked)))

def utf8_proof.from_first(+b1: U32, +more: List<&2, U32>,
  -result: Maybe<&1, U32 & List<&2, U32>>,
  decoded: Laws.decodes_first(b1 <> more, result)) ->
  utf8_proof.Decoded.nonempty(b1, more, utf8_proof.next_scalar(b1 <> more), result):
  match decoded:
    case Inl{scalar}:
      utf8_proof.from_first.scalar(b1, more, result, scalar)
    case Inr{replaced}:
      (none, rep) = replaced
      utf8_proof.from_first.none(b1, more, utf8_proof.next_scalar(b1 <> more), {==}, result, none, rep)

# `decodes_first` for a buffer where `next_scalar` finds a scalar.
def utf8_proof.first_found(+b1: U32, +more: List<&2, U32>, +cp: U32, +rest: List<&2, U32>,
  e: {utf8_proof.next_scalar(b1 <> more) == Some{(cp, rest)} : Maybe<&1, U32 & List<&2, U32>>}) ->
  Laws.decodes_first(b1 <> more, Some{(cp, rest)}):
  Inl{(cp, (rest, (utf8_proof.finds_at(b1 <> more, Some{(cp, rest)}, e), {==})))}

# From the `utf8.bend` tests to the `LAWS.bend` definitions
# ---------------------------------------------------------
#
# `LAWS.bend` states valid sequences, valid sequence prefixes and
# maximal subparts as types.  The proofs above work with the Bool
# tests: `utf8_proof.bool.is_valid_sequence`,
# `UTF8.is_valid_sequence_prefix` and `utf8_proof.bool.maximal_subpart`.
# These convert between the two, and prove the `LAWS.bend` laws about
# prefixes and maximal subparts from the Bool versions.

# The two directions of an "if and only if" stated as a pair.
def utf8_proof.iff.to(-A: Type, -B: Type, both: (A -> B) & (B -> A), a: A) -> B:
  (to, from) = both
  to(a)

def utf8_proof.iff.from(-A: Type, -B: Type, both: (A -> B) & (B -> A), b: B) -> A:
  (to, from) = both
  from(b)

def utf8_proof.valid_to_laws(+seq: List<&2, U32>,
  valid: {utf8_proof.bool.is_valid_sequence(seq) == True{} : Bool}) ->
  Laws.is_valid_sequence(seq):
  utf8_proof.iff.to({utf8_proof.bool.is_valid_sequence(seq) == True{} : Bool},
    Exists(U32, cp => Laws.encodes(seq, cp)),
    utf8_proof.bool.valid_sequence_encodes(seq), valid)

def utf8_proof.valid_from_laws(+seq: List<&2, U32>,
  valid: Laws.is_valid_sequence(seq)) ->
  {utf8_proof.bool.is_valid_sequence(seq) == True{} : Bool}:
  utf8_proof.iff.from({utf8_proof.bool.is_valid_sequence(seq) == True{} : Bool},
    Exists(U32, cp => Laws.encodes(seq, cp)),
    utf8_proof.bool.valid_sequence_encodes(seq), valid)

def utf8_proof.completion_to_laws(+seq: List<&2, U32>,
  completion: Exists(List<&2, U32>, rest =>
    {utf8_proof.bool.is_valid_sequence(List.append(&2, U32, seq, rest)) == True{} : Bool})) ->
  Exists(List<&2, U32>, rest => Laws.is_valid_sequence(List.append(&2, U32, seq, rest))):
  (+rest, valid) = completion
  (rest, utf8_proof.valid_to_laws(List.append(&2, U32, seq, rest), valid))

def utf8_proof.completion_from_laws(+seq: List<&2, U32>,
  completion: Exists(List<&2, U32>, rest => Laws.is_valid_sequence(List.append(&2, U32, seq, rest)))) ->
  Exists(List<&2, U32>, rest =>
    {utf8_proof.bool.is_valid_sequence(List.append(&2, U32, seq, rest)) == True{} : Bool}):
  (+rest, valid) = completion
  (rest, utf8_proof.valid_from_laws(List.append(&2, U32, seq, rest), valid))

def utf8_proof.prefix_to_laws(+seq: List<&2, U32>,
  begins: {UTF8.is_valid_sequence_prefix(seq) == True{} : Bool}) ->
  Laws.is_valid_sequence_prefix(seq):
  match seq:
    case Nil{}:
      UTF8.false_true(begins)
    case +b1 <> +more:
      utf8_proof.completion_to_laws(b1 <> more,
        utf8_proof.iff.to({UTF8.is_valid_sequence_prefix(b1 <> more) == True{} : Bool},
          Exists(List<&2, U32>, rest =>
          {utf8_proof.bool.is_valid_sequence(List.append(&2, U32, b1 <> more, rest)) == True{} : Bool}),
          utf8_proof.impl.is_valid_sequence_prefix(b1, more), begins))

def utf8_proof.prefix_from_laws(+seq: List<&2, U32>,
  begins: Laws.is_valid_sequence_prefix(seq)) ->
  {UTF8.is_valid_sequence_prefix(seq) == True{} : Bool}:
  match seq:
    case Nil{}:
      Empty.absurd({UTF8.is_valid_sequence_prefix(Nil{}) == True{} : Bool}, begins)
    case +b1 <> +more:
      utf8_proof.iff.from({UTF8.is_valid_sequence_prefix(b1 <> more) == True{} : Bool},
        Exists(List<&2, U32>, rest =>
          {utf8_proof.bool.is_valid_sequence(List.append(&2, U32, b1 <> more, rest)) == True{} : Bool}),
        utf8_proof.impl.is_valid_sequence_prefix(b1, more),
        utf8_proof.completion_from_laws(b1 <> more, begins))

# A sequence that fails the Bool test is not a valid sequence prefix.
def utf8_proof.not_prefix_absurd(+seq: List<&2, U32>,
  not_begins: {UTF8.is_valid_sequence_prefix(seq) == False{} : Bool},
  begins: Laws.is_valid_sequence_prefix(seq)) -> Empty:
  utf8_proof.true_false(Equal.trans(Bool, True{}, UTF8.is_valid_sequence_prefix(seq), False{},
    Equal.sym(Bool, UTF8.is_valid_sequence_prefix(seq), True{}, utf8_proof.prefix_from_laws(seq, begins)),
    not_begins))

def utf8_proof.not_prefix_from_laws.if(+seq: List<&2, U32>, begins: Bool,
  checked: {UTF8.is_valid_sequence_prefix(seq) == begins : Bool},
  not_begins: Laws.is_valid_sequence_prefix(seq) -> Empty) ->
  {UTF8.is_valid_sequence_prefix(seq) == False{} : Bool}:
  match begins:
    case True{}:
      Empty.absurd({UTF8.is_valid_sequence_prefix(seq) == False{} : Bool},
        not_begins(utf8_proof.prefix_to_laws(seq, checked)))
    case False{}:
      checked

def utf8_proof.not_prefix_from_laws(+seq: List<&2, U32>,
  not_begins: Laws.is_valid_sequence_prefix(seq) -> Empty) ->
  {UTF8.is_valid_sequence_prefix(seq) == False{} : Bool}:
  utf8_proof.not_prefix_from_laws.if(seq, UTF8.is_valid_sequence_prefix(seq), {==}, not_begins)

def utf8_proof.longer_to_laws(+subpart: List<&2, U32>, +bytes: List<&2, U32>,
  longer: utf8_proof.bool.maximal_subpart.longer_not_valid_prefix(subpart, bytes)) ->
  Laws.maximal_subpart.longer_not_valid_prefix(subpart, bytes):
  +c => +extra => prefix => begins =>
    utf8_proof.not_prefix_absurd(List.append(&2, U32, subpart, c <> extra),
      longer(c, extra, prefix), begins)

def utf8_proof.longer_from_laws(+subpart: List<&2, U32>, +bytes: List<&2, U32>,
  longer: Laws.maximal_subpart.longer_not_valid_prefix(subpart, bytes)) ->
  utf8_proof.bool.maximal_subpart.longer_not_valid_prefix(subpart, bytes):
  +c => +extra => prefix =>
    utf8_proof.not_prefix_from_laws(List.append(&2, U32, subpart, c <> extra),
      longer(c, extra, prefix))

# When `[b1]` is not a valid sequence prefix, no longer prefix is one.
def utf8_proof.single_longer(+b1: U32, +more: List<&2, U32>,
  not_begins: {UTF8.is_valid_sequence_prefix([b1]) == False{} : Bool}) ->
  Laws.maximal_subpart.longer_not_valid_prefix([b1], b1 <> more):
  +c => +extra => prefix => begins =>
    utf8_proof.not_prefix_absurd(List.append(&2, U32, [b1], c <> extra),
      utf8_proof.impl.not_valid_sequence_prefix_extended(b1, Nil{}, c <> extra, not_begins),
      begins)

def utf8_proof.maximal_to_laws.if(+b1: U32, +more: List<&2, U32>, begins: Bool,
  checked: {UTF8.is_valid_sequence_prefix([b1]) == begins : Bool},
  +subpart: List<&2, U32>,
  maximal: utf8_proof.bool.maximal_subpart.if(b1, more, begins, subpart)) ->
  Laws.maximal_subpart(b1, more, subpart):
  match begins:
    case True{}:
      (prefix, facts) = maximal
      (begins_sub, longer) = facts
      (prefix, (Inl{utf8_proof.prefix_to_laws(subpart, begins_sub)},
        utf8_proof.longer_to_laws(subpart, b1 <> more, longer)))
    case False{}:
      %Equal.sym(List<&2, U32>, subpart, [b1], maximal) : Laws.maximal_subpart(b1, more, _)
      ((more, {==}), (Inr{{==}}, utf8_proof.single_longer(b1, more, checked)))

def utf8_proof.maximal_to_laws(+b1: U32, +more: List<&2, U32>, +subpart: List<&2, U32>,
  maximal: utf8_proof.bool.maximal_subpart(b1, more, subpart)) ->
  Laws.maximal_subpart(b1, more, subpart):
  utf8_proof.maximal_to_laws.if(b1, more, UTF8.is_valid_sequence_prefix([b1]), {==}, subpart, maximal)

def utf8_proof.prefix_or_single(+b1: U32, +subpart: List<&2, U32>,
  first: {UTF8.is_valid_sequence_prefix([b1]) == True{} : Bool},
  either: Or(Laws.is_valid_sequence_prefix(subpart), {subpart == [b1] : List<&2, U32>})) ->
  {UTF8.is_valid_sequence_prefix(subpart) == True{} : Bool}:
  match either:
    case Inl{begins}:
      utf8_proof.prefix_from_laws(subpart, begins)
    case Inr{e}:
      %Equal.sym(List<&2, U32>, subpart, [b1], e) : {UTF8.is_valid_sequence_prefix(_) == True{} : Bool}
      first

def utf8_proof.not_prefix_single.move(+h: U32, +b1: U32, e: {b1 == h : U32},
  not_begins: {UTF8.is_valid_sequence_prefix([b1]) == False{} : Bool}) ->
  {UTF8.is_valid_sequence_prefix([h]) == False{} : Bool}:
  %e : {UTF8.is_valid_sequence_prefix([_]) == False{} : Bool}
  not_begins

# A valid sequence prefix that starts with `h`, when `[h]` is not one,
# is `[h]` itself.
def utf8_proof.prefix_single.tail(+h: U32, +tail: List<&2, U32>,
  not_begins: {UTF8.is_valid_sequence_prefix([h]) == False{} : Bool},
  begins: Laws.is_valid_sequence_prefix(h <> tail)) -> {h <> tail == [h] : List<&2, U32>}:
  match tail:
    case Nil{}:
      {==}
    case +c <> +extra:
      Empty.absurd({h <> (c <> extra) == [h] : List<&2, U32>},
        utf8_proof.not_prefix_absurd(List.append(&2, U32, [h], c <> extra),
          utf8_proof.impl.not_valid_sequence_prefix_extended(h, Nil{}, c <> extra, not_begins),
          begins))

# When `[b1]` is not a valid sequence prefix, a prefix of `b1 <> more`
# that is one can only be `[b1]` (so in fact there is none).
def utf8_proof.prefix_single(+b1: U32, +more: List<&2, U32>, +subpart: List<&2, U32>,
  not_begins: {UTF8.is_valid_sequence_prefix([b1]) == False{} : Bool},
  prefix: Laws.is_prefix(subpart, b1 <> more),
  begins: Laws.is_valid_sequence_prefix(subpart)) -> {subpart == [b1] : List<&2, U32>}:
  match subpart:
    case Nil{}:
      Empty.absurd({Nil{} == [b1] : List<&2, U32>}, begins)
    case +h <> +tail:
      (+rest, split) = prefix
      +same = utf8_proof.cons_head(h, b1, List.append(&2, U32, tail, rest), more, split)
      Equal.trans(List<&2, U32>, h <> tail, [h], [b1],
        utf8_proof.prefix_single.tail(h, tail,
          utf8_proof.not_prefix_single.move(h, b1, Equal.sym(U32, h, b1, same), not_begins), begins),
        Equal.cong(U32, List<&2, U32>, x => [x], h, b1, same))

def utf8_proof.single_from_or(+b1: U32, +more: List<&2, U32>, +subpart: List<&2, U32>,
  not_first: {UTF8.is_valid_sequence_prefix([b1]) == False{} : Bool},
  prefix: Laws.is_prefix(subpart, b1 <> more),
  either: Or(Laws.is_valid_sequence_prefix(subpart), {subpart == [b1] : List<&2, U32>})) ->
  {subpart == [b1] : List<&2, U32>}:
  match either:
    case Inl{begins}:
      utf8_proof.prefix_single(b1, more, subpart, not_first, prefix, begins)
    case Inr{e}:
      e

def utf8_proof.maximal_from_laws.if(+b1: U32, +more: List<&2, U32>, begins: Bool,
  checked: {UTF8.is_valid_sequence_prefix([b1]) == begins : Bool},
  +subpart: List<&2, U32>,
  maximal: Laws.maximal_subpart(b1, more, subpart)) ->
  utf8_proof.bool.maximal_subpart.if(b1, more, begins, subpart):
  match begins:
    case True{}:
      (prefix, facts) = maximal
      (either, longer) = facts
      (prefix, (utf8_proof.prefix_or_single(b1, subpart, checked, either),
        utf8_proof.longer_from_laws(subpart, b1 <> more, longer)))
    case False{}:
      (prefix, facts) = maximal
      (either, longer) = facts
      utf8_proof.single_from_or(b1, more, subpart, checked, prefix, either)

def utf8_proof.maximal_from_laws(+b1: U32, +more: List<&2, U32>, +subpart: List<&2, U32>,
  maximal: Laws.maximal_subpart(b1, more, subpart)) ->
  utf8_proof.bool.maximal_subpart(b1, more, subpart):
  utf8_proof.maximal_from_laws.if(b1, more, UTF8.is_valid_sequence_prefix([b1]), {==}, subpart, maximal)

def utf8_proof.valid_assoc(+x: List<&2, U32>, +y: List<&2, U32>, +z: List<&2, U32>,
  valid: Laws.is_valid_sequence(List.append(&2, U32, List.append(&2, U32, x, y), z))) ->
  Laws.is_valid_sequence(List.append(&2, U32, x, List.append(&2, U32, y, z))):
  %utf8_proof.append_assoc(x, y, z) : Laws.is_valid_sequence(_)
  valid

# A completion of `b1 <> more` followed by `extra` completes `b1 <> more`.
def utf8_proof.extended_completion(+b1: U32, +more: List<&2, U32>, +extra: List<&2, U32>,
  begins: Laws.is_valid_sequence_prefix(List.append(&2, U32, b1 <> more, extra))) ->
  Laws.is_valid_sequence_prefix(b1 <> more):
  (+rest, valid) = begins
  (List.append(&2, U32, extra, rest), utf8_proof.valid_assoc(b1 <> more, extra, rest, valid))

def Laws.not_valid_sequence_prefix_extended(b1, more, extra, invalid):
  begins => invalid(utf8_proof.extended_completion(b1, more, extra, begins))

def utf8_proof.maximal_exists_to_laws(+b1: U32, +more: List<&2, U32>,
  found: Exists(List<&2, U32>, s => utf8_proof.bool.maximal_subpart(b1, more, s))) ->
  Exists(List<&2, U32>, s => Laws.maximal_subpart(b1, more, s)):
  (+s, maximal) = found
  (s, utf8_proof.maximal_to_laws(b1, more, s, maximal))

def Laws.maximal_subpart_exists(b1, more, invalid):
  utf8_proof.maximal_exists_to_laws(b1, more, utf8_proof.bool.maximal_subpart_exists(b1, more, invalid))

def Laws.maximal_subpart_unique(b1, more, s1, s2, p1, p2):
  utf8_proof.bool.maximal_subpart_unique(b1, more, s1, s2,
    utf8_proof.maximal_from_laws(b1, more, s1, p1),
    utf8_proof.maximal_from_laws(b1, more, s2, p2))

# `decodes_first` for a buffer that does not begin with a valid
# sequence, given its maximal subpart.
def utf8_proof.first_replaced(+b1: U32, +more: List<&2, U32>, +sub: List<&2, U32>,
  +rest: List<&2, U32>,
  e: {utf8_proof.next_scalar(b1 <> more) == None{} : Maybe<&1, U32 & List<&2, U32>>},
  maximal: utf8_proof.bool.maximal_subpart(b1, more, sub),
  split: {List.append(&2, U32, sub, rest) == b1 <> more : List<&2, U32>}) ->
  Laws.decodes_first(b1 <> more, Some{(Laws.replacement_char(), rest)}):
  Inr{(utf8_proof.no_valid_from_none(b1 <> more, e),
    (sub, (rest, (utf8_proof.maximal_to_laws(b1, more, sub, maximal), (split, {==})))))}

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
  utf8_proof.Progress(more, utf8_proof.next_scalar.found(scalar, rest, otherwise)):
  match scalar:
    case Some{cp}: suffix
    case None{}: other

def utf8_proof.progress_cons.pair(+b: U32, +more: List<&2, U32>, x: U32 & List<&2, U32>,
  p: utf8_proof.Progress.pair(more, x)) -> utf8_proof.Progress.pair(b <> more, x):
  (cp, +rest) = x
  (+q, e) = p
  (b <> q, Equal.cong(List<&2, U32>, List<&2, U32>, xs => b <> xs, List.append(&2, U32, q, rest), more, e))

def utf8_proof.progress_cons(+b: U32, +more: List<&2, U32>, result: Maybe<&1, U32 & List<&2, U32>>, p: utf8_proof.Progress(more, result)) ->
  utf8_proof.Progress(b <> more, result):
  match result:
    case None{}: Unit{}
    case Some{x}: utf8_proof.progress_cons.pair(b, more, x, p)

def utf8_proof.next_four_progress(+b1: U32, +b2: U32, +b3: U32, +more: List<&2, U32>) ->
  utf8_proof.Progress(more, utf8_proof.next_scalar.four(b1, b2, b3, more)):
  match more:
    case Nil{}:
      Unit{}
    case +b4 <> +after:
      utf8_proof.next_found_progress(UTF8.four_byte_scalar(b1, b2, b3, b4), after, r => None{},
        b4 <> after, ([b4], {==}), Unit{})

def utf8_proof.next_three_progress(+b1: U32, +b2: U32, +more: List<&2, U32>) ->
  utf8_proof.Progress(more, utf8_proof.next_scalar.three(b1, b2, more)):
  match more:
    case Nil{}:
      Unit{}
    case +b3 <> +after:
      utf8_proof.next_found_progress(UTF8.three_byte_scalar(b1, b2, b3), after, r => utf8_proof.next_scalar.four(b1, b2, b3, r),
        b3 <> after, ([b3], {==}),
        utf8_proof.progress_cons(b3, after, utf8_proof.next_scalar.four(b1, b2, b3, after), utf8_proof.next_four_progress(b1, b2, b3, after)))

def utf8_proof.next_two_progress(+b1: U32, +more: List<&2, U32>) ->
  utf8_proof.Progress(more, utf8_proof.next_scalar.two(b1, more)):
  match more:
    case Nil{}:
      Unit{}
    case +b2 <> +after:
      utf8_proof.next_found_progress(utf8_proof.two_byte_scalar(b1, b2), after, r => utf8_proof.next_scalar.three(b1, b2, r),
        b2 <> after, ([b2], {==}),
        utf8_proof.progress_cons(b2, after, utf8_proof.next_scalar.three(b1, b2, after), utf8_proof.next_three_progress(b1, b2, after)))

def utf8_proof.next_progress(+b1: U32, +more: List<&2, U32>) ->
  utf8_proof.Progress(more, utf8_proof.next_scalar(b1 <> more)):
  utf8_proof.next_found_progress(utf8_proof.one_byte_scalar(b1), more,
    r => utf8_proof.next_scalar.two(b1, r), more, (Nil{}, {==}),
    utf8_proof.next_two_progress(b1, more))

def utf8_proof.next_progress_at(+b1: U32, +more: List<&2, U32>,
  -found: Maybe<&1, U32 & List<&2, U32>>,
  checked: {utf8_proof.next_scalar(b1 <> more) == found : Maybe<&1, U32 & List<&2, U32>>}) ->
  utf8_proof.Progress(more, found):
  %checked : utf8_proof.Progress(more, _)
  utf8_proof.next_progress(b1, more)

# The replaced result with its maximal subpart in the Bool form, as
# `Laws.decodes_first.replaced`.
def utf8_proof.replaced_to_laws(+b1: U32, +more: List<&2, U32>,
  found: Exists(Maybe<&1, U32 & List<&2, U32>>, result =>
    Exists(List<&2, U32>, subpart => Exists(List<&2, U32>, rest =>
      utf8_proof.bool.maximal_subpart(b1, more, subpart) &
      {List.append(&2, U32, subpart, rest) == b1 <> more : List<&2, U32>} &
      {result == Some{(Laws.replacement_char(), rest)} : Maybe<&1, U32 & List<&2, U32>>})) &
    utf8_proof.Progress(more, result))) ->
  Exists(Maybe<&1, U32 & List<&2, U32>>, result =>
    Laws.decodes_first.replaced(b1, more, result) & utf8_proof.Progress(more, result)):
  (result, both) = found
  (replaced, progress) = both
  (+subpart, r1) = replaced
  (+rest, r2) = r1
  (maximal, r3) = r2
  (result, ((subpart, (rest, (utf8_proof.maximal_to_laws(b1, more, subpart, maximal), r3))), progress))

# The replaced result, given the maximal subpart: U+FFFD and the bytes
# after the subpart, which its `is_prefix` clause supplies.  The subpart
# is not empty, since `[]` is not a valid sequence prefix; so the bytes
# after it are a suffix of `more`.
def utf8_proof.replaced_from.sequence(+b1: U32, +more: List<&2, U32>,
  checked: {UTF8.is_valid_sequence_prefix([b1]) == True{} : Bool},
  +sub: List<&2, U32>, +rest: List<&2, U32>,
  +split: {List.append(&2, U32, sub, rest) == b1 <> more : List<&2, U32>},
  facts: {UTF8.is_valid_sequence_prefix(sub) == True{} : Bool} &
    utf8_proof.bool.maximal_subpart.longer_not_valid_prefix(sub, b1 <> more)) ->
  Exists(Maybe<&1, U32 & List<&2, U32>>, result =>
    Exists(List<&2, U32>, subpart => Exists(List<&2, U32>, rest =>
      utf8_proof.bool.maximal_subpart.sequence_prefix(b1, more, subpart) &
      {List.append(&2, U32, subpart, rest) == b1 <> more : List<&2, U32>} &
      {result == Some{(Laws.replacement_char(), rest)} : Maybe<&1, U32 & List<&2, U32>>})) &
    utf8_proof.Progress(more, result)):
  match sub:
    case Nil{}:
      (begins_sub, longer_not_valid) = facts
      Empty.absurd(Exists(Maybe<&1, U32 & List<&2, U32>>, result =>
          Exists(List<&2, U32>, subpart => Exists(List<&2, U32>, rest =>
            utf8_proof.bool.maximal_subpart.sequence_prefix(b1, more, subpart) &
            {List.append(&2, U32, subpart, rest) == b1 <> more : List<&2, U32>} &
            {result == Some{(Laws.replacement_char(), rest)} : Maybe<&1, U32 & List<&2, U32>>})) &
          utf8_proof.Progress(more, result)),
        utf8_proof.true_false(Equal.trans(Bool, True{}, UTF8.is_valid_sequence_prefix(Nil{}), False{},
          Equal.sym(Bool, UTF8.is_valid_sequence_prefix(Nil{}), True{}, begins_sub),
          utf8_proof.impl.empty_not_valid_sequence_prefix())))
    case +s <> +ss:
      (Some{(Laws.replacement_char(), rest)},
        ((s <> ss, (rest, (((rest, split), facts), (split, {==})))),
         (ss, utf8_proof.cons_tail(s, b1, List.append(&2, U32, ss, rest), more, split))))

def utf8_proof.replaced_from.if(+b1: U32, +more: List<&2, U32>, begins: Bool,
  checked: {UTF8.is_valid_sequence_prefix([b1]) == begins : Bool},
  +sub: List<&2, U32>, maximal: utf8_proof.bool.maximal_subpart.if(b1, more, begins, sub)) ->
  Exists(Maybe<&1, U32 & List<&2, U32>>, result =>
    Exists(List<&2, U32>, subpart => Exists(List<&2, U32>, rest =>
      utf8_proof.bool.maximal_subpart.if(b1, more, begins, subpart) &
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
  found: Exists(List<&2, U32>, subpart => utf8_proof.bool.maximal_subpart(b1, more, subpart))) ->
  Exists(Maybe<&1, U32 & List<&2, U32>>, result =>
    Laws.decodes_first.replaced(b1, more, result) & utf8_proof.Progress(more, result)):
  (+sub, maximal) = found
  utf8_proof.replaced_to_laws(b1, more,
    utf8_proof.replaced_from.if(b1, more, UTF8.is_valid_sequence_prefix([b1]), {==}, sub, maximal))

def utf8_proof.nonempty_exists(+b1: U32, +more: List<&2, U32>,
  found: Maybe<&1, U32 & List<&2, U32>>,
  checked: {utf8_proof.next_scalar(b1 <> more) == found : Maybe<&1, U32 & List<&2, U32>>}) ->
  Exists(Maybe<&1, U32 & List<&2, U32>>, result =>
    utf8_proof.Decoded.nonempty(b1, more, found, result) & utf8_proof.Progress(more, result)):
  match found:
    case Some{x}:
      (Some{x}, ({==}, utf8_proof.next_progress_at(b1, more, Some{x}, checked)))
    case None{}:
      utf8_proof.replaced_from(b1, more,
        utf8_proof.bool.maximal_subpart_exists(b1, more, utf8_proof.no_valid_from_none(b1 <> more, checked)))

# Decoding the first code point of a non-empty buffer has a result that
# leaves a suffix of the bytes after the first.
def utf8_proof.first_exists.convert(+b1: U32, +more: List<&2, U32>,
  found: Exists(Maybe<&1, U32 & List<&2, U32>>, result =>
    utf8_proof.Decoded.nonempty(b1, more, utf8_proof.next_scalar(b1 <> more), result) &
    utf8_proof.Progress(more, result))) ->
  Exists(Maybe<&1, U32 & List<&2, U32>>, result =>
    Laws.decodes_first(b1 <> more, result) & utf8_proof.Progress(more, result)):
  (result, both) = found
  (decoded, progress) = both
  (result, (utf8_proof.to_first(b1, more, result, decoded), progress))

def utf8_proof.first_exists(+b1: U32, +more: List<&2, U32>) ->
  Exists(Maybe<&1, U32 & List<&2, U32>>, result =>
    Laws.decodes_first(b1 <> more, result) & utf8_proof.Progress(more, result)):
  utf8_proof.first_exists.convert(b1, more,
    utf8_proof.nonempty_exists(b1, more, utf8_proof.next_scalar(b1 <> more), {==}))

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

def utf8_proof.nonempty_some(+b1: U32, +more: List<&2, U32>,
  found: Maybe<&1, U32 & List<&2, U32>>, result: Maybe<&1, U32 & List<&2, U32>>,
  decoded: utf8_proof.Decoded.nonempty(b1, more, found, result)) ->
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
  utf8_proof.nonempty_some(b1, more, utf8_proof.next_scalar(b1 <> more), result,
    utf8_proof.from_first(b1, more, result, decoded))

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

def utf8_proof.nonempty_unique(+b1: U32, +more: List<&2, U32>,
  found: Maybe<&1, U32 & List<&2, U32>>,
  r1: Maybe<&1, U32 & List<&2, U32>>, r2: Maybe<&1, U32 & List<&2, U32>>,
  d1: utf8_proof.Decoded.nonempty(b1, more, found, r1),
  d2: utf8_proof.Decoded.nonempty(b1, more, found, r2)) ->
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
      utf8_proof.nonempty_unique(b1, more, utf8_proof.next_scalar(b1 <> more), r1, r2,
        utf8_proof.from_first(b1, more, r1, d1), utf8_proof.from_first(b1, more, r2, d2))

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
  (([66], (utf8_proof.first_found(65, [66], 65, [66], {==}), ([], (utf8_proof.first_found(66, [], 66, [], {==}), {==})))),
  (([], (utf8_proof.first_found(194, [169], 169, [], {==}), {==})),
  (([65], (utf8_proof.first_replaced(194, [65], [194], [65], {==}, (([65], {==}), ({==}, utf8_proof.longer_not_valid_from_not_extended([194], [194, 65], {==}))), {==}), ([], (utf8_proof.first_found(65, [], 65, [], {==}), {==})))),
  (([128], (utf8_proof.first_replaced(192, [128], [192], [128], {==}, {==}, {==}), ([], (utf8_proof.first_replaced(128, [], [128], [], {==}, {==}, {==}), {==})))),
  (([], (utf8_proof.first_replaced(194, [], [194], [], {==}, (([], {==}), ({==}, utf8_proof.longer_not_valid_from_not_extended([194], [194], Unit{}))), {==}), {==})),
  (([194, 169], (utf8_proof.first_replaced(194, [194, 169], [194], [194, 169], {==}, (([194, 169], {==}), ({==}, utf8_proof.longer_not_valid_from_not_extended([194], [194, 194, 169], {==}))), {==}), ([], (utf8_proof.first_found(194, [169], 169, [], {==}), {==})))),
  (([194, 169, 255], (utf8_proof.first_found(72, [194, 169, 255], 72, [194, 169, 255], {==}), ([255], (utf8_proof.first_found(194, [169, 255], 169, [255], {==}), ([], (utf8_proof.first_replaced(255, [], [255], [], {==}, {==}, {==}), {==})))))),
  (([], (utf8_proof.first_found(226, [130, 172], 8364, [], {==}), {==})),
  (([], (utf8_proof.first_found(240, [159, 152, 128], 128512, [], {==}), {==})),
  (([], (utf8_proof.first_replaced(226, [130], [226, 130], [], {==}, (([], {==}), ({==}, utf8_proof.longer_not_valid_from_not_extended([226, 130], [226, 130], Unit{}))), {==}), {==})),
  (([65], (utf8_proof.first_replaced(226, [130, 65], [226, 130], [65], {==}, (([65], {==}), ({==}, utf8_proof.longer_not_valid_from_not_extended([226, 130], [226, 130, 65], {==}))), {==}), ([], (utf8_proof.first_found(65, [], 65, [], {==}), {==})))),
  (([], (utf8_proof.first_replaced(240, [159, 152], [240, 159, 152], [], {==}, (([], {==}), ({==}, utf8_proof.longer_not_valid_from_not_extended([240, 159, 152], [240, 159, 152], Unit{}))), {==}), {==})),
  (([128, 128], (utf8_proof.first_replaced(224, [128, 128], [224], [128, 128], {==}, (([128, 128], {==}), ({==}, utf8_proof.longer_not_valid_from_not_extended([224], [224, 128, 128], {==}))), {==}), ([128], (utf8_proof.first_replaced(128, [128], [128], [128], {==}, {==}, {==}), ([], (utf8_proof.first_replaced(128, [], [128], [], {==}, {==}, {==}), {==})))))),
  (([160, 128], (utf8_proof.first_replaced(237, [160, 128], [237], [160, 128], {==}, (([160, 128], {==}), ({==}, utf8_proof.longer_not_valid_from_not_extended([237], [237, 160, 128], {==}))), {==}), ([128], (utf8_proof.first_replaced(160, [128], [160], [128], {==}, {==}, {==}), ([], (utf8_proof.first_replaced(128, [], [128], [], {==}, {==}, {==}), {==})))))),
  ([144, 128, 128], (utf8_proof.first_replaced(244, [144, 128, 128], [244], [144, 128, 128], {==}, (([144, 128, 128], {==}), ({==}, utf8_proof.longer_not_valid_from_not_extended([244], [244, 144, 128, 128], {==}))), {==}), ([128, 128], (utf8_proof.first_replaced(144, [128, 128], [144], [128, 128], {==}, {==}, {==}), ([128], (utf8_proof.first_replaced(128, [128], [128], [128], {==}, {==}, {==}), ([], (utf8_proof.first_replaced(128, [], [128], [], {==}, {==}, {==}), {==})))))))))))))))))))))))

# Running the decoder satisfies `decodes`
# ---------------------------------------
#
# The decoder's byte loop, `UTF8.decode_buffer.bytes`, keeps pending
# either nothing or some bytes that are a valid sequence prefix without
# being a whole valid sequence.  Each step turns a decoding of what
# follows into a decoding of the whole input; at the end, the pending
# bytes are replaced by one U+FFFD.

def utf8_proof.Pending(pending: List<&2, U32>) -> Type:
  match pending:
    case Nil{}:
      Unit
    case +p <> +ps:
      {UTF8.is_valid_sequence_prefix(p <> ps) == True{} : Bool} &
      {UTF8.sequence_scalar(p <> ps) == None{} : Maybe<&2, U32>}

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
  {utf8_proof.one_byte_scalar(b1) == m : Maybe<&2, U32>}:
  Equal.trans(Maybe<&2, U32>, utf8_proof.one_byte_scalar(b1), UTF8.sequence_scalar([b1]), m,
    Equal.sym(Maybe<&2, U32>, UTF8.sequence_scalar([b1]), utf8_proof.one_byte_scalar(b1),
      utf8_proof.one_scalar_agrees(b1, UTF8.valid_one_byte(b1), {==},
        UTF8.valid_one_byte(b1), {==}, {==})), e)

def utf8_proof.two_scalar_is(+b1: U32, +b2: U32, -m: Maybe<&2, U32>,
  e: {UTF8.sequence_scalar([b1, b2]) == m : Maybe<&2, U32>}) ->
  {utf8_proof.two_byte_scalar(b1, b2) == m : Maybe<&2, U32>}:
  Equal.trans(Maybe<&2, U32>, utf8_proof.two_byte_scalar(b1, b2), UTF8.sequence_scalar([b1, b2]), m,
    Equal.sym(Maybe<&2, U32>, UTF8.sequence_scalar([b1, b2]), utf8_proof.two_byte_scalar(b1, b2),
      utf8_proof.two_scalar_agrees(b1, b2, UTF8.valid_two_bytes(b1, b2), {==},
        UTF8.valid_two_bytes(b1, b2), {==}, {==})), e)

def utf8_proof.prefix_contra(+b: U32,
  begins: {UTF8.is_valid_sequence_prefix([b]) == True{} : Bool},
  not_begins: {UTF8.is_valid_sequence_prefix([b]) == False{} : Bool}) -> Empty:
  utf8_proof.true_false(Equal.trans(Bool, True{}, UTF8.is_valid_sequence_prefix([b]), False{},
    Equal.sym(Bool, UTF8.is_valid_sequence_prefix([b]), True{}, begins), not_begins))

# The implementation's scalar function and `Decodes` agree.
def utf8_proof.scalar_to_decodes(+seq: List<&2, U32>, +cp: U32, e: {UTF8.sequence_scalar(seq) == Some{cp} : Maybe<&2, U32>}) -> utf8_proof.Decodes(seq, cp):
  match seq:
    case Nil{}:
      Empty.absurd(utf8_proof.Decodes(Nil{}, cp),
        UTF8.false_true(Equal.cong(Maybe<&2, U32>, Bool, m => Maybe.is_some(&2, U32, m), None{}, Some{cp}, e)))
    case +x <> Nil{}:
      utf8_proof.one_scalar_is(x, Some{cp}, e)
    case +x <> +y <> Nil{}:
      utf8_proof.two_scalar_is(x, y, Some{cp}, e)
    case +x <> +y <> +z <> Nil{}:
      e
    case +x <> +y <> +z <> +w <> Nil{}:
      e
    case x <> y <> z <> w <> v <> rest:
      Empty.absurd(utf8_proof.Decodes(x <> y <> z <> w <> v <> rest, cp),
        UTF8.false_true(Equal.cong(Maybe<&2, U32>, Bool, m => Maybe.is_some(&2, U32, m), None{}, Some{cp}, e)))

def utf8_proof.decodes_to_scalar(+seq: List<&2, U32>, +cp: U32, d: utf8_proof.Decodes(seq, cp)) -> {UTF8.sequence_scalar(seq) == Some{cp} : Maybe<&2, U32>}:
  match seq:
    case Nil{}:
      Empty.absurd({UTF8.sequence_scalar(Nil{}) == Some{cp} : Maybe<&2, U32>}, d)
    case +x <> Nil{}:
      Equal.trans(Maybe<&2, U32>, UTF8.one_byte_scalar(x), utf8_proof.one_byte_scalar(x), Some{cp},
        utf8_proof.one_scalar_agrees(x, UTF8.valid_one_byte(x), {==}, UTF8.valid_one_byte(x), {==}, {==}), d)
    case +x <> +y <> Nil{}:
      Equal.trans(Maybe<&2, U32>, UTF8.two_byte_scalar(x, y), utf8_proof.two_byte_scalar(x, y), Some{cp},
        utf8_proof.two_scalar_agrees(x, y, UTF8.valid_two_bytes(x, y), {==}, UTF8.valid_two_bytes(x, y), {==}, {==}), d)
    case +x <> +y <> +z <> Nil{}:
      d
    case +x <> +y <> +z <> +w <> Nil{}:
      d
    case x <> y <> z <> w <> v <> rest:
      Empty.absurd({UTF8.sequence_scalar(x <> y <> z <> w <> v <> rest) == Some{cp} : Maybe<&2, U32>}, d)

# A reference scalar is None when its validity test cannot be True.
# A byte that is not a valid sequence prefix is its own maximal subpart.
def utf8_proof.single_subpart.if(+b1: U32, +more: List<&2, U32>, begins: Bool,
  checked: {UTF8.is_valid_sequence_prefix([b1]) == begins : Bool},
  not_begins: {UTF8.is_valid_sequence_prefix([b1]) == False{} : Bool}) ->
  utf8_proof.bool.maximal_subpart.if(b1, more, begins, [b1]):
  match begins:
    case False{}: {==}
    case True{}:
      Empty.absurd(utf8_proof.bool.maximal_subpart.sequence_prefix(b1, more, [b1]),
        utf8_proof.prefix_contra(b1, checked, not_begins))

def utf8_proof.single_subpart(+b1: U32, +more: List<&2, U32>,
  not_begins: {UTF8.is_valid_sequence_prefix([b1]) == False{} : Bool}) ->
  utf8_proof.bool.maximal_subpart(b1, more, [b1]):
  utf8_proof.single_subpart.if(b1, more, UTF8.is_valid_sequence_prefix([b1]), {==}, not_begins)

def utf8_proof.append_nil(+x: List<&2, U32>) -> {List.append(&2, U32, x, Nil{}) == x : List<&2, U32>}:
  match x:
    case Nil{}: {==}
    case +h <> +t:
      Equal.cong(List<&2, U32>, List<&2, U32>, y => h <> y, List.append(&2, U32, t, Nil{}), t, utf8_proof.append_nil(t))

def utf8_proof.valid_append_nil(+h: U32, +t: List<&2, U32>, v: {utf8_proof.bool.is_valid_sequence(h <> t) == True{} : Bool}) ->
  {utf8_proof.bool.is_valid_sequence(List.append(&2, U32, h <> t, Nil{})) == True{} : Bool}:
  %Equal.sym(List<&2, U32>, List.append(&2, U32, h <> t, Nil{}), h <> t, utf8_proof.append_nil(h <> t)) : {utf8_proof.bool.is_valid_sequence(_) == True{} : Bool}
  v

# No valid sequence is a proper prefix of another: their lead bytes say
# how long they are.
def utf8_proof.valid_prefix_free(+b1: U32, +more: List<&2, U32>, +c: U32, +extra: List<&2, U32>,
  v1: {utf8_proof.bool.is_valid_sequence(b1 <> more) == True{} : Bool},
  v2: {utf8_proof.bool.is_valid_sequence(List.append(&2, U32, b1 <> more, c <> extra)) == True{} : Bool}) -> Empty:
  match more extra:
    case Nil{} Nil{}:
      UTF8.false_true(Equal.cong(Nat, Bool, m => Nat.is_eq(m, 2n), 1n, 2n, Equal.trans(Nat, 1n, utf8_proof.kind(b1), 2n, Equal.sym(Nat, utf8_proof.kind(b1), 1n, utf8_proof.valid_kind1(b1, v1)), utf8_proof.valid_kind2(b1, c, v2))))
    case Nil{} +e2 <> Nil{}:
      UTF8.false_true(Equal.cong(Nat, Bool, m => Nat.is_eq(m, 3n), 1n, 3n, Equal.trans(Nat, 1n, utf8_proof.kind(b1), 3n, Equal.sym(Nat, utf8_proof.kind(b1), 1n, utf8_proof.valid_kind1(b1, v1)), utf8_proof.valid_kind3(b1, c, e2, v2))))
    case Nil{} +e2 <> +e3 <> Nil{}:
      UTF8.false_true(Equal.cong(Nat, Bool, m => Nat.is_eq(m, 4n), 1n, 4n, Equal.trans(Nat, 1n, utf8_proof.kind(b1), 4n, Equal.sym(Nat, utf8_proof.kind(b1), 1n, utf8_proof.valid_kind1(b1, v1)), utf8_proof.valid_kind4(b1, c, e2, e3, v2))))
    case Nil{} e2 <> e3 <> e4 <> after:
      UTF8.false_true(v2)
    case +b2 <> Nil{} Nil{}:
      UTF8.false_true(Equal.cong(Nat, Bool, m => Nat.is_eq(m, 3n), 2n, 3n, Equal.trans(Nat, 2n, utf8_proof.kind(b1), 3n, Equal.sym(Nat, utf8_proof.kind(b1), 2n, utf8_proof.valid_kind2(b1, b2, v1)), utf8_proof.valid_kind3(b1, b2, c, v2))))
    case +b2 <> Nil{} +e2 <> Nil{}:
      UTF8.false_true(Equal.cong(Nat, Bool, m => Nat.is_eq(m, 4n), 2n, 4n, Equal.trans(Nat, 2n, utf8_proof.kind(b1), 4n, Equal.sym(Nat, utf8_proof.kind(b1), 2n, utf8_proof.valid_kind2(b1, b2, v1)), utf8_proof.valid_kind4(b1, b2, c, e2, v2))))
    case +b2 <> Nil{} e2 <> e3 <> after:
      UTF8.false_true(v2)
    case +b2 <> +b3 <> Nil{} Nil{}:
      UTF8.false_true(Equal.cong(Nat, Bool, m => Nat.is_eq(m, 4n), 3n, 4n, Equal.trans(Nat, 3n, utf8_proof.kind(b1), 4n, Equal.sym(Nat, utf8_proof.kind(b1), 3n, utf8_proof.valid_kind3(b1, b2, b3, v1)), utf8_proof.valid_kind4(b1, b2, b3, c, v2))))
    case +b2 <> +b3 <> Nil{} e2 <> after:
      UTF8.false_true(v2)
    case +b2 <> +b3 <> +b4 <> Nil{} _:
      UTF8.false_true(v2)
    case b2 <> b3 <> b4 <> b5 <> after _:
      UTF8.false_true(v2)

def utf8_proof.valid_is_prefix(+h: U32, +t: List<&2, U32>, v: {utf8_proof.bool.is_valid_sequence(h <> t) == True{} : Bool}) -> {UTF8.is_valid_sequence_prefix(h <> t) == True{} : Bool}:
  utf8_proof.prefix_from_completion(h, t, (Nil{},
    utf8_proof.valid_append_nil(h, t, v)))

def utf8_proof.pf_scalar_none(+b1: U32, +more: List<&2, U32>, +c: U32, +extra: List<&2, U32>, m: Maybe<&2, U32>,
  +checked: {UTF8.sequence_scalar(b1 <> more) == m : Maybe<&2, U32>},
  v2: {utf8_proof.bool.is_valid_sequence(List.append(&2, U32, b1 <> more, c <> extra)) == True{} : Bool}) -> {UTF8.sequence_scalar(b1 <> more) == None{} : Maybe<&2, U32>}:
  match m:
    case None{}: checked
    case Some{+x}:
      Empty.absurd({UTF8.sequence_scalar(b1 <> more) == None{} : Maybe<&2, U32>},
        utf8_proof.valid_prefix_free(b1, more, c, extra,
          utf8_proof.decodes_valid(b1 <> more, x, utf8_proof.scalar_to_decodes(b1 <> more, x, checked)), v2))

def utf8_proof.next_none.if(+bytes: List<&2, U32>, found: Maybe<&1, U32 & List<&2, U32>>,
  +checked: {utf8_proof.next_scalar(bytes) == found : Maybe<&1, U32 & List<&2, U32>>}, none: Laws.no_valid_sequence(bytes)) ->
  {utf8_proof.next_scalar(bytes) == None{} : Maybe<&1, U32 & List<&2, U32>>}:
  match found:
    case None{}: checked
    case Some{x}:
      (+cp, +rest) = x
      Empty.absurd({utf8_proof.next_scalar(bytes) == None{} : Maybe<&1, U32 & List<&2, U32>>}, none(cp, rest, utf8_proof.finds_at(bytes, Some{(cp, rest)}, checked)))

def utf8_proof.next_none(+bytes: List<&2, U32>, none: Laws.no_valid_sequence(bytes)) -> {utf8_proof.next_scalar(bytes) == None{} : Maybe<&1, U32 & List<&2, U32>>}:
  utf8_proof.next_none.if(bytes, utf8_proof.next_scalar(bytes), {==}, none)

def utf8_proof.no_begin_not_prefix.seq(+b: U32, +rest: List<&2, U32>, +seq: List<&2, U32>, +r: List<&2, U32>, +split: {List.append(&2, U32, seq, r) == b <> rest : List<&2, U32>},
  valid: {utf8_proof.bool.is_valid_sequence(seq) == True{} : Bool}, not_begins: {UTF8.is_valid_sequence_prefix([b]) == False{} : Bool}) -> Empty:
  match seq:
    case Nil{}: UTF8.false_true(valid)
    case +h <> +t:
      +same = utf8_proof.cons_head(h, b, List.append(&2, U32, t, r), rest, split)
      +closed = utf8_proof.prefix_closed(h, Nil{}, t, utf8_proof.valid_is_prefix(h, t, valid))
      utf8_proof.prefix_contra(b, Equal.trans(Bool, UTF8.is_valid_sequence_prefix([b]), UTF8.is_valid_sequence_prefix([h]), True{}, Equal.cong(U32, Bool, x => UTF8.is_valid_sequence_prefix([x]), b, h, Equal.sym(U32, h, b, same)), closed), not_begins)

def utf8_proof.no_begin_not_prefix(+b: U32, +rest: List<&2, U32>, not_begins: {UTF8.is_valid_sequence_prefix([b]) == False{} : Bool},
  +cp: U32, +r: List<&2, U32>, begins: Laws.begins_with_scalar(b <> rest, cp, r)) -> Empty:
  (+seq, facts) = begins
  (enc, split) = facts
  utf8_proof.no_begin_not_prefix.seq(b, rest, seq, r, split,
    utf8_proof.decodes_valid(seq, cp, utf8_proof.to_old(seq, cp, enc)), not_begins)

def utf8_proof.no_begin.shorter_seq(+h: U32, +t: List<&2, U32>, +q: List<&2, U32>, +c: U32, +extra: List<&2, U32>,
  v1: {utf8_proof.bool.is_valid_sequence(h <> t) == True{} : Bool},
  +eq: {q == List.append(&2, U32, h <> t, c <> extra) : List<&2, U32>},
  completion: PrefixCompletion(q)) -> Empty:
  (+rest2, v) = completion
  +regrouped = Equal.trans(List<&2, U32>, List.append(&2, U32, h <> t, c <> List.append(&2, U32, extra, rest2)), List.append(&2, U32, List.append(&2, U32, h <> t, c <> extra), rest2), List.append(&2, U32, q, rest2),
    Equal.sym(List<&2, U32>, List.append(&2, U32, List.append(&2, U32, h <> t, c <> extra), rest2), List.append(&2, U32, h <> t, c <> List.append(&2, U32, extra, rest2)), utf8_proof.append_assoc(h <> t, c <> extra, rest2)),
    Equal.cong(List<&2, U32>, List<&2, U32>, x => List.append(&2, U32, x, rest2), List.append(&2, U32, h <> t, c <> extra), q, Equal.sym(List<&2, U32>, q, List.append(&2, U32, h <> t, c <> extra), eq)))
  utf8_proof.valid_prefix_free(h, t, c, List.append(&2, U32, extra, rest2), v1,
    Equal.trans(Bool, utf8_proof.bool.is_valid_sequence(List.append(&2, U32, h <> t, c <> List.append(&2, U32, extra, rest2))), utf8_proof.bool.is_valid_sequence(List.append(&2, U32, q, rest2)), True{},
      Equal.cong(List<&2, U32>, Bool, x => utf8_proof.bool.is_valid_sequence(x), List.append(&2, U32, h <> t, c <> List.append(&2, U32, extra, rest2)), List.append(&2, U32, q, rest2), regrouped), v))

def utf8_proof.no_begin.shorter(+seq: List<&2, U32>, +q: List<&2, U32>, +c: U32, +extra: List<&2, U32>,
  v1: {utf8_proof.bool.is_valid_sequence(seq) == True{} : Bool},
  +eq: {q == List.append(&2, U32, seq, c <> extra) : List<&2, U32>},
  completion: PrefixCompletion(q)) -> Empty:
  match seq:
    case Nil{}: UTF8.false_true(v1)
    case +h <> +t: utf8_proof.no_begin.shorter_seq(h, t, q, c, extra, v1, eq, completion)

def utf8_proof.valid_head_prefix(+seq: List<&2, U32>, v: {utf8_proof.bool.is_valid_sequence(seq) == True{} : Bool}) -> {UTF8.is_valid_sequence_prefix(seq) == True{} : Bool}:
  match seq:
    case Nil{}: Empty.absurd({UTF8.is_valid_sequence_prefix(Nil{}) == True{} : Bool}, UTF8.false_true(v))
    case +h <> +t: utf8_proof.valid_is_prefix(h, t, v)

def utf8_proof.no_begin.shorter_unpack(+seq: List<&2, U32>, +q: List<&2, U32>, +bytes: List<&2, U32>,
  shorter: utf8_proof.Shorter(seq, q, bytes),
  v1: {utf8_proof.bool.is_valid_sequence(seq) == True{} : Bool}, completion: PrefixCompletion(q)) -> Empty:
  (+c, more) = shorter
  (+extra, facts) = more
  (eq, next) = facts
  utf8_proof.no_begin.shorter(seq, q, c, extra, v1, eq, completion)

def utf8_proof.no_begin.longer_unpack(+q: List<&2, U32>, +seq: List<&2, U32>, +bytes: List<&2, U32>, +r: List<&2, U32>,
  +split: {List.append(&2, U32, seq, r) == bytes : List<&2, U32>},
  shorter: utf8_proof.Shorter(q, seq, bytes),
  not_ext: utf8_proof.not_extended_by(q, utf8_proof.next_byte_after(bytes, q)),
  begins_seq: {UTF8.is_valid_sequence_prefix(seq) == True{} : Bool}) -> Empty:
  (+c, more) = shorter
  (+extra, facts) = more
  (+eq, next) = facts
  +split2 = Equal.trans(List<&2, U32>, List.append(&2, U32, List.append(&2, U32, q, c <> extra), r), List.append(&2, U32, seq, r), bytes,
    Equal.cong(List<&2, U32>, List<&2, U32>, x => List.append(&2, U32, x, r), List.append(&2, U32, q, c <> extra), seq, Equal.sym(List<&2, U32>, seq, List.append(&2, U32, q, c <> extra), eq)), split)
  +no = utf8_proof.longer_not_valid_from_not_extended(q, bytes, not_ext)(c, extra, (r, split2))
  utf8_proof.true_false(Equal.trans(Bool, True{}, UTF8.is_valid_sequence_prefix(seq), False{},
    Equal.sym(Bool, UTF8.is_valid_sequence_prefix(seq), True{}, begins_seq),
    Equal.trans(Bool, UTF8.is_valid_sequence_prefix(seq), UTF8.is_valid_sequence_prefix(List.append(&2, U32, q, c <> extra)), False{},
      Equal.cong(List<&2, U32>, Bool, x => UTF8.is_valid_sequence_prefix(x), seq, List.append(&2, U32, q, c <> extra), eq), no)))

def utf8_proof.no_begin.compared(+q: List<&2, U32>, +seq: List<&2, U32>, +bytes: List<&2, U32>, +cp: U32, +r: List<&2, U32>,
  +split: {List.append(&2, U32, seq, r) == bytes : List<&2, U32>},
  enc: Laws.encodes(seq, cp),
  begins_q: {UTF8.is_valid_sequence_prefix(q) == True{} : Bool},
  none_q: {UTF8.sequence_scalar(q) == None{} : Maybe<&2, U32>},
  not_ext: utf8_proof.not_extended_by(q, utf8_proof.next_byte_after(bytes, q)),
  compared: utf8_proof.Compared(seq, q, bytes)) -> Empty:
  match compared:
    case Inl{same}:
      UTF8.false_true(Equal.cong(Maybe<&2, U32>, Bool, m => Maybe.is_some(&2, U32, m), None{}, Some{cp},
        Equal.trans(Maybe<&2, U32>, None{}, UTF8.sequence_scalar(q), Some{cp}, Equal.sym(Maybe<&2, U32>, UTF8.sequence_scalar(q), None{}, none_q),
          Equal.trans(Maybe<&2, U32>, UTF8.sequence_scalar(q), UTF8.sequence_scalar(seq), Some{cp}, Equal.cong(List<&2, U32>, Maybe<&2, U32>, x => UTF8.sequence_scalar(x), q, seq, Equal.sym(List<&2, U32>, seq, q, same)),
            utf8_proof.decodes_to_scalar(seq, cp, utf8_proof.to_old(seq, cp, enc))))))
    case Inr{Inl{shorter}}:
      utf8_proof.no_begin.shorter_unpack(seq, q, bytes, shorter,
        utf8_proof.decodes_valid(seq, cp, utf8_proof.to_old(seq, cp, enc)), utf8_proof.prefix_completion(q, begins_q))
    case Inr{Inr{shorter}}:
      utf8_proof.no_begin.longer_unpack(q, seq, bytes, r, split, shorter, not_ext,
        utf8_proof.valid_head_prefix(seq, utf8_proof.decodes_valid(seq, cp, utf8_proof.to_old(seq, cp, enc))))

def utf8_proof.no_begin.split(+q: List<&2, U32>, +tail: List<&2, U32>, +seq: List<&2, U32>, +cp: U32, +r: List<&2, U32>,
  +split: {List.append(&2, U32, seq, r) == List.append(&2, U32, q, tail) : List<&2, U32>},
  enc: Laws.encodes(seq, cp),
  begins_q: {UTF8.is_valid_sequence_prefix(q) == True{} : Bool},
  none_q: {UTF8.sequence_scalar(q) == None{} : Maybe<&2, U32>},
  not_ext: utf8_proof.not_extended_by(q, utf8_proof.next_byte_after(List.append(&2, U32, q, tail), q))) -> Empty:
  utf8_proof.no_begin.compared(q, seq, List.append(&2, U32, q, tail), cp, r, split, enc, begins_q, none_q, not_ext,
    utf8_proof.compare(seq, q, List.append(&2, U32, q, tail), r, tail, split, {==}))

def utf8_proof.no_begin_pending(+q: List<&2, U32>, +tail: List<&2, U32>,
  begins_q: {UTF8.is_valid_sequence_prefix(q) == True{} : Bool},
  none_q: {UTF8.sequence_scalar(q) == None{} : Maybe<&2, U32>},
  not_ext: utf8_proof.not_extended_by(q, utf8_proof.next_byte_after(List.append(&2, U32, q, tail), q)),
  +cp: U32, +r: List<&2, U32>, begins: Laws.begins_with_scalar(List.append(&2, U32, q, tail), cp, r)) -> Empty:
  (+seq, facts) = begins
  (enc, split) = facts
  utf8_proof.no_begin.split(q, tail, seq, cp, r, split, enc, begins_q, none_q, not_ext)

def utf8_proof.not_ext_some(+q: List<&2, U32>, +b: U32, +rest: List<&2, U32>,
  not_begins: {UTF8.is_valid_sequence_prefix(List.append(&2, U32, q, [b])) == False{} : Bool}) ->
  utf8_proof.not_extended_by(q, utf8_proof.next_byte_after(List.append(&2, U32, q, b <> rest), q)):
  %Equal.sym(Maybe<&2, U32>, utf8_proof.next_byte_after(List.append(&2, U32, q, b <> rest), q), Some{b}, utf8_proof.next_after_append(q, b <> rest)) : utf8_proof.not_extended_by(q, _)
  not_begins

def utf8_proof.not_ext_nil(+q: List<&2, U32>) ->
  utf8_proof.not_extended_by(q, utf8_proof.next_byte_after(List.append(&2, U32, q, Nil{}), q)):
  %Equal.sym(Maybe<&2, U32>, utf8_proof.next_byte_after(List.append(&2, U32, q, Nil{}), q), None{}, utf8_proof.next_after_append(q, Nil{})) : utf8_proof.not_extended_by(q, _)
  Unit{}

def utf8_proof.pending_subpart.if(+p: U32, +ps: List<&2, U32>, +tail: List<&2, U32>, begins: Bool,
  checked: {UTF8.is_valid_sequence_prefix([p]) == begins : Bool},
  prefix_q: {UTF8.is_valid_sequence_prefix(p <> ps) == True{} : Bool},
  not_ext: utf8_proof.not_extended_by(p <> ps, utf8_proof.next_byte_after(List.append(&2, U32, p <> ps, tail), p <> ps))) ->
  utf8_proof.bool.maximal_subpart.if(p, List.append(&2, U32, ps, tail), begins, p <> ps):
  match begins:
    case True{}:
      ((tail, {==}), (prefix_q, utf8_proof.longer_not_valid_from_not_extended(p <> ps, List.append(&2, U32, p <> ps, tail), not_ext)))
    case False{}:
      Empty.absurd(utf8_proof.bool.maximal_subpart.single_byte(p, p <> ps),
        utf8_proof.prefix_contra(p, utf8_proof.prefix_closed(p, Nil{}, ps, prefix_q), checked))

def utf8_proof.pending_subpart(+p: U32, +ps: List<&2, U32>, +tail: List<&2, U32>,
  prefix_q: {UTF8.is_valid_sequence_prefix(p <> ps) == True{} : Bool},
  not_ext: utf8_proof.not_extended_by(p <> ps, utf8_proof.next_byte_after(List.append(&2, U32, p <> ps, tail), p <> ps))) ->
  utf8_proof.bool.maximal_subpart(p, List.append(&2, U32, ps, tail), p <> ps):
  utf8_proof.pending_subpart.if(p, ps, tail, UTF8.is_valid_sequence_prefix([p]), {==}, prefix_q, not_ext)

# A step with nothing pending.
def utf8_proof.start_ok.if(+b: U32, +rest: List<&2, U32>, scalar: Maybe<&2, U32>,
  scalar_is: {UTF8.sequence_scalar([b]) == scalar : Maybe<&2, U32>}, begins: Bool,
  +begins_is: {UTF8.is_valid_sequence_prefix([b]) == begins : Bool}) ->
  utf8_proof.StepOK(Nil{}, b, rest, UTF8.decode_buffer.advance([b], scalar, begins,
    u => (UTF8.replacement_char_string(), Nil{}))):
  match scalar begins:
    case Some{+cp} _:
      (Unit{}, after => d =>
        (rest, (utf8_proof.first_found(b, rest, cp, rest,
          utf8_proof.next_one(b, rest, cp, utf8_proof.one_scalar_is(b, Some{cp}, scalar_is))), d)))
    case None{} True{}:
      ((begins_is, scalar_is), after => d => d)
    case None{} False{}:
      (Unit{}, after => d =>
        (rest, (utf8_proof.first_replaced(b, rest, [b], rest,
          utf8_proof.next_none(b <> rest, c => r => bg => utf8_proof.no_begin_not_prefix(b, rest, begins_is, c, r, bg)),
          utf8_proof.single_subpart(b, rest, begins_is), {==}), d)))

def utf8_proof.start_ok(+b: U32, +rest: List<&2, U32>) ->
  utf8_proof.StepOK(Nil{}, b, rest, UTF8.decode_buffer.start(b)):
  utf8_proof.start_ok.if(b, rest, UTF8.sequence_scalar([b]), {==},
    UTF8.is_valid_sequence_prefix([b]), {==})

# The pending bytes cannot be continued: they are replaced by one
# U+FFFD, and the new byte starts afresh.
def utf8_proof.extend_fail(+p: U32, +ps: List<&2, U32>, +b: U32, +rest: List<&2, U32>,
  s: UTF8.decode_buffer.Step(), started: utf8_proof.StepOK(Nil{}, b, rest, s),
  +begins_q: {UTF8.is_valid_sequence_prefix(p <> ps) == True{} : Bool},
  +none_q: {UTF8.sequence_scalar(p <> ps) == None{} : Maybe<&2, U32>},
  +not_begins: {UTF8.is_valid_sequence_prefix(List.append(&2, U32, p <> ps, [b])) == False{} : Bool}) ->
  utf8_proof.StepOK(p <> ps, b, rest,
    UTF8.decode_buffer.prepend(UTF8.replacement_char_string(), s)):
  (+t, +q) = s
  (pending_q, continue) = started
  (pending_q, after => d =>
    (b <> rest, (utf8_proof.first_replaced(p, List.append(&2, U32, ps, b <> rest), p <> ps, b <> rest,
      utf8_proof.next_none(p <> List.append(&2, U32, ps, b <> rest),
        c => r => bg => utf8_proof.no_begin_pending(p <> ps, b <> rest, begins_q, none_q,
          utf8_proof.not_ext_some(p <> ps, b, rest, not_begins), c, r, bg)),
      utf8_proof.pending_subpart(p, ps, b <> rest, begins_q, utf8_proof.not_ext_some(p <> ps, b, rest, not_begins)), {==}),
      continue(after, d))))

# A step with bytes pending.
def utf8_proof.extend_found(+p: U32, +ps: List<&2, U32>, +b: U32, +rest: List<&2, U32>, +cp: U32,
  e: {utf8_proof.next_scalar(List.append(&2, U32, List.append(&2, U32, p <> ps, [b]), rest)) == Some{(cp, rest)} : Maybe<&1, U32 & List<&2, U32>>}) ->
  {utf8_proof.next_scalar(p <> List.append(&2, U32, ps, b <> rest)) == Some{(cp, rest)} : Maybe<&1, U32 & List<&2, U32>>}:
  %utf8_proof.append_assoc(p <> ps, [b], rest) : {utf8_proof.next_scalar(_) == Some{(cp, rest)} : Maybe<&1, U32 & List<&2, U32>>}
  e

def utf8_proof.extend_keep(+p: U32, +ps: List<&2, U32>, +b: U32, +rest: List<&2, U32>, +after: String,
  d: Laws.decodes(List.append(&2, U32, List.append(&2, U32, p <> ps, [b]), rest), after)) ->
  Laws.decodes(p <> List.append(&2, U32, ps, b <> rest), after):
  %utf8_proof.append_assoc(p <> ps, [b], rest) : Laws.decodes(_, after)
  d

def utf8_proof.extend_ok.if(+p: U32, +ps: List<&2, U32>, +b: U32, +rest: List<&2, U32>, scalar: Maybe<&2, U32>,
  scalar_is: {UTF8.sequence_scalar(List.append(&2, U32, p <> ps, [b])) == scalar : Maybe<&2, U32>}, begins: Bool,
  begins_is: {UTF8.is_valid_sequence_prefix(List.append(&2, U32, p <> ps, [b])) == begins : Bool},
  pending: utf8_proof.Pending(p <> ps)) ->
  utf8_proof.StepOK(p <> ps, b, rest, UTF8.decode_buffer.advance(List.append(&2, U32, p <> ps, [b]), scalar, begins,
    u => UTF8.decode_buffer.prepend(UTF8.replacement_char_string(), UTF8.decode_buffer.start(b)))):
  match scalar begins:
    case Some{+cp} _:
      (Unit{}, after => d =>
        (rest, (utf8_proof.first_found(p, List.append(&2, U32, ps, b <> rest), cp, rest,
          utf8_proof.extend_found(p, ps, b, rest, cp,
            utf8_proof.next_of_encodes(List.append(&2, U32, p <> ps, [b]), cp, rest,
              utf8_proof.scalar_to_decodes(List.append(&2, U32, p <> ps, [b]), cp, scalar_is)))), d)))
    case None{} True{}:
      ((begins_is, scalar_is), after => d => utf8_proof.extend_keep(p, ps, b, rest, after, d))
    case None{} False{}:
      (lead, alone) = pending
      utf8_proof.extend_fail(p, ps, b, rest, UTF8.decode_buffer.start(b), utf8_proof.start_ok(b, rest),
        lead, alone, begins_is)

def utf8_proof.step_ok(+pending: List<&2, U32>, +b: U32, +rest: List<&2, U32>,
  invariant: utf8_proof.Pending(pending)) ->
  utf8_proof.StepOK(pending, b, rest, UTF8.decode_buffer.step(pending, b)):
  match pending:
    case Nil{}:
      utf8_proof.start_ok(b, rest)
    case +p <> +ps:
      utf8_proof.extend_ok.if(p, ps, b, rest, UTF8.sequence_scalar(List.append(&2, U32, p <> ps, [b])), {==}, UTF8.is_valid_sequence_prefix(List.append(&2, U32, p <> ps, [b])), {==}, invariant)

# At the end of the input, pending bytes are replaced by one U+FFFD.
def utf8_proof.done_pending(+p: U32, +ps: List<&2, U32>,
  +lead: {UTF8.is_valid_sequence_prefix(p <> ps) == True{} : Bool}, +alone: {UTF8.sequence_scalar(p <> ps) == None{} : Maybe<&2, U32>}) ->
  Laws.decodes(List.append(&2, U32, p <> ps, Nil{}), UTF8.decode_done(p <> ps)):
  (Nil{}, (utf8_proof.first_replaced(p, List.append(&2, U32, ps, Nil{}), p <> ps, Nil{},
    utf8_proof.next_none(p <> List.append(&2, U32, ps, Nil{}),
      c => r => bg => utf8_proof.no_begin_pending(p <> ps, Nil{}, lead, alone, utf8_proof.not_ext_nil(p <> ps), c, r, bg)),
    utf8_proof.pending_subpart(p, ps, Nil{}, lead, utf8_proof.not_ext_nil(p <> ps)), {==}), {==}))

def utf8_proof.done_ok(+pending: List<&2, U32>, invariant: utf8_proof.Pending(pending)) ->
  Laws.decodes(List.append(&2, U32, pending, Nil{}), UTF8.decode_done(pending)):
  match pending:
    case Nil{}:
      {==}
    case +p <> +ps:
      (lead, alone) = invariant
      utf8_proof.done_pending(p, ps, lead, alone)

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

def utf8_proof.decoded_text(step: UTF8.decode_buffer.Step()) ->
  {Laws.decoded.text(utf8_proof.fed_step(step)) == utf8_proof.final_text(step) : String}:
  (text, pending) = step
  {==}

def utf8_proof.decoded_is(+buffers: List<&2, List<&2, U32>>, -valid: Laws.all_buffers_bytes(buffers)) ->
  {Laws.decoded(buffers, valid) ==
    utf8_proof.final_text(UTF8.decode_buffer.bytes(List.concat(&2, U32, buffers), Nil{})) : String}:
  %Equal.sym(UTF8.DecodeState() & String, Laws.feed(buffers, valid, Nil{}), utf8_proof.fed_step(UTF8.decode_buffer.bytes(List.concat(&2, U32, buffers), Nil{})), utf8_proof.feed_agrees(buffers, valid, Nil{})) : {Laws.decoded.text(_) ==
    utf8_proof.final_text(UTF8.decode_buffer.bytes(List.concat(&2, U32, buffers), Nil{})) : String}
  utf8_proof.decoded_text(UTF8.decode_buffer.bytes(List.concat(&2, U32, buffers), Nil{}))

def Laws.utf8_decodes(buffers, valid):
  %Equal.sym(String, Laws.decoded(buffers, valid), utf8_proof.final_text(UTF8.decode_buffer.bytes(List.concat(&2, U32, buffers), Nil{})), utf8_proof.decoded_is(buffers, valid)) : Laws.decodes(List.concat(&2, U32, buffers), _)
  utf8_proof.bytes_ok(List.concat(&2, U32, buffers), Nil{}, Unit{})

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
def utf8_proof.so_far_text(step: UTF8.decode_buffer.Step()) ->
  {Laws.decoded_so_far.text(utf8_proof.fed_step(step)) == utf8_proof.step_text(step) : String}:
  (text, pending) = step
  {==}

def utf8_proof.so_far_is(+buffers: List<&2, List<&2, U32>>, -valid: Laws.all_buffers_bytes(buffers)) ->
  {utf8_proof.step_text(UTF8.decode_buffer.bytes(List.concat(&2, U32, buffers), Nil{})) ==
    Laws.decoded_so_far(buffers, valid) : String}:
  %Equal.sym(UTF8.DecodeState() & String, Laws.feed(buffers, valid, Nil{}), utf8_proof.fed_step(UTF8.decode_buffer.bytes(List.concat(&2, U32, buffers), Nil{})), utf8_proof.feed_agrees(buffers, valid, Nil{})) : {utf8_proof.step_text(UTF8.decode_buffer.bytes(List.concat(&2, U32, buffers), Nil{})) ==
    Laws.decoded_so_far.text(_) : String}
  Equal.sym(String, Laws.decoded_so_far.text(utf8_proof.fed_step(UTF8.decode_buffer.bytes(List.concat(&2, U32, buffers), Nil{}))),
    utf8_proof.step_text(UTF8.decode_buffer.bytes(List.concat(&2, U32, buffers), Nil{})),
    utf8_proof.so_far_text(UTF8.decode_buffer.bytes(List.concat(&2, U32, buffers), Nil{})))

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

def Laws.utf8_decode_buffer_safe(buffers, valid, rest, full, decoded):
  utf8_proof.safe.step(List.concat(&2, U32, buffers), rest, Laws.decoded_so_far(buffers, valid), full,
    UTF8.decode_buffer.bytes(List.concat(&2, U32, buffers), Nil{}),
    utf8_proof.so_far_is(buffers, valid),
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

def utf8_proof.ends_here(+c: U32, +more: String, e: {SCon{Chr{c}, more} == SNil{} : String}) -> Empty:
  utf8_proof.true_false(Equal.cong(String, Bool, utf8_proof.string_is_cons, SCon{Chr{c}, more}, SNil{}, e))

def utf8_proof.low6_at(+x: U32, +y: U32, +e: {x == y : U32}, v: {U32.is_eq(U32.and(x, 63), 0) == True{} : Bool}) -> {U32.is_eq(U32.and(y, 63), 0) == True{} : Bool}:
  %e : {U32.is_eq(U32.and(_, 63), 0) == True{} : Bool}
  v

def utf8_proof.not_replacement(+c: U32, +more: String,
  small: {U32.is_eq(U32.and(c, 63), 0) == True{} : Bool},
  e: {SCon{Chr{c}, more} == SCon{Chr{65533}, SNil{}} : String}) -> Empty:
  UTF8.false_true(utf8_proof.low6_at(c, 65533, utf8_proof.head_eq(c, 65533, more, SNil{}, e), small))

def utf8_proof.differs(+c: U32, +cp: U32, +more: String, +rest: String,
  large: {U32.is_eq(U32.and(c, 63), 0) == False{} : Bool},
  rest_is: {rest == SCon{Chr{cp}, SNil{}} : String},
  bound: {U32.is_eq(U32.and(cp, 63), 0) == True{} : Bool},
  e: {SCon{Chr{c}, more} == rest : String}) -> Empty:
  utf8_proof.true_false(Equal.trans(Bool, True{}, U32.is_eq(U32.and(c, 63), 0), False{},
    Equal.sym(Bool, U32.is_eq(U32.and(c, 63), 0), True{},
      utf8_proof.low6_at(cp, c, Equal.sym(U32, c, cp,
        utf8_proof.head_eq(c, cp, more, SNil{},
          Equal.trans(String, SCon{Chr{c}, more}, rest, SCon{Chr{cp}, SNil{}}, e, rest_is))), bound)),
    large))

def utf8_proof.low6(+acc: U32) -> {U32.is_eq(U32.and(UTF8.append_continuation(acc, 128), 63), 0) == True{} : Bool}:
  match acc:
    case U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      %Equal.sym(Word(32n), Word.add(32n, word_join(6n, Word.zero(6n), 26n, WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}), Word.zero(32n)), word_join(6n, Word.zero(6n), 26n, WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}), word_add_zero(32n, word_join(6n, Word.zero(6n), 26n, WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}))) :
        {U32.is_eq(U32.and(U32{_}, 63), 0) == True{} : Bool}
      %Equal.sym(Word(32n), Word.and(32n, word_join(6n, Word.zero(6n), 26n, WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}), word_join(6n, word_ones(6n), 26n, Word.zero(26n))), word_join(6n, Word.zero(6n), 26n, Word.zero(26n)),
          word_mask_fields(6n, Word.zero(6n), 26n, WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}})) :
        {U32.is_eq(U32{_}, 0) == True{} : Bool}
      {==}
def utf8_proof.some2.if(+b1: U32, +b2: U32, valid: Bool, +checked: {UTF8.valid_two_bytes(b1, b2) == valid : Bool},
  is_true: {valid == True{} : Bool}) ->
  Exists(U32, cp => {UTF8.two_byte_scalar.if(b1, b2, valid, checked) == Some{cp} : Maybe<&2, U32>} & {cp == (U32.shln(U32.and(b1, 31), 6n) + U32.and(b2, 63) : U32) : U32}):
  match valid:
    case False{}: Empty.absurd(Exists(U32, cp => {None{} == Some{cp} : Maybe<&2, U32>} & {cp == (U32.shln(U32.and(b1, 31), 6n) + U32.and(b2, 63) : U32) : U32}), UTF8.false_true(is_true))
    case True{}: (UTF8.decode_two_bytes(b1, b2, UTF8.valid_two_bytes.has_shape(b1, b2, checked)), ({==}, {==}))

def utf8_proof.none2.contra(+b1: U32, +b2: U32, valid: Bool, -checked: {UTF8.valid_two_bytes(b1, b2) == valid : Bool},
  none: {UTF8.two_byte_scalar.if(b1, b2, valid, checked) == None{} : Maybe<&2, U32>}, is_true: {valid == True{} : Bool}) -> Empty:
  match valid:
    case False{}: UTF8.false_true(is_true)
    case True{}:
      utf8_proof.true_false(Equal.cong(Maybe<&2, U32>, Bool, m => Maybe.is_some(&2, U32, m), UTF8.two_byte_scalar.if(b1, b2, True{}, checked), None{}, none))

def utf8_proof.some3.if(+b1: U32, +b2: U32, +b3: U32, valid: Bool, +checked: {UTF8.valid_three_bytes(b1, b2, b3) == valid : Bool},
  is_true: {valid == True{} : Bool}) ->
  Exists(U32, cp => {UTF8.three_byte_scalar.if(b1, b2, b3, valid, checked) == Some{cp} : Maybe<&2, U32>} & {cp == utf8_proof.dec3(b1, b2, b3) : U32}):
  match valid:
    case False{}: Empty.absurd(Exists(U32, cp => {None{} == Some{cp} : Maybe<&2, U32>} & {cp == utf8_proof.dec3(b1, b2, b3) : U32}), UTF8.false_true(is_true))
    case True{}: (UTF8.decode_three_bytes(b1, b2, b3, UTF8.valid_three_bytes.has_shape(b1, b2, b3, checked)), ({==}, {==}))

def utf8_proof.none3.contra(+b1: U32, +b2: U32, +b3: U32, valid: Bool, -checked: {UTF8.valid_three_bytes(b1, b2, b3) == valid : Bool},
  none: {UTF8.three_byte_scalar.if(b1, b2, b3, valid, checked) == None{} : Maybe<&2, U32>}, is_true: {valid == True{} : Bool}) -> Empty:
  match valid:
    case False{}: UTF8.false_true(is_true)
    case True{}:
      utf8_proof.true_false(Equal.cong(Maybe<&2, U32>, Bool, m => Maybe.is_some(&2, U32, m), UTF8.three_byte_scalar.if(b1, b2, b3, True{}, checked), None{}, none))

def utf8_proof.some4.if(+b1: U32, +b2: U32, +b3: U32, +b4: U32, valid: Bool, +checked: {UTF8.valid_four_bytes(b1, b2, b3, b4) == valid : Bool},
  is_true: {valid == True{} : Bool}) ->
  Exists(U32, cp => {UTF8.four_byte_scalar.if(b1, b2, b3, b4, valid, checked) == Some{cp} : Maybe<&2, U32>} & {cp == utf8_proof.dec4(b1, b2, b3, b4) : U32}):
  match valid:
    case False{}: Empty.absurd(Exists(U32, cp => {None{} == Some{cp} : Maybe<&2, U32>} & {cp == utf8_proof.dec4(b1, b2, b3, b4) : U32}), UTF8.false_true(is_true))
    case True{}: (UTF8.decode_four_bytes(b1, b2, b3, b4, UTF8.valid_four_bytes.has_shape(b1, b2, b3, b4, checked)), ({==}, {==}))

def utf8_proof.none4.contra(+b1: U32, +b2: U32, +b3: U32, +b4: U32, valid: Bool, -checked: {UTF8.valid_four_bytes(b1, b2, b3, b4) == valid : Bool},
  none: {UTF8.four_byte_scalar.if(b1, b2, b3, b4, valid, checked) == None{} : Maybe<&2, U32>}, is_true: {valid == True{} : Bool}) -> Empty:
  match valid:
    case False{}: UTF8.false_true(is_true)
    case True{}:
      utf8_proof.true_false(Equal.cong(Maybe<&2, U32>, Bool, m => Maybe.is_some(&2, U32, m), UTF8.four_byte_scalar.if(b1, b2, b3, b4, True{}, checked), None{}, none))

def utf8_proof.none1.contra(+b1: U32, valid: Bool, -checked: {UTF8.valid_one_byte(b1) == valid : Bool},
  none: {UTF8.one_byte_scalar.if(b1, valid, checked) == None{} : Maybe<&2, U32>}, is_true: {valid == True{} : Bool}) -> Empty:
  match valid:
    case False{}: UTF8.false_true(is_true)
    case True{}:
      utf8_proof.true_false(Equal.cong(Maybe<&2, U32>, Bool, m => Maybe.is_some(&2, U32, m), UTF8.one_byte_scalar.if(b1, True{}, checked), None{}, none))

def utf8_proof.Completion(+p: U32, +ps: List<&2, U32>) -> Type:
  Exists(U32, c0 => Exists(List<&2, U32>, cs => Exists(U32, cp =>
    {UTF8.sequence_scalar(List.append(&2, U32, p <> ps, c0 <> cs)) == Some{cp} : Maybe<&2, U32>} &
    {U32.is_eq(U32.and(cp, 63), 0) == True{} : Bool} &
    {Laws.all_bytes(c0 <> cs) == True{} : Bool})))

def utf8_proof.complete2.w(+b1: U32, +b2: U32, +acc: U32, +c0: U32, +cs: List<&2, U32>, +p: U32, +ps: List<&2, U32>,
  +eqacc: {UTF8.append_continuation(acc, 128) == (U32.shln(U32.and(b1, 31), 6n) + U32.and(b2, 63) : U32) : U32},
  +same: {List.append(&2, U32, p <> ps, c0 <> cs) == [b1, b2] : List<&2, U32>},
  allb: {Laws.all_bytes(c0 <> cs) == True{} : Bool},
  w: Exists(U32, cp => {UTF8.two_byte_scalar.if(b1, b2, UTF8.valid_two_bytes(b1, b2), {==}) == Some{cp} : Maybe<&2, U32>} & {cp == (U32.shln(U32.and(b1, 31), 6n) + U32.and(b2, 63) : U32) : U32})) ->
  utf8_proof.Completion(p, ps):
  (+cp, r) = w
  (+some, +eq) = r
  (c0, (cs, (cp, (
    Equal.trans(Maybe<&2, U32>, UTF8.sequence_scalar(List.append(&2, U32, p <> ps, c0 <> cs)), UTF8.sequence_scalar([b1, b2]), Some{cp}, Equal.cong(List<&2, U32>, Maybe<&2, U32>, x => UTF8.sequence_scalar(x), List.append(&2, U32, p <> ps, c0 <> cs), [b1, b2], same), some),
    (utf8_proof.low6_at(UTF8.append_continuation(acc, 128), cp, Equal.sym(U32, cp, UTF8.append_continuation(acc, 128), Equal.trans(U32, cp, (U32.shln(U32.and(b1, 31), 6n) + U32.and(b2, 63) : U32), UTF8.append_continuation(acc, 128), eq, Equal.sym(U32, UTF8.append_continuation(acc, 128), (U32.shln(U32.and(b1, 31), 6n) + U32.and(b2, 63) : U32), eqacc))), utf8_proof.low6(acc)), allb)))))

def utf8_proof.complete3.w(+b1: U32, +b2: U32, +b3: U32, +acc: U32, +c0: U32, +cs: List<&2, U32>, +p: U32, +ps: List<&2, U32>,
  +eqacc: {UTF8.append_continuation(acc, 128) == utf8_proof.dec3(b1, b2, b3) : U32},
  +same: {List.append(&2, U32, p <> ps, c0 <> cs) == [b1, b2, b3] : List<&2, U32>},
  allb: {Laws.all_bytes(c0 <> cs) == True{} : Bool},
  w: Exists(U32, cp => {UTF8.three_byte_scalar.if(b1, b2, b3, UTF8.valid_three_bytes(b1, b2, b3), {==}) == Some{cp} : Maybe<&2, U32>} & {cp == utf8_proof.dec3(b1, b2, b3) : U32})) ->
  utf8_proof.Completion(p, ps):
  (+cp, r) = w
  (+some, +eq) = r
  (c0, (cs, (cp, (
    Equal.trans(Maybe<&2, U32>, UTF8.sequence_scalar(List.append(&2, U32, p <> ps, c0 <> cs)), UTF8.sequence_scalar([b1, b2, b3]), Some{cp}, Equal.cong(List<&2, U32>, Maybe<&2, U32>, x => UTF8.sequence_scalar(x), List.append(&2, U32, p <> ps, c0 <> cs), [b1, b2, b3], same), some),
    (utf8_proof.low6_at(UTF8.append_continuation(acc, 128), cp, Equal.sym(U32, cp, UTF8.append_continuation(acc, 128), Equal.trans(U32, cp, utf8_proof.dec3(b1, b2, b3), UTF8.append_continuation(acc, 128), eq, Equal.sym(U32, UTF8.append_continuation(acc, 128), utf8_proof.dec3(b1, b2, b3), eqacc))), utf8_proof.low6(acc)), allb)))))

def utf8_proof.complete4.w(+b1: U32, +b2: U32, +b3: U32, +b4: U32, +acc: U32, +c0: U32, +cs: List<&2, U32>, +p: U32, +ps: List<&2, U32>,
  +eqacc: {UTF8.append_continuation(acc, 128) == utf8_proof.dec4(b1, b2, b3, b4) : U32},
  +same: {List.append(&2, U32, p <> ps, c0 <> cs) == [b1, b2, b3, b4] : List<&2, U32>},
  allb: {Laws.all_bytes(c0 <> cs) == True{} : Bool},
  w: Exists(U32, cp => {UTF8.four_byte_scalar.if(b1, b2, b3, b4, UTF8.valid_four_bytes(b1, b2, b3, b4), {==}) == Some{cp} : Maybe<&2, U32>} & {cp == utf8_proof.dec4(b1, b2, b3, b4) : U32})) ->
  utf8_proof.Completion(p, ps):
  (+cp, r) = w
  (+some, +eq) = r
  (c0, (cs, (cp, (
    Equal.trans(Maybe<&2, U32>, UTF8.sequence_scalar(List.append(&2, U32, p <> ps, c0 <> cs)), UTF8.sequence_scalar([b1, b2, b3, b4]), Some{cp}, Equal.cong(List<&2, U32>, Maybe<&2, U32>, x => UTF8.sequence_scalar(x), List.append(&2, U32, p <> ps, c0 <> cs), [b1, b2, b3, b4], same), some),
    (utf8_proof.low6_at(UTF8.append_continuation(acc, 128), cp, Equal.sym(U32, cp, UTF8.append_continuation(acc, 128), Equal.trans(U32, cp, utf8_proof.dec4(b1, b2, b3, b4), UTF8.append_continuation(acc, 128), eq, Equal.sym(U32, UTF8.append_continuation(acc, 128), utf8_proof.dec4(b1, b2, b3, b4), eqacc))), utf8_proof.low6(acc)), allb)))))

def utf8_proof.complete.of1(+b1: U32, none: {UTF8.sequence_scalar([b1]) == None{} : Maybe<&2, U32>}, o: utf8_proof.OrT6(UTF8.valid_one_byte(b1), UTF8.valid_two_bytes(b1, 128), UTF8.valid_three_bytes(b1, 128, 128), UTF8.valid_three_bytes(b1, 191, 128), UTF8.valid_four_bytes(b1, 128, 128, 128), UTF8.valid_four_bytes(b1, 191, 128, 128))) -> utf8_proof.Completion(b1, Nil{}):
  match o:
    case Inl{e}: Empty.absurd(utf8_proof.Completion(b1, Nil{}), utf8_proof.none1.contra(b1, UTF8.valid_one_byte(b1), {==}, none, e))
    case Inr{Inl{e}}: utf8_proof.complete2.w(b1, 128, U32.and(b1, 31), 128, Nil{}, b1, Nil{}, {==}, {==}, {==}, utf8_proof.some2.if(b1, 128, UTF8.valid_two_bytes(b1, 128), {==}, e))
    case Inr{Inr{Inl{e}}}: utf8_proof.complete3.w(b1, 128, 128, UTF8.append_continuation(U32.and(b1, 15), 128), 128, [128], b1, Nil{}, {==}, {==}, {==}, utf8_proof.some3.if(b1, 128, 128, UTF8.valid_three_bytes(b1, 128, 128), {==}, e))
    case Inr{Inr{Inr{Inl{e}}}}: utf8_proof.complete3.w(b1, 191, 128, UTF8.append_continuation(U32.and(b1, 15), 191), 191, [128], b1, Nil{}, {==}, {==}, {==}, utf8_proof.some3.if(b1, 191, 128, UTF8.valid_three_bytes(b1, 191, 128), {==}, e))
    case Inr{Inr{Inr{Inr{Inl{e}}}}}: utf8_proof.complete4.w(b1, 128, 128, 128, UTF8.append_continuation(UTF8.append_continuation(U32.and(b1, 7), 128), 128), 128, [128, 128], b1, Nil{}, {==}, {==}, {==}, utf8_proof.some4.if(b1, 128, 128, 128, UTF8.valid_four_bytes(b1, 128, 128, 128), {==}, e))
    case Inr{Inr{Inr{Inr{Inr{e}}}}}: utf8_proof.complete4.w(b1, 191, 128, 128, UTF8.append_continuation(UTF8.append_continuation(U32.and(b1, 7), 191), 128), 191, [128, 128], b1, Nil{}, {==}, {==}, {==}, utf8_proof.some4.if(b1, 191, 128, 128, UTF8.valid_four_bytes(b1, 191, 128, 128), {==}, e))

def utf8_proof.complete.of2(+b1: U32, +b2: U32, none: {UTF8.sequence_scalar([b1, b2]) == None{} : Maybe<&2, U32>}, o: utf8_proof.OrT3(UTF8.valid_two_bytes(b1, b2), UTF8.valid_three_bytes(b1, b2, 128), UTF8.valid_four_bytes(b1, b2, 128, 128))) -> utf8_proof.Completion(b1, [b2]):
  match o:
    case Inl{e}: Empty.absurd(utf8_proof.Completion(b1, [b2]), utf8_proof.none2.contra(b1, b2, UTF8.valid_two_bytes(b1, b2), {==}, none, e))
    case Inr{Inl{e}}: utf8_proof.complete3.w(b1, b2, 128, UTF8.append_continuation(U32.and(b1, 15), b2), 128, Nil{}, b1, [b2], {==}, {==}, {==}, utf8_proof.some3.if(b1, b2, 128, UTF8.valid_three_bytes(b1, b2, 128), {==}, e))
    case Inr{Inr{e}}: utf8_proof.complete4.w(b1, b2, 128, 128, UTF8.append_continuation(UTF8.append_continuation(U32.and(b1, 7), b2), 128), 128, [128], b1, [b2], {==}, {==}, {==}, utf8_proof.some4.if(b1, b2, 128, 128, UTF8.valid_four_bytes(b1, b2, 128, 128), {==}, e))

def utf8_proof.complete.of3(+b1: U32, +b2: U32, +b3: U32, none: {UTF8.sequence_scalar([b1, b2, b3]) == None{} : Maybe<&2, U32>}, o: utf8_proof.OrT2(UTF8.valid_three_bytes(b1, b2, b3), UTF8.valid_four_bytes(b1, b2, b3, 128))) -> utf8_proof.Completion(b1, [b2, b3]):
  match o:
    case Inl{e}: Empty.absurd(utf8_proof.Completion(b1, [b2, b3]), utf8_proof.none3.contra(b1, b2, b3, UTF8.valid_three_bytes(b1, b2, b3), {==}, none, e))
    case Inr{e}: utf8_proof.complete4.w(b1, b2, b3, 128, UTF8.append_continuation(UTF8.append_continuation(U32.and(b1, 7), b2), b3), 128, Nil{}, b1, [b2, b3], {==}, {==}, {==}, utf8_proof.some4.if(b1, b2, b3, 128, UTF8.valid_four_bytes(b1, b2, b3, 128), {==}, e))

def utf8_proof.complete(+p: U32, +ps: List<&2, U32>, begins: {UTF8.is_valid_sequence_prefix(p <> ps) == True{} : Bool}, none: {UTF8.sequence_scalar(p <> ps) == None{} : Maybe<&2, U32>}) -> utf8_proof.Completion(p, ps):
  match ps:
    case Nil{}:
      utf8_proof.complete.of1(p, none, utf8_proof.or_split6(UTF8.valid_one_byte(p), UTF8.valid_two_bytes(p, 128), UTF8.valid_three_bytes(p, 128, 128), UTF8.valid_three_bytes(p, 191, 128), UTF8.valid_four_bytes(p, 128, 128, 128), UTF8.valid_four_bytes(p, 191, 128, 128), begins))
    case +b2 <> Nil{}:
      utf8_proof.complete.of2(p, b2, none, utf8_proof.or_split3(UTF8.valid_two_bytes(p, b2), UTF8.valid_three_bytes(p, b2, 128), UTF8.valid_four_bytes(p, b2, 128, 128), begins))
    case +b2 <> +b3 <> Nil{}:
      utf8_proof.complete.of3(p, b2, b3, none, utf8_proof.or_split2(UTF8.valid_three_bytes(p, b2, b3), UTF8.valid_four_bytes(p, b2, b3, 128), begins))
    case +b2 <> +b3 <> +b4 <> Nil{}:
      Empty.absurd(utf8_proof.Completion(p, [b2, b3, b4]), utf8_proof.none4.contra(p, b2, b3, b4, UTF8.valid_four_bytes(p, b2, b3, b4), {==}, none, begins))
    case b2 <> b3 <> b4 <> b5 <> after:
      Empty.absurd(utf8_proof.Completion(p, b2 <> b3 <> b4 <> b5 <> after), UTF8.false_true(begins))

def utf8_proof.run.regroup(+p: U32, +ps: List<&2, U32>, +c0: U32, +c1: U32, +cs: List<&2, U32>, +cp: U32,
  e: {UTF8.sequence_scalar(List.append(&2, U32, p <> ps, c0 <> c1 <> cs)) == Some{cp} : Maybe<&2, U32>}) ->
  {UTF8.sequence_scalar(List.append(&2, U32, p <> List.append(&2, U32, ps, [c0]), c1 <> cs)) == Some{cp} : Maybe<&2, U32>}:
  %Equal.sym(List<&2, U32>, List.append(&2, U32, List.append(&2, U32, p <> ps, [c0]), c1 <> cs), List.append(&2, U32, p <> ps, c0 <> c1 <> cs), utf8_proof.append_assoc(p <> ps, [c0], c1 <> cs)) : {UTF8.sequence_scalar(_) == Some{cp} : Maybe<&2, U32>}
  e

def utf8_proof.run.last(+p: U32, +ps: List<&2, U32>, +c0: U32, +cp: U32,
  e: {UTF8.sequence_scalar(List.append(&2, U32, p <> ps, [c0])) == Some{cp} : Maybe<&2, U32>}) ->
  {utf8_proof.final_text(UTF8.decode_buffer.bytes([c0], p <> ps)) == SCon{Chr{cp}, SNil{}} : String}:
  %Equal.sym(Maybe<&2, U32>, UTF8.sequence_scalar(List.append(&2, U32, p <> ps, [c0])), Some{cp}, e) :
    {utf8_proof.final_text(UTF8.decode_buffer.then(UTF8.decode_buffer.advance(List.append(&2, U32, p <> ps, [c0]), _, UTF8.is_valid_sequence_prefix(List.append(&2, U32, p <> ps, [c0])), u => UTF8.decode_buffer.prepend(UTF8.replacement_char_string(), UTF8.decode_buffer.start(c0))), q => UTF8.decode_buffer.bytes(Nil{}, q))) == SCon{Chr{cp}, SNil{}} : String}
  {==}

def utf8_proof.run.next(+p: U32, +ps: List<&2, U32>, +c0: U32, +c1: U32, +cs: List<&2, U32>, +cp: U32,
  +none: {UTF8.sequence_scalar(List.append(&2, U32, p <> ps, [c0])) == None{} : Maybe<&2, U32>},
  +begins: {UTF8.is_valid_sequence_prefix(List.append(&2, U32, p <> ps, [c0])) == True{} : Bool},
  ih: {utf8_proof.final_text(UTF8.decode_buffer.bytes(c1 <> cs, List.append(&2, U32, p <> ps, [c0]))) == SCon{Chr{cp}, SNil{}} : String}) ->
  {utf8_proof.final_text(UTF8.decode_buffer.bytes(c0 <> c1 <> cs, p <> ps)) == SCon{Chr{cp}, SNil{}} : String}:
  %Equal.sym(Maybe<&2, U32>, UTF8.sequence_scalar(List.append(&2, U32, p <> ps, [c0])), None{}, none) :
    {utf8_proof.final_text(UTF8.decode_buffer.then(UTF8.decode_buffer.advance(List.append(&2, U32, p <> ps, [c0]), _, UTF8.is_valid_sequence_prefix(List.append(&2, U32, p <> ps, [c0])), u => UTF8.decode_buffer.prepend(UTF8.replacement_char_string(), UTF8.decode_buffer.start(c0))), q => UTF8.decode_buffer.bytes(c1 <> cs, q))) == SCon{Chr{cp}, SNil{}} : String}
  %Equal.sym(Bool, UTF8.is_valid_sequence_prefix(List.append(&2, U32, p <> ps, [c0])), True{}, begins) :
    {utf8_proof.final_text(UTF8.decode_buffer.then(UTF8.decode_buffer.advance(List.append(&2, U32, p <> ps, [c0]), None{}, _, u => UTF8.decode_buffer.prepend(UTF8.replacement_char_string(), UTF8.decode_buffer.start(c0))), q => UTF8.decode_buffer.bytes(c1 <> cs, q))) == SCon{Chr{cp}, SNil{}} : String}
  Equal.trans(String, utf8_proof.final_text(UTF8.decode_buffer.prepend("", UTF8.decode_buffer.bytes(c1 <> cs, List.append(&2, U32, p <> ps, [c0])))), "" ++ utf8_proof.final_text(UTF8.decode_buffer.bytes(c1 <> cs, List.append(&2, U32, p <> ps, [c0]))), SCon{Chr{cp}, SNil{}},
    utf8_proof.final_prepend("", UTF8.decode_buffer.bytes(c1 <> cs, List.append(&2, U32, p <> ps, [c0]))), ih)

def utf8_proof.run(+cs: List<&2, U32>, +p: U32, +ps: List<&2, U32>, +c0: U32, +cp: U32,
  e: {UTF8.sequence_scalar(List.append(&2, U32, p <> ps, c0 <> cs)) == Some{cp} : Maybe<&2, U32>}) ->
  {utf8_proof.final_text(UTF8.decode_buffer.bytes(c0 <> cs, p <> ps)) == SCon{Chr{cp}, SNil{}} : String}:
  match cs:
    case Nil{}:
      utf8_proof.run.last(p, ps, c0, cp, e)
    case +c1 <> +more:
      +e2 = utf8_proof.run.regroup(p, ps, c0, c1, more, cp, e)
      +v2 = utf8_proof.decodes_valid(List.append(&2, U32, p <> List.append(&2, U32, ps, [c0]), c1 <> more), cp, utf8_proof.scalar_to_decodes(List.append(&2, U32, p <> List.append(&2, U32, ps, [c0]), c1 <> more), cp, e2))
      utf8_proof.run.next(p, ps, c0, c1, more, cp,
        utf8_proof.pf_scalar_none(p, List.append(&2, U32, ps, [c0]), c1, more, UTF8.sequence_scalar(p <> List.append(&2, U32, ps, [c0])), {==}, v2),
        utf8_proof.prefix_from_valid(p, List.append(&2, U32, ps, [c0]), c1 <> more, v2),
        utf8_proof.run(more, p, List.append(&2, U32, ps, [c0]), c1, cp, e2))

def utf8_proof.prompt.large(+bytes: List<&2, U32>, +text: String, +c: U32, +t: String, +p: U32, +ps: List<&2, U32>,
  +same: {t == text : String},
  split: @rest: List<&2, U32> -> Laws.decodes(List.append(&2, U32, bytes, rest),
    t ++ utf8_proof.final_text(UTF8.decode_buffer.bytes(rest, p <> ps))),
  +large: {U32.is_eq(U32.and(c, 63), 0) == False{} : Bool},
  comp: utf8_proof.Completion(p, ps)) ->
  utf8_proof.PromptGoal(bytes, text, c):
  (+c0, r1) = comp
  (+cs, r2) = r1
  (+cp, facts) = r2
  (e, r3) = facts
  (bound, allb) = r3
  +rest_is = utf8_proof.run(cs, p, ps, c0, cp, e)
  (c0 <> cs, (allb, (t ++ utf8_proof.final_text(UTF8.decode_buffer.bytes(c0 <> cs, p <> ps)),
    (split(c0 <> cs), prefix => utf8_proof.not_prefix(text, t, c,
      utf8_proof.final_text(UTF8.decode_buffer.bytes(c0 <> cs, p <> ps)), same, prefix,
      more => e2 => utf8_proof.differs(c, cp, more, utf8_proof.final_text(UTF8.decode_buffer.bytes(c0 <> cs, p <> ps)), large, rest_is, bound, e2))))))

def utf8_proof.prompt.lead(+bytes: List<&2, U32>, +text: String, +c: U32, +t: String, +p: U32, +ps: List<&2, U32>,
  +same: {t == text : String},
  lead: {UTF8.is_valid_sequence_prefix(p <> ps) == True{} : Bool},
  alone: {UTF8.sequence_scalar(p <> ps) == None{} : Maybe<&2, U32>},
  split: @rest: List<&2, U32> -> Laws.decodes(List.append(&2, U32, bytes, rest),
    t ++ utf8_proof.final_text(UTF8.decode_buffer.bytes(rest, p <> ps))),
  small: Bool, +small_is: {U32.is_eq(U32.and(c, 63), 0) == small : Bool}) ->
  utf8_proof.PromptGoal(bytes, text, c):
  match small:
    case True{}:
      (Nil{}, ({==}, (t ++ utf8_proof.final_text(UTF8.decode_buffer.bytes(Nil{}, p <> ps)),
        (split(Nil{}), prefix => utf8_proof.not_prefix(text, t, c, SCon{Chr{65533}, SNil{}}, same, prefix,
          more => e => utf8_proof.not_replacement(c, more, small_is, e))))))
    case False{}:
      utf8_proof.prompt.large(bytes, text, c, t, p, ps, same, split, small_is,
        utf8_proof.complete(p, ps, lead, alone))

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
    case +p <> +ps:
      (lead, alone) = pending
      utf8_proof.prompt.lead(bytes, text, c, t, p, ps, same, lead, alone, split, U32.is_eq(U32.and(c, 63), 0), {==})

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

def Laws.utf8_decode_buffer_prompt(buffers, valid, c):
  utf8_proof.prompt.step(List.concat(&2, U32, buffers), Laws.decoded_so_far(buffers, valid), c,
    UTF8.decode_buffer.bytes(List.concat(&2, U32, buffers), Nil{}),
    utf8_proof.so_far_is(buffers, valid),
    utf8_proof.pending_ok(List.concat(&2, U32, buffers), Nil{}, Unit{}),
    rest => utf8_proof.decodes_split(List.concat(&2, U32, buffers), rest))
