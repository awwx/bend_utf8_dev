import Base
import ./binary.bend as B

# Encoding capacity is separate from shortest-form validity.
def can_encode_as_one_byte(+cp: U32) -> Bool:
  U32.is_le(cp, 127)

def can_encode_as_two_bytes(+cp: U32) -> Bool:
  U32.is_le(cp, 2047)

def encode_as_one_byte(+cp: U32,
  -valid: {can_encode_as_one_byte(cp) == True{} : Bool}) -> U32:
  cp

# A one-byte encoding has the same value as its code point (0..127).
def has_one_byte_shape(byte: U32) -> Bool:
  can_encode_as_one_byte(byte)

# Decode only bytes with the one-byte shape.
def decode_one_byte(+byte: U32,
  -valid_shape: {has_one_byte_shape(byte) == True{} : Bool}) -> U32:
  byte

# Deliberately permits overlong encodings of code points 0..127.
def encode_as_two_bytes(+cp: U32,
  -valid: {can_encode_as_two_bytes(cp) == True{} : Bool}) -> U32 & U32:
  ((192 + U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(cp)))))) : U32),
   (128 + U32.and(cp, 63) : U32))

def has_two_byte_shape(b1: U32, b2: U32) -> Bool:
  B.byte_mask("110xxxxx", b1, {==}) && B.byte_mask("10xxxxxx", b2, {==})

# Decode only pairs with the two-byte shape, including overlong encodings.
def decode_two_bytes(+b1: U32, +b2: U32,
  -valid_shape: {has_two_byte_shape(b1, b2) == True{} : Bool}) -> U32:
  (U32.shl(U32.shl(U32.shl(U32.shl(U32.shl(U32.shl(U32.and(b1, 31))))))) + U32.and(b2, 63) : U32)

# The decoded code point also has a one-byte representation.
def overlong_two_bytes(+b1: U32, +b2: U32,
  -valid_shape: {has_two_byte_shape(b1, b2) == True{} : Bool}) -> Bool:
  can_encode_as_one_byte(decode_two_bytes(b1, b2, valid_shape))

# Test the shape before checking whether the encoding is shortest.
def valid_two_bytes.if(+b1: U32, +b2: U32, shape: Bool,
  -checked: {has_two_byte_shape(b1, b2) == shape : Bool}) -> Bool:
  match shape:
    case False{}: False{}
    case True{}: Bool.not(overlong_two_bytes(b1, b2, checked))

def valid_two_bytes(+b1: U32, +b2: U32) -> Bool:
  valid_two_bytes.if(b1, b2, has_two_byte_shape(b1, b2), {==})

# An eleven-bit payload covers exactly the two-byte encoding capacity.
def codepoint11(bits: Word(11n)) -> U32:
  match bits:
    case WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WNil{}}}}}}}}}}}}:
      U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, Word.zero(21n)}}}}}}}}}}}}

def first(pair: U32 & U32) -> U32:
  (a, b) = pair
  a

def second(pair: U32 & U32) -> U32:
  (a, b) = pair
  b
