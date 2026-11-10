import Base
import ./binary_mask.bend as B

# Byte masks
#
#
# A byte mask is a string of exactly eight characters, each '0', '1',
# or 'x'.
#
# A byte matches a mask if for each '0' and '1' in the mask, the byte
# has a matching 0 or 1 at that position.

law byte_mask_examples:
  {B.byte_mask("01xxxxxx",  64, {==}) == True{}  : Bool} &
  {B.byte_mask("01xxxxxx", 127, {==}) == True{}  : Bool} &
  {B.byte_mask("01xxxxxx", 128, {==}) == False{} : Bool} &
  {B.byte_mask("xxxxxxxx", 255, {==}) == True{}  : Bool} &
  {B.byte_mask("xxxxxxxx", 256, {==}) == False{} : Bool} &
  {B.byte_mask("10000001", 129, {==}) == True{}  : Bool} &
  {B.byte_mask("10000001", 128, {==}) == False{} : Bool}

law is_mask_digit:
  for +c: Char
  {B.is_mask_digit(c) ==
    (Char.is_eq(c, '0') || Char.is_eq(c, '1') || Char.is_eq(c, 'x')) : Bool}

law is_valid_byte_mask:
  for +mask: String
  {B.is_valid_byte_mask(mask) ==
    (Nat.is_eq(String.length(mask), 8n) &&
     List.all(~&2, ~Char, ~(c => B.is_mask_digit(c)), String.to_list(mask))) : Bool}

def mask_positions(mask: String, weights: +List<U32>, +byte: U32) -> Bool:
  match mask weights:
    case SNil{} Nil{}:
      True{}
    case SCon{+c, rest} Con{+weight, tail}:
      (Char.is_eq(c, 'x') ||
       (Char.is_eq(c, '0') && U32.is_eq(U32.and(byte, weight), 0)) ||
       (Char.is_eq(c, '1') && U32.is_eq(U32.and(byte, weight), weight))) &&
      mask_positions(rest, tail, byte)
    case _ _:
      False{}

# First position = bit 7; U32 values above 255 never match.
law byte_mask:
  for +mask: String
  for +byte: U32
  for valid: {B.is_valid_byte_mask(mask) == True{} : Bool}
  exs accepted: {B.is_valid_byte_mask(mask) == True{} : Bool}
  {B.byte_mask(mask, byte, accepted) ==
    (U32.is_le(byte, 255) && mask_positions(mask, [128, 64, 32, 16, 8, 4, 2, 1], byte)) : Bool}
