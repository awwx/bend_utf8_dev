import Base
import ./defs.bend as Defs
import ./binary.bend as B
import ./utf8.bend as UTF8
import ./binary_LAWS.bend as BinaryLaws
import ./hexdigits.bend as H
import ./func_LAWS.bend as Func


## Surrogate code points

# Surrogate code points are U+D800..U+DFFF.

def is_surrogate_code_point(+cp: U32) -> Bool:
  U32.is_ge(cp, H.hex_u32("D800", {==})) &&
  U32.is_le(cp, H.hex_u32("DFFF", {==}))

law is_surrogate_code_point_examples:
  {is_surrogate_code_point(H.hex_u32("0000", {==})) == False{} : Bool} &
  {is_surrogate_code_point(H.hex_u32("D7FF", {==})) == False{} : Bool} &
  {is_surrogate_code_point(H.hex_u32("D800", {==})) == True{} : Bool} &
  {is_surrogate_code_point(H.hex_u32("DC00", {==})) == True{} : Bool} &
  {is_surrogate_code_point(H.hex_u32("DFFF", {==})) == True{} : Bool} &
  {is_surrogate_code_point(H.hex_u32("E000", {==})) == False{} : Bool}


## Unicode scalars

# A Unicode scalar is any code point from U+0000 to U+10FFFF excluding
# surrogate code points.

def is_unicode_scalar(+cp: U32) -> Bool:
  U32.is_ge(cp, H.hex_u32("000000", {==})) &&
  U32.is_le(cp, H.hex_u32("10FFFF", {==})) &&
  Bool.not(is_surrogate_code_point(cp))


## Byte shapes

# By a "byte shape" we mean a series of bytes that has the correct bit
# pattern for a UTF-8 encoding.  This includes invalid UTF-8 encodings
# such as overlong encodings, encodings of surrogate code points, and
# encodings of code points values above U+10FFFF.

# UTF-8 one-byte shape
#
# 00000000 00000000 00000000 0yyyzzzz -> 0yyyzzzz
#
# Returns Some U32 representing the byte if the shape matches, or None
# if the shape doesn't match.

def one_byte_shape.bits(bits: Defs.Byte4()) -> Maybe<&2, U32>:
  match bits:
    case ((False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}),
          (False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}),
          (False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}),
          (False{}, y1, y2, y3, z1, z2, z3, z4)):
      Some{B.bit8_value((False{}, y1, y2, y3, z1, z2, z3, z4))}
    case _:
      None{}

def one_byte_shape(cp: U32) -> Maybe<&2, U32>:
  one_byte_shape.bits(B.u32_byte4(cp))

# UTF-8 two-byte shape
#
# 00000000 00000000 00000xxx yyyyzzzz -> 110xxxyy 10yyzzzz
#
# Returns two U32 representing the two bytes if the shape matches, or
# None if the shape doesn't match.
#
# Capacity includes overlong encodings of 0..127; shortest-form
# validity is separate.

def two_byte_shape.bits(bits: Defs.Byte4()) -> Maybe<&1, U32 & U32>:
  match bits:
    case ((False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}),
          (False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}),
          (False{}, False{}, False{}, False{}, False{}, x1, x2, x3),
          (y1, y2, y3, y4, z1, z2, z3, z4)):
      Some{(B.bit8_value((True{}, True{}, False{}, x1, x2, x3, y1, y2)),
            B.bit8_value((True{}, False{}, y3, y4, z1, z2, z3, z4)))}
    case _:
      None{}

def two_byte_shape(cp: U32) -> Maybe<&1, U32 & U32>:
  two_byte_shape.bits(B.u32_byte4(cp))


## Can encode

# A code point can be encoded as a sequence of bytes iff the shape
# matches.

law utf8_can_encode_as_one_byte:
  for +cp: U32
  {UTF8.can_encode_as_one_byte(cp) == Maybe.is_some(&2, U32, one_byte_shape(cp)) : Bool}

law utf8_can_encode_as_two_bytes:
  for +cp: U32
  {UTF8.can_encode_as_two_bytes(cp) == Maybe.is_some(&1, U32 & U32, two_byte_shape(cp)) : Bool}


## Encode as

# Require that given a supplied proof that a code point *can* be encoded
# as a byte sequence, `encode_as_*` returns those bytes.
# (Supplying the proof means that we don't have to return a Maybe.)

law utf8_encode_as_one_byte:
  for +cp: U32
  for valid: {UTF8.can_encode_as_one_byte(cp) == True{} : Bool}
  {Some{UTF8.encode_as_one_byte(cp, valid)} == one_byte_shape(cp) : Maybe<&2, U32>}

law utf8_encode_as_two_bytes:
  for +cp: U32
  for valid: {UTF8.can_encode_as_two_bytes(cp) == True{} : Bool}
  {Some{UTF8.encode_as_two_bytes(cp, valid)} == two_byte_shape(cp) : Maybe<&1, U32 & U32>}


## has_N_byte_shape(cp) -> Bool

# Return True if the code point *can be* encoded as a sequence of the
# specified number of bytes.  (At this point we're still ignoring
# overlong encodings.)

law utf8_has_one_byte_shape:
  for +byte: U32
  representation = Exists(U32, cp =>
    {one_byte_shape(cp) == Some{byte} : Maybe<&2, U32>})
  ({UTF8.has_one_byte_shape(byte) == True{} : Bool} -> representation) &
  (representation -> {UTF8.has_one_byte_shape(byte) == True{} : Bool})

law utf8_has_two_byte_shape:
  for +b1: U32
  for +b2: U32
  representation = Exists(U32, cp =>
    {two_byte_shape(cp) == Some{(b1, b2)} : Maybe<&1, U32 & U32>})
  ({UTF8.has_two_byte_shape(b1, b2) == True{} : Bool} -> representation) &
  (representation -> {UTF8.has_two_byte_shape(b1, b2) == True{} : Bool})


## Encoding is bijective

# Each encode_as_N_byte is bijective, and decode_N_byte is exactly its
# inverse.
#
# For a code point which *can be* encoded as the specified number of
# bytes, we can roundtrip `decode(encode(cp)) == cp` and vice versa.

law utf8_one_byte_inverse:
  Func.Bijection(U32, U32,
    cp => UTF8.can_encode_as_one_byte(cp),
    byte => UTF8.has_one_byte_shape(byte),
    cp => valid => UTF8.encode_as_one_byte(cp, valid),
    byte => valid => UTF8.decode_one_byte(byte, valid))

law utf8_two_byte_inverse:
  Func.Bijection(U32, U32 & U32,
    cp => UTF8.can_encode_as_two_bytes(cp),
    p => UTF8.has_two_byte_shape(B.first(p), B.second(p)),
    cp => valid => UTF8.encode_as_two_bytes(cp, valid),
    p => valid => UTF8.decode_two_bytes(B.first(p), B.second(p), valid))


## Overlong encodings

# In UTF-8, an "overlong" encoding is an encoding which is the correct
# shape for encoding the code point, but a shorter enconding also
# encodes the code point.  These are invalid in UTF-8.

# No one-byte encoding is overlong.

def overlong_one_byte(b1: U32) -> Bool:
  False{}

# A two-byte encoding is overlong if the code point it encodes could
# be encoded as a one byte encoding.

law utf8_overlong_two_bytes:
  for +b1: U32
  for +b2: U32
  for -valid_shape: {UTF8.has_two_byte_shape(b1, b2) == True{} : Bool}
  {UTF8.overlong_two_bytes(b1, b2, valid_shape) ==
    UTF8.can_encode_as_one_byte(UTF8.decode_two_bytes(b1, b2, valid_shape)) : Bool}


## Valid encodings

# An encoding is valid when:
# * It has the correct byte shape, and
# * It is not overlong, and
# * the code point it encodes is a Unicode scalar (not a forbidden
#   surrogate).

# Testing the shape first supplies the proof that decoding needs.

def valid_one_byte.if(+byte: U32, shape: Bool,
  -checked: {UTF8.has_one_byte_shape(byte) == shape : Bool}) -> Bool:
  match shape:
    case False{}:
      False{}
    case True{}:
      Bool.not(overlong_one_byte(byte)) &&
      is_unicode_scalar(UTF8.decode_one_byte(byte, checked))

law utf8_valid_one_byte:
  for +byte: U32
  {UTF8.valid_one_byte(byte) == valid_one_byte.if(byte, UTF8.has_one_byte_shape(byte), {==}) : Bool}

def valid_two_bytes.if(+b1: U32, +b2: U32, shape: Bool,
  -checked: {UTF8.has_two_byte_shape(b1, b2) == shape : Bool}) -> Bool:
  match shape:
    case False{}:
      False{}
    case True{}:
      Bool.not(UTF8.overlong_two_bytes(b1, b2, checked)) &&
      is_unicode_scalar(UTF8.decode_two_bytes(b1, b2, checked))

law utf8_valid_two_bytes:
  for +b1: U32
  for +b2: U32
  {UTF8.valid_two_bytes(b1, b2) == valid_two_bytes.if(b1, b2, UTF8.has_two_byte_shape(b1, b2), {==}) : Bool}


## Valid sequences have their correct byte shape.

# Since our definition of a valid sequence includes that a sequence is
# only valid when it has the correct byte shape, if we have a valid
# sequence we know that it has a correct byte shape.
#
# We use this law below when we have a valid sequence and we need
# a proof that it has a correct byte shape.

law valid_one_byte_has_shape:
  for +byte: U32
  for valid: {UTF8.valid_one_byte(byte) == True{} : Bool}
  {UTF8.has_one_byte_shape(byte) == True{} : Bool}

law valid_two_bytes_has_shape:
  for +b1: U32
  for +b2: U32
  for valid: {UTF8.valid_two_bytes(b1, b2) == True{} : Bool}
  {UTF8.has_two_byte_shape(b1, b2) == True{} : Bool}


## Decoding a valid sequence

# Given a sequence of bytes, return the code point encoded by the
# sequence if it's a valid sequence, or return None if the sequence is
# invalid.

def one_byte_scalar.if(+byte: U32, valid: Bool,
  -checked: {UTF8.valid_one_byte(byte) == valid : Bool}) -> Maybe<&2, U32>:
  match valid:
    case False{}:
      None{}
    case True{}:
      Some{UTF8.decode_one_byte(byte, valid_one_byte_has_shape(byte, checked))}

def one_byte_scalar(+byte: U32) -> Maybe<&2, U32>:
  one_byte_scalar.if(byte, UTF8.valid_one_byte(byte), {==})

def two_byte_scalar.if(+b1: U32, +b2: U32, valid: Bool,
  -checked: {UTF8.valid_two_bytes(b1, b2) == valid : Bool}) -> Maybe<&2, U32>:
  match valid:
    case False{}:
      None{}
    case True{}:
      Some{UTF8.decode_two_bytes(b1, b2, valid_two_bytes_has_shape(b1, b2, checked))}

def two_byte_scalar(+b1: U32, +b2: U32) -> Maybe<&2, U32>:
  two_byte_scalar.if(b1, b2, UTF8.valid_two_bytes(b1, b2), {==})


## is_valid_sequence

# Returns True when the sequence is exactly a valid sequence.

def is_valid_sequence(seq: List<&2, U32>) -> Bool:
  match seq:
    case +b1 <> Nil{}:
      UTF8.valid_one_byte(b1)
    case +b1 <> +b2 <> Nil{}:
      UTF8.valid_two_bytes(b1, b2)
    case _:
      False{}


## Decode the first sequence from a buffer.

# If the buffer starts with a valid sequence, returns the scalar that
# the sequence encodes and the remaining buffer after that sequence.
#
# Returns None if the buffer doesn't start with a valid sequence.

def next_scalar.found(scalar: Maybe<&2, U32>, rest: List<&2, U32>,
  otherwise: List<&2, U32> -> Maybe<&1, U32 & List<&2, U32>>) ->
  Maybe<&1, U32 & List<&2, U32>>:
  match scalar:
    case Some{cp}:
      Some{(cp, rest)}
    case None{}:
      otherwise(rest)

def next_scalar.two(+b1: U32, rest: List<&2, U32>) ->
  Maybe<&1, U32 & List<&2, U32>>:
  match rest:
    case Nil{}:
      None{}
    case +b2 <> after:
      next_scalar.found(two_byte_scalar(b1, b2), after, r => None{})

def next_scalar(bytes: List<&2, U32>) -> Maybe<&1, U32 & List<&2, U32>>:
  match bytes:
    case Nil{}:
      None{}
    case +b1 <> rest:
      next_scalar.found(one_byte_scalar(b1), rest,
        r => next_scalar.two(b1, r))


## Begins a valid sequence

# `UTF8.begins_valid_sequence(seq)` returns True iff `seq` begins a
# valid sequence: there exists zero or more bytes which when added to
# `seq` makes it a valid sequence.
#
# Later we may find out that the actual input doesn't describe a valid
# sequence, so this says that if we've only seen `seq` so far, it
# *could* be a valid prefix for a legal encoding (including being
# itself a valid complete sequence).

law utf8_begins_valid_sequence:
  for +seq: List<&2, U32>
  completion = Exists(List<&2, U32>, rest =>
    {is_valid_sequence(List.append(&2, U32, seq, rest)) == True{} : Bool})
  ({UTF8.begins_valid_sequence(seq) == True{} : Bool} -> completion) &
  (completion -> {UTF8.begins_valid_sequence(seq) == True{} : Bool})


## Byte prefix

# Define a "prefix" to mean that the buffer begins with the prefix
# bytes.

def is_prefix(prefix: List<&2, U32>, bytes: List<&2, U32>) -> Type:
  Exists(List<&2, U32>, rest =>
    {List.append(&2, U32, prefix, rest) == bytes : List<&2, U32>})


## Next byte after a prefix.

# Returns the byte that follows a prefix, if the buffer is longer than
# the prefix, or None if there are no bytes following the prefix.
#
# This is a convenience function, we only pass in `prefix` for its length.

def next_byte_after(bytes: List<&2, U32>, prefix: List<&2, U32>) ->
  Maybe<&2, U32>:
  match bytes prefix:
    case Nil{} _:
      None{}
    case b <> rest Nil{}:
      Some{b}
    case b <> rest p <> ps:
      next_byte_after(rest, ps)



# Streaming decoding
# ==================
#
# `UTF8.decode_start()` is the decoder state before any input.
# `UTF8.decode_buffer(state, buffer)` takes the next buffer of bytes and
# returns the new state and the text that is now fully resolved.
# `UTF8.decode_done(state)` returns the text that ends the input.  The
# state type, `UTF8.DecodeState()`, is the implementation's choice: the
# laws below only describe the text that comes out.
#
# Ill-formed input is replaced as the Unicode Standard recommends (§3.9,
# "U+FFFD Substitution of Maximal Subparts"): each maximal subpart, the
# longest run of bytes that begins some valid sequence or else a single
# byte, becomes one U+FFFD.

def code_point_to_string(cp: U32) -> String:
  SCon{Chr{cp}, SNil{}}

# U+FFFD REPLACEMENT CHARACTER.

def replacement_char() -> U32:
  H.hex_u32("FFFD", {==})

# U+FFFD REPLACEMENT CHARACTER, as a one-character string.

def replacement_char_string() -> String:
  code_point_to_string(replacement_char())

# Valid sequences
# ---------------






# Maximal subparts
# ----------------

# `subpart` cannot be extended by `next`, the byte after it, if any.

def maximal_subpart.longest(subpart: List<&2, U32>, next: Maybe<&2, U32>) -> Type:
  match next:
    case None{}:
      Unit
    case Some{b}:
      {UTF8.begins_valid_sequence(List.append(&2, U32, subpart, [b])) == False{} : Bool}

# The maximal subpart when the first byte begins a valid sequence:
# `subpart` is the longest prefix of `b1 <> more` that begins a valid
# sequence.  (Unicode's "initial subsequence of a well-formed code unit
# sequence".)
#
# It suffices that adding the next byte does not begin a valid sequence:
# by `utf8_begins_valid_sequence`, every prefix of a sequence that begins
# a valid sequence also begins one, so no longer prefix can either.
#
# `first` makes `subpart` non-empty: `[b1]` begins a valid sequence, so
# `[]` is never the longest.

def maximal_subpart.sequence_prefix(+b1: U32, +more: List<&2, U32>,
  -first: {UTF8.begins_valid_sequence([b1]) == True{} : Bool},
  +subpart: List<&2, U32>) -> Type:
  is_prefix(subpart, b1 <> more) &
  {UTF8.begins_valid_sequence(subpart) == True{} : Bool} &
  maximal_subpart.longest(subpart, next_byte_after(b1 <> more, subpart))

# The maximal subpart when the first byte begins no valid sequence:
# `subpart` is that byte alone.  (Unicode's "subsequence of length one".)
# By `utf8_begins_valid_sequence`, no longer prefix begins a valid
# sequence either.

def maximal_subpart.single_byte(+b1: U32, +more: List<&2, U32>,
  -first: {UTF8.begins_valid_sequence([b1]) == False{} : Bool},
  +subpart: List<&2, U32>) -> Type:
  {subpart == [b1] : List<&2, U32>}

def maximal_subpart.if(+b1: U32, +more: List<&2, U32>, begins: Bool,
  -checked: {UTF8.begins_valid_sequence([b1]) == begins : Bool},
  +subpart: List<&2, U32>) -> Type:
  match begins:
    case True{}:
      maximal_subpart.sequence_prefix(b1, more, checked, subpart)
    case False{}:
      maximal_subpart.single_byte(b1, more, checked, subpart)

# `subpart` is the maximal subpart at the front of the non-empty bytes
# `b1 <> more`, as the Unicode Standard defines it (§3.9): the longest
# prefix that begins a valid sequence, or else the first byte alone.
# Meant for bytes that do not begin with a valid sequence.

def maximal_subpart(+b1: U32, +more: List<&2, U32>,
  +subpart: List<&2, U32>) -> Type:
  maximal_subpart.if(b1, more, UTF8.begins_valid_sequence([b1]), {==}, subpart)

# A non-empty buffer that does not begin with a valid sequence has a
# maximal subpart.

law maximal_subpart_exists:
  for +b1: U32
  for +more: List<&2, U32>
  for invalid: {next_scalar(b1 <> more) == None{} : Maybe<&1, U32 & List<&2, U32>>}
  Exists(List<&2, U32>, subpart => maximal_subpart(b1, more, subpart))

# A buffer has only one maximal subpart.

law maximal_subpart_unique:
  for +b1: U32
  for +more: List<&2, U32>
  for +s1: List<&2, U32>
  for +s2: List<&2, U32>
  for p1: maximal_subpart(b1, more, s1)
  for p2: maximal_subpart(b1, more, s2)
  {s1 == s2 : List<&2, U32>}

# Decoding the first code point of a complete buffer
# --------------------------------------------------
#
# The buffer is complete: nothing more will follow it, so a sequence
# left unfinished at its end is not valid and is replaced.

# The bytes do not begin with a valid sequence: decoding gives U+FFFD
# and the bytes after the maximal subpart.

def decodes_first.replaced(+b1: U32, +more: List<&2, U32>,
  result: Maybe<&1, U32 & List<&2, U32>>) -> Type:
  Exists(List<&2, U32>, subpart => Exists(List<&2, U32>, rest =>
    maximal_subpart(b1, more, subpart) &
    {List.append(&2, U32, subpart, rest) == b1 <> more : List<&2, U32>} &
    {result == Some{(replacement_char(), rest)} : Maybe<&1, U32 & List<&2, U32>>}))

# `found` is the scalar of a valid sequence at the front of the bytes,
# and the bytes after it, if they begin with one.

def decodes_first.found(+b1: U32, +more: List<&2, U32>,
  found: Maybe<&1, U32 & List<&2, U32>>,
  result: Maybe<&1, U32 & List<&2, U32>>) -> Type:
  match found:
    case Some{scalar_rest}:
      {result == Some{scalar_rest} : Maybe<&1, U32 & List<&2, U32>>}
    case None{}:
      decodes_first.replaced(b1, more, result)

# Decoding the first code point of the complete buffer `bytes` gives
# `result`: None if `bytes` is empty, otherwise the code point and the
# bytes that follow it.

def decodes_first(bytes: List<&2, U32>,
  result: Maybe<&1, U32 & List<&2, U32>>) -> Type:
  match bytes:
    case Nil{}:
      {result == None{} : Maybe<&1, U32 & List<&2, U32>>}
    case +b1 <> +more:
      decodes_first.found(b1, more, next_scalar(b1 <> more), result)

# Now we add some checks for our definition.

# Now we check that for any buffer, decodes_first implies that a
# result exists. (That is, we haven't created a definition for which
# there is some buffer that no `result` value at all satisfies the
# definition.)  The result itself can be None or Some, we just require
# that there is one.

law decodes_first_exists:
  for +bytes: List<&2, U32>
  Exists(Maybe<&1, U32 & List<&2, U32>>, result => decodes_first(bytes, result))

# Check for uniqueness: for any buffer, there is only one `result`
# value which satisfies our definition.

law decodes_first_unique:
  for +bytes: List<&2, U32>
  for r1: Maybe<&1, U32 & List<&2, U32>>
  for r2: Maybe<&1, U32 & List<&2, U32>>
  for d1: decodes_first(bytes, r1)
  for d2: decodes_first(bytes, r2)
  {r1 == r2 : Maybe<&1, U32 & List<&2, U32>>}

# Check that decoding the first code point of an empty buffer gives
# None.  This is trivial given our decodes_first def above, but we
# include for completeness.

law decodes_first_empty:
  for result: Maybe<&1, U32 & List<&2, U32>>
  for decoded: decodes_first([], result)
  {result == None{} : Maybe<&1, U32 & List<&2, U32>>}

# Check that decoding the first code point of any non-empty buffer
# always gives Some.

law decodes_first_nonempty:
  for +b1: U32
  for +more: List<&2, U32>
  for result: Maybe<&1, U32 & List<&2, U32>>
  for decoded: decodes_first(b1 <> more, result)
  {Maybe.is_some(&1, U32 & List<&2, U32>, result) == True{} : Bool}

# Decoding a complete buffer
# --------------------------

# Decoding the complete buffer `bytes` gives the string `text`: empty if
# there is nothing to decode, otherwise the code point that
# `decodes_first` gives followed by the text from decoding the bytes
# after it.
#
# The recursion is on `text`, which shrinks at each step, so `text`
# comes first in `decodes.go`.

def decodes.go(text: String, bytes: List<&2, U32>) -> Type:
  match text:
    case SNil{}:
      decodes_first(bytes, None{})
    case SCon{Chr{cp}, more}:
      Exists(List<&2, U32>, rest =>
        decodes_first(bytes, Some{(cp, rest)}) & decodes.go(more, rest))

def decodes(bytes: List<&2, U32>, text: String) -> Type:
  decodes.go(text, bytes)

# Every buffer decodes to some text.

law decodes_exists:
  for +bytes: List<&2, U32>
  Exists(String, text => decodes(bytes, text))

# A buffer decodes to only one text.

law decodes_unique:
  for +bytes: List<&2, U32>
  for +t1: String
  for +t2: String
  for d1: decodes(bytes, t1)
  for d2: decodes(bytes, t2)
  {t1 == t2 : String}

# Bytes in hex: 65 = 0x41 "A", 66 = 0x42 "B", 72 = 0x48 "H",
# 128 = 0x80, 169 = 0xA9, 192 = 0xC0, 194 = 0xC2, 255 = 0xFF.

law decodes_examples:
  # Nothing to decode.
  decodes([], "") &
  # One-byte sequences.
  decodes([65, 66], "AB") &
  # A two-byte sequence: C2 A9 is U+00A9.
  decodes([194, 169], code_point_to_string(169)) &
  # A lead byte followed by a byte that cannot continue it: the lead
  # byte is replaced, and "A" decodes afresh.
  decodes([194, 65], replacement_char_string() ++ "A") &
  # C0 begins no valid sequence (it would be overlong), and neither does
  # a lone continuation byte: each is replaced separately.
  decodes([192, 128], replacement_char_string() ++ replacement_char_string()) &
  # A sequence left unfinished at the end of the buffer is replaced.
  decodes([194], replacement_char_string()) &
  # The second C2 cannot continue the first; it then begins C2 A9.
  decodes([194, 194, 169], replacement_char_string() ++ code_point_to_string(169)) &
  # Valid sequences around a byte that never appears in UTF-8.
  decodes([72, 194, 169, 255],
    "H" ++ code_point_to_string(169) ++ replacement_char_string())

# Running the decoder
# -------------------

# Every value in `bytes` is a byte, 0..255.

def all_bytes(bytes: List<&2, U32>) -> Bool:
  List.all(~&2, ~U32, ~(b => U32.is_le(b, 255)), bytes)

# The decoder state and the text so far, or None if `UTF8.decode_buffer`
# returned None for some buffer (which it does when the buffer holds a
# value above 255).  No buffers are given to the decoder after that.

def Fed() -> Type:
  Maybe<&1, UTF8.DecodeState() & String>

def feed.prepend(text: String, result: Fed()) -> Fed():
  match result:
    case None{}:
      None{}
    case Some{(state, more)}:
      Some{(state, text ++ more)}

def feed.then(result: Fed(), rest: UTF8.DecodeState() -> Fed()) -> Fed():
  match result:
    case None{}:
      None{}
    case Some{(state, text)}:
      feed.prepend(text, rest(state))

# Give `buffers` to `UTF8.decode_buffer` in order, starting from `state`,
# and join the text that the calls return.

def feed(buffers: List<&2, List<&2, U32>>, state: UTF8.DecodeState()) -> Fed():
  match buffers:
    case Nil{}:
      Some{(state, "")}
    case buffer <> rest:
      feed.then(UTF8.decode_buffer(state, buffer), s => feed(rest, s))

# The text returned for `buffers`, without and with `UTF8.decode_done`.

def decoded_so_far.text(result: Fed()) -> Maybe<&2, String>:
  match result:
    case None{}:
      None{}
    case Some{(state, text)}:
      Some{text}

def decoded_so_far(buffers: List<&2, List<&2, U32>>) -> Maybe<&2, String>:
  decoded_so_far.text(feed(buffers, UTF8.decode_start()))

def decoded.text(result: Fed()) -> Maybe<&2, String>:
  match result:
    case None{}:
      None{}
    case Some{(state, text)}:
      Some{text ++ UTF8.decode_done(state)}

def decoded(buffers: List<&2, List<&2, U32>>) -> Maybe<&2, String>:
  decoded.text(feed(buffers, UTF8.decode_start()))

# Running the decoder satisfies `decodes`
# ---------------------------------------

# What running the decoder on `bytes` should give: None if a value is
# above 255, otherwise text that `bytes` decodes to.

def decodes_result.if(ok: Bool, +bytes: List<&2, U32>, result: Maybe<&2, String>) -> Type:
  match ok:
    case False{}:
      {result == None{} : Maybe<&2, String>}
    case True{}:
      Exists(String, text => {result == Some{text} : Maybe<&2, String>} & decodes(bytes, text))

def decodes_result(+bytes: List<&2, U32>, result: Maybe<&2, String>) -> Type:
  decodes_result.if(all_bytes(bytes), bytes, result)

# However the input is split into buffers, giving them in order to
# `UTF8.decode_buffer` and then calling `UTF8.decode_done` gives what
# their concatenation decodes to.

law utf8_decodes:
  for +buffers: List<&2, List<&2, U32>>
  decodes_result(List.concat(&2, U32, buffers), decoded(buffers))

# `prefix` is a prefix of `text`.

def is_text_prefix(prefix: String, text: String) -> Type:
  Exists(String, more => {prefix ++ more == text : String})

# After each buffer, the decoder has returned the longest text that
# every continuation of the input agrees on.  This has two halves.

# Safe: whatever bytes follow, the whole input decodes to text that
# begins with the text returned so far.  Later bytes cannot change
# anything already returned.

law utf8_decode_buffer_safe:
  for +buffers: List<&2, List<&2, U32>>
  for +text: String
  for so_far: {decoded_so_far(buffers) == Some{text} : Maybe<&2, String>}
  for +rest: List<&2, U32>
  for +full: String
  for decoded: decodes(List.append(&2, U32, List.concat(&2, U32, buffers), rest), full)
  is_text_prefix(text, full)

# Prompt: nothing is held back.  No longer text is safe: for any code
# point `c`, some bytes could follow for which the whole input does not
# decode to text beginning with the text returned so far followed by
# `c`.

law utf8_decode_buffer_prompt:
  for +buffers: List<&2, List<&2, U32>>
  for +text: String
  for so_far: {decoded_so_far(buffers) == Some{text} : Maybe<&2, String>}
  for +c: U32
  Exists(List<&2, U32>, rest =>
    {all_bytes(rest) == True{} : Bool} &
    Exists(String, full =>
      decodes(List.append(&2, U32, List.concat(&2, U32, buffers), rest), full) &
      (is_text_prefix(text ++ code_point_to_string(c), full) -> Empty)))
