import Base

# Encoding capacity is separate from shortest-form validity.
def can_encode_as_one_byte(+cp: U32) -> Bool:
  U32.is_le(cp, 127)

def can_encode_as_two_bytes(+cp: U32) -> Bool:
  U32.is_le(cp, 2047)

def can_encode_as_three_bytes(+cp: U32) -> Bool:
  U32.is_le(cp, 65535)

# The kinds of UTF-8 byte, by their high bits. Each test is one AND and
# one comparison. The mask keeps every bit above the payload, so a value
# above 255 never matches. The mask comes first so that proofs can
# compute the AND without knowing every bit of `b`.

# 10xxxxxx: mask 0xFFFFFFC0, bits 0x80.
def is_continuation_byte(+b: U32) -> Bool:
  U32.is_eq(U32.and(4294967232, b), 128)

# 110xxxxx: mask 0xFFFFFFE0, bits 0xC0.
def is_two_byte_lead(+b: U32) -> Bool:
  U32.is_eq(U32.and(4294967264, b), 192)

# 1110xxxx: mask 0xFFFFFFF0, bits 0xE0.
def is_three_byte_lead(+b: U32) -> Bool:
  U32.is_eq(U32.and(4294967280, b), 224)

# 11110xxx: mask 0xFFFFFFF8, bits 0xF0.
def is_four_byte_lead(+b: U32) -> Bool:
  U32.is_eq(U32.and(4294967288, b), 240)

def has_two_byte_shape(b1: U32, b2: U32) -> Bool:
  is_two_byte_lead(b1) && is_continuation_byte(b2)

def has_three_byte_shape(b1: U32, b2: U32, b3: U32) -> Bool:
  is_three_byte_lead(b1) && is_continuation_byte(b2) &&
  is_continuation_byte(b3)

def has_four_byte_shape(b1: U32, b2: U32, b3: U32, b4: U32) -> Bool:
  is_four_byte_lead(b1) && is_continuation_byte(b2) &&
  is_continuation_byte(b3) && is_continuation_byte(b4)

# Shift in the six payload bits of a continuation byte.
def append_continuation(+acc: U32, +b: U32) -> U32:
  (U32.shln(acc, 6n) + U32.and(b, 63) : U32)

# Decode only pairs with the two-byte shape, including overlong encodings.
def decode_two_bytes(+b1: U32, +b2: U32,
  -valid_shape: {has_two_byte_shape(b1, b2) == True{} : Bool}) -> U32:
  append_continuation(U32.and(b1, 31), b2)

# Decode only triples with the three-byte shape, including invalid encodings.
def decode_three_bytes(+b1: U32, +b2: U32, +b3: U32,
  -valid_shape: {has_three_byte_shape(b1, b2, b3) == True{} : Bool}) -> U32:
  append_continuation(append_continuation(U32.and(b1, 15), b2), b3)

# Decode only sequences with the four-byte shape, including invalid encodings.
def decode_four_bytes(+b1: U32, +b2: U32, +b3: U32, +b4: U32,
  -valid_shape: {has_four_byte_shape(b1, b2, b3, b4) == True{} : Bool}) -> U32:
  append_continuation(append_continuation(append_continuation(U32.and(b1, 7), b2), b3), b4)

# Unicode scalars: at most U+10FFFF, excluding the surrogates
# U+D800..U+DFFF.
def is_surrogate(+cp: U32) -> Bool:
  U32.is_ge(cp, 55296) && U32.is_le(cp, 57343)

def is_scalar(+cp: U32) -> Bool:
  U32.is_le(cp, 1114111) && Bool.not(is_surrogate(cp))

# Streaming decoder
# -----------------
#
# A simple decoder that reads one byte at a time.  Its state is the
# pending bytes of a sequence that has begun but not yet finished.

def DecodeState() -> Type:
  List<&2, U32>

def decode_start_state() -> DecodeState():
  Nil{}

def code_point_to_string(cp: U32) -> String:
  SCon{Chr{cp}, SNil{}}

# U+FFFD REPLACEMENT CHARACTER, as a one-character string.
def replacement_char_string() -> String:
  code_point_to_string(65533)

# Complete sequences
# ------------------
#
# Each `*_scalar` function returns the scalar that its bytes encode when
# they are exactly one valid sequence, otherwise None.  The code point
# is decoded once, after the shape test, and then checked: a sequence
# is valid when its code point has no shorter encoding (is not
# overlong) and is a Unicode scalar.
#
# As of Bend 2.0.40 there is no `if` statement: the `.if` helpers match
# on a Bool, with evidence of its value where the branch needs it.

# `Some{cp}` when `valid`, otherwise None.
def scalar_if(+cp: U32, valid: Bool) -> Maybe<&2, U32>:
  match valid:
    case False{}:
      None{}
    case True{}:
      Some{cp}

# A byte 00..7F is a one-byte sequence, encoding itself.
def one_byte_scalar(+b1: U32) -> Maybe<&2, U32>:
  scalar_if(b1, can_encode_as_one_byte(b1))

def two_byte_scalar.of(+cp: U32) -> Maybe<&2, U32>:
  scalar_if(cp, Bool.not(can_encode_as_one_byte(cp)))

def two_byte_scalar.if(+b1: U32, +b2: U32, shape: Bool,
  -checked: {has_two_byte_shape(b1, b2) == shape : Bool}) -> Maybe<&2, U32>:
  match shape:
    case False{}:
      None{}
    case True{}:
      two_byte_scalar.of(decode_two_bytes(b1, b2, checked))

def two_byte_scalar(+b1: U32, +b2: U32) -> Maybe<&2, U32>:
  two_byte_scalar.if(b1, b2, has_two_byte_shape(b1, b2), {==})

def three_byte_scalar.of(+cp: U32) -> Maybe<&2, U32>:
  scalar_if(cp, Bool.not(can_encode_as_two_bytes(cp)) && is_scalar(cp))

def three_byte_scalar.if(+b1: U32, +b2: U32, +b3: U32, shape: Bool,
  -checked: {has_three_byte_shape(b1, b2, b3) == shape : Bool}) -> Maybe<&2, U32>:
  match shape:
    case False{}:
      None{}
    case True{}:
      three_byte_scalar.of(decode_three_bytes(b1, b2, b3, checked))

def three_byte_scalar(+b1: U32, +b2: U32, +b3: U32) -> Maybe<&2, U32>:
  three_byte_scalar.if(b1, b2, b3, has_three_byte_shape(b1, b2, b3), {==})

def four_byte_scalar.of(+cp: U32) -> Maybe<&2, U32>:
  scalar_if(cp, Bool.not(can_encode_as_three_bytes(cp)) && is_scalar(cp))

def four_byte_scalar.if(+b1: U32, +b2: U32, +b3: U32, +b4: U32, shape: Bool,
  -checked: {has_four_byte_shape(b1, b2, b3, b4) == shape : Bool}) -> Maybe<&2, U32>:
  match shape:
    case False{}:
      None{}
    case True{}:
      four_byte_scalar.of(decode_four_bytes(b1, b2, b3, b4, checked))

def four_byte_scalar(+b1: U32, +b2: U32, +b3: U32, +b4: U32) -> Maybe<&2, U32>:
  four_byte_scalar.if(b1, b2, b3, b4, has_four_byte_shape(b1, b2, b3, b4), {==})

# The scalar that `seq` encodes when `seq` is exactly one valid sequence,
# otherwise None.
def sequence_scalar(seq: List<&2, U32>) -> Maybe<&2, U32>:
  match seq:
    case +b1 <> Nil{}:
      one_byte_scalar(b1)
    case +b1 <> +b2 <> Nil{}:
      two_byte_scalar(b1, b2)
    case +b1 <> +b2 <> +b3 <> Nil{}:
      three_byte_scalar(b1, b2, b3)
    case +b1 <> +b2 <> +b3 <> +b4 <> Nil{}:
      four_byte_scalar(b1, b2, b3, b4)
    case _:
      None{}

# Incomplete sequences
# --------------------
#
# The well-formed sequences, from the Unicode Standard's Table 3-7:
#
#   00..7F
#   C2..DF  80..BF
#   E0      A0..BF  80..BF
#   E1..EC  80..BF  80..BF
#   ED      80..9F  80..BF
#   EE..EF  80..BF  80..BF
#   F0      90..BF  80..BF  80..BF
#   F1..F3  80..BF  80..BF  80..BF
#   F4      80..8F  80..BF  80..BF
#
# (C0, C1 and the narrower ranges after E0 and F0 would be overlong;
# the range after ED excludes the surrogates; F4's range and F5..F7
# exclude values above U+10FFFF.)  Only the second byte's range depends
# on the lead byte.  Bytes after the second need only be 80..BF.

# Bits 5 and 4 of a continuation byte, which say which quarter of
# 80..BF it lies in: 0x00 for 80..8F, 0x10 for 90..9F, 0x20 for A0..AF
# and 0x30 for B0..BF.  (Masking keeps the proofs simple: unlike a
# comparison, the AND doesn't depend on the low bits.)
def continuation_quarter(+b: U32) -> U32:
  U32.and(48, b)

# Whether `b1` begins a sequence of two to four bytes: C2..DF, E0..EF
# or F0..F4.
def is_multibyte_lead(+b1: U32) -> Bool:
  (is_two_byte_lead(b1) && U32.is_ge(b1, 194)) || is_three_byte_lead(b1) ||
  (is_four_byte_lead(b1) && U32.is_le(b1, 244))

# For a three-byte lead byte `b1` and continuation byte `b2`: whether
# `b2` is in the second byte's range, A0..BF after E0 and 80..9F after
# ED.
def is_three_byte_second(+b1: U32, +b2: U32) -> Bool:
  +quarter = continuation_quarter(b2)
  (Bool.not(U32.is_eq(b1, 224)) || U32.is_ge(quarter, 32)) &&
  (Bool.not(U32.is_eq(b1, 237)) || U32.is_le(quarter, 16))

# For a four-byte lead byte `b1` and continuation byte `b2`: whether
# `b1` is F0..F4 and `b2` in the second byte's range, 90..BF after F0
# and 80..8F after F4.
def is_four_byte_second(+b1: U32, +b2: U32) -> Bool:
  +quarter = continuation_quarter(b2)
  U32.is_le(b1, 244) &&
  (Bool.not(U32.is_eq(b1, 240)) || U32.is_ge(quarter, 16)) &&
  (Bool.not(U32.is_eq(b1, 244)) || U32.is_eq(quarter, 0))

# Whether `seq` is incomplete: not itself a valid sequence, but the
# start of one, so that some more bytes would make it a valid sequence.
def is_incomplete_sequence(seq: List<&2, U32>) -> Bool:
  match seq:
    case +b1 <> Nil{}:
      is_multibyte_lead(b1)
    case +b1 <> +b2 <> Nil{}:
      is_continuation_byte(b2) &&
      ((is_three_byte_lead(b1) && is_three_byte_second(b1, b2)) ||
       (is_four_byte_lead(b1) && is_four_byte_second(b1, b2)))
    case +b1 <> +b2 <> +b3 <> Nil{}:
      is_four_byte_lead(b1) && is_continuation_byte(b2) &&
      is_continuation_byte(b3) && is_four_byte_second(b1, b2)
    case _:
      False{}

# Decoding a buffer
# -----------------

# The text now resolved, and the new pending bytes.
def decode_buffer.Step() -> Type:
  String & List<&2, U32>

def decode_buffer.prepend(text: String, step: decode_buffer.Step()) ->
  decode_buffer.Step():
  (more, pending) = step
  (text ++ more, pending)

# Keep an incomplete `seq` pending, or else do `otherwise`.
def decode_buffer.keep(+seq: List<&2, U32>, incomplete: Bool,
  otherwise: Unit -> decode_buffer.Step()) -> decode_buffer.Step():
  match incomplete:
    case True{}:
      ("", seq)
    case False{}:
      otherwise(Unit{})

# `seq` is the pending bytes followed by the new byte, and `scalar` is
# `sequence_scalar(seq)`.  Emit a complete sequence, keep an incomplete
# one, or else do `otherwise`.  The incompleteness test runs only when
# `seq` isn't complete.
def decode_buffer.advance(+seq: List<&2, U32>, scalar: Maybe<&2, U32>,
  otherwise: Unit -> decode_buffer.Step()) -> decode_buffer.Step():
  match scalar:
    case Some{cp}:
      (code_point_to_string(cp), Nil{})
    case None{}:
      decode_buffer.keep(seq, is_incomplete_sequence(seq), otherwise)

# A byte with nothing pending; on its own it is either a sequence, the
# start of one, or replaced.
def decode_buffer.start(+b: U32) -> decode_buffer.Step():
  +seq = {[b] : List<&2, U32>}
  decode_buffer.advance(seq, sequence_scalar(seq),
    u => (replacement_char_string(), Nil{}))

# A byte after pending bytes.  If it cannot continue them, the pending
# bytes are replaced and the byte starts afresh.
def decode_buffer.extend(pending: List<&2, U32>, +b: U32) -> decode_buffer.Step():
  +seq = List.append(&2, U32, pending, [b])
  decode_buffer.advance(seq, sequence_scalar(seq),
    u => decode_buffer.prepend(replacement_char_string(), decode_buffer.start(b)))

def decode_buffer.step(pending: List<&2, U32>, +b: U32) -> decode_buffer.Step():
  match pending:
    case Nil{}:
      decode_buffer.start(b)
    case p <> ps:
      decode_buffer.extend(p <> ps, b)

# The byte loop, a tail call per byte.  `stepped` is the previous
# step's text and pending bytes, and `out` is the text before that,
# reversed so that each step adds to it in time proportional to its own
# text.  The final text is `out` reversed, then `stepped`'s text.
def decode_buffer.bytes(bytes: List<&2, U32>, stepped: decode_buffer.Step(),
  out: String) -> decode_buffer.Step():
  match bytes:
    case Nil{}:
      (text, pending) = stepped
      (String.reverse.go(out, text), pending)
    case b <> rest:
      (text, pending) = stepped
      decode_buffer.bytes(rest, decode_buffer.step(pending, b),
        String.reverse.go(text, out))

def decode_buffer.all_bytes(bytes: List<&2, U32>) -> Bool:
  List.all(~&2, ~U32, ~(b => U32.is_le(b, 255)), bytes)

def decode_buffer.result(step: decode_buffer.Step()) -> DecodeState() & String:
  (text, pending) = step
  (pending, text)

# Decode the next buffer, whose values must all be bytes.
def decode_buffer(state: DecodeState(), +buffer: List<&2, U32>,
  -valid: {decode_buffer.all_bytes(buffer) == True{} : Bool}) ->
  DecodeState() & String:
  decode_buffer.result(decode_buffer.bytes(buffer, ("", state), ""))

# An unfinished sequence at the end of the input is replaced.
def decode_done(state: DecodeState()) -> String:
  match state:
    case Nil{}:
      ""
    case p <> ps:
      replacement_char_string()
