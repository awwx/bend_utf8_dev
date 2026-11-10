import Base
import ./binary_mask.bend as B

# Encoding capacity is separate from shortest-form validity.
def can_encode_as_one_byte(+cp: U32) -> Bool:
  U32.is_le(cp, 127)

def can_encode_as_two_bytes(+cp: U32) -> Bool:
  U32.is_le(cp, 2047)

def can_encode_as_three_bytes(+cp: U32) -> Bool:
  U32.is_le(cp, 65535)

def can_encode_as_four_bytes(+cp: U32) -> Bool:
  U32.is_le(cp, 2097151)

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

# Every byte with the one-byte shape is a valid encoding.
def valid_one_byte(+byte: U32) -> Bool:
  has_one_byte_shape(byte)

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

# Deliberately permits overlong encodings and surrogate code points.
def encode_as_three_bytes(+cp: U32,
  -valid: {can_encode_as_three_bytes(cp) == True{} : Bool}) -> U32 & U32 & U32:
  ((224 + U32.shrn(cp, 12n) : U32),
   (128 + U32.and(U32.shrn(cp, 6n), 63) : U32),
   (128 + U32.and(cp, 63) : U32))

# Deliberately permits overlong encodings and values above U+10FFFF.
def encode_as_four_bytes(+cp: U32,
  -valid: {can_encode_as_four_bytes(cp) == True{} : Bool}) -> U32 & U32 & U32 & U32:
  ((240 + U32.shrn(cp, 18n) : U32),
   (128 + U32.and(U32.shrn(cp, 12n), 63) : U32),
   (128 + U32.and(U32.shrn(cp, 6n), 63) : U32),
   (128 + U32.and(cp, 63) : U32))

def has_three_byte_shape(b1: U32, b2: U32, b3: U32) -> Bool:
  B.byte_mask("1110xxxx", b1, {==}) && B.byte_mask("10xxxxxx", b2, {==}) &&
  B.byte_mask("10xxxxxx", b3, {==})

def has_four_byte_shape(b1: U32, b2: U32, b3: U32, b4: U32) -> Bool:
  B.byte_mask("11110xxx", b1, {==}) && B.byte_mask("10xxxxxx", b2, {==}) &&
  B.byte_mask("10xxxxxx", b3, {==}) && B.byte_mask("10xxxxxx", b4, {==})

# Shift in the six payload bits of a continuation byte.
def append_continuation(+acc: U32, +b: U32) -> U32:
  (U32.shln(acc, 6n) + U32.and(b, 63) : U32)

# Decode only triples with the three-byte shape, including invalid encodings.
def decode_three_bytes(+b1: U32, +b2: U32, +b3: U32,
  -valid_shape: {has_three_byte_shape(b1, b2, b3) == True{} : Bool}) -> U32:
  append_continuation(append_continuation(U32.and(b1, 15), b2), b3)

# Decode only sequences with the four-byte shape, including invalid encodings.
def decode_four_bytes(+b1: U32, +b2: U32, +b3: U32, +b4: U32,
  -valid_shape: {has_four_byte_shape(b1, b2, b3, b4) == True{} : Bool}) -> U32:
  append_continuation(append_continuation(append_continuation(U32.and(b1, 7), b2), b3), b4)

# The decoded code point also has a one- or two-byte representation.
# Two-byte capacity includes everything that fits in one byte.
def overlong_three_bytes(+b1: U32, +b2: U32, +b3: U32,
  -valid_shape: {has_three_byte_shape(b1, b2, b3) == True{} : Bool}) -> Bool:
  can_encode_as_two_bytes(decode_three_bytes(b1, b2, b3, valid_shape))

# The decoded code point also has a representation of three bytes or fewer.
# Three-byte capacity includes everything that fits in fewer bytes.
def overlong_four_bytes(+b1: U32, +b2: U32, +b3: U32, +b4: U32,
  -valid_shape: {has_four_byte_shape(b1, b2, b3, b4) == True{} : Bool}) -> Bool:
  can_encode_as_three_bytes(decode_four_bytes(b1, b2, b3, b4, valid_shape))

# Unicode scalars: at most U+10FFFF, excluding the surrogates
# U+D800..U+DFFF.
def is_surrogate(+cp: U32) -> Bool:
  U32.is_ge(cp, 55296) && U32.is_le(cp, 57343)

def is_scalar(+cp: U32) -> Bool:
  U32.is_le(cp, 1114111) && Bool.not(is_surrogate(cp))

def valid_three_bytes.if(+b1: U32, +b2: U32, +b3: U32, shape: Bool,
  -checked: {has_three_byte_shape(b1, b2, b3) == shape : Bool}) -> Bool:
  match shape:
    case False{}: False{}
    case True{}:
      Bool.not(overlong_three_bytes(b1, b2, b3, checked)) &&
      is_scalar(decode_three_bytes(b1, b2, b3, checked))

def valid_three_bytes(+b1: U32, +b2: U32, +b3: U32) -> Bool:
  valid_three_bytes.if(b1, b2, b3, has_three_byte_shape(b1, b2, b3), {==})

def valid_four_bytes.if(+b1: U32, +b2: U32, +b3: U32, +b4: U32, shape: Bool,
  -checked: {has_four_byte_shape(b1, b2, b3, b4) == shape : Bool}) -> Bool:
  match shape:
    case False{}: False{}
    case True{}:
      Bool.not(overlong_four_bytes(b1, b2, b3, b4, checked)) &&
      is_scalar(decode_four_bytes(b1, b2, b3, b4, checked))

def valid_four_bytes(+b1: U32, +b2: U32, +b3: U32, +b4: U32) -> Bool:
  valid_four_bytes.if(b1, b2, b3, b4, has_four_byte_shape(b1, b2, b3, b4), {==})

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

# `False == True` is impossible.
def false_true.motive(b: Bool) -> Type:
  match b:
    case False{}:
      Unit
    case True{}:
      Empty

def false_true(e: {False{} == True{} : Bool}) -> Empty:
  %e : false_true.motive(_)
  Unit{}

# A valid two-byte sequence has the two-byte shape, which decoding needs.
def valid_two_bytes.has_shape.if(+b1: U32, +b2: U32, shape: Bool,
  checked: {has_two_byte_shape(b1, b2) == shape : Bool},
  valid: {valid_two_bytes.if(b1, b2, shape, checked) == True{} : Bool}) ->
  {has_two_byte_shape(b1, b2) == True{} : Bool}:
  match shape:
    case False{}:
      Empty.absurd({has_two_byte_shape(b1, b2) == True{} : Bool}, false_true(valid))
    case True{}:
      checked

def valid_two_bytes.has_shape(+b1: U32, +b2: U32,
  valid: {valid_two_bytes(b1, b2) == True{} : Bool}) ->
  {has_two_byte_shape(b1, b2) == True{} : Bool}:
  valid_two_bytes.has_shape.if(b1, b2, has_two_byte_shape(b1, b2), {==}, valid)

# The scalar that a valid one-byte sequence encodes, or None.
def one_byte_scalar.if(+byte: U32, valid: Bool,
  -checked: {valid_one_byte(byte) == valid : Bool}) -> Maybe<&2, U32>:
  match valid:
    case False{}:
      None{}
    case True{}:
      Some{decode_one_byte(byte, checked)}

def one_byte_scalar(+byte: U32) -> Maybe<&2, U32>:
  one_byte_scalar.if(byte, valid_one_byte(byte), {==})

# The scalar that a valid two-byte sequence encodes, or None.
def two_byte_scalar.if(+b1: U32, +b2: U32, valid: Bool,
  -checked: {valid_two_bytes(b1, b2) == valid : Bool}) -> Maybe<&2, U32>:
  match valid:
    case False{}:
      None{}
    case True{}:
      Some{decode_two_bytes(b1, b2, valid_two_bytes.has_shape(b1, b2, checked))}

def two_byte_scalar(+b1: U32, +b2: U32) -> Maybe<&2, U32>:
  two_byte_scalar.if(b1, b2, valid_two_bytes(b1, b2), {==})

# A valid three-byte sequence has the three-byte shape, which decoding needs.
def valid_three_bytes.has_shape.if(+b1: U32, +b2: U32, +b3: U32, shape: Bool,
  checked: {has_three_byte_shape(b1, b2, b3) == shape : Bool},
  valid: {valid_three_bytes.if(b1, b2, b3, shape, checked) == True{} : Bool}) ->
  {has_three_byte_shape(b1, b2, b3) == True{} : Bool}:
  match shape:
    case False{}:
      Empty.absurd({has_three_byte_shape(b1, b2, b3) == True{} : Bool}, false_true(valid))
    case True{}:
      checked

def valid_three_bytes.has_shape(+b1: U32, +b2: U32, +b3: U32,
  valid: {valid_three_bytes(b1, b2, b3) == True{} : Bool}) ->
  {has_three_byte_shape(b1, b2, b3) == True{} : Bool}:
  valid_three_bytes.has_shape.if(b1, b2, b3, has_three_byte_shape(b1, b2, b3), {==}, valid)

# A valid four-byte sequence has the four-byte shape, which decoding needs.
def valid_four_bytes.has_shape.if(+b1: U32, +b2: U32, +b3: U32, +b4: U32, shape: Bool,
  checked: {has_four_byte_shape(b1, b2, b3, b4) == shape : Bool},
  valid: {valid_four_bytes.if(b1, b2, b3, b4, shape, checked) == True{} : Bool}) ->
  {has_four_byte_shape(b1, b2, b3, b4) == True{} : Bool}:
  match shape:
    case False{}:
      Empty.absurd({has_four_byte_shape(b1, b2, b3, b4) == True{} : Bool}, false_true(valid))
    case True{}:
      checked

def valid_four_bytes.has_shape(+b1: U32, +b2: U32, +b3: U32, +b4: U32,
  valid: {valid_four_bytes(b1, b2, b3, b4) == True{} : Bool}) ->
  {has_four_byte_shape(b1, b2, b3, b4) == True{} : Bool}:
  valid_four_bytes.has_shape.if(b1, b2, b3, b4, has_four_byte_shape(b1, b2, b3, b4), {==}, valid)

# The scalar that a valid three-byte sequence encodes, or None.
def three_byte_scalar.if(+b1: U32, +b2: U32, +b3: U32, valid: Bool,
  -checked: {valid_three_bytes(b1, b2, b3) == valid : Bool}) -> Maybe<&2, U32>:
  match valid:
    case False{}:
      None{}
    case True{}:
      Some{decode_three_bytes(b1, b2, b3, valid_three_bytes.has_shape(b1, b2, b3, checked))}

def three_byte_scalar(+b1: U32, +b2: U32, +b3: U32) -> Maybe<&2, U32>:
  three_byte_scalar.if(b1, b2, b3, valid_three_bytes(b1, b2, b3), {==})

# The scalar that a valid four-byte sequence encodes, or None.
def four_byte_scalar.if(+b1: U32, +b2: U32, +b3: U32, +b4: U32, valid: Bool,
  -checked: {valid_four_bytes(b1, b2, b3, b4) == valid : Bool}) -> Maybe<&2, U32>:
  match valid:
    case False{}:
      None{}
    case True{}:
      Some{decode_four_bytes(b1, b2, b3, b4, valid_four_bytes.has_shape(b1, b2, b3, b4, checked))}

def four_byte_scalar(+b1: U32, +b2: U32, +b3: U32, +b4: U32) -> Maybe<&2, U32>:
  four_byte_scalar.if(b1, b2, b3, b4, valid_four_bytes(b1, b2, b3, b4), {==})

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

# Whether `seq` is a valid sequence prefix: one or more bytes that
# some bytes, possibly none, can follow to make a valid sequence.
#
# Validity depends on the final continuation bytes only through their
# shape, so 0x80 stands for them all.  The byte after a three- or
# four-byte lead byte also limits the code point, and only through its
# high bits.  Some lead bytes need that byte to be low (ED, F4) and some
# high (E0, F0), so testing both 0x80 and 0xBF covers every lead byte.
def is_valid_sequence_prefix(seq: List<&2, U32>) -> Bool:
  match seq:
    case Nil{}:
      False{}
    case +b1 <> Nil{}:
      valid_one_byte(b1) || valid_two_bytes(b1, 128) ||
      valid_three_bytes(b1, 128, 128) || valid_three_bytes(b1, 191, 128) ||
      valid_four_bytes(b1, 128, 128, 128) || valid_four_bytes(b1, 191, 128, 128)
    case +b1 <> +b2 <> Nil{}:
      valid_two_bytes(b1, b2) || valid_three_bytes(b1, b2, 128) ||
      valid_four_bytes(b1, b2, 128, 128)
    case +b1 <> +b2 <> +b3 <> Nil{}:
      valid_three_bytes(b1, b2, b3) || valid_four_bytes(b1, b2, b3, 128)
    case +b1 <> +b2 <> +b3 <> +b4 <> Nil{}:
      valid_four_bytes(b1, b2, b3, b4)
    case _:
      False{}

# The text now resolved, and the new pending bytes.
def decode_buffer.Step() -> Type:
  String & List<&2, U32>

def decode_buffer.prepend(text: String, step: decode_buffer.Step()) ->
  decode_buffer.Step():
  (more, pending) = step
  (text ++ more, pending)

# `seq` is the pending bytes followed by the new byte.  Emit a complete
# sequence, keep a sequence that can still complete, or else do
# `otherwise`.
def decode_buffer.advance(seq: List<&2, U32>, scalar: Maybe<&2, U32>,
  begins: Bool, otherwise: Unit -> decode_buffer.Step()) -> decode_buffer.Step():
  match scalar begins:
    case Some{cp} _:
      (code_point_to_string(cp), Nil{})
    case None{} True{}:
      ("", seq)
    case None{} False{}:
      otherwise(Unit{})

# A byte with nothing pending; on its own it is either a sequence, the
# start of one, or replaced.
def decode_buffer.start(+b: U32) -> decode_buffer.Step():
  +seq = {[b] : List<&2, U32>}
  decode_buffer.advance(seq, sequence_scalar(seq), is_valid_sequence_prefix(seq),
    u => (replacement_char_string(), Nil{}))

# A byte after pending bytes.  If it cannot continue them, the pending
# bytes are replaced and the byte starts afresh.
def decode_buffer.extend(pending: List<&2, U32>, +b: U32) -> decode_buffer.Step():
  +seq = List.append(&2, U32, pending, [b])
  decode_buffer.advance(seq, sequence_scalar(seq), is_valid_sequence_prefix(seq),
    u => decode_buffer.prepend(replacement_char_string(), decode_buffer.start(b)))

def decode_buffer.step(pending: List<&2, U32>, +b: U32) -> decode_buffer.Step():
  match pending:
    case Nil{}:
      decode_buffer.start(b)
    case p <> ps:
      decode_buffer.extend(p <> ps, b)

def decode_buffer.then(stepped: decode_buffer.Step(),
  rest: List<&2, U32> -> decode_buffer.Step()) -> decode_buffer.Step():
  (text, pending) = stepped
  decode_buffer.prepend(text, rest(pending))

def decode_buffer.bytes(bytes: List<&2, U32>, pending: List<&2, U32>) ->
  decode_buffer.Step():
  match bytes:
    case Nil{}:
      ("", pending)
    case +b <> rest:
      decode_buffer.then(decode_buffer.step(pending, b),
        p => decode_buffer.bytes(rest, p))

def decode_buffer.all_bytes(bytes: List<&2, U32>) -> Bool:
  List.all(~&2, ~U32, ~(b => U32.is_le(b, 255)), bytes)

def decode_buffer.result(step: decode_buffer.Step()) -> DecodeState() & String:
  (text, pending) = step
  (pending, text)

# Decode the next buffer, whose values must all be bytes.
def decode_buffer(state: DecodeState(), +buffer: List<&2, U32>,
  -valid: {decode_buffer.all_bytes(buffer) == True{} : Bool}) ->
  DecodeState() & String:
  decode_buffer.result(decode_buffer.bytes(buffer, state))

# An unfinished sequence at the end of the input is replaced.
def decode_done(state: DecodeState()) -> String:
  match state:
    case Nil{}:
      ""
    case p <> ps:
      replacement_char_string()
