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

# Streaming decoder
# -----------------
#
# A simple decoder that reads one byte at a time.  Its state is the
# pending bytes of a sequence that has begun but not yet finished.

def DecodeState() -> Type:
  List<&2, U32>

def decode_start() -> DecodeState():
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

# The scalar that `seq` encodes when `seq` is exactly one valid sequence,
# otherwise None.
def sequence_scalar(seq: List<&2, U32>) -> Maybe<&2, U32>:
  match seq:
    case +b1 <> Nil{}:
      one_byte_scalar(b1)
    case +b1 <> +b2 <> Nil{}:
      two_byte_scalar(b1, b2)
    case _:
      None{}

# Whether `seq` is a valid sequence prefix: one or more bytes that
# some bytes, possibly none, can follow to make a valid sequence.
# Whether a lead byte can begin a two-byte sequence does not depend on
# which continuation byte follows, so 0x80 stands for them all.
def is_valid_sequence_prefix(seq: List<&2, U32>) -> Bool:
  match seq:
    case Nil{}:
      False{}
    case +b1 <> Nil{}:
      valid_one_byte(b1) || valid_two_bytes(b1, 128)
    case +b1 <> +b2 <> Nil{}:
      valid_two_bytes(b1, b2)
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
