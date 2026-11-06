import Base
import ./defs.bend as Defs
import ./binary.bend as B
import ./utf8.bend as UTF8
import ./binary_LAWS.bend as BinaryLaws
import ./hexdigits.bend as H
import ./func_LAWS.bend as Func

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

# A Unicode scalar is any code point from U+0000 to U+10FFFF excluding
# surrogate code points.

def is_unicode_scalar(+cp: U32) -> Bool:
  U32.is_ge(cp, H.hex_u32("000000", {==})) &&
  U32.is_le(cp, H.hex_u32("10FFFF", {==})) &&
  Bool.not(is_surrogate_code_point(cp))

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

# A code point can be encoded as one byte iff iff one_byte_shape
# matches.

def can_encode_as_one_byte(cp: U32) -> Bool:
  Maybe.is_some(&2, U32, one_byte_shape(cp))

law utf8_can_encode_as_one_byte:
  for +cp: U32
  {UTF8.can_encode_as_one_byte(cp) == can_encode_as_one_byte(cp) : Bool}

law utf8_encode_as_one_byte:
  for +cp: U32
  for valid: {UTF8.can_encode_as_one_byte(cp) == True{} : Bool}
  {Some{UTF8.encode_as_one_byte(cp, valid)} == one_byte_shape(cp) : Maybe<&2, U32>}

# True exactly when the byte is produced by the one-byte encoding table.
law utf8_has_one_byte_shape:
  for +byte: U32
  representation = Exists(U32, cp =>
    {one_byte_shape(cp) == Some{byte} : Maybe<&2, U32>})
  ({UTF8.has_one_byte_shape(byte) == True{} : Bool} -> representation) &
  (representation -> {UTF8.has_one_byte_shape(byte) == True{} : Bool})

# We require that `encode_as_one_byte` be bijective between accepted
# code points and bytes satisfying `has_one_byte_shape`, and we specify
# that `decode_one_byte` is exactly its inverse.

law utf8_one_byte_inverse:
  Func.Bijection(U32, U32,
    cp => UTF8.can_encode_as_one_byte(cp),
    byte => UTF8.has_one_byte_shape(byte),
    cp => valid => UTF8.encode_as_one_byte(cp, valid),
    byte => valid => UTF8.decode_one_byte(byte, valid))

# No one-byte encoding is overlong.

def overlong_one_byte(b1: U32) -> Bool:
  False{}

# A valid one-byte encoding has the one-byte shape, and if it does
# have the one-byte shape, it is not overlong and decodes to a Unicode
# scalar.
#
# Testing the shape first supplies the proof that decoding needs.

def valid_one_byte.if(+byte: U32, shape: Bool,
  -checked: {UTF8.has_one_byte_shape(byte) == shape : Bool}) -> Bool:
  match shape:
    case False{}:
      False{}
    case True{}:
      Bool.not(overlong_one_byte(byte)) &&
      is_unicode_scalar(UTF8.decode_one_byte(byte, checked))

def valid_one_byte(+byte: U32) -> Bool:
  valid_one_byte.if(byte, UTF8.has_one_byte_shape(byte), {==})

law utf8_valid_one_byte:
  for +byte: U32
  {UTF8.valid_one_byte(byte) == valid_one_byte(byte) : Bool}

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

# Specification for UTF8.can_encode_as_two_bytes: it returns True iff
# two_byte_shape matches.

law utf8_can_encode_as_two_bytes:
  for +cp: U32
  {UTF8.can_encode_as_two_bytes(cp) == Maybe.is_some(&1, U32 & U32, two_byte_shape(cp)) : Bool}

# Given a code point and a proof that the code point can be encoded in
# a UTF-8 two-byte shape (as specified by two_byte_shape above),
# `UTF8.encode_as_two_bytes` returns the two bytes of the shape
# directly as U32 values without needing to use a Maybe.

law utf8_encode_as_two_bytes:
  for +cp: U32
  for valid: {UTF8.can_encode_as_two_bytes(cp) == True{} : Bool}
  {Some{UTF8.encode_as_two_bytes(cp, valid)} == two_byte_shape(cp) : Maybe<&1, U32 & U32>}

# `UTF8.has_two_byte_shape(b1, b2)` returns True iff `(b1, b2)` can be
# returned by `two_byte_shape` for some code point.

law utf8_has_two_byte_shape:
  for +b1: U32
  for +b2: U32
  representation = Exists(U32, cp =>
    {two_byte_shape(cp) == Some{(b1, b2)} : Maybe<&1, U32 & U32>})
  ({UTF8.has_two_byte_shape(b1, b2) == True{} : Bool} -> representation) &
  (representation -> {UTF8.has_two_byte_shape(b1, b2) == True{} : Bool})

# We require that `encode_as_two_bytes` be bijective between accepted
# code points and byte pairs satisfying `has_two_byte_shape`, and we
# specify that `decode_two_bytes` is exactly its inverse.  A pair `p`
# stands for its bytes `B.first(p)` and `B.second(p)`.

law utf8_two_byte_inverse:
  Func.Bijection(U32, U32 & U32,
    cp => UTF8.can_encode_as_two_bytes(cp),
    p => UTF8.has_two_byte_shape(B.first(p), B.second(p)),
    cp => valid => UTF8.encode_as_two_bytes(cp, valid),
    p => valid => UTF8.decode_two_bytes(B.first(p), B.second(p), valid))

# Overlong means that the decoded code point fits in one byte.
law utf8_overlong_two_bytes:
  for +b1: U32
  for +b2: U32
  for -valid_shape: {UTF8.has_two_byte_shape(b1, b2) == True{} : Bool}
  {UTF8.overlong_two_bytes(b1, b2, valid_shape) ==
    UTF8.can_encode_as_one_byte(UTF8.decode_two_bytes(b1, b2, valid_shape)) : Bool}

# A valid two-byte encoding has the two-byte shape, and, if it does
# have the two-byte shape, it is not overlong and decodes to a Unicode
# scalar.
#
# Testing the shape first supplies the proof that the overlong check
# and decoding need.

def valid_two_bytes.if(+b1: U32, +b2: U32, shape: Bool,
  -checked: {UTF8.has_two_byte_shape(b1, b2) == shape : Bool}) -> Bool:
  match shape:
    case False{}:
      False{}
    case True{}:
      Bool.not(UTF8.overlong_two_bytes(b1, b2, checked)) &&
      is_unicode_scalar(UTF8.decode_two_bytes(b1, b2, checked))

def valid_two_bytes(+b1: U32, +b2: U32) -> Bool:
  valid_two_bytes.if(b1, b2, UTF8.has_two_byte_shape(b1, b2), {==})

law utf8_valid_two_bytes:
  for +b1: U32
  for +b2: U32
  {UTF8.valid_two_bytes(b1, b2) == valid_two_bytes(b1, b2) : Bool}

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

# U+FFFD REPLACEMENT CHARACTER, as a one-character string.

def replacement_char_string() -> String:
  code_point_to_string(H.hex_u32("FFFD", {==}))

# Valid sequences
# ---------------

# A valid one-byte sequence has the one-byte shape.

law valid_one_byte_has_shape:
  for +byte: U32
  for valid: {valid_one_byte(byte) == True{} : Bool}
  {UTF8.has_one_byte_shape(byte) == True{} : Bool}

# The scalar that a valid one-byte sequence encodes, or None.

def one_byte_scalar.if(+byte: U32, valid: Bool,
  -checked: {valid_one_byte(byte) == valid : Bool}) -> Maybe<&2, U32>:
  match valid:
    case False{}:
      None{}
    case True{}:
      Some{UTF8.decode_one_byte(byte, valid_one_byte_has_shape(byte, checked))}

def one_byte_scalar(+byte: U32) -> Maybe<&2, U32>:
  one_byte_scalar.if(byte, valid_one_byte(byte), {==})

# Since one of the conditions for a byte sequence to be valid is that
# it has the right shape, if two bytes are a valid two-byte sequence,
# this implies that the two bytes also have the two-byte shape.
#
# We use this law when we have a valid two-byte sequence and we need
# a proof that it has the two-byte shape.

law valid_two_bytes_has_shape:
  for +b1: U32
  for +b2: U32
  for valid: {valid_two_bytes(b1, b2) == True{} : Bool}
  {UTF8.has_two_byte_shape(b1, b2) == True{} : Bool}

# Given any two bytes, return the scalar that the two-byte sequence
# encodes if it is a valid sequence, otherwise return None.

def two_byte_scalar.if(+b1: U32, +b2: U32, valid: Bool,
  -checked: {valid_two_bytes(b1, b2) == valid : Bool}) -> Maybe<&2, U32>:
  match valid:
    case False{}:
      None{}
    case True{}:
      Some{UTF8.decode_two_bytes(b1, b2, valid_two_bytes_has_shape(b1, b2, checked))}

def two_byte_scalar(+b1: U32, +b2: U32) -> Maybe<&2, U32>:
  two_byte_scalar.if(b1, b2, valid_two_bytes(b1, b2), {==})

# The scalar that `seq` encodes when `seq` is exactly one valid
# sequence, otherwise None.

def sequence_scalar(seq: List<&2, U32>) -> Maybe<&2, U32>:
  match seq:
    case +b1 <> Nil{}:
      one_byte_scalar(b1)
    case +b1 <> +b2 <> Nil{}:
      two_byte_scalar(b1, b2)
    case _:
      None{}

# `seq` is exactly one valid sequence.

def is_valid_sequence(seq: List<&2, U32>) -> Bool:
  Maybe.is_some(&2, U32, sequence_scalar(seq))

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

# The reference decoder
# ---------------------
#
# The reference decoder reads one byte at a time.  Between bytes it holds
# the pending bytes of a sequence that has begun but not yet finished.
# It exists only to say what text is expected; the implementation may
# work however it likes.

# What a step returns: the text now resolved, and the new pending bytes.

def Step() -> Type:
  String & List<&2, U32>

def Step.prepend(text: String, step: Step()) -> Step():
  (more, pending) = step
  (text ++ more, pending)

# `seq` is the pending bytes followed by the new byte.  If `seq` is a
# valid sequence, emit its scalar.  If it begins one, keep it pending.
# Otherwise do `otherwise`.

def advance(seq: List<&2, U32>, scalar: Maybe<&2, U32>, begins: Bool,
  otherwise: Unit -> Step()) -> Step():
  match scalar begins:
    case Some{cp} _:
      (code_point_to_string(cp), Nil{})
    case None{} True{}:
      ("", seq)
    case None{} False{}:
      otherwise(Unit{})

# A byte with nothing pending.  If it neither is nor begins a valid
# sequence, it is a maximal subpart by itself: U+FFFD.

def start_sequence(+b: U32) -> Step():
  +seq = {[b] : List<&2, U32>}
  advance(seq, sequence_scalar(seq), UTF8.begins_valid_sequence(seq),
    u => (replacement_char_string(), Nil{}))

# A byte that follows the pending bytes of an unfinished sequence.  If
# the byte neither completes nor continues that sequence, the pending
# bytes are a maximal subpart: emit U+FFFD for them, and then treat the
# byte as having nothing pending.

def extend_sequence(pending: List<&2, U32>, +b: U32) -> Step():
  +seq = List.append(&2, U32, pending, [b])
  advance(seq, sequence_scalar(seq), UTF8.begins_valid_sequence(seq),
    u => Step.prepend(replacement_char_string(), start_sequence(b)))

def step(pending: List<&2, U32>, +b: U32) -> Step():
  match pending:
    case Nil{}:
      start_sequence(b)
    case p <> ps:
      extend_sequence(p <> ps, b)

# Run the reference decoder over `bytes`, starting with `pending`.

def reference.then(stepped: Step(), rest: List<&2, U32> -> Step()) -> Step():
  (text, pending) = stepped
  Step.prepend(text, rest(pending))

def reference.go(bytes: List<&2, U32>, pending: List<&2, U32>) -> Step():
  match bytes:
    case Nil{}:
      ("", pending)
    case +b <> rest:
      reference.then(step(pending, b), p => reference.go(rest, p))

# The text that `bytes` fully determine, whatever bytes follow them.

def Step.text(step: Step()) -> String:
  (text, pending) = step
  text

def reference_so_far(bytes: List<&2, U32>) -> String:
  Step.text(reference.go(bytes, Nil{}))

# The text for `bytes` as the whole input.  An unfinished sequence at the
# end is a maximal subpart: U+FFFD.

def unfinished_text(pending: List<&2, U32>) -> String:
  match pending:
    case Nil{}:
      ""
    case p <> ps:
      replacement_char_string()

def Step.final_text(step: Step()) -> String:
  (text, pending) = step
  text ++ unfinished_text(pending)

def reference_final(bytes: List<&2, U32>) -> String:
  Step.final_text(reference.go(bytes, Nil{}))

# Running the decoder
# -------------------

# `Some{x}` when `cond` holds, otherwise None.
def when(-A: Data, cond: Bool, x: A) -> Maybe<&2, A>:
  match cond:
    case False{}:
      None{}
    case True{}:
      Some{x}

# Every value in `bytes` is a byte, 0..255.

def all_bytes(bytes: List<&2, U32>) -> Bool:
  List.all(~&2, ~U32, ~(b => U32.is_le(b, 255)), bytes)

# The decoder state and the text so far, or None once a buffer is
# rejected.

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

# However the input is split into buffers, after each buffer the decoder
# has returned exactly the text that the bytes so far fully determine:
# nothing that later bytes could change, and nothing held back.  A buffer
# containing a value above 255 is rejected.

law utf8_decode_buffer:
  for +buffers: List<&2, List<&2, U32>>
  +bytes = List.concat(&2, U32, buffers)
  {decoded_so_far(buffers) ==
    when(String, all_bytes(bytes), reference_so_far(bytes)) : Maybe<&2, String>}

# `UTF8.decode_done` then completes the text of the whole input.

law utf8_decode_done:
  for +buffers: List<&2, List<&2, U32>>
  +bytes = List.concat(&2, U32, buffers)
  {decoded(buffers) ==
    when(String, all_bytes(bytes), reference_final(bytes)) : Maybe<&2, String>}
