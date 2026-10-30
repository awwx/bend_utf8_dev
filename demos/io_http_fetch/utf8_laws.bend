# Unicode values are defined first, independently of UTF-8 byte layouts.
# The range constructors below partition the valid scalar values into the
# binary intervals used to describe their canonical UTF-8 encodings.
import Base
import ./utf8.bend as UTF8

def ascii_0() -> U32:
  48

def ascii_9() -> U32:
  57

def ascii_A() -> U32:
  65

def ascii_F() -> U32:
  70

# Exactly eight ASCII hexadecimal digits: 0..9 and A..F, without a prefix.
# The erased proof makes an invalid literal a type error, for example:
# hex_u32("0001F600", {==}) succeeds; hex_u32("foo", {==}) fails to type-check.
def hex_u32.digit(+value: U32) -> Bool:
  Bool.or(
    Bool.and(U32.is_ge(value, ascii_0), U32.is_le(value, ascii_9)),
    Bool.and(U32.is_ge(value, ascii_A), U32.is_le(value, ascii_F)))

def hex_u32.valid_n(text: String, left: Nat) -> Bool:
  match text left:
    case SNil{} Zero{}:
      True{}
    case SCon{Chr{value}, tail} Succ{rest}:
      Bool.and(hex_u32.digit(value), hex_u32.valid_n(tail, rest))
    case _ _:
      False{}

def hex_u32.valid(text: String) -> Bool:
  hex_u32.valid_n(text, 8n)

# Internal fold; hex_u32's proof guarantees valid digits and prevents overflow.
def hex_u32.fold(text: String, acc: U32) -> U32:
  match text:
    case SNil{}:
      acc
    case SCon{Chr{+value}, tail}:
      hex_u32.fold(tail, U32.add(U32.shln(acc, 4n),
        Bool.pick(U32, U32.is_le(value, ascii_9),
          U32.sub(value, ascii_0), U32.add(U32.sub(value, ascii_A), 10))))

def hex_u32(text: String, -valid: {hex_u32.valid(text) == True{} : Bool}) -> U32:
  hex_u32.fold(text, 0)

# Concrete examples stated as equalities that must all be proved.
law hex_u32_examples:
  {hex_u32("00000000", {==}) == 0 : U32} &
  {hex_u32("01234567", {==}) == 19088743 : U32} &
  {hex_u32("89ABCDEF", {==}) == 2309737967 : U32} &
  {hex_u32("0001F600", {==}) == 128512 : U32} &
  {hex_u32("0010FFFF", {==}) == 1114111 : U32} &
  {hex_u32("80000000", {==}) == 2147483648 : U32} &
  {hex_u32("FFFFFFFF", {==}) == 4294967295 : U32}

# U+0000..U+10FFFF, including surrogates, unassigned values and noncharacters.
def codepoint_valid(+value: U32) -> Bool:
  Bool.and(
    U32.is_ge(value, hex_u32("00000000", {==})),
    U32.is_le(value, hex_u32("0010FFFF", {==})))

type UnicodeCodepoint is Data:
  UnicodeCodepoint{value: U32,
    -valid: {codepoint_valid(value) == True{} : Bool}}

def codepoint_value(point: UnicodeCodepoint) -> U32:
  UnicodeCodepoint{value, valid} = point
  value

# The inclusive surrogate range U+D800..U+DFFF.
def surrogate_value(+value: U32) -> Bool:
  Bool.and(
    U32.is_ge(value, hex_u32("0000D800", {==})),
    U32.is_le(value, hex_u32("0000DFFF", {==})))

# This predicate only excludes surrogates; the codepoint type enforces the bound.
def not_surrogate_value(value: U32) -> Bool:
  Bool.not(surrogate_value(value))

type UnicodeScalar is Data:
  UnicodeScalar{point: UnicodeCodepoint,
    -valid: {not_surrogate_value(codepoint_value(point)) == True{} : Bool}}

def scalar_value(scalar: UnicodeScalar) -> U32:
  UnicodeScalar{point, valid} = scalar
  codepoint_value(point)

# A value within one of the valid Unicode scalar ranges used for UTF-8.
type Utf8RangeValue is Data:
  # U+0000..U+007F
  Ascii{low: Word(7n)}
  # U+0080..U+00FF
  Two8{low: Word(7n)}
  # U+0100..U+01FF
  Two9{low: Word(8n)}
  # U+0200..U+03FF
  Two10{low: Word(9n)}
  # U+0400..U+07FF
  Two11{low: Word(10n)}
  # U+0800..U+0FFF
  Three12{low: Word(11n)}
  # U+1000..U+1FFF
  Three13{low: Word(12n)}
  # U+2000..U+3FFF
  Three14{low: Word(13n)}
  # U+4000..U+7FFF
  Three15{low: Word(14n)}
  # U+8000..U+BFFF
  Three16a{low: Word(14n)}
  # U+C000..U+CFFF
  Three16b{low: Word(12n)}
  # U+D000..U+D7FF
  Three16c{low: Word(11n)}
  # U+E000..U+FFFF
  Three16d{low: Word(13n)}
  # U+10000..U+1FFFF
  Four17{low: Word(16n)}
  # U+20000..U+3FFFF
  Four18{low: Word(17n)}
  # U+40000..U+7FFFF
  Four19{low: Word(18n)}
  # U+80000..U+FFFFF
  Four20{low: Word(19n)}
  # U+100000..U+10FFFF
  Four21{low: Word(16n)}

def cat(n: Nat, -m: Nat, lo: Word(n), hi: Word(m)) -> Word(Nat.add(n, m)):
  match n:
    case 0n:
      hi
    case 1n+p:
      match lo:
        case WCon{b, rest}:
          WCon{b, cat(p, m, rest, hi)}

# The numeric value fixed by a range constructor and its low payload bits.
def range_value(s: Utf8RangeValue) -> U32:
  match s:
    case Ascii{low}:
      U32{cat(7n, 25n, low, Word.zero(25n))}
    case Two8{low}:
      U32{cat(7n, 25n, low, WCon{True{}, Word.zero(24n)})}
    case Two9{low}:
      U32{cat(8n, 24n, low, WCon{True{}, Word.zero(23n)})}
    case Two10{low}:
      U32{cat(9n, 23n, low, WCon{True{}, Word.zero(22n)})}
    case Two11{low}:
      U32{cat(10n, 22n, low, WCon{True{}, Word.zero(21n)})}
    case Three12{low}:
      U32{cat(11n, 21n, low, WCon{True{}, Word.zero(20n)})}
    case Three13{low}:
      U32{cat(12n, 20n, low, WCon{True{}, Word.zero(19n)})}
    case Three14{low}:
      U32{cat(13n, 19n, low, WCon{True{}, Word.zero(18n)})}
    case Three15{low}:
      U32{cat(14n, 18n, low, WCon{True{}, Word.zero(17n)})}
    case Three16a{low}:
      U32{cat(14n, 18n, low, WCon{False{}, WCon{True{}, Word.zero(16n)}})}
    case Three16b{low}:
      U32{cat(12n, 20n, low, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, Word.zero(16n)}}}})}
    case Three16c{low}:
      U32{cat(11n, 21n, low, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, Word.zero(16n)}}}}})}
    case Three16d{low}:
      U32{cat(13n, 19n, low, WCon{True{}, WCon{True{}, WCon{True{}, Word.zero(16n)}}})}
    case Four17{low}:
      U32{cat(16n, 16n, low, WCon{True{}, Word.zero(15n)})}
    case Four18{low}:
      U32{cat(17n, 15n, low, WCon{True{}, Word.zero(14n)})}
    case Four19{low}:
      U32{cat(18n, 14n, low, WCon{True{}, Word.zero(13n)})}
    case Four20{low}:
      U32{cat(19n, 13n, low, WCon{True{}, Word.zero(12n)})}
    case Four21{low}:
      U32{cat(16n, 16n, low, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, Word.zero(11n)}}}}})}

# Every range value denotes a scalar; the bit-level proof lives in utf8_proof.bend.
law code_valid:
  for +s: Utf8RangeValue
  {codepoint_valid(range_value(s)) == True{} : Bool} &
    {not_surrogate_value(range_value(s)) == True{} : Bool}

def code_checked(value: U32,
  -valid: {codepoint_valid(value) == True{} : Bool} &
    {not_surrogate_value(value) == True{} : Bool}) -> UnicodeScalar:
  UnicodeScalar{UnicodeCodepoint{value,
    Pair.fst({codepoint_valid(value) == True{} : Bool},
      {not_surrogate_value(value) == True{} : Bool}, valid)},
    Pair.snd({codepoint_valid(value) == True{} : Bool},
      {not_surrogate_value(value) == True{} : Bool}, valid)}

# The public conversion returns a scalar with both validity proofs attached.
def code(+s: Utf8RangeValue) -> UnicodeScalar:
  code_checked(range_value(s), code_valid(s))

# The wire specification uses the standard 0xxxxxxx, 110xxxxx,
# 1110xxxx, 11110xxx and 10xxxxxx byte layouts. It does not call encode.
def wire.cont(code: U32, shift: Nat) -> U32:
  U32.or(128, U32.and(63, U32.shrn(code, shift)))

def wire.two(+c: U32) -> List<&2, U32>:
  [U32.or(192, U32.shrn(c, 6n)), wire.cont(c, 0n)]

def wire.three(+c: U32) -> List<&2, U32>:
  [U32.or(224, U32.shrn(c, 12n)), wire.cont(c, 6n), wire.cont(c, 0n)]

def wire.four(+c: U32) -> List<&2, U32>:
  [U32.or(240, U32.shrn(c, 18n)), wire.cont(c, 12n), wire.cont(c, 6n), wire.cont(c, 0n)]

# Fixed UTF-8 layouts, chosen by the scalar interval, not by the decoder.
def scalar_bytes(s: Utf8RangeValue) -> List<&2, U32>:
  match s:
    case Ascii{low}:
      scalar_value(code(Ascii{low})) <> Nil{}
    case Two8{low}:
      wire.two(scalar_value(code(Two8{low})))
    case Two9{low}:
      wire.two(scalar_value(code(Two9{low})))
    case Two10{low}:
      wire.two(scalar_value(code(Two10{low})))
    case Two11{low}:
      wire.two(scalar_value(code(Two11{low})))
    case Three12{low}:
      wire.three(scalar_value(code(Three12{low})))
    case Three13{low}:
      wire.three(scalar_value(code(Three13{low})))
    case Three14{low}:
      wire.three(scalar_value(code(Three14{low})))
    case Three15{low}:
      wire.three(scalar_value(code(Three15{low})))
    case Three16a{low}:
      wire.three(scalar_value(code(Three16a{low})))
    case Three16b{low}:
      wire.three(scalar_value(code(Three16b{low})))
    case Three16c{low}:
      wire.three(scalar_value(code(Three16c{low})))
    case Three16d{low}:
      wire.three(scalar_value(code(Three16d{low})))
    case Four17{low}:
      wire.four(scalar_value(code(Four17{low})))
    case Four18{low}:
      wire.four(scalar_value(code(Four18{low})))
    case Four19{low}:
      wire.four(scalar_value(code(Four19{low})))
    case Four20{low}:
      wire.four(scalar_value(code(Four20{low})))
    case Four21{low}:
      wire.four(scalar_value(code(Four21{low})))

# Byte-level execution, with output accumulated in reverse order.
def scan(bytes: List<&2, U32>, acc: UTF8.Acc) -> UTF8.Acc:
  List.foldl(~&2, ~U32, ~UTF8.Acc,
    ~(acc => b => UTF8.step(acc, b)), bytes, acc)

def wire(chars: List<&2, Utf8RangeValue>) -> List<&2, U32>:
  match chars:
    case Nil{}:
      Nil{}
    case s <> rest:
      List.append(&2, U32, scalar_bytes(s), wire(rest))

def text(chars: List<&2, Utf8RangeValue>) -> String:
  match chars:
    case Nil{}:
      ""
    case s <> rest:
      SCon{Chr{scalar_value(code(s))}, text(rest)}

# A byte sequence is valid precisely when it is the canonical UTF-8
# encoding of a sequence of Unicode scalars. No decoder property is assumed.
def Valid(bytes: List<&2, U32>) -> Type:
  &chars: List<&2, Utf8RangeValue> -> {wire(chars) == bytes : List<&2, U32>}

def flatten(chunks: List<&2, List<&2, U32>>) -> List<&2, U32>:
  match chunks:
    case Nil{}:
      Nil{}
    case chunk <> rest:
      List.append(&2, U32, chunk, flatten(rest))

# This is the public streaming interface's output: concatenate each feed's
# text in order, followed by done at EOF. Empty chunks are allowed.
def decoded_next(result: UTF8.State & String, rest: UTF8.State -> String) -> String:
  (state, text) = result
  String.append(text, rest(state))

def decoded(chunks: List<&2, List<&2, U32>>, state: UTF8.State) -> String:
  match chunks:
    case Nil{}:
      UTF8.done(state)
    case chunk <> rest:
      decoded_next(UTF8.feed(state, chunk), next => decoded(rest, next))

law roundtrip:
  for +chunks: List<&2, List<&2, U32>>
  for valid: Valid(flatten(chunks))
  {UTF8.encode(decoded(chunks, UTF8.new())) == flatten(chunks) : List<&2, U32>}

# The same claim with the original input and its partition named explicitly.
law split_roundtrip:
  for +bytes: List<&2, U32>
  for +chunks: List<&2, List<&2, U32>>
  for valid: Valid(bytes)
  for split: {flatten(chunks) == bytes : List<&2, U32>}
  {UTF8.encode(decoded(chunks, UTF8.new())) == bytes : List<&2, U32>}

# Finish byte-level execution: restore output order, then flush EOF.
def render(acc: UTF8.Acc) -> String:
  UTF8.Acc{state, text} = acc
  String.append(String.reverse(text), UTF8.done(state))

# Independent byte-pattern specification
# --------------------------------------
# These are exactly the four raw UTF-8 layouts. All payload bits are free:
# unlike Utf8RangeValue, this type includes overlong, surrogate and >U+10FFFF forms.
# Word widths enforce byte/payload widths without trusting the decoder.
type Pattern is Data:
  One{payload: Word(7n)}
  Two{payload: Word(11n)}
  Three{payload: Word(16n)}
  Four{payload: Word(21n)}

def pattern_code(p: Pattern) -> U32:
  match p:
    case One{payload}:
      U32{cat(7n, 25n, payload, Word.zero(25n))}
    case Two{payload}:
      U32{cat(11n, 21n, payload, Word.zero(21n))}
    case Three{payload}:
      U32{cat(16n, 16n, payload, Word.zero(16n))}
    case Four{payload}:
      U32{cat(21n, 11n, payload, Word.zero(11n))}

# 0xxxxxxx / 110xxxxx 10xxxxxx / 1110xxxx 10xxxxxx 10xxxxxx /
# 11110xxx 10xxxxxx 10xxxxxx 10xxxxxx. No validity restrictions here.
def pattern_bytes(p: Pattern) -> List<&2, U32>:
  match p:
    case One{payload}:
      [pattern_code(One{payload})]
    case Two{payload}:
      wire.two(pattern_code(Two{payload}))
    case Three{payload}:
      wire.three(pattern_code(Three{payload}))
    case Four{payload}:
      wire.four(pattern_code(Four{payload}))

# A structural predicate: the byte list has exactly one of the raw layouts.
def Shape(bytes: List<&2, U32>) -> Type:
  &p: Pattern -> {pattern_bytes(p) == bytes : List<&2, U32>}

# True means that the candidate passes this rule. Each rule is independent:
# shortest can accept a surrogate; not_surrogate can accept an overlong form.
def shortest(p: Pattern) -> Bool:
  match p:
    case One{payload}:
      True{}
    case Two{payload}:
      Bool.not(U32.is_zero(U32.shrn(pattern_code(Two{payload}), 7n)))
    case Three{payload}:
      Bool.not(U32.is_zero(U32.shrn(pattern_code(Three{payload}), 11n)))
    case Four{payload}:
      Bool.not(U32.is_zero(U32.shrn(pattern_code(Four{payload}), 16n)))

# U+D800..U+DFFF have the same high bits after dropping eleven low bits.
def not_surrogate(p: Pattern) -> Bool:
  not_surrogate_value(pattern_code(p))

# code < 0x110000, equivalently floor(code / 65536) < 17.
# This rejects U+110000 even though it fits the raw four-byte layout.
def within_unicode(p: Pattern) -> Bool:
  codepoint_valid(pattern_code(p))

def Checks(p: Pattern) -> Type:
  {shortest(p) == True{} : Bool} &
  {not_surrogate(p) == True{} : Bool} &
  {within_unicode(p) == True{} : Bool}

# A single sequence is accepted by the independent specification exactly
# when it has a raw layout and passes all three semantic rules.
def RuleScalar(bytes: List<&2, U32>) -> Type:
  &p: Pattern -> {pattern_bytes(p) == bytes : List<&2, U32>} & Checks(p)

# The raw representation of a Utf8RangeValue. This function is used only to state
# soundness; the patterns and rules above do not depend on Utf8RangeValue.
def representation(s: Utf8RangeValue) -> Pattern:
  match s:
    case Ascii{low}:
      One{low}
    case Two8{low}:
      Two{cat(7n, 4n, low, WCon{True{}, Word.zero(3n)})}
    case Two9{low}:
      Two{cat(8n, 3n, low, WCon{True{}, Word.zero(2n)})}
    case Two10{low}:
      Two{cat(9n, 2n, low, WCon{True{}, Word.zero(1n)})}
    case Two11{low}:
      Two{cat(10n, 1n, low, WCon{True{}, Word.zero(0n)})}
    case Three12{low}:
      Three{cat(11n, 5n, low, WCon{True{}, Word.zero(4n)})}
    case Three13{low}:
      Three{cat(12n, 4n, low, WCon{True{}, Word.zero(3n)})}
    case Three14{low}:
      Three{cat(13n, 3n, low, WCon{True{}, Word.zero(2n)})}
    case Three15{low}:
      Three{cat(14n, 2n, low, WCon{True{}, Word.zero(1n)})}
    case Three16a{low}:
      Three{cat(14n, 2n, low, WCon{False{}, WCon{True{}, Word.zero(0n)}})}
    case Three16b{low}:
      Three{cat(12n, 4n, low, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, Word.zero(0n)}}}})}
    case Three16c{low}:
      Three{cat(11n, 5n, low, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, Word.zero(0n)}}}}})}
    case Three16d{low}:
      Three{cat(13n, 3n, low, WCon{True{}, WCon{True{}, WCon{True{}, Word.zero(0n)}}})}
    case Four17{low}:
      Four{cat(16n, 5n, low, WCon{True{}, Word.zero(4n)})}
    case Four18{low}:
      Four{cat(17n, 4n, low, WCon{True{}, Word.zero(3n)})}
    case Four19{low}:
      Four{cat(18n, 3n, low, WCon{True{}, Word.zero(2n)})}
    case Four20{low}:
      Four{cat(19n, 2n, low, WCon{True{}, Word.zero(1n)})}
    case Four21{low}:
      Four{cat(16n, 5n, low, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, Word.zero(0n)}}}}})}

law scalar_sound:
  for +s: Utf8RangeValue
  Checks(representation(s)) &
    {pattern_bytes(representation(s)) == scalar_bytes(s) : List<&2, U32>}

law scalar_complete:
  for +p: Pattern
  for checks: Checks(p)
  (&s: Utf8RangeValue -> {scalar_bytes(s) == pattern_bytes(p) : List<&2, U32>})

# These versions state the equivalence directly for an arbitrary byte list.
law scalar_rules:
  for +s: Utf8RangeValue
  RuleScalar(scalar_bytes(s))

law rules_scalar:
  for bytes: List<&2, U32>
  for valid: RuleScalar(bytes)
  (&s: Utf8RangeValue -> {scalar_bytes(s) == bytes : List<&2, U32>})

# Independent validity for a stream: a concatenation of raw patterns,
# each accepted by the three rules. No Utf8RangeValue or codec is used here.
def pattern_wire(patterns: List<&2, Pattern>) -> List<&2, U32>:
  match patterns:
    case Nil{}:
      Nil{}
    case p <> rest:
      List.append(&2, U32, pattern_bytes(p), pattern_wire(rest))

def PatternChecks(patterns: List<&2, Pattern>) -> Type:
  match patterns:
    case Nil{}:
      Unit
    case p <> rest:
      Checks(p) & PatternChecks(rest)

def RulesValid(bytes: List<&2, U32>) -> Type:
  &patterns: List<&2, Pattern> -> PatternChecks(patterns) &
    {pattern_wire(patterns) == bytes : List<&2, U32>}

law rules_valid:
  for bytes: List<&2, U32>
  for valid: RulesValid(bytes)
  Valid(bytes)

# The original chunked round-trip theorem, now with the independent rules
# as its input hypothesis rather than validity defined using Utf8RangeValue.
law rules_split_roundtrip:
  for +bytes: List<&2, U32>
  for +chunks: List<&2, List<&2, U32>>
  for valid: RulesValid(bytes)
  for split: {flatten(chunks) == bytes : List<&2, U32>}
  {UTF8.encode(decoded(chunks, UTF8.new())) == bytes : List<&2, U32>}
