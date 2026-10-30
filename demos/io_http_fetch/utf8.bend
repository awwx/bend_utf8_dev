# Streaming UTF-8 decoder. feed returns only the text completed by that
# chunk; an empty chunk is not EOF. Call done once after the last chunk.
# Malformed sequences use Unicode maximal-subpart replacement (U+FFFD).
import Base

# Pending continuation count, partial code point, and next-byte bounds.
# Output is kept outside the state so earlier chunks need not be retained.
type State is Data:
  Decoder{left: U32, code: U32, low: U32, high: U32}

# Internal fold accumulator; feed exposes the state and text as a pair.
type Acc is Data:
  Acc{state: State, text: String}

def new() -> State:
  Decoder{0, 0, 128, 191}

# Append the low six bits of a continuation byte to a partial code point.
# Spelling the disjoint bit fields directly also makes their inverse provable.
def join6(code: U32, byte: U32) -> U32:
  match code byte:
    case U32{WCon{c0, WCon{c1, WCon{c2, WCon{c3, WCon{c4, WCon{c5, WCon{c6, WCon{c7, WCon{c8, WCon{c9, WCon{c10, WCon{c11, WCon{c12, WCon{c13, WCon{c14, WCon{c15, WCon{c16, WCon{c17, WCon{c18, WCon{c19, WCon{c20, WCon{c21, WCon{c22, WCon{c23, WCon{c24, WCon{c25, _}}}}}}}}}}}}}}}}}}}}}}}}}}} U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, _}}}}}}}:
      U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{c0, WCon{c1, WCon{c2, WCon{c3, WCon{c4, WCon{c5, WCon{c6, WCon{c7, WCon{c8, WCon{c9, WCon{c10, WCon{c11, WCon{c12, WCon{c13, WCon{c14, WCon{c15, WCon{c16, WCon{c17, WCon{c18, WCon{c19, WCon{c20, WCon{c21, WCon{c22, WCon{c23, WCon{c24, WCon{c25, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

# UTF-8 continuation ranges are prefixes; low payload bits are irrelevant.
def continuation(+b: U32, low: U32, high: U32) -> Bool:
  match low high:
    case 128 191:
      U32.is_eq(U32.shrn(b, 6n), 2)
    case 160 191:
      U32.is_eq(U32.shrn(b, 5n), 5)
    case 128 159:
      U32.is_eq(U32.shrn(b, 5n), 4)
    case 144 191:
      Bool.or(U32.is_eq(U32.shrn(b, 4n), 9), U32.is_eq(U32.shrn(b, 5n), 5))
    case 128 143:
      U32.is_eq(U32.shrn(b, 4n), 8)
    case _ _:
      False{}

def start(+b: U32, +text: String) -> Acc:
  +left = Bool.pick(U32, U32.is_lt(b, 224), 1,
    Bool.pick(U32, U32.is_lt(b, 240), 2, 3))
  Bool.pick(Acc, U32.is_lt(b, 128),
    Acc{new(), SCon{Chr{b}, text}},
    Bool.pick(Acc, Bool.or(U32.is_lt(U32.shrn(b, 1n), 97), U32.is_gt(b, 244)),
      Acc{new(), SCon{Chr{65533}, text}},
      Acc{Decoder{left, U32.and(U32.shrn(63, U32.to_nat(left)), b),
        Bool.pick(U32, U32.is_eq(b, 224), 160,
          Bool.pick(U32, U32.is_eq(b, 240), 144, 128)),
        Bool.pick(U32, U32.is_eq(b, 237), 159,
          Bool.pick(U32, U32.is_eq(b, 244), 143, 191))}, text}))

def more(+b: U32, +left: U32, +code: U32, +text: String,
  valid: Bool) -> Acc:
  match valid:
    case False{}:
      # Replace the interrupted sequence, then reconsider this byte.
      start(b, SCon{Chr{65533}, text})
    case True{}:
      +next = U32.sub(left, 1)
      +value = join6(code, b)
      Acc{Bool.pick(State, U32.is_zero(next), new(), Decoder{next, value, 128, 191}),
        Bool.pick(String, U32.is_zero(next), SCon{Chr{value}, text}, text)}

def byte(state: State, +b: U32, text: String) -> Acc:
  match state:
    case Decoder{left, code, low, high}:
      match left:
        case 0:
          start(b, text)
        case _:
          more(b, left, code, text,
            continuation(b, low, high))

def extend(acc: Acc, tail: String) -> Acc:
  Acc{state, text} = acc
  Acc{state, String.append(text, tail)}

def step(acc: Acc, b: U32) -> Acc:
  Acc{state, text} = acc
  extend(byte(state, b, ""), text)

def finish(acc: Acc) -> State & String:
  Acc{state, text} = acc
  (state, String.reverse(text))

# Each U32 is a byte (0..255); out-of-range values become U+FFFD.
# Complete characters are returned now; only an unfinished one is carried.
def feed(state: State, bytes: List<&2, U32>) -> State & String:
  finish(List.foldl(~&2, ~U32, ~Acc,
    ~(acc => b => step(acc, b)), bytes, Acc{state, ""}))

# Flush EOF: a pending sequence contributes exactly one replacement.
def done(state: State) -> String:
  match state:
    case Decoder{left, code, low, high}:
      match left:
        case 0:
          ""
        case _:
          "�"

# A UTF-8 continuation byte carrying the six bits at this offset.
def encode.cont(+code: U32, shift: Nat) -> U32:
  U32.or(128, U32.and(63, U32.shrn(code, shift)))

def encode.two(+code: U32, tail: List<&2, U32>) -> List<&2, U32>:
  U32.or(192, U32.shrn(code, 6n)) <> encode.cont(code, 0n) <> tail

def encode.three(+code: U32, tail: List<&2, U32>) -> List<&2, U32>:
  U32.or(224, U32.shrn(code, 12n)) <> encode.cont(code, 6n) <>
    encode.cont(code, 0n) <> tail

def encode.four(+code: U32, tail: List<&2, U32>) -> List<&2, U32>:
  U32.or(240, U32.shrn(code, 18n)) <> encode.cont(code, 12n) <>
    encode.cont(code, 6n) <> encode.cont(code, 0n) <> tail

# Unicode scalar values exclude surrogates and stop before U+110000.
def scalar(+code: U32) -> Bool:
  Bool.and(U32.is_lt(code, 1114112),
    Bool.not(U32.is_eq(U32.shrn(code, 11n), 27)))

def encode.scalar(+code: U32, +tail: List<&2, U32>) -> List<&2, U32>:
  Bool.pick(List<&2, U32>, U32.is_zero(U32.shrn(code, 7n)), code <> tail,
    Bool.pick(List<&2, U32>, U32.is_zero(U32.shrn(code, 11n)), encode.two(code, tail),
      Bool.pick(List<&2, U32>, U32.is_zero(U32.shrn(code, 16n)),
        encode.three(code, tail), encode.four(code, tail))))

# Like IO.print's codec, replace a non-scalar Char with U+FFFD.
# No BOM is inserted. The result contains one U32 (0..255) per byte.
def encode(text: String) -> List<&2, U32>:
  match text:
    case SNil{}:
      Nil{}
    case SCon{Chr{+code}, rest}:
      encode.scalar(Bool.pick(U32, scalar(code), code, 65533), encode(rest))
