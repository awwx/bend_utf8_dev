# Proofs for the actual UTF-8 encoder and decoder. Check with:
# bend demos/io_http_fetch/utf8_proof.bend --verdict
import Base
import ./utf8.bend as UTF8
import ./utf8_laws.bend as Laws

def Laws.hex_u32_examples():
  ({==}, {==}, {==}, {==}, {==}, {==}, {==})

# Comparing an unsigned word with zero always satisfies the lower bound.
def cmp_ge_zero_bit(order: Cmp, bit: Bool) ->
  {Cmp.is_ge(order) == Cmp.is_ge(Word.cmp.fin(bit, False{}, order)) : Bool}:
  match order bit:
    case LT{} _: {==}
    case EQ{} False{}: {==}
    case EQ{} True{}: {==}
    case GT{} _: {==}

def word_ge_zero(+n: Nat, +word: Word(n)) ->
  {True{} == Cmp.is_ge(Word.cmp(n, word, Word.zero(n))) : Bool}:
  match n:
    case 0n: {==}
    case 1n+p:
      match word:
        case WCon{bit, rest}:
          %cmp_ge_zero_bit(Word.cmp(p, rest, Word.zero(p)), bit) : {True{} == _ : Bool}
          word_ge_zero(p, rest)

def u32_ge_zero(value: U32) ->
  {True{} == U32.is_ge(value, Laws.hex_u32("00000000", {==})) : Bool}:
  match value:
    case U32{word}: word_ge_zero(32n, word)

# Every n-bit payload is at most the n-bit all-ones word.
def cmp_le_ones_bit(order: Cmp, bit: Bool) ->
  {Cmp.is_le(order) == Cmp.is_le(Word.cmp.fin(bit, True{}, order)) : Bool}:
  match order bit:
    case LT{} _: {==}
    case EQ{} False{}: {==}
    case EQ{} True{}: {==}
    case GT{} _: {==}

def word_le_ones(+n: Nat, +word: Word(n)) ->
  {Cmp.is_le(Word.cmp(n, word, Word.not(n, Word.zero(n)))) == True{} : Bool}:
  match n:
    case 0n: {==}
    case 1n+p:
      match word:
        case WCon{bit, rest}:
          %cmp_le_ones_bit(Word.cmp(p, rest, Word.not(p, Word.zero(p))), bit) : {_ == True{} : Bool}
          word_le_ones(p, rest)

# Every payload between the two surrogate endpoints violates the exclusion.
def surrogate_reject(+low: Word(11n),
  bad: {Bool.not(Bool.and(
    Cmp.is_ge(Word.cmp(11n, low, Word.zero(11n))),
    Cmp.is_le(Word.cmp(11n, low, Word.not(11n, Word.zero(11n)))))) == True{} : Bool}) ->
  {False{} == True{} : Bool}:
  %bad : {False{} == _ : Bool}
  %word_ge_zero(11n, low) :
    {False{} == Bool.not(Bool.and(_, Cmp.is_le(Word.cmp(11n, low, Word.not(11n, Word.zero(11n)))))) : Bool}
  %Equal.sym(Bool, Cmp.is_le(Word.cmp(11n, low, Word.not(11n, Word.zero(11n)))),
    True{}, word_le_ones(11n, low)) : {False{} == Bool.not(_) : Bool}
  {==}

# Remove the universally true lower bound when proving properties of the
# explicit inclusive codepoint range in the laws.
def codepoint_upper(+value: U32) ->
  {U32.is_le(value, Laws.hex_u32("0010FFFF", {==})) == Laws.codepoint_valid(value) : Bool}:
  %u32_ge_zero(value) :
    {U32.is_le(value, Laws.hex_u32("0010FFFF", {==})) ==
      Bool.and(_, U32.is_le(value, Laws.hex_u32("0010FFFF", {==}))) : Bool}
  {==}

def codepoint_bound(+value: U32,
  upper: {U32.is_le(value, Laws.hex_u32("0010FFFF", {==})) == True{} : Bool}) ->
  {Laws.codepoint_valid(value) == True{} : Bool}:
  %codepoint_upper(value) : {_ == True{} : Bool}
  upper

def codepoint_upper_evidence(+value: U32,
  bound: {Laws.codepoint_valid(value) == True{} : Bool}) ->
  {U32.is_le(value, Laws.hex_u32("0010FFFF", {==})) == True{} : Bool}:
  %bound : {U32.is_le(value, Laws.hex_u32("0010FFFF", {==})) == _ : Bool}
  codepoint_upper(value)

# Each UTF-8 range denotes a bounded codepoint outside the surrogate range.
def Laws.code_valid(s):
  match s:
    case Laws.Ascii{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WNil{}}}}}}}}}:
      (codepoint_bound(Laws.range_value(s), {==}), {==})
    case Laws.Two8{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WNil{}}}}}}}}}:
      (codepoint_bound(Laws.range_value(s), {==}), {==})
    case Laws.Two9{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WNil{}}}}}}}}}}:
      (codepoint_bound(Laws.range_value(s), {==}), {==})
    case Laws.Two10{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WNil{}}}}}}}}}}}:
      (codepoint_bound(Laws.range_value(s), {==}), {==})
    case Laws.Two11{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WNil{}}}}}}}}}}}}:
      (codepoint_bound(Laws.range_value(s), {==}), {==})
    case Laws.Three12{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WNil{}}}}}}}}}}}}}:
      (codepoint_bound(Laws.range_value(s), {==}), {==})
    case Laws.Three13{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WNil{}}}}}}}}}}}}}}:
      (codepoint_bound(Laws.range_value(s), {==}), {==})
    case Laws.Three14{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WNil{}}}}}}}}}}}}}}}:
      (codepoint_bound(Laws.range_value(s), {==}), {==})
    case Laws.Three15{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WNil{}}}}}}}}}}}}}}}}:
      (codepoint_bound(Laws.range_value(s), {==}), {==})
    case Laws.Three16a{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WNil{}}}}}}}}}}}}}}}}:
      (codepoint_bound(Laws.range_value(s), {==}), {==})
    case Laws.Three16b{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WNil{}}}}}}}}}}}}}}:
      (codepoint_bound(Laws.range_value(s), {==}), {==})
    case Laws.Three16c{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WNil{}}}}}}}}}}}}}:
      (codepoint_bound(Laws.range_value(s), {==}), {==})
    case Laws.Three16d{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WNil{}}}}}}}}}}}}}}}:
      (codepoint_bound(Laws.range_value(s), {==}), {==})
    case Laws.Four17{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WNil{}}}}}}}}}}}}}}}}}}:
      (codepoint_bound(Laws.range_value(s), {==}), {==})
    case Laws.Four18{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WNil{}}}}}}}}}}}}}}}}}}}:
      (codepoint_bound(Laws.range_value(s), {==}), {==})
    case Laws.Four19{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WNil{}}}}}}}}}}}}}}}}}}}}:
      (codepoint_bound(Laws.range_value(s), {==}), {==})
    case Laws.Four20{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WNil{}}}}}}}}}}}}}}}}}}}}}:
      (codepoint_bound(Laws.range_value(s), {==}), {==})
    case Laws.Four21{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WNil{}}}}}}}}}}}}}}}}}}:
      (codepoint_bound(Laws.range_value(s), word_le_ones(16n, WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WNil{}}}}}}}}}}}}}}}}})), {==})


def range_bound(+s: Laws.Utf8RangeValue) ->
  {Laws.codepoint_valid(Laws.range_value(s)) == True{} : Bool}:
  Pair.fst({Laws.codepoint_valid(Laws.range_value(s)) == True{} : Bool},
    {Laws.not_surrogate_value(Laws.range_value(s)) == True{} : Bool}, Laws.code_valid(s))

# Expose arbitrary symbolic low bits for each scalar interval. Reduction
# then checks the actual byte transitions; these are not sampled scalars.
def scalar_step(s: Laws.Utf8RangeValue, -text: String) ->
  {List.foldl(~&2, ~U32, ~UTF8.Acc,
    ~(acc => b => UTF8.step(acc, b)), Laws.scalar_bytes(s), UTF8.Acc{UTF8.new(), text}) ==
    UTF8.Acc{UTF8.new(), SCon{Chr{Laws.scalar_value(Laws.code(s))}, text}} : UTF8.Acc}:
  match s:
    case Laws.Ascii{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WNil{}}}}}}}}}:
      {==}
    case Laws.Two8{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WNil{}}}}}}}}}:
      {==}
    case Laws.Two9{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WNil{}}}}}}}}}}:
      {==}
    case Laws.Two10{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WNil{}}}}}}}}}}}:
      {==}
    case Laws.Two11{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WNil{}}}}}}}}}}}}:
      {==}
    case Laws.Three12{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WNil{}}}}}}}}}}}}}:
      {==}
    case Laws.Three13{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WNil{}}}}}}}}}}}}}}:
      {==}
    case Laws.Three14{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WNil{}}}}}}}}}}}}}}}:
      {==}
    case Laws.Three15{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WNil{}}}}}}}}}}}}}}}}:
      {==}
    case Laws.Three16a{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WNil{}}}}}}}}}}}}}}}}:
      {==}
    case Laws.Three16b{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WNil{}}}}}}}}}}}}}}:
      {==}
    case Laws.Three16c{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WNil{}}}}}}}}}}}}}:
      {==}
    case Laws.Three16d{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WNil{}}}}}}}}}}}}}}}:
      {==}
    case Laws.Four17{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WNil{}}}}}}}}}}}}}}}}}}:
      {==}
    case Laws.Four18{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WNil{}}}}}}}}}}}}}}}}}}}:
      {==}
    case Laws.Four19{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WNil{}}}}}}}}}}}}}}}}}}}}:
      {==}
    case Laws.Four20{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WNil{}}}}}}}}}}}}}}}}}}}}}:
      {==}
    case Laws.Four21{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WNil{}}}}}}}}}}}}}}}}}}:
      {==}

def scalar_encode(s: Laws.Utf8RangeValue, -tail: String) ->
  {UTF8.encode(SCon{Chr{Laws.scalar_value(Laws.code(s))}, tail}) ==
    List.append(&2, U32, Laws.scalar_bytes(s), UTF8.encode(tail)) : List<&2, U32>}:
  match s:
    case Laws.Ascii{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WNil{}}}}}}}}}:
      {==}
    case Laws.Two8{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WNil{}}}}}}}}}:
      {==}
    case Laws.Two9{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WNil{}}}}}}}}}}:
      {==}
    case Laws.Two10{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WNil{}}}}}}}}}}}:
      {==}
    case Laws.Two11{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WNil{}}}}}}}}}}}}:
      {==}
    case Laws.Three12{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WNil{}}}}}}}}}}}}}:
      {==}
    case Laws.Three13{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WNil{}}}}}}}}}}}}}}:
      {==}
    case Laws.Three14{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WNil{}}}}}}}}}}}}}}}:
      {==}
    case Laws.Three15{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WNil{}}}}}}}}}}}}}}}}:
      {==}
    case Laws.Three16a{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WNil{}}}}}}}}}}}}}}}}:
      {==}
    case Laws.Three16b{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WNil{}}}}}}}}}}}}}}:
      {==}
    case Laws.Three16c{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WNil{}}}}}}}}}}}}}:
      {==}
    case Laws.Three16d{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WNil{}}}}}}}}}}}}}}}:
      {==}
    case Laws.Four17{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WNil{}}}}}}}}}}}}}}}}}}:
      {==}
    case Laws.Four18{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WNil{}}}}}}}}}}}}}}}}}}}:
      {==}
    case Laws.Four19{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WNil{}}}}}}}}}}}}}}}}}}}}:
      {==}
    case Laws.Four20{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WNil{}}}}}}}}}}}}}}}}}}}}}:
      {==}
    case Laws.Four21{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WNil{}}}}}}}}}}}}}}}}}}:
      {==}

# A fold over concatenated byte lists is the composition of the two folds.
def scan_append(xs: List<&2, U32>, -ys: List<&2, U32>, -acc: UTF8.Acc) ->
  {Laws.scan(ys, Laws.scan(xs, acc)) ==
    Laws.scan(List.append(&2, U32, xs, ys), acc) : UTF8.Acc}:
  match xs:
    case Nil{}:
      {==}
    case h <> t:
      scan_append(t, ys, UTF8.step(acc, h))

# Reversing while prepending an accumulator distributes over append.
def string_assoc(a: String, -b: String, -c: String) ->
  {String.append(String.append(a, b), c) == String.append(a, String.append(b, c)) : String}:
  match a:
    case SNil{}:
      {==}
    case SCon{h, t}:
      %string_assoc(t, b, c) : {SCon{h, String.append(String.append(t, b), c)} == SCon{h, _} : String}
      {==}

def reverse_acc(+xs: String, -acc: String) ->
  {String.append(String.reverse(xs), acc) == String.reverse.go(xs, acc) : String}:
  match xs:
    case SNil{}:
      {==}
    case SCon{h, t}:
      %reverse_acc(t, SCon{h, acc}) : {String.append(String.reverse.go(t, SCon{h, ""}), acc) == _ : String}
      %reverse_acc(t, SCon{h, ""}) : {String.append(_, acc) == String.append(String.reverse(t), SCon{h, acc}) : String}
      string_assoc(String.reverse(t), SCon{h, ""}, acc)

def reverse_append(+a: String, +b: String) ->
  {String.append(String.reverse(b), String.reverse(a)) == String.reverse(String.append(a, b)) : String}:
  match a:
    case SNil{}:
      reverse_acc(b, "")
    case SCon{h, t}:
      %reverse_acc(String.append(t, b), SCon{h, ""}) : {String.append(String.reverse(b), String.reverse.go(t, SCon{h, ""})) == _ : String}
      %reverse_append(t, b) : {String.append(String.reverse(b), String.reverse.go(t, SCon{h, ""})) == String.append(_, SCon{h, ""}) : String}
      %reverse_acc(t, SCon{h, ""}) : {String.append(String.reverse(b), _) == String.append(String.append(String.reverse(b), String.reverse(t)), SCon{h, ""}) : String}
      Equal.sym(String,
        String.append(String.append(String.reverse(b), String.reverse(t)), SCon{h, ""}),
        String.append(String.reverse(b), String.append(String.reverse(t), SCon{h, ""})),
        string_assoc(String.reverse(b), String.reverse(t), SCon{h, ""}))

def reverse_reverse(+a: String) -> {String.reverse(String.reverse(a)) == a : String}:
  match a:
    case SNil{}:
      {==}
    case SCon{h, t}:
      %reverse_acc(t, SCon{h, ""}) : {String.reverse(_) == SCon{h, t} : String}
      %reverse_append(String.reverse(t), SCon{h, ""}) : {_ == SCon{h, t} : String}
      %reverse_reverse(t) : {SCon{h, String.reverse(String.reverse(t))} == SCon{h, _} : String}
      {==}

def append_nil(a: String) -> {String.append(a, "") == a : String}:
  match a:
    case SNil{}:
      {==}
    case SCon{h, t}:
      %append_nil(t) : {SCon{h, String.append(t, "")} == SCon{h, _} : String}
      {==}

def extend_assoc(acc: UTF8.Acc, -a: String, -b: String) ->
  {UTF8.extend(UTF8.extend(acc, a), b) == UTF8.extend(acc, String.append(a, b)) : UTF8.Acc}:
  UTF8.Acc{state, text} = acc
  Equal.cong(String, UTF8.Acc, s => UTF8.Acc{state, s},
    String.append(String.append(text, a), b), String.append(text, String.append(a, b)),
    string_assoc(text, a, b))

def step_extend(acc: UTF8.Acc, b: U32, -pre: String) ->
  {UTF8.extend(UTF8.step(acc, b), pre) == UTF8.step(UTF8.extend(acc, pre), b) : UTF8.Acc}:
  UTF8.Acc{state, text} = acc
  extend_assoc(UTF8.byte(state, b, ""), text, pre)

def scan_extend(+xs: List<&2, U32>, +acc: UTF8.Acc, -pre: String) ->
  {UTF8.extend(Laws.scan(xs, acc), pre) == Laws.scan(xs, UTF8.extend(acc, pre)) : UTF8.Acc}:
  match xs:
    case Nil{}:
      {==}
    case h <> t:
      %step_extend(acc, h, pre) : {UTF8.extend(Laws.scan(t, UTF8.step(acc, h)), pre) == Laws.scan(t, _) : UTF8.Acc}
      scan_extend(t, UTF8.step(acc, h), pre)

def render_extend(acc: UTF8.Acc, +pre: String) ->
  {Laws.render(UTF8.extend(acc, pre)) == String.append(String.reverse(pre), Laws.render(acc)) : String}:
  UTF8.Acc{state, text} = acc
  %reverse_append(text, pre) : {String.append(_, UTF8.done(state)) == String.append(String.reverse(pre), String.append(String.reverse(text), UTF8.done(state))) : String}
  string_assoc(String.reverse(pre), String.reverse(text), UTF8.done(state))

# One chunk: account for the accumulated text before continuing with rest.
def decoded_scan_next(+rest: List<&2, List<&2, U32>>, acc: UTF8.Acc,
  ih: @state: UTF8.State ->
    {Laws.render(Laws.scan(Laws.flatten(rest), UTF8.Acc{state, ""})) == Laws.decoded(rest, state) : String}) ->
  {Laws.render(Laws.scan(Laws.flatten(rest), acc)) ==
    Laws.decoded_next(UTF8.finish(acc), state => Laws.decoded(rest, state)) : String}:
  UTF8.Acc{+state, +text} = acc
  %ih(state) : {Laws.render(Laws.scan(Laws.flatten(rest), UTF8.Acc{state, text})) == String.append(String.reverse(text), _) : String}
  %scan_extend(Laws.flatten(rest), UTF8.Acc{state, ""}, text) : {Laws.render(_) == String.append(String.reverse(text), Laws.render(Laws.scan(Laws.flatten(rest), UTF8.Acc{state, ""}))) : String}
  render_extend(Laws.scan(Laws.flatten(rest), UTF8.Acc{state, ""}), text)

# This holds for arbitrary bytes and starting state, not just valid UTF-8.
# In particular, neither empty chunks nor splitting a scalar changes output.
def decoded_scan(+chunks: List<&2, List<&2, U32>>, +state: UTF8.State) ->
  {Laws.render(Laws.scan(Laws.flatten(chunks), UTF8.Acc{state, ""})) == Laws.decoded(chunks, state) : String}:
  match chunks:
    case Nil{}:
      {==}
    case chunk <> rest:
      %scan_append(chunk, Laws.flatten(rest), UTF8.Acc{state, ""}) : {Laws.render(_) == Laws.decoded_next(UTF8.feed(state, chunk), next => Laws.decoded(rest, next)) : String}
      decoded_scan_next(rest, Laws.scan(chunk, UTF8.Acc{state, ""}),
        next => decoded_scan(rest, next))

# Canonical scalar sequences return to the idle state after each scalar.
def scan_wire(+chars: List<&2, Laws.Utf8RangeValue>, -pre: String) ->
  {Laws.scan(Laws.wire(chars), UTF8.Acc{UTF8.new(), pre}) ==
    UTF8.Acc{UTF8.new(), String.reverse.go(Laws.text(chars), pre)} : UTF8.Acc}:
  match chars:
    case Nil{}:
      {==}
    case s <> rest:
      %scan_append(Laws.scalar_bytes(s), Laws.wire(rest), UTF8.Acc{UTF8.new(), pre}) : {_ == UTF8.Acc{UTF8.new(), String.reverse.go(Laws.text(rest), SCon{Chr{Laws.scalar_value(Laws.code(s))}, pre})} : UTF8.Acc}
      %Equal.sym(UTF8.Acc,
        Laws.scan(Laws.scalar_bytes(s), UTF8.Acc{UTF8.new(), pre}),
        UTF8.Acc{UTF8.new(), SCon{Chr{Laws.scalar_value(Laws.code(s))}, pre}}, scalar_step(s, pre)) :
        {Laws.scan(Laws.wire(rest), _) == UTF8.Acc{UTF8.new(), String.reverse.go(Laws.text(rest), SCon{Chr{Laws.scalar_value(Laws.code(s))}, pre})} : UTF8.Acc}
      scan_wire(rest, SCon{Chr{Laws.scalar_value(Laws.code(s))}, pre})

def encode_wire(+chars: List<&2, Laws.Utf8RangeValue>) ->
  {UTF8.encode(Laws.text(chars)) == Laws.wire(chars) : List<&2, U32>}:
  match chars:
    case Nil{}:
      {==}
    case s <> rest:
      %Equal.sym(List<&2, U32>,
        UTF8.encode(SCon{Chr{Laws.scalar_value(Laws.code(s))}, Laws.text(rest)}),
        List.append(&2, U32, Laws.scalar_bytes(s), UTF8.encode(Laws.text(rest))),
        scalar_encode(s, Laws.text(rest))) : {_ == List.append(&2, U32, Laws.scalar_bytes(s), Laws.wire(rest)) : List<&2, U32>}
      %encode_wire(rest) : {List.append(&2, U32, Laws.scalar_bytes(s), UTF8.encode(Laws.text(rest))) == List.append(&2, U32, Laws.scalar_bytes(s), _) : List<&2, U32>}
      {==}

def render_closed(+text: String) ->
  {Laws.render(UTF8.Acc{UTF8.new(), String.reverse(text)}) == text : String}:
  %reverse_reverse(text) : {String.append(String.reverse(String.reverse(text)), "") == _ : String}
  append_nil(String.reverse(String.reverse(text)))

def render_wire(+chars: List<&2, Laws.Utf8RangeValue>) ->
  {Laws.render(Laws.scan(Laws.wire(chars), UTF8.Acc{UTF8.new(), ""})) == Laws.text(chars) : String}:
  Equal.trans(String,
    Laws.render(Laws.scan(Laws.wire(chars), UTF8.Acc{UTF8.new(), ""})),
    Laws.render(UTF8.Acc{UTF8.new(), String.reverse(Laws.text(chars))}), Laws.text(chars),
    Equal.cong(UTF8.Acc, String, acc => Laws.render(acc),
      Laws.scan(Laws.wire(chars), UTF8.Acc{UTF8.new(), ""}),
      UTF8.Acc{UTF8.new(), String.reverse(Laws.text(chars))}, scan_wire(chars, "")),
    render_closed(Laws.text(chars)))

# Arbitrary chunk boundaries, with no restriction on chunk count or size.
# Validity supplies only canonical bytes, never any round-trip assumption.
def Laws.roundtrip(chunks, valid):
  (+chars, wire_eq) = valid
  %decoded_scan(chunks, UTF8.new()) : {UTF8.encode(_) == Laws.flatten(chunks) : List<&2, U32>}
  %wire_eq : {UTF8.encode(Laws.render(Laws.scan(_, UTF8.Acc{UTF8.new(), ""}))) == _ : List<&2, U32>}
  %Equal.sym(String,
    Laws.render(Laws.scan(Laws.wire(chars), UTF8.Acc{UTF8.new(), ""})), Laws.text(chars),
    render_wire(chars)) : {UTF8.encode(_) == Laws.wire(chars) : List<&2, U32>}
  encode_wire(chars)

def split_transport(+chunks: List<&2, List<&2, U32>>, -bytes: List<&2, U32>,
  split: {Laws.flatten(chunks) == bytes : List<&2, U32>}) ->
  Laws.Valid(bytes) -> {UTF8.encode(Laws.decoded(chunks, UTF8.new())) == bytes : List<&2, U32>}:
  %split : (Laws.Valid(_) -> {UTF8.encode(Laws.decoded(chunks, UTF8.new())) == _ : List<&2, U32>})
  valid => Laws.roundtrip(chunks, valid)

def Laws.split_roundtrip(bytes, chunks, valid, split):
  split_transport(chunks, bytes, split)(valid)

# The four byte layouts plus the three independent rules are equivalent
# to Utf8RangeValue: soundness never assumes a rule, completeness assumes only them.
def Laws.scalar_sound(s):
  match s:
    case Laws.Ascii{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WNil{}}}}}}}}}:
      (({==}, {==}, range_bound(s)), {==})
    case Laws.Two8{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WNil{}}}}}}}}}:
      (({==}, {==}, range_bound(s)), {==})
    case Laws.Two9{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WNil{}}}}}}}}}}:
      (({==}, {==}, range_bound(s)), {==})
    case Laws.Two10{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WNil{}}}}}}}}}}}:
      (({==}, {==}, range_bound(s)), {==})
    case Laws.Two11{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WNil{}}}}}}}}}}}}:
      (({==}, {==}, range_bound(s)), {==})
    case Laws.Three12{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WNil{}}}}}}}}}}}}}:
      (({==}, {==}, range_bound(s)), {==})
    case Laws.Three13{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WNil{}}}}}}}}}}}}}}:
      (({==}, {==}, range_bound(s)), {==})
    case Laws.Three14{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WNil{}}}}}}}}}}}}}}}:
      (({==}, {==}, range_bound(s)), {==})
    case Laws.Three15{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WNil{}}}}}}}}}}}}}}}}:
      (({==}, {==}, range_bound(s)), {==})
    case Laws.Three16a{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WNil{}}}}}}}}}}}}}}}}:
      (({==}, {==}, range_bound(s)), {==})
    case Laws.Three16b{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WNil{}}}}}}}}}}}}}}:
      (({==}, {==}, range_bound(s)), {==})
    case Laws.Three16c{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WNil{}}}}}}}}}}}}}:
      (({==}, {==}, range_bound(s)), {==})
    case Laws.Three16d{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WNil{}}}}}}}}}}}}}}}:
      (({==}, {==}, range_bound(s)), {==})
    case Laws.Four17{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WNil{}}}}}}}}}}}}}}}}}}:
      (({==}, {==}, range_bound(s)), {==})
    case Laws.Four18{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WNil{}}}}}}}}}}}}}}}}}}}:
      (({==}, {==}, range_bound(s)), {==})
    case Laws.Four19{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WNil{}}}}}}}}}}}}}}}}}}}}:
      (({==}, {==}, range_bound(s)), {==})
    case Laws.Four20{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WNil{}}}}}}}}}}}}}}}}}}}}}:
      (({==}, {==}, range_bound(s)), {==})
    case Laws.Four21{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WNil{}}}}}}}}}}}}}}}}}}:
      (({==}, {==}, range_bound(s)), {==})

# A failed Boolean rule cannot be supplied as evidence of acceptance.
def reject(-A: Type, failed: {False{} == True{} : Bool}) -> A:
  %failed : Bool.pick(Type, _, A, Unit)
  Unit{}

def rejected_pattern(-p: Laws.Pattern, failed: {False{} == True{} : Bool}) ->
  (&s: Laws.Utf8RangeValue -> {Laws.scalar_bytes(s) == Laws.pattern_bytes(p) : List<&2, U32>}):
  reject((&s: Laws.Utf8RangeValue -> {Laws.scalar_bytes(s) == Laws.pattern_bytes(p) : List<&2, U32>}), failed)

def Laws.scalar_complete(p, checks):
  match p:
    case Laws.One{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WNil{}}}}}}}}}:
      (Laws.Ascii{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WNil{}}}}}}}}}, {==})
    case Laws.Two{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}:
      (short, surrogate, bound) = checks
      rejected_pattern(p, short)
    case Laws.Two{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}:
      (Laws.Two8{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WNil{}}}}}}}}}, {==})
    case Laws.Two{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{True{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}:
      (Laws.Two9{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WNil{}}}}}}}}}}, {==})
    case Laws.Two{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}}}}}:
      (Laws.Two10{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WNil{}}}}}}}}}}}, {==})
    case Laws.Two{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{True{}, WNil{}}}}}}}}}}}}}:
      (Laws.Two11{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WNil{}}}}}}}}}}}}, {==})
    case Laws.Three{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}:
      (short, surrogate, bound) = checks
      rejected_pattern(p, short)
    case Laws.Three{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}:
      (Laws.Three12{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WNil{}}}}}}}}}}}}}, {==})
    case Laws.Three{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}:
      (Laws.Three13{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WNil{}}}}}}}}}}}}}}, {==})
    case Laws.Three{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{True{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}:
      (Laws.Three14{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WNil{}}}}}}}}}}}}}}}, {==})
    case Laws.Three{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}:
      (Laws.Three15{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WNil{}}}}}}}}}}}}}}}}, {==})
    case Laws.Three{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}}}}}}}}}}:
      (Laws.Three16a{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WNil{}}}}}}}}}}}}}}}}, {==})
    case Laws.Three{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}}}}}}}}}}:
      (Laws.Three16b{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WNil{}}}}}}}}}}}}}}, {==})
    case Laws.Three{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}}}}}}}}}}:
      (Laws.Three16c{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WNil{}}}}}}}}}}}}}, {==})
    case Laws.Three{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}}}}}}}}}}:
      (short, surrogate, bound) = checks
      rejected_pattern(p, surrogate_reject(WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WNil{}}}}}}}}}}}}, surrogate))
    case Laws.Three{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{True{}, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}}}}}}}}}}:
      (Laws.Three16d{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WNil{}}}}}}}}}}}}}}}, {==})
    case Laws.Four{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}:
      (short, surrogate, bound) = checks
      rejected_pattern(p, short)
    case Laws.Four{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}:
      (Laws.Four17{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WNil{}}}}}}}}}}}}}}}}}}, {==})
    case Laws.Four{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}:
      (Laws.Four18{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WNil{}}}}}}}}}}}}}}}}}}}, {==})
    case Laws.Four{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{True{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}:
      (Laws.Four19{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WNil{}}}}}}}}}}}}}}}}}}}}, {==})
    case Laws.Four{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}:
      (Laws.Four20{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WNil{}}}}}}}}}}}}}}}}}}}}}, {==})
    case Laws.Four{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}:
      (Laws.Four21{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WNil{}}}}}}}}}}}}}}}}}}, {==})
    case Laws.Four{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}:
      (short, surrogate, bound) = checks
      rejected_pattern(p, codepoint_upper_evidence(Laws.pattern_code(p), bound))
    case Laws.Four{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}:
      (short, surrogate, bound) = checks
      rejected_pattern(p, codepoint_upper_evidence(Laws.pattern_code(p), bound))
    case Laws.Four{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{True{}, WCon{False{}, WCon{True{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}:
      (short, surrogate, bound) = checks
      rejected_pattern(p, codepoint_upper_evidence(Laws.pattern_code(p), bound))
    case Laws.Four{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{True{}, WCon{True{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}:
      (short, surrogate, bound) = checks
      rejected_pattern(p, codepoint_upper_evidence(Laws.pattern_code(p), bound))

def scalar_rules_next(+s: Laws.Utf8RangeValue,
  sound: Laws.Checks(Laws.representation(s)) &
    {Laws.pattern_bytes(Laws.representation(s)) == Laws.scalar_bytes(s) : List<&2, U32>}) ->
  Laws.RuleScalar(Laws.scalar_bytes(s)):
  (checks, eq) = sound
  (Laws.representation(s), eq, checks)

def Laws.scalar_rules(s):
  scalar_rules_next(s, Laws.scalar_sound(s))

def rules_scalar_next(-bytes: List<&2, U32>, -p: Laws.Pattern,
  eq: {Laws.pattern_bytes(p) == bytes : List<&2, U32>},
  complete: (&s: Laws.Utf8RangeValue -> {Laws.scalar_bytes(s) == Laws.pattern_bytes(p) : List<&2, U32>})) ->
  (&s: Laws.Utf8RangeValue -> {Laws.scalar_bytes(s) == bytes : List<&2, U32>}):
  (s, proof) = complete
  (s, Equal.trans(List<&2, U32>, Laws.scalar_bytes(s), Laws.pattern_bytes(p), bytes, proof, eq))

def Laws.rules_scalar(bytes, valid):
  (p, eq, checks) = valid
  rules_scalar_next(bytes, p, eq, Laws.scalar_complete(p, checks))

def append_eq(-a: List<&2, U32>, -b: List<&2, U32>, -c: List<&2, U32>, -d: List<&2, U32>,
  ab: {a == b : List<&2, U32>}, cd: {c == d : List<&2, U32>}) ->
  {List.append(&2, U32, a, c) == List.append(&2, U32, b, d) : List<&2, U32>}:
  %ab : {List.append(&2, U32, a, c) == List.append(&2, U32, _, d) : List<&2, U32>}
  %cd : {List.append(&2, U32, a, c) == List.append(&2, U32, a, _) : List<&2, U32>}
  {==}

def patterns_complete_next(-p: Laws.Pattern, -rest: List<&2, Laws.Pattern>,
  head: (&s: Laws.Utf8RangeValue -> {Laws.scalar_bytes(s) == Laws.pattern_bytes(p) : List<&2, U32>}),
  tail: (&ss: List<&2, Laws.Utf8RangeValue> -> {Laws.wire(ss) == Laws.pattern_wire(rest) : List<&2, U32>})) ->
  (&ss: List<&2, Laws.Utf8RangeValue> -> {Laws.wire(ss) == Laws.pattern_wire(p <> rest) : List<&2, U32>}):
  (s, head_eq) = head
  (ss, tail_eq) = tail
  (s <> ss, append_eq(Laws.scalar_bytes(s), Laws.pattern_bytes(p), Laws.wire(ss), Laws.pattern_wire(rest), head_eq, tail_eq))

def patterns_complete(patterns: List<&2, Laws.Pattern>, checks: Laws.PatternChecks(patterns)) ->
  (&ss: List<&2, Laws.Utf8RangeValue> -> {Laws.wire(ss) == Laws.pattern_wire(patterns) : List<&2, U32>}):
  match patterns:
    case Nil{}:
      (Nil{}, {==})
    case p <> rest:
      (head_checks, tail_checks) = checks
      patterns_complete_next(p, rest, Laws.scalar_complete(p, head_checks), patterns_complete(rest, tail_checks))

def rules_valid_next(-bytes: List<&2, U32>, -patterns: List<&2, Laws.Pattern>,
  eq: {Laws.pattern_wire(patterns) == bytes : List<&2, U32>},
  complete: (&ss: List<&2, Laws.Utf8RangeValue> -> {Laws.wire(ss) == Laws.pattern_wire(patterns) : List<&2, U32>})) -> Laws.Valid(bytes):
  (ss, proof) = complete
  (ss, Equal.trans(List<&2, U32>, Laws.wire(ss), Laws.pattern_wire(patterns), bytes, proof, eq))

def Laws.rules_valid(bytes, valid):
  (patterns, checks, eq) = valid
  rules_valid_next(bytes, patterns, eq, patterns_complete(patterns, checks))

def Laws.rules_split_roundtrip(bytes, chunks, valid, split):
  Laws.split_roundtrip(bytes, chunks, Laws.rules_valid(bytes, valid), split)
