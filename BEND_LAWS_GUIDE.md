# Writing Specifications as Bend Laws

This guide describes an approach to writing specifications as Bend laws, for
any project that uses `LAWS.bend` / `PROOF.bend`. It was written against
Bend 2.0.39, and version-specific details are marked as such.

The examples come from a UTF-8 encoding project. That project has three
implementation modules, `binary.bend`, `hexdigits.bend` and `utf8.bend`,
imported as `B`, `H` and `UTF8`. The examples are illustrations; the
practices themselves are general.

The goal: the laws are a specification that a reader can trust. They state
what the code must do, clearly enough for a person to check against an
outside source (a standard, an RFC, a reference table). They are also strict
enough that `bend PROOF.bend` fails whenever the implementation is wrong.

---

## 1. Principles

The rest of this guide is tactics. Each tactic is worth using when it serves
these principles, and not otherwise.

### 1.1 Laws define correctness, not the implementation

> Laws must define correctness independently of implementation details. They
> may use implementation functions when the behavior relied upon is
> established by other independently specified and proved laws. Do not rely
> on behavior that those laws leave unspecified.

The danger this guards against: a law that uses the implementation to define
its own expected result can be "satisfied" by changing the implementation.

*Example:* suppose an encoding law's precondition is the implementation's
`can_encode(cp) == True`. Then making `can_encode` always return `False`
makes the law vacuously true.

Changing the implementation should be able to break proofs. It must never be
able to quietly change what the laws require.

**Why not be stricter.** A stricter version of the rule forbids
implementation calls in laws entirely. Every precondition and expected result
would then come from independent `*_spec` definitions. That works, but it
produces many parallel definitions that duplicate laws already present (see
§1.2). The rule above allows a law to call an implementation function `foo`
as long as it relies only on behavior that `foo`'s own laws pin down. For
example, once `law bit8_value` fixes exactly what `B.bit8_value` returns for
every input, other definitions can call `B.bit8_value` instead of keeping a
duplicate `bit8_value_spec`.

**The test to apply.** For each implementation call that appears in a law,
ask:

- Which law fixes the behavior I am relying on here?
- Does that law cover *every* input this use can reach, or just some?
- Could someone change this function, while its own laws still pass, so that
  this law's meaning changes?

If no law covers the behavior, either add one, or state the behavior
independently.

**Examples of the distinction:**

| Use in a law | Why it's acceptable or not |
|---|---|
| `B.first(UTF8.encode_as_two_bytes(cp, valid))` | OK: `law first` fixes `B.first` completely. |
| `H.hex_u32("D800", {==})` used as a constant | OK: `law hex_u32` fixes the value of every valid input. |
| A reference definition that used `B.bit32` to split a code point into bits | Violation: no law fixed `bit32`'s bit positions. |
| A reference definition that used `B.bit_to_char` to define a binary string | Violation: nothing fixed `False → '0'`, `True → '1'`. |

"Merely having laws for `foo`" is not enough: the *particular* properties
being used must be covered.

### 1.2 One source of truth

Aim to describe each fact once, and to derive what depends on it from that
description. Two independent descriptions of the same thing can drift
apart, and then the laws contradict each other or quietly allow mismatched
behavior.

This is a goal to balance against readability (§1.3), not an absolute rule.
Restating something is fine when it makes the spec clearer or gives a
useful cross-check. A restatement inside the laws can't drift unnoticed,
because the proofs have to show it agrees with the primary description.
What to avoid is a duplicate that nothing checks, or a restatement that adds
volume without adding clarity. When you do restate, make clear which
description is primary. For example:

- **Example laws restate concrete values**, which makes the spec easier to
  check at a glance.
- **Diagrams in comments** restate the table that the code encodes.
- **Redundant-check laws** (§6.2) restate a property in a second form.
- **A law can spell out a calculation** (`b7 * 128 + b6 * 64 + …`) instead
  of referring to a helper, when that makes the law self-explanatory.

Tactics that serve this principle:

- **Call an implementation function whose behavior is already fixed by a
  law**, instead of keeping a parallel `*_spec` copy. The rule in §1.1 is
  partly an application of this principle.
- **Layer concepts** (§4.4), defining each in terms of the ones before.
- **Define one direction and derive the other** (§5.5). For example, decoding
  can be defined as the inverse of encoding.

### 1.3 Make the spec easy to read and understand

The spec is what a person checks against the standard, so its value is only
as good as its readability. Write it so that a reader can confirm it against
the source without having to reconstruct it in their head.

Tactics that serve this principle:

- **Mirror the source's presentation** (§4.1).
- **Prefer stating a layout directly over computing it** (§4.3).
- **Give every law a plain-language comment** (§10).
- **Write examples in a sensible order, in the domain's notation** (§6.1).
- **Keep the specified surface small** by deriving where that stays clear,
  and restating where restating is clearer (§1.2).

### 1.4 A spec need not be an efficient algorithm

A spec can be written in a way that would be wildly inefficient, or not
computable at all, if the implementation followed it literally. That's
fine: the spec is checked by proof, not run. The implementation is written
separately for efficiency, and proved to agree with the spec.

Examples:

- A UTF-8 shape spec splits a `U32` into 32 booleans and pattern-matches
  them against the encoding table. The implementation uses shifts and masks.
- A hex-string spec builds a list of nibbles and then folds it. The
  implementation accumulates directly.
- "Decode is the code point whose encoding is these bytes" would, as an
  algorithm, search all 2³² code points. As a spec it's a single inverse
  law.
- `Exists` laws ("some code point produces this pair") describe no
  computation at all. The proof supplies the witness.

So choose a formulation by weighing clarity (§1.3) against a single source
of truth (§1.2). Don't choose one because it would run well.

---

## 2. File layout

| File | Contents |
|---|---|
| `<module>.bend` | Implementation modules: only what runs, plus the minimum lemmas the code needs to type-check. *Example:* `binary.bend`, `utf8.bend`. |
| `<module>_LAWS.bend` | Laws for one module or subject, when `LAWS.bend` would otherwise grow too large. *Example:* `binary_LAWS.bend`. |
| `LAWS.bend` | Laws for the project's main subject. It imports the `*_LAWS.bend` files it builds on. |
| `defs.bend` | Type aliases and definitions shared by several laws or implementation files. *Example:* `Bit8()`, a tuple of eight `Bool`. |
| `PROOF.bend` | Proofs of every law in every laws file, plus all proof-only helpers. |
| `AGENTS.md` | The independence rule (§1.1), for coding agents working on the project. |

How the files fit together:

- **Validation is `bend PROOF.bend`.** It must print `ALL PROOFS CHECK`.
  `--verdict` isn't needed for routine checks.
- **`PROOF.bend` imports every laws file** under an alias, and supplies
  each proof as `def Alias.law_name(...)`. For example, after
  `import ./binary_LAWS.bend as BinaryLaws`, it defines
  `def BinaryLaws.first(high, low): {==}`. Bend reports an unproved law, or
  an unimplemented operation, as a TODO in any imported laws file, not only
  in `LAWS.bend`.
- **`PROOF.bend` must import `./LAWS.bend`** when a `LAWS.bend` sits next to
  it. Bend enforces this.
- **Laws files import the implementation** (`import ./binary.bend as B`) and
  name its functions directly. This is how the Bend demos do it; for
  example, `demos/proof_insertion_sort/LAWS.bend` constrains `Sort.sort`.
- **Proof-only helpers go in `PROOF.bend`, not in the implementation.** This
  includes lemmas and lists of proofs that only a proof uses.
- **Put a type where it belongs.** A type shared by several files goes in
  `defs.bend`. A type that belongs to one subject goes at the top of that
  subject's laws file. *Example:* `Nibble` lives in `hexdigits_LAWS.bend`.
- **Group related definitions together** within a laws file: a reference
  definition, then the laws that use it, then their examples.

---

## 3. Don't use abstract functions

Bend allows a law whose body is just a type. For example, `law foo: for x: T`
with `U32` as the body declares an abstract function, and `PROOF.bend`
supplies its definition. **Don't use this to stand in for the
implementation.** It adds no independence: the correctness laws are what
define behavior. It also adds wiring. Worse, the laws then constrain whatever
`PROOF.bend` binds to the name, not necessarily the real implementation.

State laws about the imported implementation function directly. If an
abstract function seems necessary as an adapter between proofs, an
existential acceptance proof (§5.6) usually replaces it.

---

## 4. How to state the specification

### 4.1 Follow the authoritative source and write for the reader

The specification should read like the source it encodes.

*Example:* the UTF-8 two-byte shape follows the Wikipedia table bit for bit:

```bend
# 00000000 00000000 00000xxx yyyyzzzz -> 110xxxyy 10yyzzzz
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
```

The implementation is free to be different and efficient (§1.4). Here, it
uses shifts and masks. Don't rewrite the implementation to look like the
spec. Prove that they agree.

Aim for specs that are self-contained, simple, easy to follow and
non-repetitive.

### 4.2 Reference definitions

When a behavior is easiest to state as a computation, write a plain `def` in
the laws file, and write a law equating the implementation to it.

- **Tables**, for example a `match` from each hex digit character to its
  value.
- **Shapes**, for example a bit pattern from a standard (§4.1).
- **Partial functions**: a reference definition that returns `Maybe` gives
  `None` outside its domain (§5.3).
- **Folds**, for example a left fold `acc * 16 + digit` over a list of
  digits.

Keep a reference definition when it states something independently that is
clearer than the implementation. Delete it, and call the implementation
function instead, once the implementation is pinned down by a law that is
just as clear. For example, a duplicate `is_hex_digit_spec` is unnecessary
once `law is_hex_digit` defines `H.is_hex_digit` exactly.

### 4.3 Prefer stating a layout over computing it

A bit layout stated directly is easier to check than arithmetic that happens
to produce it:

- **Quantify over the individual bits** to state a layout. *Example:*
  `law u32_byte4` takes `for +b31: Bool` … `for +b0: Bool`, builds
  `U32{WCon{b0, …WCon{b31, WNil{}}}}`, and states which tuple of bytes comes
  out.
- **Quantify over a fixed-width `Word(n)`** to state "any value in this
  range" with no bound proof needed. *Example:* `for +bits: Word(11n)`
  covers exactly the eleven-bit values, such as the code points that fit in
  two UTF-8 bytes.
- **Quantify over the unused high bits** to say they are ignored. *Example:*
  `for rest_high: Word(24n)` shows that a byte-packing function discards
  everything above bit 7.
- **Say which end is first.** For example, "most significant first" for
  tuples and strings, and "Word stores its least significant bit first".

### 4.4 Separate concepts in layers

Define each concept once, then build later concepts on top of it, so that no
law has to re-derive the low-level details.

*Example:* the UTF-8 laws keep three ideas apart:

1. **Shape.** The bit pattern matches the encoding table. This deliberately
   includes overlong encodings, surrogates, and values above U+10FFFF.
2. **Capacity.** A code point *can* be written in this shape.
3. **Validity.** Shape plus shortest form. An overlong encoding is a
   two-byte shape whose code point also has a one-byte shape.

Define the vocabulary in a comment ("By a 'byte shape' we mean…"), and say
what each layer deliberately includes or excludes.

---

## 5. Law patterns

### 5.1 Exact equation

The most direct form: for every input, the function equals a stated
expression.

```bend
law is_binary_digit:
  for +c: Char
  {B.is_binary_digit(c) == (Char.is_eq('0', c) || Char.is_eq('1', c)) : Bool}
```

Validators are specified the same way, as a formula over `String.length`,
`List.all`, and so on:

```bend
law is_valid_hex_u32_input:
  for +s: String
  {H.is_valid_hex_u32(s) ==
    ((Nat.is_ge(String.length(s), 1n) && Nat.is_le(String.length(s), 8n)) &&
     List.all(~&2, ~Char, ~(c => H.is_hex_digit(c)), String.to_list(s))) : Bool}
```

### 5.2 Functions with preconditions take a proof

A function with a precondition takes a proof of it as its **last** argument,
**erased** with `-` so that it costs nothing at runtime:

```bend
def strbyte(+s: String, -valid: {valid_byte_string(s) == True{} : Bool}) -> U32
```

Callers with literal input pass `{==}`, so the precondition is checked when
the proofs are checked: `B.byte_mask("01xxxxxx", byte, {==})`. Name the proof
for what it proves. Use `valid` for a general precondition, a specific name
such as `valid_shape` when there are several kinds, and `accepted` for the
implementation-side proof in §5.6.

### 5.3 Partial reference definitions return `Maybe`

When a function is only defined on part of its domain, the reference
definition returns `None` outside it. Two laws then connect the
implementation:

```bend
# The capacity predicate agrees with the reference definition's domain.
law utf8_can_encode_as_two_bytes:
  for +cp: U32
  {UTF8.can_encode_as_two_bytes(cp) == Maybe.is_some(&1, U32 & U32, two_byte_shape(cp)) : Bool}

# Given the precondition, the result is the reference definition's Some value.
law utf8_encode_as_two_bytes:
  for +cp: U32
  for valid: {UTF8.can_encode_as_two_bytes(cp) == True{} : Bool}
  {Some{UTF8.encode_as_two_bytes(cp, valid)} == two_byte_shape(cp) : Maybe<&1, U32 & U32>}
```

Comparing `Some{f(x)}` against the reference definition avoids writing an
extractor with an impossible `None` branch inside the law.

### 5.4 Characterize predicates with "iff" and a witness

To say that a predicate is true exactly for the outputs a reference
definition can produce, state both directions with an `Exists` witness:

```bend
law utf8_has_two_byte_shape:
  for +b1: U32
  for +b2: U32
  representation = Exists(U32, cp =>
    {two_byte_shape(cp) == Some{(b1, b2)} : Maybe<&1, U32 & U32>})
  ({UTF8.has_two_byte_shape(b1, b2) == True{} : Bool} -> representation) &
  (representation -> {UTF8.has_two_byte_shape(b1, b2) == True{} : Bool})
```

Both directions matter. The first stops the predicate from accepting inputs
the reference definition never produces, because no witness exists for
them. The second stops it from rejecting inputs that the reference
definition does produce.

### 5.5 Specify one direction, define the other as its inverse

This tactic applies to pairs of functions that undo each other: encode and
decode, print and parse, serialize and deserialize. Give an independent spec
for only one direction: the one closest to the source and easiest to state.
Specify the other through its relationship to the first. This serves all
three principles:

- **One source of truth (§1.2).** There is no second description of the
  format to drift.
- **Readability (§1.3).** Only one table needs checking.
- **Efficiency is irrelevant (§1.4).** Run literally, the inverse would mean
  searching every input.

The implementation can still have separate encode and decode functions.

The tactic only applies when:

- **The specified direction is injective on its domain.** Otherwise "the
  inverse" isn't well defined.
- **Its outputs are characterized.** The decoder's domain is the set of
  outputs the encoder can produce, typically specified by an "iff" with a
  witness (§5.4).

To apply it, don't write "the unique `x` such that…". Instead, state two
inverse laws, each supplying the proof that its second call needs:

- **Decode after encode.** For an encodable input, the encoded output is in
  the decoder's domain, and decoding it returns the input.
- **Encode after decode.** For an input in the decoder's domain, the decoded
  value is encodable, and encoding it returns the original.

Together these make the encoder a bijection between its domain and its
outputs. Keep the encoder's own law against the reference definition: the
inverse laws relate the two functions, while that law fixes *which* encoding
they implement.

### 5.6 Spec-side precondition, implementation-side acceptance

When a law's precondition is a specification predicate rather than the
implementation's own validator, have the proof show that the implementation
accepts the input, using `exs`:

```bend
law hex_u32:
  for +s: String
  for valid: {H.is_valid_hex_u32(s) == True{} : Bool}
  exs accepted: {H.is_valid_hex_u32(s) == True{} : Bool}
  {H.hex_u32(s, accepted) == hex_u32_spec(s) : U32}
```

The law then quantifies over the *specified* inputs, and the proof must show
that the implementation accepts each one. When the validator is itself fixed
by a law, the two predicates can be the same (as here). Keeping the pattern
lets the precondition change to a reference predicate without restructuring
the law.

### 5.7 An existential witness for a reference parse

To use an intermediate structure in a law without an extractor, state that it
exists and pin it down:

```bend
law strbyte:
  for +s: String
  for +valid: {B.valid_byte_string(s) == True{} : Bool}
  exs accepted: {B.valid_byte_string(s) == True{} : Bool}
  exs bits: Defs.Bit8()
  {Some{bits} == str_bit8(s) : Maybe<&1, Defs.Bit8()>} &
  {B.strbyte(s, accepted) == B.bit8_value(bits) : U32}
```

### 5.8 Choose `v = …`, `exs`, or `Exists(…)`

| Form | Meaning | Who supplies the value |
|---|---|---|
| `+v = f(x, valid)` | `v` *is* this value | The law fixes it |
| `exs v: T` | A value with these properties exists | The proof |
| `Exists(T, v => …)` | Same as `exs`, but usable inside an expression or after local bindings | The proof |

`exs` clauses must come before the law's body, so use `Exists` when the
witness depends on a local binding. `@name: A -> B` names the hypothesis of
an implication so that `B` can mention it, for example when `B` needs to
pass that proof to a function.

### 5.9 Laws can use other laws as proof terms

A law may build a proof that its statement needs, such as the proof
argument of a function it calls, from other laws inside its own statement.

In `PROOF.bend`, laws are likewise reused as lemmas by calling
`Laws.name(...)`. *Example:* given `produced`, a proof that the reference
table maps `cp` to `Some{(b1, b2)}`, a proof obtains evidence that `cp` is
accepted by chaining the capacity law with that fact:

```bend
accepted = Equal.trans(Bool, UTF8.can_encode_as_two_bytes(cp),
  Maybe.is_some(&1, U32 & U32, Laws.two_byte_shape(cp)), True{}, Laws.utf8_can_encode_as_two_bytes(cp),
  Equal.cong(Maybe<&1, U32 & U32>, Bool, shape => Maybe.is_some(&1, U32 & U32, shape),
    Laws.two_byte_shape(cp), Some{(b1, b2)}, produced))
```

---

## 6. Examples and redundant checks

### 6.1 Example laws

Every specified function gets a `<name>_examples` law of concrete cases,
proved with `{==}`.

- **Order the examples sensibly**, for example numerically.
- **Include boundaries on both sides.** For example, `D7FF`/`D800` and
  `DFFF`/`E000` for the surrogate range.
- **Include negative cases.** For example, an empty string, a string one
  character too long, an invalid character, and an out-of-range value.
- **Make examples read like the domain.** If the domain writes values in
  hex, write them in hex (here, through `H.hex_u32("D800", {==})`). Keep
  notation consistent within one expression. For example, give all hex
  literals in an expression the same width, dropping only the leading zeros
  that *every* literal in it can lose: `"000000"` and `"10FFFF"`, not `"0"`
  and `"10FFFF"`.
- **Keep an example that demonstrates a property**, even if it looks
  redundant. For example, `"0000000A"` next to `"A"` shows left-padding.

### 6.2 Redundant checks are labeled

Extra laws that the main specification already implies are welcome as
cross-checks, but say so in a comment:

- **Alternative formulations.** For example, computing a byte's value via
  `Word(8n)` → `Word.to_nat` → `U32.from_nat`, independently of the
  weighted-sum law.
- **Round trips.** Converting there and back returns the input.
- **Bounds and injectivity.** The result is `< 256`, or different inputs give
  different outputs.

A round trip alone is not a specification. Coordinated changes to both
directions can preserve it. Each direction also needs its own law.

### 6.3 Remove what is subsumed

Before deleting a law, check that the remaining laws cover everything it
required. Then remove it, along with the definitions and proofs used only by
it. Periodically look for unused definitions.

---

## 7. Bend techniques

### 7.1 Quantities and erasure

- **`+x`** marks an argument that is used more than once. **`-x`** marks one
  erased at runtime. Use `-` for every proof argument and proof-carrying
  constructor field that runtime code doesn't need.
- **An erased value can't be matched in live code**, and an erased tuple
  can't be destructured. If a live computation needs to take a proof apart,
  either keep that proof live, or restructure (see 7.3) so that each step
  receives the proof it needs.
- **Erasure has to be consistent along a call chain.** A function receiving
  an erased proof can only pass it to parameters that are themselves erased.

### 7.2 Branching on Bool, with evidence

Bend 2.0.39 has no `if` statement. Write a `name.if` helper that matches on
the Bool, and pass `{==}` as evidence of what was matched, so that each
branch knows the condition's value:

```bend
def valid_two_bytes.if(+b1: U32, +b2: U32, shape: Bool,
  -checked: {has_two_byte_shape(b1, b2) == shape : Bool}) -> Bool:
  match shape:
    case False{}: False{}
    case True{}: Bool.not(overlong_two_bytes(b1, b2, checked))

def valid_two_bytes(+b1: U32, +b2: U32) -> Bool:
  valid_two_bytes.if(b1, b2, has_two_byte_shape(b1, b2), {==})
```

Put a short comment on version-specific idioms ("As of Bend 2.0.39 'if'
statements are written this way.") so they're easy to revisit.

### 7.3 Splitting validity proofs

A validator written as `A && List.all(p, xs)` produces a proof that
`… == True{}`. Recursive code peels that proof apart with small lemmas:

- `and_right`: from `left && right == True`, get `right == True`. Match on
  `left`. In the `False` case, the proof is a contradiction.
- `head_true` / `tail_true`: split `List.all`'s conjunction for `Con`.
- `false_true`: turn `False{} == True{}` into `Empty`, then use
  `Empty.absurd(T, …)` for any unreachable branch.

With these, a function can walk its input one element at a time. Each step
hands the head its proof and recurses with the tail's proof. This avoids
matching a fixed number of elements, and it lets the matching proof be a
single induction instead of a case split.

### 7.4 Types and representation

- **Use Base types.** For example, use `Bool` for bits, with `Bool.to_u32`
  for their numeric value, rather than a custom bit type. Name tuple shapes
  with type aliases (`Bit8() = Bool & …`).
- **Use `U32` as the numeric carrier for small values**, with a range proof
  where needed, as Base does for bytes. `Word(n)` gives an exact width
  without a bound proof, and is the right tool in specs and proofs. Assume
  that a general `Word(8n)` is not compiled as efficiently as `U32`.
- **A match on `U32{WCon{b0, …}}` is exhaustive by type.** `Word(n)` reduces
  to exactly one constructor at each width, so no fallback case is needed.
- **Bundle a value with its erased validity proof** when the pair is passed
  around. *Example:* `type HexDigitChar is Data: HexDigitChar{char: Char,
  -valid: {…}}`. Functions taking it then need no separate proof argument.
- **Use `Maybe` for "may not exist", in reference definitions.** In
  implementations, prefer a precondition proof over returning `Maybe`.

---

## 8. Proofs

- **Keep `bend PROOF.bend` fast.**
  - Prefer reusable lemmas (for example, about disjoint bit fields) and
    induction over exhaustive enumeration. Treat a split into hundreds of
    cases as a last resort.
  - When a case split is needed, split on the parts that decide the outcome
    ("compare high bits first; inspect low bits only at the boundary").
  - Measure before and after.
  - *Example:* applying these took the UTF-8 project's check from 142 s to
    about 5 s.
- **Never change a law to make a proof easier or faster.** Proof
  optimizations leave every laws file untouched.
- **Mutation-test new laws.** Temporarily make a law or example wrong,
  confirm that `bend PROOF.bend` fails at that law, then revert. Also try
  invalid inputs with `{==}`, to confirm that preconditions reject them.
- **Organize proofs by law.** State each proof's goal as a named type, prove
  a general `*_agrees` lemma, and then bind `def Laws.name(...)` to it.

---

## 9. Naming

- **A law that specifies a function is named after it**: `law strbyte`,
  `law is_binary_digit`. When one laws file covers functions from several
  modules, prefix the law with the module (`law utf8_encode_as_two_bytes`).
- **Use these suffixes:** `_examples`, `_roundtrip`, `_injective`, and
  `_spec` (for reference definitions that would otherwise clash with an
  implementation name).
- **Function names say what they do**, and distinguish related things.
  *Example:* `can_encode_as_two_bytes`, `encode_as_two_bytes`,
  `decode_two_bytes`, and `has_two_byte_shape` (the implementation's
  predicate) vs `two_byte_shape` (the reference definition).
- **Helpers belonging to a function** are named `fn.helper`
  (`hex_u32.combine`, `two_byte_shape.bits`, `str_bit8.if`).
- **Proof argument names say what they prove** (`valid`, `valid_shape`,
  `accepted`, `checked`).
- **Follow the domain's vocabulary**, as its standard does. *Example:*
  "code point" is two words in the Unicode standard.

---

## 10. Comments

- Every law gets a plain-language comment saying what it requires, with the
  diagram or table it encodes where one exists.
- Comments must be precise. Review them as carefully as code: wrong bit
  order, wrong ranges and "iff" vs "if" all matter.
- Define terms once, and say what is deliberately included or excluded.
  *Example:* "Capacity includes overlong encodings of 0..127; shortest-form
  validity is separate."
- Mark redundant checks as redundant (§6.2).

---

## 11. Checklist for a new specified function

1. Write the comment: what the function means, and the source table or
   diagram.
2. Decide on the domain. If the function is partial, write the validator
   with an exact-equation law (§5.1), and give the function an erased proof
   argument (§5.2), or write a `Maybe` reference definition (§5.3).
3. State the result:
   - an exact equation, or
   - equality with a reference definition, or
   - an iff with a witness, or
   - inverse laws.

   Use only implementation functions whose relevant behavior is already
   fixed by laws (§1.1).
4. Add `<name>_examples`, in a sensible order, covering boundaries and
   negative cases.
5. Optionally, add labeled redundant checks: round trip, bound, injectivity,
   or an alternative formulation.
6. Prove everything in `PROOF.bend`. Keep proof-only helpers there.
7. Run `bend PROOF.bend` and check that it's still fast. Mutation-test the
   new laws.
8. Remove anything the new laws make redundant or unused.
