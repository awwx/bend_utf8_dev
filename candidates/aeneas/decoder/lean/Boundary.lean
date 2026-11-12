/-
Boundary.lean -- what is proved about the Rust decoder, for review together
with Utf8Laws.lean (the spec).  Definitions and statements only; the proofs
are in Proofs.lean.

The artifact is the Lean model that Charon + Aeneas generate from the safe
Rust core (src/lib.rs, outside `mod shim`): `decoder.decode_start_state`,
`decoder.decode_buffer`, `decoder.decode_done` in Decoder/Funs.lean.
In that model a Rust function returns a `Result`; `= ok x` means it returns
`x` (no panic, no arithmetic overflow, no out-of-bounds index, terminates).
A `&mut` argument becomes an extra result: the slice after the call.

Rust signatures:
  decode_start_state() -> u32
  decode_buffer(state: u32, input: &[u8], out: &mut [u32]) -> (u32, usize)
  decode_done(state: u32, out: &mut [u32]) -> usize
The state is a plain `u32` value; text is written as code points (one `u32`
per code point) at the front of `out`, and the `usize` result is how many.
-/
import Aeneas
import Decoder.Funs
import Utf8Laws

open Aeneas Aeneas.Std Result

namespace Boundary

/-- A Rust `u8` as a spec byte. -/
def byte (x : U8) : UInt8 := UInt8.ofNat x.val

/-- The bytes held by a Rust `&[u8]`. -/
def bytes (s : Slice U8) : List UInt8 := s.val.map byte

/-- A Rust `u32` as a spec code point. -/
def codePoint (x : U32) : UInt32 := UInt32.ofNat x.val

/-- `out'` is `out` with its first `t.length` elements replaced by the code
points of `t`, and the count `k` returned with it is `t.length`. -/
def WritesText (out out' : Slice U32) (k : Usize) (t : Text) : Prop :=
  k.val = t.length ∧
  out'.length = out.length ∧
  (out'.val.take t.length).map codePoint = t ∧
  out'.val.drop t.length = out.val.drop t.length

/-- The body of `Realizes` below, for one given relation `R` between `D`'s
states and Rust state values (named so that the statement about the wrapper,
further down, can refer to the same `R`). -/
def RealizesWith (D : Decoder) (R : D.State → U32 → Prop) : Prop :=
    (∃ v, decoder.decode_start_state = ok v ∧ R D.start v) ∧
    (∀ (s : D.State) (v : U32) (input : Slice U8) (out : Slice U32),
      R s v → 2 * input.length ≤ out.length →
      ∃ (v' : U32) (k : Usize) (out' : Slice U32),
        decoder.decode_buffer v input out = ok ((v', k), out') ∧
        R (D.decode_buffer s (bytes input)).1 v' ∧
        WritesText out out' k (D.decode_buffer s (bytes input)).2) ∧
    (∀ (s : D.State) (v : U32) (out : Slice U32),
      R s v → 1 ≤ out.length →
      ∃ (k : Usize) (out' : Slice U32),
        decoder.decode_done v out = ok (k, out') ∧
        WritesText out out' k (D.decode_done s))

/-- The generated Rust model implements the stream decoder `D`: some relation
`R` between `D`'s states and Rust state values holds initially and is
preserved, and each Rust call returns (never fails or diverges) exactly the
text `D` returns, provided the output slice is large enough: two code points
per input byte for `decode_buffer`, one for `decode_done`. -/
def Realizes (D : Decoder) : Prop :=
  ∃ R : D.State → U32 → Prop, RealizesWith D R

/-- The top-level claim: the Rust decoder implements some stream decoder that
satisfies the three streaming laws of the spec. -/
def Verified : Prop := ∃ D : Decoder, D.Correct ∧ Realizes D

/-! ## Does the guarantee apply to the shipped wrapper?  (non-vacuity)

`Verified` promises results only under conditions: the state passed in must
be one the decoder itself produced, and the output slice must have room for
two code points per input byte (one for `decode_done`).  A promise whose
conditions are never met in practice would be empty.  The definitions below
record what the JavaScript wrapper decoder.mjs passes on every call, through
the export shim (`mod shim` in src/lib.rs), and `VerifiedForWrapper` says that
every such call meets the conditions, so the guarantee really applies.

What the wrapper does (check.sh reads the numbers from decoder.mjs and fails
if they differ from the ones here; it also checks that the shim and wrapper
lines that pass the lengths and the state are as described):
  * Once, it reserves one memory region holding, in order: the input chunk
    (`MaxChunkBytes` bytes), the output (`OutCapacity` code points, 4 bytes
    each), and a 4-byte slot where the shim stores the new state.
  * Every `decode_buffer` call gets at most `MaxChunkBytes` input bytes
    (longer input is cut into chunks of that size, which the spec's split law
    makes harmless) and the whole output area, `OutCapacity` code points.
  * Every `decode_done` call gets the same output area.
  * The state passed to a call is the start state or the state returned by
    an earlier call, passed back unchanged (the wrapper's own users must hand
    back the state values it gave them; a made-up state is not covered).
  The shim itself only turns (address, length) pairs into slices and passes
  them, with the state, to the verified functions; it has no buffer sizes of
  its own.

What this covers, and what it does not.  This is about the Lean model of
the Rust: it proves that the model's conditions hold for the arguments the
shim passes when called as the wrapper calls it.  Still trusted and not
checked: that the shim's raw addresses and lengths really give slices of
those lengths over the wrapper's region (`from_raw_parts`); that the region
the wrapper reserves really exists in Wasm linear memory, is large enough
and is used by nothing else; that the wrapper hands back the state value
unchanged; and the conversion of code points to a JS string.
-/

/-- Most input bytes passed to one `decode_buffer` call (`CHUNK` in
decoder.mjs). -/
def MaxChunkBytes : Nat := 65536

/-- Length, in code points, of the output slice passed to every call
(`OUT_CAP` in decoder.mjs). -/
def OutCapacity : Nat := 131072

/-- Byte offsets of the input chunk, the output area and the state slot from
the start of the wrapper's region (`IN`, `OUT`, `ST` in decoder.mjs), and the
region's size (`need`). -/
def InputOffset : Nat := 0
def OutputOffset : Nat := InputOffset + MaxChunkBytes
def StateOffset : Nat := OutputOffset + 4 * OutCapacity
def ReservedBytes : Nat := MaxChunkBytes + 4 * OutCapacity + 4

/-- The wrapper's region is laid out consistently: input, output and state
slot do not overlap and all lie inside the reserved size; the output and the
state slot start on a multiple of 4 bytes (the region starts on a 64 KiB
page), as `u32` values need; and the region is smaller than 4 GiB, so every
offset and length fits the 32-bit addresses and `usize` of wasm32. -/
def WrapperLayoutFits : Prop :=
  InputOffset + MaxChunkBytes ≤ OutputOffset ∧
  OutputOffset + 4 * OutCapacity ≤ StateOffset ∧
  StateOffset + 4 ≤ ReservedBytes ∧
  OutputOffset % 4 = 0 ∧ StateOffset % 4 = 0 ∧
  ReservedBytes < 2 ^ 32

/-- The count returned is at most two code points per input byte for
`decode_buffer`, and at most one for `decode_done` (the audit noted that this
was implied by `Realizes` but not stated).  For states related by `R` and
calls that meet `Realizes`'s output-size condition. -/
def CountsBounded (D : Decoder) (R : D.State → U32 → Prop) : Prop :=
  (∀ (s : D.State) (v : U32) (input : Slice U8) (out : Slice U32)
     (v' : U32) (k : Usize) (out' : Slice U32),
    R s v → 2 * input.length ≤ out.length →
    decoder.decode_buffer v input out = ok ((v', k), out') →
    k.val ≤ 2 * input.length) ∧
  (∀ (s : D.State) (v : U32) (out : Slice U32) (k : Usize) (out' : Slice U32),
    R s v → 1 ≤ out.length →
    decoder.decode_done v out = ok (k, out') →
    k.val ≤ 1)

/-- Every call the wrapper makes is one that `RealizesWith D R` gives its
guarantee for.  Call a Rust state value "accepted" if `R` relates it to a
state of `D`; the guarantee covers exactly calls from accepted states.
  1. Start: `decode_start_state` returns a state, and it is accepted.
  2. Slices of the wrapper's sizes can exist in the model (a model slice is
     at most `Usize.max` long).
  3. A `decode_buffer` call from an accepted state, with at most
     `MaxChunkBytes` input bytes and an output slice of `OutCapacity` code
     points, meets the output-size condition, returns, and returns an
     accepted state.
  4. A `decode_done` call from an accepted state with that output slice
     meets its condition and returns.
By 1 and 3, every state the wrapper ever passes is accepted (by induction
over the calls it has made), so by 3 and 4 every call it makes is covered. -/
def WrapperCallsCovered (D : Decoder) (R : D.State → U32 → Prop) : Prop :=
  (∃ v, decoder.decode_start_state = ok v ∧ R D.start v) ∧
  (∃ input : Slice U8, input.length = MaxChunkBytes) ∧
  (∃ out : Slice U32, out.length = OutCapacity) ∧
  (∀ (s : D.State) (v : U32) (input : Slice U8) (out : Slice U32),
    R s v → input.length ≤ MaxChunkBytes → out.length = OutCapacity →
    2 * input.length ≤ out.length ∧
    ∃ (v' : U32) (k : Usize) (out' : Slice U32),
      decoder.decode_buffer v input out = ok ((v', k), out') ∧
      R (D.decode_buffer s (bytes input)).1 v') ∧
  (∀ (s : D.State) (v : U32) (out : Slice U32),
    R s v → out.length = OutCapacity →
    1 ≤ out.length ∧
    ∃ (k : Usize) (out' : Slice U32), decoder.decode_done v out = ok (k, out'))

/-- The second top-level claim: the same kind of guarantee as `Verified`
(which it implies), for one relation `R`, together with the count bounds,
the fact that every call the wrapper makes is covered by the guarantee, and
the consistency of the wrapper's memory layout. -/
def VerifiedForWrapper : Prop :=
  ∃ D : Decoder, D.Correct ∧ ∃ R : D.State → U32 → Prop,
    RealizesWith D R ∧ CountsBounded D R ∧ WrapperCallsCovered D R ∧
    WrapperLayoutFits

end Boundary
