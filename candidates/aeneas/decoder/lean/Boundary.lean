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

/-- The generated Rust model implements the stream decoder `D`: some relation
`R` between `D`'s states and Rust state values holds initially and is
preserved, and each Rust call returns (never fails or diverges) exactly the
text `D` returns, provided the output slice is large enough: two code points
per input byte for `decode_buffer`, one for `decode_done`. -/
def Realizes (D : Decoder) : Prop :=
  ∃ R : D.State → U32 → Prop,
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

/-- The top-level claim: the Rust decoder implements some stream decoder that
satisfies the three streaming laws of the spec. -/
def Verified : Prop := ∃ D : Decoder, D.Correct ∧ Realizes D

end Boundary
