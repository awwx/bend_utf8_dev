/-! Hand-written specification (the part a human reviews). Independent of the Rust code and of
the generated model, except that statements about the model live in `Spike/Proofs.lean`. -/

namespace SpikeSpec

/-- Surrogate code points are U+D800..U+DFFF. (LAWS.bend: is_surrogate_code_point) -/
def IsSurrogate (cp : Nat) : Prop := 0xD800 ≤ cp ∧ cp ≤ 0xDFFF

instance (cp : Nat) : Decidable (IsSurrogate cp) := by unfold IsSurrogate; infer_instance

/-- The six examples of LAWS.bend `is_surrogate_code_point_examples`. -/
theorem is_surrogate_examples :
    ¬ IsSurrogate 0x0000 ∧ ¬ IsSurrogate 0xD7FF ∧ IsSurrogate 0xD800 ∧
    IsSurrogate 0xDC00 ∧ IsSurrogate 0xDFFF ∧ ¬ IsSurrogate 0xE000 := by
  decide

/-- Number of non-ASCII bytes (value >= 0x80) in a list of bytes, each given as a number. -/
def countNonAscii : List Nat → Nat
  | [] => 0
  | b :: bs => (if 128 ≤ b then 1 else 0) + countNonAscii bs

/-- Index of the first non-ASCII byte, or the length if there is none. -/
def firstNonAscii : List Nat → Nat
  | [] => 0
  | b :: bs => if 128 ≤ b then 0 else 1 + firstNonAscii bs

theorem countNonAscii_examples :
    countNonAscii [] = 0 ∧ countNonAscii [0x41, 0x7F] = 0 ∧
    countNonAscii [0x80, 0x41, 0xFF, 0xC3] = 3 := by decide

theorem firstNonAscii_examples :
    firstNonAscii [] = 0 ∧ firstNonAscii [0x41, 0x80, 0xFF] = 1 ∧ firstNonAscii [1, 2, 3] = 3 := by
  decide

end SpikeSpec
