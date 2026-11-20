/-
Utf8StepFacts.lean -- facts about RefDecoder's `step` / `decodeBuffer`
(Utf8Ref.lean) that refinement proofs use: sizes of the state and of the
output, and decoding a buffer one byte at a time from the end.  Pure (no
Wasm, Talos or Aeneas types).  Counterpart of ../pure-rocq/Utf8StepFacts.v.
Moved here from the Talos candidate (ProofPureExtras.lean: isVSP4,
step_length, step_text_length, decodeBuffer_bounds) and the Aeneas
candidate (lean/Proofs.lean: decodeBuffer_snoc; its ref_step_bad was the
existing Utf8Proofs.step_bad_pending and is now used from there).

EXPORTS (namespace Utf8Pure)
  isVSP4               a 4-byte list is a valid prefix exactly when it is valid
  decodeBuffer_snoc    decoding l ++ [b] is decoding l, then one `step`
  step_length          (step p x).1.length ≤ 3              (when |p| ≤ 3)
  step_text_length     (step p x).2.length ≤ 2
  Output size in code points (the count behind the decoders' output-area
  bound; mirrors the Rocq layer's decode_units_bound, here counting code
  points rather than UTF-16 units):
    pendingCount p     0 if p = [], else 1 (pending bytes can later turn into
                       at most one more code point than the bytes still to come)
    step_count_bound   (step p b).2.length + pendingCount (step p b).1
                         ≤ 1 + pendingCount p
    decodeBuffer_count_bound
                       (decodeBuffer p bs).2.length + pendingCount (decodeBuffer p bs).1
                         ≤ bs.length + pendingCount p
    decodeBuffer_text_length  (decodeBuffer p bs).2.length ≤ 2 * bs.length
                       (from the count bound; the form the candidates' output
                       capacity "2 per input byte" needs)
    decodeBuffer_bounds  |p| ≤ 3 → |state| ≤ 3 ∧ |text| ≤ 2 * |bytes|
-/
import Utf8Proofs

namespace Utf8Pure

/-- A 4-byte list is a valid prefix exactly when it is a valid sequence. -/
theorem isVSP4 (a b c d : UInt8) : isVSP ([a, b, c] ++ [d]) = isVS ([a, b, c] ++ [d]) := rfl

/-- Decoding `l ++ [b]`: decode `l`, then one `step` on the state reached. -/
theorem decodeBuffer_snoc (s : State) (l : List UInt8) (b : UInt8) :
    decodeBuffer s (l ++ [b]) =
      ((step (decodeBuffer s l).1 b).1, (decodeBuffer s l).2 ++ (step (decodeBuffer s l).1 b).2) := by
  simp [decodeBuffer, List.foldl_append, stepAcc]

theorem step_length (p : List UInt8) (hp : p.length ≤ 3) (x : UInt8) :
    (step p x).1.length ≤ 3 := by
  unfold step
  by_cases h1 : isVS (p ++ [x]) = true
  · simp [h1]
  by_cases h2 : isVSP (p ++ [x]) = true
  · simp only [h1, h2, Bool.false_eq_true, ↓reduceIte]
    match p, hp with
    | [], _ | [_], _ | [_, _], _ => simp
    | [b, c, d], _ => rw [isVSP4] at h2; exact absurd h2 h1
    | _ :: _ :: _ :: _ :: _, h => simp at h
  · simp only [h1, h2, Bool.false_eq_true, ↓reduceIte]
    split
    · simp
    · simp only [stepFresh]; split <;> (try split) <;> simp

theorem step_text_length (p : List UInt8) (x : UInt8) : (step p x).2.length ≤ 2 := by
  unfold step stepFresh
  repeat (first | split | simp)

/-! ## Output size in code points -/

/-- 1 for a non-empty pending state (it can still produce one U+FFFD more
than the bytes still to come), else 0. -/
def pendingCount (p : State) : Nat := if p = [] then 0 else 1

theorem stepFresh_count_bound (b : UInt8) :
    (stepFresh b).2.length + pendingCount (stepFresh b).1 ≤ 1 := by
  unfold stepFresh
  repeat (first | split | simp [pendingCount])

theorem step_count_bound (p : State) (b : UInt8) :
    (step p b).2.length + pendingCount (step p b).1 ≤ 1 + pendingCount p := by
  have hf := stepFresh_count_bound b
  unfold step
  split
  · simp [pendingCount]
  split
  · simp [pendingCount]
  split
  · simp [pendingCount]
  · next h => have : p ≠ [] := by cases p <;> simp_all
              simp only [List.length_cons, pendingCount, this, ↓reduceIte] at hf ⊢; omega

theorem decodeBuffer_count_bound (bs : List UInt8) : ∀ p : State,
    (decodeBuffer p bs).2.length + pendingCount (decodeBuffer p bs).1 ≤ bs.length + pendingCount p := by
  induction bs with
  | nil => intro p; simp [decodeBuffer_nil]
  | cons b bs ih =>
    intro p
    have h1 := ih (step p b).1
    have h2 := step_count_bound p b
    rw [decodeBuffer_cons]
    simp only [List.length_append, List.length_cons]
    omega

theorem decodeBuffer_text_length (p : State) (bs : List UInt8) :
    (decodeBuffer p bs).2.length ≤ 2 * bs.length := by
  cases bs with
  | nil => simp [decodeBuffer_nil]
  | cons b bs =>
    have h := decodeBuffer_count_bound (b :: bs) p
    have : pendingCount p ≤ 1 := by unfold pendingCount; split <;> omega
    simp only [List.length_cons] at h ⊢
    omega

theorem decodeBuffer_bounds (bs : List UInt8) : ∀ p : List UInt8, p.length ≤ 3 →
    (decodeBuffer p bs).1.length ≤ 3 ∧ (decodeBuffer p bs).2.length ≤ 2 * bs.length := by
  induction bs with
  | nil => intro p hp; simpa [decodeBuffer_nil] using hp
  | cons b bs ih =>
    intro p hp
    refine ⟨?_, decodeBuffer_text_length p (b :: bs)⟩
    rw [decodeBuffer_cons]
    exact (ih (step p b).1 (step_length p hp b)).1

end Utf8Pure
