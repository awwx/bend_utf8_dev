import Aeneas
import Spike.Funs
import Spike.Spec
open Aeneas Aeneas.Std Result ControlFlow Error
open SpikeSpec

namespace spike

/-! ## (a) is_surrogate_code_point -/

/-- The generated function never fails and agrees with the spec on every `u32`. -/
theorem is_surrogate_code_point_correct (cp : Std.U32) :
    ∃ b, is_surrogate_code_point cp = ok b ∧ (b = true ↔ IsSurrogate cp.val) := by
  unfold is_surrogate_code_point IsSurrogate
  split
  · refine ⟨_, rfl, ?_⟩
    simp only [decide_eq_true_eq]
    scalar_tac
  · refine ⟨_, rfl, ?_⟩
    simp only [Bool.false_eq_true, false_iff]
    scalar_tac

/-- The six LAWS.bend examples, on the generated function. -/
theorem is_surrogate_code_point_examples :
    is_surrogate_code_point 0#u32 = ok false ∧
    is_surrogate_code_point 0xD7FF#u32 = ok false ∧
    is_surrogate_code_point 0xD800#u32 = ok true ∧
    is_surrogate_code_point 0xDC00#u32 = ok true ∧
    is_surrogate_code_point 0xDFFF#u32 = ok true ∧
    is_surrogate_code_point 0xE000#u32 = ok false := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [is_surrogate_code_point]

/-! ## (b) count_non_ascii -/

/-- The byte contents of a slice as naturals. -/
def bytesOf (s : Slice Std.U8) : List Nat := s.val.map (·.val)

theorem countNonAscii_le_length (l : List Nat) : countNonAscii l ≤ l.length := by
  induction l with
  | nil => simp [countNonAscii]
  | cons b bs ih => simp only [countNonAscii, List.length_cons]; split <;> omega

theorem count_drop (s : Slice Std.U8) (i : Nat) (h : i < s.length) :
    countNonAscii ((bytesOf s).drop i) =
      (if 128 ≤ (s.val[i]'h).val then 1 else 0) + countNonAscii ((bytesOf s).drop (i + 1)) := by
  have h' : i < (bytesOf s).length := by simp [bytesOf, Slice.length] at *; exact h
  rw [List.drop_eq_getElem_cons h']
  simp [countNonAscii, bytesOf]

/-- Loop invariant: `n` plus the count in the unread suffix is the total. -/
theorem count_non_ascii_loop_spec (s : Slice Std.U8)
    (hlen : s.length ≤ Std.U32.max) (n : Std.U32) (i : Std.Usize)
    (hi : i.val ≤ s.length)
    (hn : n.val + countNonAscii ((bytesOf s).drop i.val) = countNonAscii (bytesOf s)) :
    ∃ r, count_non_ascii_loop s n i = ok r ∧ r.val = countNonAscii (bytesOf s) := by
  have key := loop.spec_decr_nat
    (measure := fun (p : Std.U32 × Std.Usize) => s.length - p.2.val)
    (inv := fun p => p.2.val ≤ s.length ∧
      p.1.val + countNonAscii ((bytesOf s).drop p.2.val) = countNonAscii (bytesOf s))
    (post := fun r : Std.U32 => r.val = countNonAscii (bytesOf s))
    (body := fun p => count_non_ascii_loop.body s p.1 p.2) (n, i)
    (by
      rintro ⟨n, i⟩ ⟨hi, hn⟩
      simp only [count_non_ascii_loop.body]
      split
      · rename_i hlt
        have hlt' : i.val < s.length := by scalar_tac
        have hc := count_drop s i.val hlt'
        have htot := countNonAscii_le_length (bytesOf s)
        have hbl : (bytesOf s).length = s.length := by simp [bytesOf, Slice.length]
        simp only at hn hi
        step as ⟨ i2, hi2 ⟩
        have hi2' : i2.val = s.val[i.val].val := by rw [hi2]
        split
        · rename_i hge
          have hge' : 128 ≤ i2.val := by scalar_tac
          step*
          have : 128 ≤ (s.val[i.val]).val := by rw [← hi2']; exact hge'
          simp only [this, ite_true] at hc
          rw [i3_post]
          refine ⟨by scalar_tac, ?_, by scalar_tac⟩
          omega
        · rename_i hge
          have hge' : ¬ 128 ≤ i2.val := by scalar_tac
          step*
          have : ¬ 128 ≤ (s.val[i.val]).val := by rw [← hi2']; exact hge'
          simp only [this, ite_false] at hc
          rw [i3_post]
          refine ⟨by scalar_tac, ?_, by scalar_tac⟩
          omega
      · rename_i hge
        simp only [WP.spec_ok]
        have hi' : i.val = s.length := by scalar_tac
        simp only at hn
        rw [hi'] at hn
        simp [bytesOf, Slice.length, countNonAscii] at hn ⊢
        omega) ⟨hi, hn⟩
  unfold count_non_ascii_loop
  generalize hr : loop (fun x => match x with | (n1, i1) => count_non_ascii_loop.body s n1 i1) (n, i) = r at key ⊢
  cases r with
  | ret v => exact ⟨v, rfl, by simpa using key⟩
  | vis e k => simp [WP.spec_vis] at key
  | div => simp at key

/-- Final theorem for `count_non_ascii`: under the length bound the function does not fail and
returns the spec's count. (On wasm32, `usize` is 32-bit so the bound always holds.) -/
theorem count_non_ascii_correct (s : Slice Std.U8) (hlen : s.length ≤ Std.U32.max) :
    ∃ r, count_non_ascii s = ok r ∧ r.val = countNonAscii (bytesOf s) := by
  unfold count_non_ascii
  exact count_non_ascii_loop_spec s hlen 0#u32 0#usize (by simp) (by simp)

/-! ## (b') early-exit variants -/

theorem first_drop (s : Slice Std.U8) (i : Nat) (h : i < s.length) :
    firstNonAscii ((bytesOf s).drop i) =
      if 128 ≤ (s.val[i]'h).val then 0 else 1 + firstNonAscii ((bytesOf s).drop (i + 1)) := by
  have h' : i < (bytesOf s).length := by simp [bytesOf, Slice.length] at *; exact h
  rw [List.drop_eq_getElem_cons h']
  simp [firstNonAscii, bytesOf]

/-- Common invariant for both early-exit loops. -/
def FirstInv (s : Slice Std.U8) (i : Std.Usize) : Prop :=
  i.val ≤ s.length ∧ i.val + firstNonAscii ((bytesOf s).drop i.val) = firstNonAscii (bytesOf s)

theorem first_non_ascii_return_loop_spec (s : Slice Std.U8) (i : Std.Usize) (hi : FirstInv s i) :
    ∃ r, first_non_ascii_return_loop s i = ok r ∧ r.val = firstNonAscii (bytesOf s) := by
  have key := loop.spec_decr_nat
    (measure := fun (i : Std.Usize) => s.length - i.val)
    (inv := FirstInv s)
    (post := fun r : Std.Usize => r.val = firstNonAscii (bytesOf s))
    (body := fun i => first_non_ascii_return_loop.body s i) i
    (by
      intro i hi
      obtain ⟨hi1, hi2⟩ := hi
      simp only [first_non_ascii_return_loop.body]
      have hbl : (bytesOf s).length = s.length := by simp [bytesOf, Slice.length]
      split
      · rename_i hlt
        have hlt' : i.val < s.length := by scalar_tac
        have hf := first_drop s i.val hlt'
        step as ⟨ i2, hi2' ⟩
        have e : i2.val = s.val[i.val].val := by rw [hi2']
        split
        · rename_i hge
          have hge' : 128 ≤ (s.val[i.val]).val := by rw [← e]; scalar_tac
          simp only [hge', ite_true] at hf
          simp only [WP.spec_ok]
          omega
        · rename_i hge
          have hge' : ¬ 128 ≤ (s.val[i.val]).val := by rw [← e]; scalar_tac
          simp only [hge', ite_false] at hf
          step*
          unfold FirstInv
          rw [i3_post]
          refine ⟨⟨by scalar_tac, by omega⟩, by scalar_tac⟩
      · rename_i hge
        have hi' : i.val = s.length := by scalar_tac
        simp only [WP.spec_ok]
        have hnil : List.drop i.val (bytesOf s) = [] := List.drop_eq_nil_of_le (by omega)
        rw [hnil] at hi2
        simp only [firstNonAscii] at hi2
        have := Slice.len_val s
        omega) hi
  unfold first_non_ascii_return_loop
  generalize hr : loop (fun x => first_non_ascii_return_loop.body s x) i = r at key ⊢
  cases r with
  | ret v => exact ⟨v, rfl, by simpa using key⟩
  | vis e k => simp [WP.spec_vis] at key
  | div => simp at key

theorem first_non_ascii_return_correct (s : Slice Std.U8) :
    ∃ r, first_non_ascii_return s = ok r ∧ r.val = firstNonAscii (bytesOf s) := by
  unfold first_non_ascii_return
  exact first_non_ascii_return_loop_spec s 0#usize ⟨by simp, by simp⟩

theorem first_non_ascii_break_loop_spec (s : Slice Std.U8) (i : Std.Usize) (hi : FirstInv s i) :
    ∃ r, first_non_ascii_break_loop s i = ok r ∧ r.val = firstNonAscii (bytesOf s) := by
  have key := loop.spec_decr_nat
    (measure := fun (i : Std.Usize) => s.length - i.val)
    (inv := FirstInv s)
    (post := fun r : Std.Usize => r.val = firstNonAscii (bytesOf s))
    (body := fun i => first_non_ascii_break_loop.body s i) i
    (by
      intro i hi
      obtain ⟨hi1, hi2⟩ := hi
      simp only [first_non_ascii_break_loop.body]
      have hbl : (bytesOf s).length = s.length := by simp [bytesOf, Slice.length]
      split
      · rename_i hge
        have hi' : i.val = s.length := by scalar_tac
        simp only [WP.spec_ok]
        have hnil : List.drop i.val (bytesOf s) = [] := List.drop_eq_nil_of_le (by omega)
        rw [hnil] at hi2
        simp only [firstNonAscii] at hi2
        have := Slice.len_val s
        omega
      · rename_i hlt
        have hlt' : i.val < s.length := by scalar_tac
        have hf := first_drop s i.val hlt'
        step as ⟨ i2, hi2' ⟩
        have e : i2.val = s.val[i.val].val := by rw [hi2']
        split
        · rename_i hge
          have hge' : ¬ 128 ≤ (s.val[i.val]).val := by rw [← e]; scalar_tac
          simp only [hge', ite_false] at hf
          step*
          unfold FirstInv
          rw [i3_post]
          refine ⟨⟨by scalar_tac, by omega⟩, by scalar_tac⟩
        · rename_i hge
          have hge' : 128 ≤ (s.val[i.val]).val := by rw [← e]; scalar_tac
          simp only [hge', ite_true] at hf
          simp only [WP.spec_ok]
          omega) hi
  unfold first_non_ascii_break_loop
  generalize hr : loop (fun x => first_non_ascii_break_loop.body s x) i = r at key ⊢
  cases r with
  | ret v => exact ⟨v, rfl, by simpa using key⟩
  | vis e k => simp [WP.spec_vis] at key
  | div => simp at key

theorem first_non_ascii_break_correct (s : Slice Std.U8) :
    ∃ r, first_non_ascii_break s = ok r ∧ r.val = firstNonAscii (bytesOf s) := by
  unfold first_non_ascii_break
  exact first_non_ascii_break_loop_spec s 0#usize ⟨by simp, by simp⟩

end spike

#print axioms spike.is_surrogate_code_point_correct
#print axioms spike.is_surrogate_code_point_examples
#print axioms spike.count_non_ascii_correct
#print axioms spike.first_non_ascii_return_correct
#print axioms spike.first_non_ascii_break_correct
#print axioms SpikeSpec.is_surrogate_examples
#print axioms SpikeSpec.countNonAscii_examples
#print axioms SpikeSpec.firstNonAscii_examples
