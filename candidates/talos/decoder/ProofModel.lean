/-
ProofModel.lean -- (partial) refinement of the Wasm-level model `stepM` to Utf8Ref's `step`
(STATUS.txt, missing statement 1).  Only the empty-pending case is done so far, plus
byte-level lemmas (packing/extraction, contB/secondB) for the other cases.
-/
import ProofStep
import ProofDone

namespace Utf8Wasm
open Utf8Pure

theorem by1_toUInt32 (x : UInt8) : by1 x.toUInt32 = x.toUInt32 := by
  apply UInt32.toNat_inj.mp
  simp only [by1, UInt32.toNat_and, UInt8.toNat_toUInt32]
  rw [show (255 : UInt32).toNat = 2 ^ 8 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  have := x.toNat_lt
  omega

/-- Missing statement 1, empty-pending case. -/
theorem stepM_nil (x : UInt8) : stepM 0 x.toUInt32 = (enc (step [] x).1, (step [] x).2) := by
  have hq : qOf 0 x.toUInt32 = x.toUInt32 := by simp [qOf]
  have hn : nOf 0 = 0 := by simp [nOf]
  have hx := x.toNat_lt
  simp only [stepM, stepA, hq, hn, vsB, vspB, cpV, by1_toUInt32, step, isVS, isVSP, cpOf,
    isLead1, isLead2, isLead3, isLead4, List.nil_append]
  by_cases h1 : x ≤ 0x7F
  · have : x.toUInt32 ≤ 127 := by simp [UInt32.le_iff_toNat_le, UInt8.le_iff_toNat_le] at *; omega
    simp [h1, this, enc]
  · have h1' : ¬ x.toUInt32 ≤ 127 := by
      simp [UInt32.le_iff_toNat_le, UInt8.le_iff_toNat_le] at *; omega
    by_cases h2 : 0xC2 ≤ x ∧ x ≤ 0xF4
    · have h2' : 194 ≤ x.toUInt32 ∧ x.toUInt32 ≤ 244 := by
        simp [UInt32.le_iff_toNat_le, UInt8.le_iff_toNat_le] at *; omega
      have h3 : ((194 ≤ x ∧ x ≤ 223) ∨ (224 ≤ x ∧ x ≤ 239)) ∨ (240 ≤ x ∧ x ≤ 244) := by
        simp [UInt8.le_iff_toNat_le] at *; omega
      simp [h1, h1', h2', h3, enc]
      rfl
    · have h2' : ¬ (194 ≤ x.toUInt32 ∧ x.toUInt32 ≤ 244) := by
        simp [UInt32.le_iff_toNat_le, UInt8.le_iff_toNat_le] at *; omega
      have h3 : ¬ (((194 ≤ x ∧ x ≤ 223) ∨ (224 ≤ x ∧ x ≤ 239)) ∨ (240 ≤ x ∧ x ≤ 244)) := by
        simp [UInt8.le_iff_toNat_le] at *; omega
      simp [h1, h1']
      rw [if_neg h2', if_neg h3]
      rfl

/-! ## Byte-level lemmas for the remaining cases (packing, extraction, ranges) -/

theorem u8lt (x : UInt8) : x.toUInt32.toNat < 256 := by simp; exact x.toNat_lt

theorem or_shl_toNat (x y : UInt32) (k : Nat) (hk : k < 32) (hx : x.toNat < 2 ^ k)
    (hy : y.toNat * 2 ^ k < 2 ^ 32) :
    (x ||| y <<< (UInt32.ofNat k)).toNat = x.toNat + y.toNat * 2 ^ k := by
  have hk' : (UInt32.ofNat k).toNat = k := by simp; omega
  simp only [UInt32.toNat_or, UInt32.toNat_shiftLeft, hk', Nat.mod_eq_of_lt hk]
  rw [Nat.mod_eq_of_lt (by rw [Nat.shiftLeft_eq]; omega)]
  rw [Nat.or_comm, ← Nat.shiftLeft_add_eq_or_of_lt hx, Nat.shiftLeft_eq]
  omega

theorem contB_eq (x : UInt8) : contB x.toUInt32 = isCont x := by
  simp only [contB, isCont, UInt32.le_iff_toNat_le, UInt8.le_iff_toNat_le, ge_iff_le]
  simp

theorem secondB_eq (a b : UInt8) : secondB a.toUInt32 b.toUInt32 = secondOk a b := by
  have ha := a.toNat_lt
  simp only [secondB, secondOk, contB_eq]
  have e1 : (a.toUInt32 = 224) ↔ (a = 0xE0) := by
    simp [← UInt32.toNat_inj, ← UInt8.toNat_inj]
  have e2 : (a.toUInt32 = 237) ↔ (a = 0xED) := by simp [← UInt32.toNat_inj, ← UInt8.toNat_inj]
  have e3 : (a.toUInt32 = 240) ↔ (a = 0xF0) := by simp [← UInt32.toNat_inj, ← UInt8.toNat_inj]
  have e4 : (a.toUInt32 = 244) ↔ (a = 0xF4) := by simp [← UInt32.toNat_inj, ← UInt8.toNat_inj]
  simp only [e1, e2, e3, e4]
  split <;> (try split) <;> (try split) <;> (try split) <;>
    simp [UInt32.le_iff_toNat_le, UInt8.le_iff_toNat_le, isCont]
theorem bytes_of_toNat (q : UInt32) (a b c d : UInt8)
    (h : q.toNat = a.toNat + 256 * b.toNat + 65536 * c.toNat + 16777216 * d.toNat) :
    by1 q = a.toUInt32 ∧ by2 q = b.toUInt32 ∧ by3 q = c.toUInt32 ∧ by4 q = d.toUInt32 := by
  have ha := a.toNat_lt; have hb := b.toNat_lt; have hc := c.toNat_lt; have hd := d.toNat_lt
  have m255 : ∀ n : Nat, n &&& (255 : UInt32).toNat = n % 256 := fun n => by
    rw [show (255 : UInt32).toNat = 2 ^ 8 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> apply UInt32.toNat_inj.mp <;>
    simp only [by1, by2, by3, by4, UInt32.toNat_and, UInt32.toNat_shiftRight, m255,
      UInt8.toNat_toUInt32, Nat.shiftRight_eq_div_pow] <;>
    (try simp) <;> omega

end Utf8Wasm
