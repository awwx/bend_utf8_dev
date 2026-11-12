/-
Utf8Table.lean -- the byte table (`isVS`/`isVSP`/`cpOf` of Utf8Ref) against
the spec's `encodes`, and finite facts about valid sequences.

EXPORTS
  cpOf_one cpOf_two cpOf_three cpOf_four   `(cpOf [..]).toNat` as Nat arithmetic
                                           (statements used by the Aeneas proofs)
  secondOk_iff isCont_iff isLead1_iff .. isLead4_iff   byte classes as toNat ranges
  is_unicode_scalar_iff                    toNat form of the spec's scalar test
  encodes_iff : encodes seq cp ↔ isVS seq = true ∧ cp = cpOf seq
  lead1_not lead2_not lead3_not            the lead classes are disjoint
  isVS_isVSP isVSP_of_isVS_append isVS_not_proper   structural facts
  completion, completion_spec, isVSP_extends  every pending prefix can be completed
                                              to a valid sequence whose code point
                                              is not U+FFFD

METHOD
  Arithmetic facts go through `toNat` and `omega`; each `omega` call sees one
  sequence length and one lead-byte class, never a split over byte values.
  Structural facts are Bool reasoning (`simp_all`) plus class disjointness.
  Kernel-checked; no `bv_decide`.
-/
import Utf8Bits
import Utf8Ref
namespace Utf8Pure

/-! ## Shift/mask values as arithmetic -/

theorem nat_or_add (x y k : Nat) (hx : x % 2 ^ k = 0) (hy : y < 2 ^ k) : x ||| y = x + y := by
  have : x = 2 ^ k * (x / 2 ^ k) := by
    have := Nat.div_add_mod x (2 ^ k); omega
  rw [this]; exact (Nat.two_pow_add_eq_or_of_lt hy _).symm

theorem nat_and_mask (x : Nat) (k : Nat) : x &&& (2 ^ k - 1) = x % 2 ^ k :=
  Nat.and_two_pow_sub_one_eq_mod x k

theorem and_mask_31 (x : Nat) : x &&& 31 = x % 32 := nat_and_mask x 5
theorem and_mask_15 (x : Nat) : x &&& 15 = x % 16 := nat_and_mask x 4
theorem and_mask_7 (x : Nat) : x &&& 7 = x % 8 := nat_and_mask x 3
theorem and_mask_63 (x : Nat) : x &&& 63 = x % 64 := nat_and_mask x 6

theorem cpOf_one (b1 : UInt8) : (cpOf [b1]).toNat = b1.toNat := by
  simp [cpOf]

theorem cpOf_two (b1 b2 : UInt8) :
    (cpOf [b1, b2]).toNat = b1.toNat % 32 * 64 + b2.toNat % 64 := by
  have h1 := b1.toNat_lt; have h2 := b2.toNat_lt
  simp only [cpOf, UInt32.toNat_or, UInt32.toNat_and, UInt32.toNat_shiftLeft, UInt8.toNat_toUInt32,
    UInt32.toNat_ofNat, Nat.shiftLeft_eq]
  simp only [Nat.reducePow, Nat.reduceMod, and_mask_31, and_mask_63]
  rw [Nat.mod_eq_of_lt (by omega), nat_or_add _ _ 6 (by simp only [Nat.reducePow]; omega) (by simp only [Nat.reducePow]; omega)]
  all_goals omega

theorem cpOf_three (b1 b2 b3 : UInt8) :
    (cpOf [b1, b2, b3]).toNat = b1.toNat % 16 * 4096 + b2.toNat % 64 * 64 + b3.toNat % 64 := by
  have h1 := b1.toNat_lt; have h2 := b2.toNat_lt; have h3 := b3.toNat_lt
  simp only [cpOf, UInt32.toNat_or, UInt32.toNat_and, UInt32.toNat_shiftLeft, UInt8.toNat_toUInt32,
    UInt32.toNat_ofNat, Nat.shiftLeft_eq]
  simp only [Nat.reducePow, Nat.reduceMod, and_mask_15, and_mask_63]
  rw [Nat.mod_eq_of_lt (a := _ * 4096) (by omega), Nat.mod_eq_of_lt (a := _ * 64) (by omega),
    nat_or_add (b1.toNat % 16 * 4096) (b2.toNat % 64 * 64) 12 (by simp only [Nat.reducePow]; omega) (by simp only [Nat.reducePow]; omega),
    nat_or_add (b1.toNat % 16 * 4096 + b2.toNat % 64 * 64) _ 6 (by simp only [Nat.reducePow]; omega) (by simp only [Nat.reducePow]; omega)]

theorem cpOf_four (b1 b2 b3 b4 : UInt8) :
    (cpOf [b1, b2, b3, b4]).toNat =
      b1.toNat % 8 * 262144 + b2.toNat % 64 * 4096 + b3.toNat % 64 * 64 + b4.toNat % 64 := by
  have h1 := b1.toNat_lt; have h2 := b2.toNat_lt; have h3 := b3.toNat_lt; have h4 := b4.toNat_lt
  simp only [cpOf, UInt32.toNat_or, UInt32.toNat_and, UInt32.toNat_shiftLeft, UInt8.toNat_toUInt32,
    UInt32.toNat_ofNat, Nat.shiftLeft_eq]
  simp only [Nat.reducePow, Nat.reduceMod, and_mask_7, and_mask_63]
  rw [Nat.mod_eq_of_lt (a := _ * 262144) (by omega), Nat.mod_eq_of_lt (a := _ * 4096) (by omega),
    Nat.mod_eq_of_lt (a := _ * 64) (by omega),
    nat_or_add (b1.toNat % 8 * 262144) (b2.toNat % 64 * 4096) 18 (by simp only [Nat.reducePow]; omega) (by simp only [Nat.reducePow]; omega),
    nat_or_add (b1.toNat % 8 * 262144 + b2.toNat % 64 * 4096) (b3.toNat % 64 * 64) 12 (by simp only [Nat.reducePow]; omega) (by simp only [Nat.reducePow]; omega),
    nat_or_add (b1.toNat % 8 * 262144 + b2.toNat % 64 * 4096 + b3.toNat % 64 * 64) _ 6 (by simp only [Nat.reducePow]; omega) (by simp only [Nat.reducePow]; omega)]
  all_goals omega


/-! ## Byte classes as `toNat` ranges -/

theorem secondOk_iff (b1 b2 : UInt8) : secondOk b1 b2 = true ↔
    (b1.toNat = 0xE0 ∧ 0xA0 ≤ b2.toNat ∧ b2.toNat ≤ 0xBF) ∨
    (b1.toNat = 0xED ∧ 0x80 ≤ b2.toNat ∧ b2.toNat ≤ 0x9F) ∨
    (b1.toNat = 0xF0 ∧ 0x90 ≤ b2.toNat ∧ b2.toNat ≤ 0xBF) ∨
    (b1.toNat = 0xF4 ∧ 0x80 ≤ b2.toNat ∧ b2.toNat ≤ 0x8F) ∨
    (b1.toNat ≠ 0xE0 ∧ b1.toNat ≠ 0xED ∧ b1.toNat ≠ 0xF0 ∧ b1.toNat ≠ 0xF4 ∧
      0x80 ≤ b2.toNat ∧ b2.toNat ≤ 0xBF) := by
  have k : ∀ c : UInt8, b1 = c ↔ b1.toNat = c.toNat := fun c => UInt8.toNat_inj.symm
  unfold secondOk
  simp only [k, UInt8.toNat_ofNat, UInt8.le_iff_toNat_le, Nat.reducePow, Nat.reduceMod]
  repeat' split
  all_goals simp only [Bool.and_eq_true, decide_eq_true_eq]; constructor <;> intro <;> omega

theorem isCont_iff (b : UInt8) : isCont b = true ↔ 0x80 ≤ b.toNat ∧ b.toNat ≤ 0xBF := by
  simp [isCont, UInt8.le_iff_toNat_le]
theorem isLead1_iff (b : UInt8) : isLead1 b = true ↔ b.toNat ≤ 0x7F := by
  simp [isLead1, UInt8.le_iff_toNat_le]
theorem isLead2_iff (b : UInt8) : isLead2 b = true ↔ 0xC2 ≤ b.toNat ∧ b.toNat ≤ 0xDF := by
  simp [isLead2, UInt8.le_iff_toNat_le]
theorem isLead3_iff (b : UInt8) : isLead3 b = true ↔ 0xE0 ≤ b.toNat ∧ b.toNat ≤ 0xEF := by
  simp [isLead3, UInt8.le_iff_toNat_le]
theorem isLead4_iff (b : UInt8) : isLead4 b = true ↔ 0xF0 ≤ b.toNat ∧ b.toNat ≤ 0xF4 := by
  simp [isLead4, UInt8.le_iff_toNat_le]

theorem is_unicode_scalar_iff (cp : UInt32) :
    is_unicode_scalar cp = true ↔ cp.toNat ≤ 0x10FFFF ∧ ¬ (0xD800 ≤ cp.toNat ∧ cp.toNat ≤ 0xDFFF) := by
  simp only [is_unicode_scalar, is_surrogate_code_point, Bool.and_eq_true, decide_eq_true_eq,
    Bool.not_eq_true', Bool.and_eq_false_iff, decide_eq_false_iff_not, ge_iff_le,
    UInt32.le_iff_toNat_le, UInt32.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
  constructor <;> intro h <;> omega

theorem encodes_of_isVS (seq : List UInt8) (h : isVS seq = true) : encodes seq (cpOf seq) := by
  unfold encodes
  rw [is_unicode_scalar_iff, encoding_eq]
  match seq, h with
  | [b1], h =>
    simp only [isVS, isLead1_iff] at h
    have : (cpOf [b1]).toNat ≤ 0x10FFFF ∧ ¬ (0xD800 ≤ (cpOf [b1]).toNat ∧ (cpOf [b1]).toNat ≤ 0xDFFF) ∧
      (cpOf [b1]).toNat < 0x200000 ∧ (cpOf [b1]).toNat < 0x80 := by rw [cpOf_one]; omega
    simp only [this, enc32, ↓reduceIte, not_false_eq_true, and_self, true_and, Option.some.injEq,
      List.cons.injEq, and_true]
    rw [← UInt8.toNat_inj, UInt8.toNat_ofNat', cpOf_one]; omega
  | [b1, b2], h =>
    simp only [isVS, isLead2_iff, secondOk_iff, Bool.and_eq_true] at h
    have : (cpOf [b1, b2]).toNat ≤ 0x10FFFF ∧
      ¬ (0xD800 ≤ (cpOf [b1, b2]).toNat ∧ (cpOf [b1, b2]).toNat ≤ 0xDFFF) ∧
      (cpOf [b1, b2]).toNat < 0x200000 ∧ ¬ (cpOf [b1, b2]).toNat < 0x80 ∧
      (cpOf [b1, b2]).toNat < 0x800 := by rw [cpOf_two]; omega
    simp only [this, enc32, ↓reduceIte, not_false_eq_true, and_self, true_and, Option.some.injEq,
      List.cons.injEq, and_true]
    simp only [← UInt8.toNat_inj, UInt8.toNat_ofNat', cpOf_two]; omega
  | [b1, b2, b3], h =>
    simp only [isVS, isLead3_iff, secondOk_iff, isCont_iff, Bool.and_eq_true] at h
    have : (cpOf [b1, b2, b3]).toNat ≤ 0x10FFFF ∧
      ¬ (0xD800 ≤ (cpOf [b1, b2, b3]).toNat ∧ (cpOf [b1, b2, b3]).toNat ≤ 0xDFFF) ∧
      (cpOf [b1, b2, b3]).toNat < 0x200000 ∧ ¬ (cpOf [b1, b2, b3]).toNat < 0x80 ∧
      ¬ (cpOf [b1, b2, b3]).toNat < 0x800 ∧ (cpOf [b1, b2, b3]).toNat < 0x10000 := by
      rw [cpOf_three]; omega
    simp only [this, enc32, ↓reduceIte, not_false_eq_true, and_self, true_and, Option.some.injEq,
      List.cons.injEq, and_true]
    simp only [← UInt8.toNat_inj, UInt8.toNat_ofNat', cpOf_three]; omega
  | [b1, b2, b3, b4], h =>
    simp only [isVS, isLead4_iff, secondOk_iff, isCont_iff, Bool.and_eq_true] at h
    have : (cpOf [b1, b2, b3, b4]).toNat ≤ 0x10FFFF ∧
      ¬ (0xD800 ≤ (cpOf [b1, b2, b3, b4]).toNat ∧ (cpOf [b1, b2, b3, b4]).toNat ≤ 0xDFFF) ∧
      (cpOf [b1, b2, b3, b4]).toNat < 0x200000 ∧ ¬ (cpOf [b1, b2, b3, b4]).toNat < 0x80 ∧
      ¬ (cpOf [b1, b2, b3, b4]).toNat < 0x800 ∧ ¬ (cpOf [b1, b2, b3, b4]).toNat < 0x10000 := by
      rw [cpOf_four]; omega
    simp only [this, enc32, ↓reduceIte, not_false_eq_true, and_self, true_and, Option.some.injEq,
      List.cons.injEq, and_true]
    simp only [← UInt8.toNat_inj, UInt8.toNat_ofNat', cpOf_four]; omega

theorem isVS_of_encodes (seq : List UInt8) (cp : UInt32) (h : encodes seq cp) :
    isVS seq = true ∧ cp = cpOf seq := by
  obtain ⟨hs, he⟩ := h
  rw [is_unicode_scalar_iff] at hs
  have h2 : cp.toNat < 0x200000 := by omega
  rw [encoding_eq] at he
  simp only [h2, ↓reduceIte, Option.some.injEq] at he
  subst he
  have hn := cp.toNat_lt
  unfold enc32
  by_cases c1 : cp.toNat < 0x80
  · simp only [c1, ↓reduceIte, isVS, isLead1_iff, ← UInt32.toNat_inj, cpOf_one, UInt8.toNat_ofNat']
    omega
  by_cases c2 : cp.toNat < 0x800
  · simp only [c1, c2, ↓reduceIte, isVS, isLead2_iff, secondOk_iff, Bool.and_eq_true,
      ← UInt32.toNat_inj, cpOf_two, UInt8.toNat_ofNat']
    omega
  by_cases c3 : cp.toNat < 0x10000
  · simp only [c1, c2, c3, ↓reduceIte, isVS, isLead3_iff, secondOk_iff, isCont_iff, Bool.and_eq_true,
      ← UInt32.toNat_inj, cpOf_three, UInt8.toNat_ofNat']
    omega
  · simp only [c1, c2, c3, ↓reduceIte, isVS, isLead4_iff, secondOk_iff, isCont_iff, Bool.and_eq_true,
      ← UInt32.toNat_inj, cpOf_four, UInt8.toNat_ofNat']
    omega

theorem encodes_iff (seq : List UInt8) (cp : UInt32) :
    encodes seq cp ↔ isVS seq = true ∧ cp = cpOf seq :=
  ⟨isVS_of_encodes seq cp, fun ⟨h, e⟩ => e ▸ encodes_of_isVS seq h⟩

/-! ## Structural facts about `isVS` / `isVSP` (Bool reasoning; byte classes are disjoint) -/

/-- The lead-byte classes are pairwise disjoint (conditional `simp` rewrites). -/
theorem lead1_not (a : UInt8) (h : isLead1 a = true) :
    isLead2 a = false ∧ isLead3 a = false ∧ isLead4 a = false := by
  simp only [Bool.eq_false_iff, ne_eq, isLead1_iff, isLead2_iff, isLead3_iff, isLead4_iff] at *; omega
theorem lead2_not (a : UInt8) (h : isLead2 a = true) : isLead3 a = false ∧ isLead4 a = false := by
  simp only [Bool.eq_false_iff, ne_eq, isLead2_iff, isLead3_iff, isLead4_iff] at *; omega
theorem lead3_not (a : UInt8) (h : isLead3 a = true) : isLead4 a = false := by
  simp only [Bool.eq_false_iff, ne_eq, isLead3_iff, isLead4_iff] at *; omega

theorem isVS_isVSP (l : List UInt8) (h : isVS l = true) : isVSP l = true := by
  match l with
  | [_] | [_, _] | [_, _, _] | [_, _, _, _] => simp_all [isVS, isVSP]
  | [] | _ :: _ :: _ :: _ :: _ :: _ => simp [isVS] at h

theorem isVSP_of_isVS_append (l r : List UInt8) (hne : l ≠ []) (h : isVS (l ++ r) = true) :
    isVSP l = true := by
  rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, _ | ⟨e, l⟩⟩⟩⟩⟩ <;>
  rcases r with _ | ⟨x, _ | ⟨y, _ | ⟨z, _ | ⟨w, r⟩⟩⟩⟩ <;> simp_all [isVS, isVSP]

theorem isVS_not_proper (l : List UInt8) (c : UInt8) (e : List UInt8) (h : isVS l = true) :
    isVSP (l ++ c :: e) = false := by
  rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, _ | ⟨e, l⟩⟩⟩⟩⟩ <;>
  rcases e with _ | ⟨x, _ | ⟨y, _ | ⟨z, e⟩⟩⟩ <;>
  simp_all [isVS, isVSP, lead1_not, lead2_not, lead3_not]

/-- Second byte that completes a lead byte: the low end of its allowed range. -/
def secondLo (a : UInt8) : UInt8 :=
  if a = 0xE0 then 0xA0 else if a = 0xF0 then 0x90 else 0x80

/-- Bytes that complete a pending (valid prefix, not whole) state. -/
def completion : List UInt8 → List UInt8
  | [a] => if isLead2 a then [0x80] else if isLead3 a then [secondLo a, 0x80]
           else [secondLo a, 0x80, 0x80]
  | [a, _] => if isLead3 a then [0x80] else [0x80, 0x80]
  | _ => [0x80]

theorem secondOk_80 (a : UInt8) (h1 : a ≠ 0xE0) (h2 : a ≠ 0xF0) : secondOk a 0x80 = true := by
  unfold secondOk; simp only [h1, h2, ite_false]
  repeat' split
  all_goals decide

theorem secondOk_secondLo (a : UInt8) : secondOk a (secondLo a) = true := by
  by_cases h1 : a = 0xE0
  · subst h1; decide
  by_cases h2 : a = 0xF0
  · subst h2; decide
  simp only [secondLo, h1, h2, ite_false]; exact secondOk_80 a h1 h2

/-- Every completion ends in the byte 0x80, so the completed code point is
`0 mod 64`, while U+FFFD is `61 mod 64`. -/
theorem completion_spec (p : List UInt8) (h1 : isVSP p = true) (h2 : isVS p = false) :
    isVS (p ++ completion p) = true ∧ cpOf (p ++ completion p) ≠ 0xFFFD := by
  have c80 : isCont 0x80 = true := rfl
  rw [ne_eq, ← UInt32.toNat_inj]
  match p, h1, h2 with
  | [a], h1, h2 =>
    simp only [isVS, isVSP] at h1 h2
    simp only [completion]
    by_cases l2 : isLead2 a = true
    · have e0 : a ≠ 0xE0 := by rintro rfl; exact absurd l2 (by decide)
      have f0 : a ≠ 0xF0 := by rintro rfl; exact absurd l2 (by decide)
      simp [l2, isVS, secondOk_80 a e0 f0, cpOf_two]; omega
    by_cases l3 : isLead3 a = true
    · simp [l2, l3, isVS, secondOk_secondLo, c80, cpOf_three]; omega
    · have l4 : isLead4 a = true := by simp_all
      simp [l2, l3, l4, isVS, secondOk_secondLo, c80, cpOf_four]; omega
  | [a, b], h1, h2 =>
    simp only [isVS, isVSP, Bool.and_eq_true, Bool.or_eq_true] at h1 h2
    simp only [completion]
    cases l2 : isLead2 a <;> cases l3 : isLead3 a <;> cases l4 : isLead4 a <;>
      simp_all [isVS, cpOf_three, cpOf_four] <;> omega
  | [a, b, c], h1, h2 =>
    simp only [isVS, isVSP, Bool.and_eq_true, Bool.or_eq_true] at h1 h2
    simp only [completion]
    cases l3 : isLead3 a <;> cases l4 : isLead4 a <;> simp_all [isVS, cpOf_four] <;> omega
  | [_, _, _, _], h1, h2 => simp_all [isVS, isVSP]
  | [], h1, _ | _ :: _ :: _ :: _ :: _ :: _, h1, _ => simp [isVSP] at h1

theorem isVSP_extends (l : List UInt8) (h : isVSP l = true) : ∃ r, isVS (l ++ r) = true := by
  cases hv : isVS l
  · exact ⟨_, (completion_spec l h hv).1⟩
  · exact ⟨[], by simpa using hv⟩

end Utf8Pure
