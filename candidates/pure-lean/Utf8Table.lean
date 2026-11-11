/-
Byte-table facts: `encodes_iff` (the spec's encodes <-> table membership and
shift/mask value) and finite facts about `isVS`/`isVSP`.
Kernel-checked: `omega` over `toNat` values, no `bv_decide`.
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
  simp only [Nat.reducePow, Nat.reduceMod, and_mask_31, and_mask_15, and_mask_7, and_mask_63]
  rw [Nat.mod_eq_of_lt (by omega), nat_or_add _ _ 6 (by simp only [Nat.reducePow]; omega) (by simp only [Nat.reducePow]; omega)]
  all_goals omega

theorem cpOf_three (b1 b2 b3 : UInt8) :
    (cpOf [b1, b2, b3]).toNat = b1.toNat % 16 * 4096 + b2.toNat % 64 * 64 + b3.toNat % 64 := by
  have h1 := b1.toNat_lt; have h2 := b2.toNat_lt; have h3 := b3.toNat_lt
  simp only [cpOf, UInt32.toNat_or, UInt32.toNat_and, UInt32.toNat_shiftLeft, UInt8.toNat_toUInt32,
    UInt32.toNat_ofNat, Nat.shiftLeft_eq]
  simp only [Nat.reducePow, Nat.reduceMod, and_mask_31, and_mask_15, and_mask_7, and_mask_63]
  rw [Nat.mod_eq_of_lt (a := _ * 4096) (by omega), Nat.mod_eq_of_lt (a := _ * 64) (by omega),
    nat_or_add (b1.toNat % 16 * 4096) (b2.toNat % 64 * 64) 12 (by simp only [Nat.reducePow]; omega) (by simp only [Nat.reducePow]; omega),
    nat_or_add (b1.toNat % 16 * 4096 + b2.toNat % 64 * 64) _ 6 (by simp only [Nat.reducePow]; omega) (by simp only [Nat.reducePow]; omega)]

theorem cpOf_four (b1 b2 b3 b4 : UInt8) :
    (cpOf [b1, b2, b3, b4]).toNat =
      b1.toNat % 8 * 262144 + b2.toNat % 64 * 4096 + b3.toNat % 64 * 64 + b4.toNat % 64 := by
  have h1 := b1.toNat_lt; have h2 := b2.toNat_lt; have h3 := b3.toNat_lt; have h4 := b4.toNat_lt
  simp only [cpOf, UInt32.toNat_or, UInt32.toNat_and, UInt32.toNat_shiftLeft, UInt8.toNat_toUInt32,
    UInt32.toNat_ofNat, Nat.shiftLeft_eq]
  simp only [Nat.reducePow, Nat.reduceMod, and_mask_31, and_mask_15, and_mask_7, and_mask_63]
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
  by_cases h1 : b1.toNat = 0xE0 <;> by_cases h2 : b1.toNat = 0xED <;>
    by_cases h3 : b1.toNat = 0xF0 <;> by_cases h4 : b1.toNat = 0xF4 <;>
    simp only [h1, h2, h3, h4, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq] <;>
    (first | omega | (constructor <;> intro h <;> omega) | (simp_all <;> omega))

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

macro "byte_table" : tactic => `(tactic| (
  simp only [isVS, isVSP, List.cons_append, List.nil_append, List.append_nil, Bool.false_eq_true,
    Bool.eq_false_iff, ne_eq, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true,
    isCont_iff, isLead1_iff, isLead2_iff, isLead3_iff, isLead4_iff, secondOk_iff,
    cpOf_one, cpOf_two, cpOf_three, cpOf_four] at * <;>
  first | done | omega | (simp_all <;> omega)))

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

/-! ## Byte-table facts (finite case analysis + `omega`) -/

theorem isVS_isVSP (l : List UInt8) (h : isVS l = true) : isVSP l = true := by
  rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, _ | ⟨e, l⟩⟩⟩⟩⟩ <;> byte_table

theorem isVSP_of_isVS_append (l r : List UInt8) (hne : l ≠ []) (h : isVS (l ++ r) = true) :
    isVSP l = true := by
  rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, _ | ⟨e, l⟩⟩⟩⟩⟩ <;>
  rcases r with _ | ⟨x, _ | ⟨y, _ | ⟨z, _ | ⟨w, r⟩⟩⟩⟩ <;> first | exact absurd rfl hne | byte_table

theorem isVS_not_proper (l : List UInt8) (c : UInt8) (e : List UInt8) (h : isVS l = true) :
    isVSP (l ++ c :: e) = false := by
  rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, _ | ⟨e, l⟩⟩⟩⟩⟩ <;>
  rcases e with _ | ⟨x, _ | ⟨y, _ | ⟨z, e⟩⟩⟩ <;> byte_table

/-- Second byte that completes a lead byte: the low end of its allowed range. -/
def secondLo (a : UInt8) : UInt8 :=
  if a = 0xE0 then 0xA0 else if a = 0xF0 then 0x90 else 0x80

/-- Bytes that complete a pending (valid prefix, not whole) state. -/
def completion : List UInt8 → List UInt8
  | [a] => if isLead2 a then [0x80] else if isLead3 a then [secondLo a, 0x80]
           else [secondLo a, 0x80, 0x80]
  | [a, _] => if isLead3 a then [0x80] else [0x80, 0x80]
  | _ => [0x80]

set_option maxHeartbeats 2000000 in
theorem completion_spec (p : List UInt8) (h1 : isVSP p = true) (h2 : isVS p = false) :
    isVS (p ++ completion p) = true ∧ cpOf (p ++ completion p) ≠ 0xFFFD := by
  rw [ne_eq, ← UInt32.toNat_inj]
  rcases p with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, l⟩⟩⟩⟩
  · simp [isVSP] at h1
  · have k : ∀ c : UInt8, a = c ↔ a.toNat = c.toNat := fun c => UInt8.toNat_inj.symm
    simp only [completion]
    by_cases e0 : a.toNat = 0xE0 <;> by_cases f0 : a.toNat = 0xF0 <;>
      simp only [secondLo, k, e0, f0, UInt8.toNat_ofNat, Nat.reducePow, Nat.reduceMod, ↓reduceIte] <;>
      split <;> (try split) <;> byte_table
  · simp only [completion]; split <;> byte_table
  · simp only [completion]; byte_table
  · rcases l with _ | ⟨e, l⟩ <;> byte_table

theorem isVSP_extends (l : List UInt8) (h : isVSP l = true) : ∃ r, isVS (l ++ r) = true := by
  cases hv : isVS l
  · exact ⟨_, (completion_spec l h hv).1⟩
  · exact ⟨[], by simpa using hv⟩

end Utf8Pure
