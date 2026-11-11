/-
Bit-level bridge between the spec's tuple-of-bools byte shapes and
`Nat` arithmetic on `cp.toNat`.  Kernel-checked: no `bv_decide`.
Everything bit-level in the development is in this file; later files
work with `encoding_eq`.
-/
import Utf8Laws

namespace Utf8Pure

theorem bit8_toNat (b7 b6 b5 b4 b3 b2 b1 b0 : Bool) :
    (bit8_value (b7, b6, b5, b4, b3, b2, b1, b0)).toNat =
      b7.toNat * 128 + b6.toNat * 64 + b5.toNat * 32 + b4.toNat * 16 +
      b3.toNat * 8 + b2.toNat * 4 + b1.toNat * 2 + b0.toNat := by
  revert b7 b6 b5 b4 b3 b2 b1 b0; decide

theorem getLsbD_toNat (cp : UInt32) (i : Nat) :
    (cp.toBitVec.getLsbD i).toNat = cp.toNat / 2 ^ i % 2 := by
  show (cp.toNat.testBit i).toNat = _
  rw [Nat.testBit_eq_decide_div_mod_eq]
  rcases Nat.mod_two_eq_zero_or_one (cp.toNat / 2 ^ i) with h | h <;> simp [h]

theorem getLsbD_false (cp : UInt32) (i : Nat) :
    cp.toBitVec.getLsbD i = false ↔ cp.toNat / 2 ^ i % 2 = 0 := by
  have := getLsbD_toNat cp i
  cases h : cp.toBitVec.getLsbD i <;> simp_all <;> omega

theorem one_shape (cp : UInt32) :
    one_byte_shape cp = if cp.toNat < 0x80 then some (UInt8.ofNat cp.toNat) else none := by
  have hn := cp.toNat_lt
  unfold one_byte_shape one_byte_shape.bits u32_byte4
  split
  · rename_i heq
    simp only [Prod.mk.injEq] at heq
    obtain ⟨⟨h1,h2,h3,h4,h5,h6,h7,h8⟩,⟨g1,g2,g3,g4,g5,g6,g7,g8⟩,⟨f1,f2,f3,f4,f5,f6,f7,f8⟩,⟨e1,e2,e3,e4,e5,e6,e7,e8⟩⟩ := heq
    subst_vars
    simp only [getLsbD_false] at *
    have h : cp.toNat < 0x80 := by omega
    simp only [h, ↓reduceIte, Option.some.injEq]
    apply UInt8.toNat.inj
    rw [bit8_toNat]
    simp only [getLsbD_toNat, Bool.toNat_false, Bool.toNat_true, UInt8.toNat_ofNat']
    omega
  · rename_i hne
    have h : ¬ cp.toNat < 0x80 := by
      intro h
      apply hne (cp.toBitVec.getLsbD 6) (cp.toBitVec.getLsbD 5) (cp.toBitVec.getLsbD 4) (cp.toBitVec.getLsbD 3) (cp.toBitVec.getLsbD 2) (cp.toBitVec.getLsbD 1) (cp.toBitVec.getLsbD 0)
      clear hne
      simp only [Prod.mk.injEq, and_true, getLsbD_false]
      omega
    simp only [h, ↓reduceIte]

theorem two_shape (cp : UInt32) :
    two_byte_shape cp = if cp.toNat < 0x800 then some (UInt8.ofNat (0xC0 + cp.toNat / 64), UInt8.ofNat (0x80 + cp.toNat % 64)) else none := by
  have hn := cp.toNat_lt
  unfold two_byte_shape two_byte_shape.bits u32_byte4
  split
  · rename_i heq
    simp only [Prod.mk.injEq] at heq
    obtain ⟨⟨h1,h2,h3,h4,h5,h6,h7,h8⟩,⟨g1,g2,g3,g4,g5,g6,g7,g8⟩,⟨f1,f2,f3,f4,f5,f6,f7,f8⟩,⟨e1,e2,e3,e4,e5,e6,e7,e8⟩⟩ := heq
    subst_vars
    simp only [getLsbD_false] at *
    have h : cp.toNat < 0x800 := by omega
    simp only [h, ↓reduceIte, Option.some.injEq]
    simp only [Prod.mk.injEq]
    refine ⟨?_, ?_⟩ <;>
    (apply UInt8.toNat.inj
     rw [bit8_toNat]
     simp only [getLsbD_toNat, Bool.toNat_false, Bool.toNat_true, UInt8.toNat_ofNat']
     omega)
  · rename_i hne
    have h : ¬ cp.toNat < 0x800 := by
      intro h
      apply hne (cp.toBitVec.getLsbD 10) (cp.toBitVec.getLsbD 9) (cp.toBitVec.getLsbD 8) (cp.toBitVec.getLsbD 7) (cp.toBitVec.getLsbD 6) (cp.toBitVec.getLsbD 5) (cp.toBitVec.getLsbD 4) (cp.toBitVec.getLsbD 3) (cp.toBitVec.getLsbD 2) (cp.toBitVec.getLsbD 1) (cp.toBitVec.getLsbD 0)
      clear hne
      simp only [Prod.mk.injEq, and_true, getLsbD_false]
      omega
    simp only [h, ↓reduceIte]

theorem three_shape (cp : UInt32) :
    three_byte_shape cp = if cp.toNat < 0x10000 then some (UInt8.ofNat (0xE0 + cp.toNat / 4096), UInt8.ofNat (0x80 + cp.toNat / 64 % 64),
      UInt8.ofNat (0x80 + cp.toNat % 64)) else none := by
  have hn := cp.toNat_lt
  unfold three_byte_shape three_byte_shape.bits u32_byte4
  split
  · rename_i heq
    simp only [Prod.mk.injEq] at heq
    obtain ⟨⟨h1,h2,h3,h4,h5,h6,h7,h8⟩,⟨g1,g2,g3,g4,g5,g6,g7,g8⟩,⟨f1,f2,f3,f4,f5,f6,f7,f8⟩,⟨e1,e2,e3,e4,e5,e6,e7,e8⟩⟩ := heq
    subst_vars
    simp only [getLsbD_false] at *
    have h : cp.toNat < 0x10000 := by omega
    simp only [h, ↓reduceIte, Option.some.injEq]
    simp only [Prod.mk.injEq]
    refine ⟨?_, ?_, ?_⟩ <;>
    (apply UInt8.toNat.inj
     rw [bit8_toNat]
     simp only [getLsbD_toNat, Bool.toNat_false, Bool.toNat_true, UInt8.toNat_ofNat']
     omega)
  · rename_i hne
    have h : ¬ cp.toNat < 0x10000 := by
      intro h
      apply hne (cp.toBitVec.getLsbD 15) (cp.toBitVec.getLsbD 14) (cp.toBitVec.getLsbD 13) (cp.toBitVec.getLsbD 12) (cp.toBitVec.getLsbD 11) (cp.toBitVec.getLsbD 10) (cp.toBitVec.getLsbD 9) (cp.toBitVec.getLsbD 8) (cp.toBitVec.getLsbD 7) (cp.toBitVec.getLsbD 6) (cp.toBitVec.getLsbD 5) (cp.toBitVec.getLsbD 4) (cp.toBitVec.getLsbD 3) (cp.toBitVec.getLsbD 2) (cp.toBitVec.getLsbD 1) (cp.toBitVec.getLsbD 0)
      clear hne
      simp only [Prod.mk.injEq, and_true, getLsbD_false]
      omega
    simp only [h, ↓reduceIte]

theorem four_shape (cp : UInt32) :
    four_byte_shape cp = if cp.toNat < 0x200000 then some (UInt8.ofNat (0xF0 + cp.toNat / 262144), UInt8.ofNat (0x80 + cp.toNat / 4096 % 64),
      UInt8.ofNat (0x80 + cp.toNat / 64 % 64), UInt8.ofNat (0x80 + cp.toNat % 64)) else none := by
  have hn := cp.toNat_lt
  unfold four_byte_shape four_byte_shape.bits u32_byte4
  split
  · rename_i heq
    simp only [Prod.mk.injEq] at heq
    obtain ⟨⟨h1,h2,h3,h4,h5,h6,h7,h8⟩,⟨g1,g2,g3,g4,g5,g6,g7,g8⟩,⟨f1,f2,f3,f4,f5,f6,f7,f8⟩,⟨e1,e2,e3,e4,e5,e6,e7,e8⟩⟩ := heq
    subst_vars
    simp only [getLsbD_false] at *
    have h : cp.toNat < 0x200000 := by omega
    simp only [h, ↓reduceIte, Option.some.injEq]
    simp only [Prod.mk.injEq]
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
    (apply UInt8.toNat.inj
     rw [bit8_toNat]
     simp only [getLsbD_toNat, Bool.toNat_false, Bool.toNat_true, UInt8.toNat_ofNat']
     omega)
  · rename_i hne
    have h : ¬ cp.toNat < 0x200000 := by
      intro h
      apply hne (cp.toBitVec.getLsbD 20) (cp.toBitVec.getLsbD 19) (cp.toBitVec.getLsbD 18) (cp.toBitVec.getLsbD 17) (cp.toBitVec.getLsbD 16) (cp.toBitVec.getLsbD 15) (cp.toBitVec.getLsbD 14) (cp.toBitVec.getLsbD 13) (cp.toBitVec.getLsbD 12) (cp.toBitVec.getLsbD 11) (cp.toBitVec.getLsbD 10) (cp.toBitVec.getLsbD 9) (cp.toBitVec.getLsbD 8) (cp.toBitVec.getLsbD 7) (cp.toBitVec.getLsbD 6) (cp.toBitVec.getLsbD 5) (cp.toBitVec.getLsbD 4) (cp.toBitVec.getLsbD 3) (cp.toBitVec.getLsbD 2) (cp.toBitVec.getLsbD 1) (cp.toBitVec.getLsbD 0)
      clear hne
      simp only [Prod.mk.injEq, and_true, getLsbD_false]
      omega
    simp only [h, ↓reduceIte]

/-- The shortest-form encoding as `Nat` arithmetic on `n = cp.toNat`
(meaningful for `n < 0x200000`). -/
def enc32 (cp : UInt32) : List UInt8 :=
  let n := cp.toNat
  if n < 0x80 then [UInt8.ofNat n]
  else if n < 0x800 then [UInt8.ofNat (0xC0 + n / 64), UInt8.ofNat (0x80 + n % 64)]
  else if n < 0x10000 then
    [UInt8.ofNat (0xE0 + n / 4096), UInt8.ofNat (0x80 + n / 64 % 64), UInt8.ofNat (0x80 + n % 64)]
  else
    [UInt8.ofNat (0xF0 + n / 262144), UInt8.ofNat (0x80 + n / 4096 % 64),
     UInt8.ofNat (0x80 + n / 64 % 64), UInt8.ofNat (0x80 + n % 64)]

theorem encoding_eq (cp : UInt32) :
    encoding cp = if cp.toNat < 0x200000 then some (enc32 cp) else none := by
  unfold encoding encoding.«if» encoding.two encoding.three encoding.four
  rw [one_shape, two_shape, three_shape, four_shape]
  by_cases h1 : cp.toNat < 0x80
  · have : cp.toNat < 0x200000 := by omega
    simp [h1, this, enc32]
  by_cases h2 : cp.toNat < 0x800
  · have : cp.toNat < 0x200000 := by omega
    simp [h1, h2, this, enc32]
  by_cases h3 : cp.toNat < 0x10000
  · have : cp.toNat < 0x200000 := by omega
    simp [h1, h2, h3, this, enc32]
  by_cases h4 : cp.toNat < 0x200000
  · simp [h1, h2, h3, h4, enc32]
  · simp [h1, h2, h3, h4]

end Utf8Pure
