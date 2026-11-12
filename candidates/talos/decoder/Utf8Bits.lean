/-
Utf8Bits.lean -- bit-level bridge from the spec's tuple-of-Bool byte shapes
to `Nat` arithmetic on `cp.toNat`.  The only file that looks at bits; later
files use `encoding_eq`.

EXPORTS
  one_shape two_shape three_shape four_shape
      `<k>_byte_shape cp = if cp.toNat < 2^w then some (bytes as Nat arithmetic) else none`
  enc32 cp : List UInt8     shortest-form encoding, `Nat` arithmetic on `cp.toNat`
  encoding_eq : encoding cp = if cp.toNat < 0x200000 then some (enc32 cp) else none
  helpers: bit8_toNat, testBit_toNat, lowBits, lowBits_eq, testBit_high, lt_of_testBit,
    getLsbD_eq_testBit; tactic macros high_bits_clear, byte_value (local use)

METHOD (why it is fast)
  `u32_byte4` reads bit i as `cp.toNat.testBit i` (definitionally).  Each
  shape lemma splits on the spec's match:
  - match fails: if `cp.toNat < 2^w` all bits >= w are clear (`testBit_high`),
    so the match would succeed with the low bits -- contradiction; no omega.
  - match succeeds: the clear high bits give `cp.toNat < 2^w`
    (`lt_of_testBit`, one bit position at a time), and each byte value is a
    small `omega` goal with only that byte's <= 8 bit atoms (`byte_value`).
  The first version gave `omega` all 32 bit atoms at once (12 s per file).
-/
import Utf8Laws

namespace Utf8Pure

/-- The spec's `bit8_value` as a weighted sum (256 cases, `decide`). -/
theorem bit8_toNat (b7 b6 b5 b4 b3 b2 b1 b0 : Bool) :
    (bit8_value (b7, b6, b5, b4, b3, b2, b1, b0)).toNat =
      b7.toNat * 128 + b6.toNat * 64 + b5.toNat * 32 + b4.toNat * 16 +
      b3.toNat * 8 + b2.toNat * 4 + b1.toNat * 2 + b0.toNat := by
  revert b7 b6 b5 b4 b3 b2 b1 b0; decide

/-- A bit as `0`/`1`. -/
theorem testBit_toNat (n i : Nat) : (n.testBit i).toNat = n / 2 ^ i % 2 := by
  rw [Nat.testBit_eq_decide_div_mod_eq]
  rcases Nat.mod_two_eq_zero_or_one (n / 2 ^ i) with h | h <;> simp [h]

/-- The low `k` bits of `n`, summed with their weights (`lowBits_eq`). -/
def lowBits (n : Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => lowBits n k + n / 2 ^ k % 2 * 2 ^ k

theorem lowBits_eq (n k : Nat) : lowBits n k = n % 2 ^ k := by
  induction k with
  | zero => simp [lowBits, Nat.mod_one]
  | succ k ih => rw [lowBits, ih, Nat.mod_pow_succ, Nat.mul_comm]

/-- Bits at or above `k` of a number below `2 ^ k` are clear. -/
theorem testBit_high {n k : Nat} (h : n < 2 ^ k) (i : Nat) (hi : k ≤ i) : n.testBit i = false :=
  Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le h (Nat.pow_le_pow_right (by decide) hi))

/-- A 32-bit number whose bits `k .. 31` are clear is below `2 ^ k`. -/
theorem lt_of_testBit {n : Nat} (k : Nat) (hn : n < 2 ^ 32)
    (h : ∀ i, k ≤ i → i < 32 → n.testBit i = false) : n < 2 ^ k :=
  Nat.lt_pow_two_of_testBit n fun i hi =>
    if h32 : i < 32 then h i hi h32 else testBit_high hn i (by omega)

/-- From the shape's high zero bits (hypotheses `n.testBit i = false`, `k ≤ i < 32`)
to `n < 2 ^ k`, one candidate bit position at a time. -/
macro "high_bits_clear" : tactic => `(tactic| (
  intro i hk hi
  repeat (rcases Nat.eq_or_lt_of_le hk with e | hk; · subst e; assumption)
  omega))

/-- `byte_value cp k b` proves a byte-value goal `UInt8.ofNat e = bit8_value (...)`
whose free bits are bits `k .. k+b-1` of `cp.toNat`: it puts in context only
`lowBits (cp.toNat / 2 ^ k) b = cp.toNat / 2 ^ k % 2 ^ b`, so `omega` sees at
most eight bit atoms. -/
macro "byte_value" cp:term:max k:num b:num : tactic => `(tactic| (
  rw [← UInt8.toNat_inj]
  have hl := lowBits_eq (($cp).toNat / 2 ^ $k) $b
  simp only [lowBits, Nat.div_div_eq_div_mul, Nat.reducePow, Nat.reduceMul] at hl
  simp only [bit8_toNat, testBit_toNat, Bool.toNat_false, Bool.toNat_true, UInt8.toNat_ofNat',
    Nat.reducePow]
  omega))

/-- `u32_byte4` reads bit `i` of `cp` as `cp.toNat.testBit i`. -/
theorem getLsbD_eq_testBit (cp : UInt32) (i : Nat) : cp.toBitVec.getLsbD i = cp.toNat.testBit i := rfl

theorem one_shape (cp : UInt32) :
    one_byte_shape cp = if cp.toNat < 0x80 then some (UInt8.ofNat cp.toNat) else none := by
  unfold one_byte_shape one_byte_shape.bits u32_byte4
  simp only [getLsbD_eq_testBit]
  split
  · rename_i heq
    simp only [Prod.mk.injEq] at heq
    obtain ⟨⟨h31,h30,h29,h28,h27,h26,h25,h24⟩,⟨h23,h22,h21,h20,h19,h18,h17,h16⟩,
      ⟨h15,h14,h13,h12,h11,h10,h9,h8⟩,⟨h7,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩⟩ := heq
    have h : cp.toNat < 0x80 := lt_of_testBit 7 cp.toNat_lt (by high_bits_clear)
    simp only [h, ↓reduceIte, Option.some.injEq]
    byte_value cp 0 7
  · rename_i hne
    have h : ¬ cp.toNat < 0x80 := fun h => hne _ _ _ _ _ _ _ (by
      simp only [testBit_high (k := 7) h, Nat.reduceLeDiff]; rfl)
    simp only [h, ↓reduceIte]

theorem two_shape (cp : UInt32) :
    two_byte_shape cp = if cp.toNat < 0x800 then some (UInt8.ofNat (0xC0 + cp.toNat / 64), UInt8.ofNat (0x80 + cp.toNat % 64)) else none := by
  unfold two_byte_shape two_byte_shape.bits u32_byte4
  simp only [getLsbD_eq_testBit]
  split
  · rename_i heq
    simp only [Prod.mk.injEq] at heq
    obtain ⟨⟨h31,h30,h29,h28,h27,h26,h25,h24⟩,⟨h23,h22,h21,h20,h19,h18,h17,h16⟩,
      ⟨h15,h14,h13,h12,h11,rfl,rfl,rfl⟩,⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩⟩ := heq
    have h : cp.toNat < 0x800 := lt_of_testBit 11 cp.toNat_lt (by high_bits_clear)
    simp only [h, ↓reduceIte, Option.some.injEq, Prod.mk.injEq]
    exact ⟨by byte_value cp 6 5, by byte_value cp 0 6⟩
  · rename_i hne
    have h : ¬ cp.toNat < 0x800 := fun h => hne _ _ _ _ _ _ _ _ _ _ _ (by
      simp only [testBit_high (k := 11) h, Nat.reduceLeDiff]; rfl)
    simp only [h, ↓reduceIte]

theorem three_shape (cp : UInt32) :
    three_byte_shape cp = if cp.toNat < 0x10000 then some (UInt8.ofNat (0xE0 + cp.toNat / 4096), UInt8.ofNat (0x80 + cp.toNat / 64 % 64),
      UInt8.ofNat (0x80 + cp.toNat % 64)) else none := by
  unfold three_byte_shape three_byte_shape.bits u32_byte4
  simp only [getLsbD_eq_testBit]
  split
  · rename_i heq
    simp only [Prod.mk.injEq] at heq
    obtain ⟨⟨h31,h30,h29,h28,h27,h26,h25,h24⟩,⟨h23,h22,h21,h20,h19,h18,h17,h16⟩,
      ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩,⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩⟩ := heq
    have h : cp.toNat < 0x10000 := lt_of_testBit 16 cp.toNat_lt (by high_bits_clear)
    simp only [h, ↓reduceIte, Option.some.injEq, Prod.mk.injEq]
    exact ⟨by byte_value cp 12 4, by byte_value cp 6 6, by byte_value cp 0 6⟩
  · rename_i hne
    have h : ¬ cp.toNat < 0x10000 := fun h => hne _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (by
      simp only [testBit_high (k := 16) h, Nat.reduceLeDiff]; rfl)
    simp only [h, ↓reduceIte]

theorem four_shape (cp : UInt32) :
    four_byte_shape cp = if cp.toNat < 0x200000 then some (UInt8.ofNat (0xF0 + cp.toNat / 262144), UInt8.ofNat (0x80 + cp.toNat / 4096 % 64),
      UInt8.ofNat (0x80 + cp.toNat / 64 % 64), UInt8.ofNat (0x80 + cp.toNat % 64)) else none := by
  unfold four_byte_shape four_byte_shape.bits u32_byte4
  simp only [getLsbD_eq_testBit]
  split
  · rename_i heq
    simp only [Prod.mk.injEq] at heq
    obtain ⟨⟨h31,h30,h29,h28,h27,h26,h25,h24⟩,⟨h23,h22,h21,rfl,rfl,rfl,rfl,rfl⟩,⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩,⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩⟩ := heq
    have h : cp.toNat < 0x200000 := lt_of_testBit 21 cp.toNat_lt (by high_bits_clear)
    simp only [h, ↓reduceIte, Option.some.injEq, Prod.mk.injEq]
    exact ⟨by byte_value cp 18 3, by byte_value cp 12 6, by byte_value cp 6 6, by byte_value cp 0 6⟩
  · rename_i hne
    have h : ¬ cp.toNat < 0x200000 := fun h => hne _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (by
      simp only [testBit_high (k := 21) h, Nat.reduceLeDiff]; rfl)
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
