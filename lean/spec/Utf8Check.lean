/- Specification cross-checks. This module imports only the specification.
Arithmetic lemmas below expose the values of the specified bit patterns;
no decoder or executable sequence classifier is used. -/
import Utf8Laws

namespace Utf8SpecCheck

/-! ## Arithmetic facts about the specified byte shapes -/

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
  unfold one_byte_shape u32_byte4
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
  unfold two_byte_shape u32_byte4
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
  unfold three_byte_shape u32_byte4
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
  unfold four_byte_shape u32_byte4
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


-- The four possible encodings, with their shortest-form bounds.
theorem encoding_cases (cp : UInt32) (seq : List UInt8) (h : encoding cp = some seq) :
    (cp.toNat < 128 ∧ seq = [UInt8.ofNat cp.toNat]) ∨
    (128 ≤ cp.toNat ∧ cp.toNat < 2048 ∧ seq = [UInt8.ofNat (192 + cp.toNat / 64), UInt8.ofNat (128 + cp.toNat % 64)]) ∨
    (2048 ≤ cp.toNat ∧ cp.toNat < 65536 ∧ seq = [UInt8.ofNat (224 + cp.toNat / 4096), UInt8.ofNat (128 + cp.toNat / 64 % 64), UInt8.ofNat (128 + cp.toNat % 64)]) ∨
    (65536 ≤ cp.toNat ∧ cp.toNat < 2097152 ∧ seq = [UInt8.ofNat (240 + cp.toNat / 262144), UInt8.ofNat (128 + cp.toNat / 4096 % 64), UInt8.ofNat (128 + cp.toNat / 64 % 64), UInt8.ofNat (128 + cp.toNat % 64)]) := by
  unfold encoding encoding.two encoding.three encoding.four at h
  rw [one_shape, two_shape, three_shape, four_shape] at h
  split at h <;> simp_all
  split at h <;> simp_all
  split at h <;> simp_all
  split at h <;> simp_all

theorem encoding_front (a b : UInt32) (s t r u : List UInt8)
    (ha : encoding a = some s) (hb : encoding b = some t)
    (he : s ++ r = t ++ u) : a = b ∧ s = t := by
  have h := encoding_cases a s ha
  have k := encoding_cases b t hb
  rcases h with ⟨h, rfl⟩ | ⟨h, hh, rfl⟩ | ⟨h, hh, rfl⟩ | ⟨h, hh, rfl⟩ <;>
    rcases k with ⟨k, rfl⟩ | ⟨k, kk, rfl⟩ | ⟨k, kk, rfl⟩ | ⟨k, kk, rfl⟩ <;>
    simp only [List.cons_append, List.nil_append, List.cons.injEq] at he <;>
    simp only [← UInt8.toNat_inj, UInt8.toNat_ofNat'] at he
  all_goals
    have hab : a = b := by
      apply UInt32.toNat_inj.mp
      omega
    subst b
    exact ⟨rfl, Option.some.inj (ha.symm.trans hb)⟩

end Utf8SpecCheck

namespace Utf8Pure

/-! ## Bit conversions and uniqueness of encoding prefixes -/

theorem bit8_value_sum_proved : bit8_value_sum := by
  unfold bit8_value_sum; decide

theorem bit8_value_word_proved : bit8_value_word := by
  unfold bit8_value_word; decide

theorem u32_byte4_bits_proved : u32_byte4_bits := by
  intro b31 b30 b29 b28 b27 b26 b25 b24 b23 b22 b21 b20 b19 b18 b17 b16 b15 b14 b13 b12 b11 b10 b9 b8
    b7 b6 b5 b4 b3 b2 b1 b0
  simp only [u32_byte4, BitVec.getLsbD_ofBoolListLE]
  rfl

theorem is_surrogate_code_point_examples_proved : is_surrogate_code_point_examples := by
  unfold is_surrogate_code_point_examples; decide

theorem begins_with_scalar_unique_proved : begins_with_scalar_unique := by
  intro bytes cp1 r1 cp2 r2 ⟨s1, e1, h1⟩ ⟨s2, e2, h2⟩
  obtain ⟨rfl, rfl⟩ := Utf8SpecCheck.encoding_front cp1 cp2 s1 s2 r1 r2 e1.2 e2.2 (h1.trans h2.symm)
  exact ⟨rfl, List.append_cancel_left (h1.trans h2.symm)⟩

theorem not_valid_sequence_prefix_extended_proved : not_valid_sequence_prefix_extended := by
  intro b more extra h ⟨rest, hr⟩
  apply h
  exact ⟨extra ++ rest, by simpa [List.append_assoc] using hr⟩

theorem maximal_subpart_lt (b1 : UInt8) (more s : List UInt8) (x : UInt8) (e : List UInt8)
    (h1 : maximal_subpart b1 more s) (h2 : maximal_subpart b1 more (s ++ x :: e)) : False := by
  obtain ⟨_, v1, m1⟩ := h1
  obtain ⟨p2, v2, _⟩ := h2
  have hn := m1 x e p2
  rcases v2 with v2 | v2
  · exact hn v2
  · have : s = [] := by
      cases s with
      | nil => rfl
      | cons y t => simp at v2
    subst this
    rcases v1 with v1 | v1
    · simp [is_valid_sequence_prefix] at v1
    · cases v1

theorem maximal_subpart_unique_proved : maximal_subpart_unique := by
  intro b1 more s1 s2 h1 h2
  obtain ⟨t1, ht1⟩ := h1.1
  obtain ⟨t2, ht2⟩ := h2.1
  rcases List.append_eq_append_iff.mp (ht1.trans ht2.symm) with ⟨a, hs, _⟩ | ⟨c, hs, _⟩
  · cases a with
    | nil => simpa using hs.symm
    | cons x e => subst hs; exact (maximal_subpart_lt b1 more s1 x e h1 h2).elim
  · cases c with
    | nil => simpa using hs
    | cons x e => subst hs; exact (maximal_subpart_lt b1 more s2 x e h2 h1).elim


/-! ## Existence: a longest eligible prefix in a finite buffer -/

private theorem bounded_max (P : Nat → Prop) (bound : Nat)
    (hne : ∃ n, n ≤ bound ∧ P n) :
    ∃ n, n ≤ bound ∧ P n ∧ ∀ m, m ≤ bound → P m → m ≤ n := by
  classical
  induction bound with
  | zero =>
    obtain ⟨n, hn, hp⟩ := hne
    have : n = 0 := by omega
    subst n
    exact ⟨0, by omega, hp, by omega⟩
  | succ bound ih =>
    by_cases h : P (bound + 1)
    · exact ⟨bound + 1, by omega, h, by omega⟩
    · have small : ∃ n, n ≤ bound ∧ P n := by
        obtain ⟨n, hn, hp⟩ := hne
        have hnsmall : n ≤ bound := by
          by_cases hh : n ≤ bound
          · exact hh
          · have : n = bound + 1 := by omega
            subst n
            exact (h hp).elim
        exact ⟨n, hnsmall, hp⟩
      obtain ⟨n, hn, hp, hm⟩ := ih small
      refine ⟨n, by omega, hp, ?_⟩
      intro m hmb hmp
      apply hm m _ hmp
      by_cases hh : m ≤ bound
      · exact hh
      · have : m = bound + 1 := by omega
        subst m
        exact (h hmp).elim

theorem maximal_subpart_exists_proved : maximal_subpart_exists := by
  classical
  intro b more _
  let P := fun n => ∃ s : List UInt8, s.length = n ∧ is_prefix s (b :: more) ∧
    (is_valid_sequence_prefix s ∨ s = [b])
  have hne : ∃ n, n ≤ (b :: more).length ∧ P n :=
    ⟨1, by simp, [b], rfl, ⟨more, rfl⟩, Or.inr rfl⟩
  obtain ⟨n, _, ⟨s, hs, hp, hv⟩, hm⟩ := bounded_max P (b :: more).length hne
  refine ⟨s, hp, hv, ?_⟩
  intro c extra he hevalid
  obtain ⟨r, hr⟩ := he
  have hl := congrArg List.length hr
  simp only [List.length_append, List.length_cons] at hl
  have := hm (s ++ c :: extra).length (by simp; omega)
    ⟨s ++ c :: extra, rfl, ⟨r, hr⟩, Or.inl hevalid⟩
  simp only [List.length_append, List.length_cons] at this
  omega

theorem is_unicode_scalar_matches_char_proved : is_unicode_scalar_matches_char := by
  intro cp
  simp only [is_unicode_scalar, is_surrogate_code_point, UInt32.isValidChar,
    Bool.and_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff,
    decide_eq_true_eq, decide_eq_false_iff_not, ge_iff_le,
    UInt32.le_iff_toNat_le, UInt32.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
  omega

theorem decodes_first_exists_proved : decodes_first_exists := by
  classical
  intro bytes
  cases bytes with
  | nil => exact ⟨none, rfl⟩
  | cons b more =>
    by_cases h : ∃ cp rest, begins_with_scalar (b :: more) cp rest
    · obtain ⟨cp, rest, seq, he, hs⟩ := h
      let c : Char := ⟨cp, (is_unicode_scalar_matches_char_proved cp).mp he.1⟩
      exact ⟨some (c, rest), Or.inl ⟨c, rest, ⟨seq, he, hs⟩, rfl⟩⟩
    · have hn : no_valid_sequence (b :: more) := fun cp rest hp => h ⟨cp, rest, hp⟩
      obtain ⟨s, hs⟩ := maximal_subpart_exists_proved b more hn
      obtain ⟨rest, hr⟩ := hs.1
      exact ⟨some (replacement_char, rest), Or.inr ⟨hn, s, rest, hs, hr, rfl⟩⟩

private theorem encoding_nonempty (cp : UInt32) (s : List UInt8)
    (h : encoding cp = some s) : s ≠ [] := by
  have := Utf8SpecCheck.encoding_cases cp s h
  rcases this with ⟨_, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ <;> simp

private theorem first_progress (bytes : List UInt8) (cp : Char) (rest : List UInt8)
    (h : decodes_first bytes (some (cp, rest))) : rest.length < bytes.length := by
  cases bytes with
  | nil => cases h
  | cons b more =>
    rcases h with ⟨c, r, ⟨s, he, hs⟩, hr⟩ | ⟨_, s, r, hmax, hs, hr⟩
    · cases hr
      have hn := encoding_nonempty cp.val s he.2
      have hl := congrArg List.length hs
      have : 0 < s.length := List.length_pos_iff.mpr hn
      simp only [List.length_append, List.length_cons] at hl ⊢
      omega
    · cases hr
      have hn : s ≠ [] := by
        rcases hmax.2.1 with hv | hv
        · intro hh; subst s; exact hv
        · rw [hv]; simp
      have hl := congrArg List.length hs
      have : 0 < s.length := List.length_pos_iff.mpr hn
      simp only [List.length_append, List.length_cons] at hl ⊢
      omega

theorem decodes_exists_proved : decodes_exists := by
  intro bytes
  induction hn : bytes.length using Nat.strongRecOn generalizing bytes with
  | ind n ih =>
    obtain ⟨result, hr⟩ := decodes_first_exists_proved bytes
    cases result with
    | none => exact ⟨[], hr⟩
    | some result =>
      obtain ⟨cp, rest⟩ := result
      obtain ⟨text, ht⟩ := ih rest.length (by have := first_progress bytes cp rest hr; omega) rest rfl
      exact ⟨cp :: text, rest, hr, ht⟩

theorem decodes_first_empty_proved : decodes_first_empty :=
  fun _ h => h

theorem decodes_first_nonempty_proved : decodes_first_nonempty := by
  intro b1 more result h
  rcases h with ⟨_, _, _, rfl⟩ | ⟨_, _, _, _, _, rfl⟩ <;> rfl

theorem decodes_first_unique_proved : decodes_first_unique := by
  intro bytes r1 r2 h1 h2
  cases bytes with
  | nil => exact h1.trans h2.symm
  | cons b1 more =>
    rcases h1 with ⟨cp1, rest1, hb1, rfl⟩ | ⟨hn1, s1, rest1, hs1, he1, rfl⟩ <;>
    rcases h2 with ⟨cp2, rest2, hb2, rfl⟩ | ⟨hn2, s2, rest2, hs2, he2, rfl⟩
    · obtain ⟨hc, rfl⟩ := begins_with_scalar_unique_proved _ _ _ _ _ hb1 hb2
      rw [Char.ext hc]
    · exact (hn2 _ _ hb1).elim
    · exact (hn1 _ _ hb2).elim
    · have := maximal_subpart_unique_proved _ _ _ _ hs1 hs2
      subst this
      rw [List.append_cancel_left (he1.trans he2.symm)]

theorem decodes_unique_proved : decodes_unique := by
  intro bytes t1 t2 h1 h2
  induction t1 generalizing bytes t2 with
  | nil =>
    cases t2 with
    | nil => rfl
    | cons c t2 =>
      obtain ⟨_, h, _⟩ := h2
      cases decodes_first_unique_proved _ _ _ h1 h
  | cons c t1 ih =>
    obtain ⟨rest1, d1, g1⟩ := h1
    cases t2 with
    | nil => cases decodes_first_unique_proved _ _ _ d1 h2
    | cons c2 t2 =>
      obtain ⟨rest2, d2, g2⟩ := h2
      have e := decodes_first_unique_proved _ _ _ d1 d2
      simp only [Option.some.injEq, Prod.mk.injEq] at e
      obtain ⟨rfl, rfl⟩ := e
      rw [ih rest1 t2 g1 g2]


/-! ## Explicit certificates for the decoding examples -/

-- Discharge a concrete impossible encoding using the four specified shapes.
macro "exclude_encoding" he:ident : tactic => `(tactic| (
  have hscalar := ($he).1
  have hcases := Utf8SpecCheck.encoding_cases _ _ ($he).2
  clear $he
  simp [is_unicode_scalar, is_surrogate_code_point, UInt32.le_iff_toNat_le,
    UInt32.toNat_ofNat] at hscalar
  rcases hcases with ⟨_, hc⟩ | ⟨_, _, hc⟩ | ⟨_, _, hc⟩ | ⟨_, _, hc⟩
  all_goals
    (try simp only [List.append_eq, List.cons_append, List.nil_append, List.append_nil,
      List.cons.injEq, List.cons_ne_nil, true_and, and_true, and_false, false_and] at *) <;>
    (try subst_vars) <;>
    (try simp only [List.append_eq, List.cons_append, List.nil_append, List.append_nil,
      List.cons.injEq, List.cons_ne_nil, true_and, and_true, and_false, false_and] at *) <;>
    (try simp only [← UInt8.toNat_inj, UInt8.toNat_ofNat', UInt8.toNat_ofNat, Nat.reduceMod, Nat.reducePow] at *) <;>
    omega))



private theorem scalar_certificate (cp : Char) (seq rest : List UInt8)
    (hne : seq ≠ []) (he : encodes seq cp.val) :
    decodes_first (seq ++ rest) (some (cp, rest)) := by
  cases seq with
  | nil => exact (hne rfl).elim
  | cons b more => exact Or.inl ⟨cp, rest, ⟨b :: more, he, rfl⟩, rfl⟩

private theorem replacement_certificate (b : UInt8) (more s rest : List UInt8)
    (heq : s ++ rest = b :: more) (hs : maximal_subpart b more s)
    (hn : no_valid_sequence (b :: more)) :
    decodes_first (b :: more) (some (replacement_char, rest)) :=
  Or.inr ⟨hn, s, rest, hs, heq, rfl⟩

private theorem example_ascii_A_B : decodes_first [65, 66] (some ('A', [66])) := by
  exact scalar_certificate 'A' [65] [66] (by decide) (by unfold encodes; decide)
private theorem example_ascii_B : decodes_first [66] (some ('B', [])) := by
  exact scalar_certificate 'B' [66] [] (by decide) (by unfold encodes; decide)
private theorem example_copyright : decodes_first [194, 169] (some ('©', [])) := by
  exact scalar_certificate '©' [194, 169] [] (by decide) (by unfold encodes; decide)
private theorem example_lead_then_ascii : decodes_first [194, 65] (some (replacement_char, [65])) := by
  apply replacement_certificate 194 [65] [194] [65] rfl
  · refine ⟨⟨[65], rfl⟩, ?_, ?_⟩
    · exact Or.inr rfl
    · intro c extra ⟨tail, htail⟩ ⟨suffix, cp, he⟩
      exclude_encoding he
  · intro cp rest ⟨seq, he, hseq⟩
    exclude_encoding he
private theorem example_ascii_A : decodes_first [65] (some ('A', [])) := by
  exact scalar_certificate 'A' [65] [] (by decide) (by unfold encodes; decide)
private theorem example_overlong_lead : decodes_first [192, 128] (some (replacement_char, [128])) := by
  apply replacement_certificate 192 [128] [192] [128] rfl
  · refine ⟨⟨[128], rfl⟩, ?_, ?_⟩
    · exact Or.inr rfl
    · intro c extra ⟨tail, htail⟩ ⟨suffix, cp, he⟩
      exclude_encoding he
  · intro cp rest ⟨seq, he, hseq⟩
    exclude_encoding he
private theorem example_continuation : decodes_first [128] (some (replacement_char, [])) := by
  apply replacement_certificate 128 [] [128] [] rfl
  · refine ⟨⟨[], rfl⟩, ?_, ?_⟩
    · exact Or.inr rfl
    · intro c extra ⟨tail, htail⟩ ⟨suffix, cp, he⟩
      exclude_encoding he
  · intro cp rest ⟨seq, he, hseq⟩
    exclude_encoding he
private theorem example_unfinished_two : decodes_first [194] (some (replacement_char, [])) := by
  apply replacement_certificate 194 [] [194] [] rfl
  · refine ⟨⟨[], rfl⟩, ?_, ?_⟩
    · exact Or.inr rfl
    · intro c extra ⟨tail, htail⟩ ⟨suffix, cp, he⟩
      exclude_encoding he
  · intro cp rest ⟨seq, he, hseq⟩
    exclude_encoding he
private theorem example_restarted_two : decodes_first [194, 194, 169] (some (replacement_char, [194, 169])) := by
  apply replacement_certificate 194 [194, 169] [194] [194, 169] rfl
  · refine ⟨⟨[194, 169], rfl⟩, ?_, ?_⟩
    · exact Or.inr rfl
    · intro c extra ⟨tail, htail⟩ ⟨suffix, cp, he⟩
      exclude_encoding he
  · intro cp rest ⟨seq, he, hseq⟩
    exclude_encoding he
private theorem example_ascii_H : decodes_first [72, 194, 169, 255] (some ('H', [194, 169, 255])) := by
  exact scalar_certificate 'H' [72] [194, 169, 255] (by decide) (by unfold encodes; decide)
private theorem example_copyright_then_bad : decodes_first [194, 169, 255] (some ('©', [255])) := by
  exact scalar_certificate '©' [194, 169] [255] (by decide) (by unfold encodes; decide)
private theorem example_bad_byte : decodes_first [255] (some (replacement_char, [])) := by
  apply replacement_certificate 255 [] [255] [] rfl
  · refine ⟨⟨[], rfl⟩, ?_, ?_⟩
    · exact Or.inr rfl
    · intro c extra ⟨tail, htail⟩ ⟨suffix, cp, he⟩
      exclude_encoding he
  · intro cp rest ⟨seq, he, hseq⟩
    exclude_encoding he
private theorem example_euro : decodes_first [226, 130, 172] (some ('€', [])) := by
  exact scalar_certificate '€' [226, 130, 172] [] (by decide) (by unfold encodes; decide)
private theorem example_grinning_face : decodes_first [240, 159, 152, 128] (some ('😀', [])) := by
  exact scalar_certificate '😀' [240, 159, 152, 128] [] (by decide) (by unfold encodes; decide)
private theorem example_unfinished_three : decodes_first [226, 130] (some (replacement_char, [])) := by
  apply replacement_certificate 226 [130] [226, 130] [] rfl
  · refine ⟨⟨[], rfl⟩, ?_, ?_⟩
    · exact Or.inl ⟨[172], 8364, by unfold encodes; decide⟩
    · intro c extra ⟨tail, htail⟩ ⟨suffix, cp, he⟩
      exclude_encoding he
  · intro cp rest ⟨seq, he, hseq⟩
    exclude_encoding he
private theorem example_three_then_ascii : decodes_first [226, 130, 65] (some (replacement_char, [65])) := by
  apply replacement_certificate 226 [130, 65] [226, 130] [65] rfl
  · refine ⟨⟨[65], rfl⟩, ?_, ?_⟩
    · exact Or.inl ⟨[172], 8364, by unfold encodes; decide⟩
    · intro c extra ⟨tail, htail⟩ ⟨suffix, cp, he⟩
      exclude_encoding he
  · intro cp rest ⟨seq, he, hseq⟩
    exclude_encoding he
private theorem example_unfinished_four : decodes_first [240, 159, 152] (some (replacement_char, [])) := by
  apply replacement_certificate 240 [159, 152] [240, 159, 152] [] rfl
  · refine ⟨⟨[], rfl⟩, ?_, ?_⟩
    · exact Or.inl ⟨[128], 128512, by unfold encodes; decide⟩
    · intro c extra ⟨tail, htail⟩ ⟨suffix, cp, he⟩
      exclude_encoding he
  · intro cp rest ⟨seq, he, hseq⟩
    exclude_encoding he
private theorem example_four_then_ascii : decodes_first [240, 159, 152, 65] (some (replacement_char, [65])) := by
  apply replacement_certificate 240 [159, 152, 65] [240, 159, 152] [65] rfl
  · refine ⟨⟨[65], rfl⟩, ?_, ?_⟩
    · exact Or.inl ⟨[128], 128512, by unfold encodes; decide⟩
    · intro c extra ⟨tail, htail⟩ ⟨suffix, cp, he⟩
      exclude_encoding he
  · intro cp rest ⟨seq, he, hseq⟩
    exclude_encoding he
private theorem example_overlong_three : decodes_first [224, 128, 128] (some (replacement_char, [128, 128])) := by
  apply replacement_certificate 224 [128, 128] [224] [128, 128] rfl
  · refine ⟨⟨[128, 128], rfl⟩, ?_, ?_⟩
    · exact Or.inr rfl
    · intro c extra ⟨tail, htail⟩ ⟨suffix, cp, he⟩
      exclude_encoding he
  · intro cp rest ⟨seq, he, hseq⟩
    exclude_encoding he
private theorem example_two_continuations : decodes_first [128, 128] (some (replacement_char, [128])) := by
  apply replacement_certificate 128 [128] [128] [128] rfl
  · refine ⟨⟨[128], rfl⟩, ?_, ?_⟩
    · exact Or.inr rfl
    · intro c extra ⟨tail, htail⟩ ⟨suffix, cp, he⟩
      exclude_encoding he
  · intro cp rest ⟨seq, he, hseq⟩
    exclude_encoding he
private theorem example_surrogate : decodes_first [237, 160, 128] (some (replacement_char, [160, 128])) := by
  apply replacement_certificate 237 [160, 128] [237] [160, 128] rfl
  · refine ⟨⟨[160, 128], rfl⟩, ?_, ?_⟩
    · exact Or.inr rfl
    · intro c extra ⟨tail, htail⟩ ⟨suffix, cp, he⟩
      exclude_encoding he
  · intro cp rest ⟨seq, he, hseq⟩
    exclude_encoding he
private theorem example_surrogate_tail : decodes_first [160, 128] (some (replacement_char, [128])) := by
  apply replacement_certificate 160 [128] [160] [128] rfl
  · refine ⟨⟨[128], rfl⟩, ?_, ?_⟩
    · exact Or.inr rfl
    · intro c extra ⟨tail, htail⟩ ⟨suffix, cp, he⟩
      exclude_encoding he
  · intro cp rest ⟨seq, he, hseq⟩
    exclude_encoding he
private theorem example_above_unicode : decodes_first [244, 144, 128, 128] (some (replacement_char, [144, 128, 128])) := by
  apply replacement_certificate 244 [144, 128, 128] [244] [144, 128, 128] rfl
  · refine ⟨⟨[144, 128, 128], rfl⟩, ?_, ?_⟩
    · exact Or.inr rfl
    · intro c extra ⟨tail, htail⟩ ⟨suffix, cp, he⟩
      exclude_encoding he
  · intro cp rest ⟨seq, he, hseq⟩
    exclude_encoding he
private theorem example_above_unicode_tail : decodes_first [144, 128, 128] (some (replacement_char, [128, 128])) := by
  apply replacement_certificate 144 [128, 128] [144] [128, 128] rfl
  · refine ⟨⟨[128, 128], rfl⟩, ?_, ?_⟩
    · exact Or.inr rfl
    · intro c extra ⟨tail, htail⟩ ⟨suffix, cp, he⟩
      exclude_encoding he
  · intro cp rest ⟨seq, he, hseq⟩
    exclude_encoding he

theorem decodes_examples_proved : decodes_examples := by
  unfold decodes_examples
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact rfl
  · exact ⟨[66], example_ascii_A_B, ⟨[], example_ascii_B, rfl⟩⟩
  · exact ⟨[], example_copyright, rfl⟩
  · exact ⟨[65], example_lead_then_ascii, ⟨[], example_ascii_A, rfl⟩⟩
  · exact ⟨[128], example_overlong_lead, ⟨[], example_continuation, rfl⟩⟩
  · exact ⟨[], example_unfinished_two, rfl⟩
  · exact ⟨[194, 169], example_restarted_two, ⟨[], example_copyright, rfl⟩⟩
  · exact ⟨[194, 169, 255], example_ascii_H, ⟨[255], example_copyright_then_bad, ⟨[], example_bad_byte, rfl⟩⟩⟩
  · exact ⟨[], example_euro, rfl⟩
  · exact ⟨[], example_grinning_face, rfl⟩
  · exact ⟨[], example_unfinished_three, rfl⟩
  · exact ⟨[65], example_three_then_ascii, ⟨[], example_ascii_A, rfl⟩⟩
  · exact ⟨[], example_unfinished_four, rfl⟩
  · exact ⟨[65], example_four_then_ascii, ⟨[], example_ascii_A, rfl⟩⟩
  · exact ⟨[128, 128], example_overlong_three, ⟨[128], example_two_continuations, ⟨[], example_continuation, rfl⟩⟩⟩
  · exact ⟨[160, 128], example_surrogate, ⟨[128], example_surrogate_tail, ⟨[], example_continuation, rfl⟩⟩⟩
  · exact ⟨[144, 128, 128], example_above_unicode, ⟨[128, 128], example_above_unicode_tail, ⟨[128], example_two_continuations, ⟨[], example_continuation, rfl⟩⟩⟩⟩

end Utf8Pure
