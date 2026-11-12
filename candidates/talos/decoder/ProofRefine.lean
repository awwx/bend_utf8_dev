/-
ProofRefine.lean -- the Wasm-level per-byte model `stepM` (ProofStep.lean)
refines Utf8Ref's `step` on packed states (STATUS.txt, statement 1).

Pure Lean on UInt8/UInt32; no Wasm semantics.  Method: everything goes
through `toNat`.  A packed byte list is described by `packN` (little-endian
base-256 value); `bytes_of_toNat` (ProofModel.lean) turns a `packN` value into
the four extracted bytes; small Bool lemmas (`lead*_eq`) match the Wasm range
tests to Utf8Ref's `isLead*`.

EXPORTS
  packN : List UInt8 → Nat               little-endian value of a byte list
  toNat_or_shl                           (x ||| y <<< k).toNat as a sum (disjoint bits)
  enc_toNat      (enc p).toNat = packN p + |p| * 2^24          (|p| ≤ 3)
  qOf_enc        (qOf (enc p) x).toNat = packN (p ++ [x])      (|p| ≤ 3)
  nOf_enc        nOf (enc p) = ofNat |p|
  packed_seq     vsB/vspB/cpV of a packed 1..4-byte list = isVS/isVSP/cpOf
  stepM_eq       stepM unfolded one level, with the fresh-byte fallback as stepFresh
  stepM_enc      stepM (enc p) x = (enc (step p x).1, (step p x).2)   (|p| ≤ 3)
  (step_length and isVSP4, used here, are in the pure layer: Utf8StepFacts.lean.)
-/
import ProofModel
import Utf8StepFacts

namespace Utf8Wasm
open Utf8Pure

/-- Little-endian base-256 value of a byte list. -/
def packN : List UInt8 → Nat
  | [] => 0
  | a :: l => a.toNat + 256 * packN l

theorem toNat_or_shl (x y k : UInt32) (hk : k.toNat < 32) (hx : x.toNat < 2 ^ k.toNat)
    (hy : y.toNat * 2 ^ k.toNat < 2 ^ 32) :
    (x ||| y <<< k).toNat = x.toNat + y.toNat * 2 ^ k.toNat := by
  simp only [UInt32.toNat_or, UInt32.toNat_shiftLeft, Nat.mod_eq_of_lt hk]
  rw [Nat.mod_eq_of_lt (by rw [Nat.shiftLeft_eq]; omega)]
  rw [Nat.or_comm, ← Nat.shiftLeft_add_eq_or_of_lt hx, Nat.shiftLeft_eq]
  omega

/-! ## Packed state and packed sequence as numbers -/

theorem enc_toNat (p : List UInt8) (hp : p.length ≤ 3) :
    (enc p).toNat = packN p + p.length * 2 ^ 24 := by
  match p, hp with
  | [], _ => rfl
  | [a], _ =>
    have ha := a.toNat_lt
    simp only [enc]
    rw [show (0x1000000 : UInt32) = ((1 : UInt32) <<< (24 : UInt32)) by decide,
      toNat_or_shl _ _ _ (by decide) (by simp; omega) (by simp)]
    simp [packN]
  | [a, b], _ =>
    have ha := a.toNat_lt; have hb := b.toNat_lt
    simp only [enc]
    have h1 : (a.toUInt32 ||| b.toUInt32 <<< 8).toNat = a.toNat + b.toNat * 256 := by
      rw [toNat_or_shl _ _ _ (by decide) (by simp; omega) (by simp; omega)]; simp
    rw [show (0x2000000 : UInt32) = ((2 : UInt32) <<< (24 : UInt32)) by decide,
      toNat_or_shl _ _ _ (by decide) (by rw [h1]; simp; omega) (by simp), h1]
    simp [packN]; omega
  | [a, b, c], _ =>
    have ha := a.toNat_lt; have hb := b.toNat_lt; have hc := c.toNat_lt
    simp only [enc]
    have h1 : (a.toUInt32 ||| b.toUInt32 <<< 8).toNat = a.toNat + b.toNat * 256 := by
      rw [toNat_or_shl _ _ _ (by decide) (by simp; omega) (by simp; omega)]; simp
    have h2 : (a.toUInt32 ||| b.toUInt32 <<< 8 ||| c.toUInt32 <<< 16).toNat =
        a.toNat + b.toNat * 256 + c.toNat * 65536 := by
      rw [toNat_or_shl _ _ _ (by decide) (by rw [h1]; simp; omega) (by simp; omega), h1]; simp
    rw [show (0x3000000 : UInt32) = ((3 : UInt32) <<< (24 : UInt32)) by decide,
      toNat_or_shl _ _ _ (by decide) (by rw [h2]; simp; omega) (by simp), h2]
    simp [packN]; omega

theorem packN_lt (p : List UInt8) : packN p < 256 ^ p.length := by
  induction p with
  | nil => simp [packN]
  | cons a l ih =>
    have := a.toNat_lt
    simp only [packN, List.length_cons, Nat.pow_succ]
    omega

theorem packN_append (p : List UInt8) (x : UInt8) :
    packN (p ++ [x]) = packN p + x.toNat * 256 ^ p.length := by
  induction p with
  | nil => simp [packN]
  | cons a l ih => simp only [List.cons_append, packN, ih, List.length_cons, Nat.pow_succ]; grind

theorem pow256_le (n : Nat) (h : n ≤ 3) : 256 ^ n ≤ 2 ^ 24 := by
  match n, h with
  | 0, _ | 1, _ | 2, _ | 3, _ => decide

theorem enc_div (p : List UInt8) (hp : p.length ≤ 3) : (enc p).toNat / 2 ^ 24 = p.length := by
  have := packN_lt p
  have h256 := pow256_le p.length hp
  rw [enc_toNat p hp]; omega

theorem nOf_enc (p : List UInt8) (hp : p.length ≤ 3) : nOf (enc p) = UInt32.ofNat p.length := by
  apply UInt32.toNat_inj.mp
  simp only [nOf, UInt32.toNat_shiftRight, Nat.shiftRight_eq_div_pow]
  rw [show (24 : UInt32).toNat % 32 = 24 from rfl, enc_div p hp]
  simp; omega

theorem qOf_enc (p : List UInt8) (hp : p.length ≤ 3) (x : UInt8) :
    (qOf (enc p) x.toUInt32).toNat = packN (p ++ [x]) := by
  have hx := x.toNat_lt
  have hlt := packN_lt p
  have hdiv := enc_div p hp
  have hlow : (enc p &&& 16777215).toNat = packN p := by
    rw [UInt32.toNat_and, show (16777215 : UInt32).toNat = 2 ^ 24 - 1 from rfl,
      Nat.and_two_pow_sub_one_eq_mod, enc_toNat p hp]
    have := pow256_le p.length hp
    omega
  have hk : ((enc p >>> (24 : UInt32) <<< (3 : UInt32)) % 32).toNat = 8 * p.length := by
    simp only [UInt32.toNat_mod, UInt32.toNat_shiftLeft, UInt32.toNat_shiftRight,
      Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
    rw [show (24 : UInt32).toNat % 32 = 24 from rfl, show (3 : UInt32).toNat % 32 = 3 from rfl, hdiv]
    simp; omega
  have h8 : 2 ^ (8 * p.length) = 256 ^ p.length := by rw [Nat.pow_mul]
  have hb := pow256_le p.length hp
  have hxb : x.toNat * 256 ^ p.length ≤ 255 * 2 ^ 24 := Nat.mul_le_mul (by omega) hb
  unfold qOf
  rw [toNat_or_shl _ _ _ (by omega) (by rw [hlow, hk, h8]; exact hlt)
    (by rw [hk, h8]; simp; omega), hlow, hk, h8, packN_append]
  simp

/-! ## Range tests: Wasm form (UInt32 decide) = Utf8Ref form (UInt8 Bools) -/

section
variable (a : UInt8)

theorem lead1_eq : decide (a.toUInt32 ≤ 127) = isLead1 a := by
  simp [isLead1, UInt32.le_iff_toNat_le, UInt8.le_iff_toNat_le]
theorem lead2_eq : (decide (a.toUInt32 ≥ 194) && decide (a.toUInt32 ≤ 223)) = isLead2 a := by
  simp [isLead2, UInt32.le_iff_toNat_le, UInt8.le_iff_toNat_le]
theorem lead3_eq : (decide (a.toUInt32 ≥ 224) && decide (a.toUInt32 ≤ 239)) = isLead3 a := by
  simp [isLead3, UInt32.le_iff_toNat_le, UInt8.le_iff_toNat_le]
theorem lead4_eq : (decide (a.toUInt32 ≥ 240) && decide (a.toUInt32 ≤ 244)) = isLead4 a := by
  simp [isLead4, UInt32.le_iff_toNat_le, UInt8.le_iff_toNat_le]
theorem lead1234_eq : (isLead1 a || (decide (a.toUInt32 ≥ 194) && decide (a.toUInt32 ≤ 244))) =
    (isLead1 a || isLead2 a || isLead3 a || isLead4 a) := by
  rw [Bool.eq_iff_iff]
  simp [isLead1, isLead2, isLead3, isLead4, UInt32.le_iff_toNat_le, UInt8.le_iff_toNat_le]
  omega
theorem lead234_eq : (decide (a.toUInt32 ≥ 194) && decide (a.toUInt32 ≤ 244)) =
    (isLead2 a || isLead3 a || isLead4 a) := by
  rw [Bool.eq_iff_iff]
  simp [isLead2, isLead3, isLead4, UInt32.le_iff_toNat_le, UInt8.le_iff_toNat_le]
  omega
theorem lead34_eq : (decide (a.toUInt32 ≥ 224) && decide (a.toUInt32 ≤ 244)) =
    (isLead3 a || isLead4 a) := by
  rw [Bool.eq_iff_iff]
  simp [isLead3, isLead4, UInt32.le_iff_toNat_le, UInt8.le_iff_toNat_le]
  omega
end

/-! ## The central lemma: helper models on a packed 1..4-byte list -/

theorem packed_seq (l : List UInt8) (h1 : 1 ≤ l.length) (h4 : l.length ≤ 4) (q : UInt32)
    (hq : q.toNat = packN l) :
    vsB q (UInt32.ofNat l.length) = isVS l ∧ vspB q (UInt32.ofNat l.length) = isVSP l ∧
      cpV q (UInt32.ofNat l.length) = cpOf l := by
  match l, h1, h4 with
  | [a], _, _ =>
    rw [show UInt32.ofNat [a].length = 1 from rfl]
    obtain ⟨e1, -, -, -⟩ := bytes_of_toNat q a 0 0 0 (by simp [hq, packN])
    simp (config := {decide := true}) only [↓reduceIte, vsB, vspB, cpV, isVS, isVSP, cpOf, e1, lead1_eq, lead1234_eq]
  | [a, b], _, _ =>
    rw [show UInt32.ofNat [a, b].length = 2 from rfl]
    obtain ⟨e1, e2, -, -⟩ := bytes_of_toNat q a b 0 0 (by simp [hq, packN])
    simp (config := {decide := true}) only [↓reduceIte, vsB, vspB, cpV, isVS, isVSP, cpOf, e1, e2, lead2_eq, lead234_eq, secondB_eq]
  | [a, b, c], _, _ =>
    rw [show UInt32.ofNat [a, b, c].length = 3 from rfl]
    obtain ⟨e1, e2, e3, -⟩ := bytes_of_toNat q a b c 0 (by simp [hq, packN]; omega)
    simp (config := {decide := true}) only [↓reduceIte, vsB, vspB, cpV, isVS, isVSP, cpOf, e1, e2, e3, lead3_eq, lead34_eq, secondB_eq,
      contB_eq]
  | [a, b, c, d], _, _ =>
    rw [show UInt32.ofNat [a, b, c, d].length = 4 from rfl]
    obtain ⟨e1, e2, e3, e4⟩ := bytes_of_toNat q a b c d (by simp [hq, packN]; omega)
    simp (config := {decide := true}) only [↓reduceIte, vsB, vspB, cpV, isVS, isVSP, cpOf, e1, e2, e3, e4, lead4_eq, secondB_eq, contB_eq]

/-! ## The per-byte refinement -/

theorem stepA_zero (x : UInt8) (k : UInt32 × List UInt32) :
    stepA 0 x.toUInt32 k = (enc (stepFresh x).1, (stepFresh x).2) := by
  have h : stepA 0 x.toUInt32 k = stepM 0 x.toUInt32 := by simp [stepM, stepA, nOf]
  rw [h, stepM_nil, step_nil]

/-- `stepM` one level down: the fallback after a bad pending sequence is the fresh step. -/
theorem stepM_eq (s : UInt32) (x : UInt8) :
    stepM s x.toUInt32 =
      if vsB (qOf s x.toUInt32) (1 + nOf s) then (0, [cpV (qOf s x.toUInt32) (1 + nOf s)])
      else if vspB (qOf s x.toUInt32) (1 + nOf s) then
        (qOf s x.toUInt32 ||| ((1 + nOf s) <<< (24 : UInt32)), [])
      else if nOf s = 0 then (0, [65533])
      else (enc (stepFresh x).1, 65533 :: (stepFresh x).2) := by
  simp only [stepM, stepA_zero]; rfl

theorem stepM_enc (p : List UInt8) (hp : p.length ≤ 3) (x : UInt8) :
    stepM (enc p) x.toUInt32 = (enc (step p x).1, (step p x).2) := by
  cases p with
  | nil => exact stepM_nil x
  | cons a l =>
  have hpl : l.length ≤ 2 := by simp at hp; omega
  have hm : 1 + nOf (enc (a :: l)) = UInt32.ofNat (a :: l ++ [x]).length := by
    rw [nOf_enc _ hp]; apply UInt32.toNat_inj.mp; simp at hp ⊢; omega
  have hn : nOf (enc (a :: l)) ≠ 0 := by
    rw [nOf_enc _ hp]; intro h; have := congrArg UInt32.toNat h; simp at hp this; omega
  obtain ⟨hvs, hvsp, hcp⟩ := packed_seq (a :: l ++ [x]) (by simp) (by simp at hp ⊢; omega) _
    (qOf_enc _ hp x)
  have hnew : isVSP (a :: l ++ [x]) = true → isVS (a :: l ++ [x]) = false →
      qOf (enc (a :: l)) x.toUInt32 ||| (1 + nOf (enc (a :: l))) <<< (24 : UInt32) =
        enc (a :: l ++ [x]) := by
    intro h1 h2
    have h3 : (a :: l ++ [x]).length ≤ 3 := by
      match l, hp with
      | [], _ | [_], _ => simp
      | [b, c], _ => rw [isVSP4, h2] at h1; exact absurd h1 (by decide)
      | _ :: _ :: _ :: _, h => simp at h
    have hq := qOf_enc _ hp x
    have hlt := Nat.lt_of_lt_of_le (packN_lt (a :: l ++ [x])) (pow256_le _ h3)
    have h24 : (24 : UInt32).toNat = 24 := rfl
    apply UInt32.toNat_inj.mp
    rw [enc_toNat _ h3, hm, toNat_or_shl _ _ _ (by decide) (by rw [hq, h24]; exact hlt)
      (by rw [h24]; simp; omega), hq, h24]
    simp; omega
  rw [stepM_eq, hm, hvs, hvsp, hcp, ← hm]
  unfold step
  by_cases h1 : isVS (a :: l ++ [x]) = true
  · simp only [h1, ↓reduceIte]; rfl
  simp only [Bool.not_eq_true] at h1
  by_cases h2 : isVSP (a :: l ++ [x]) = true
  · simp only [h1, h2, ↓reduceIte, Bool.false_eq_true, hnew h2 h1]
  · simp only [Bool.not_eq_true] at h2
    simp only [h1, h2, hn, ↓reduceIte, Bool.false_eq_true, List.isEmpty_cons, replacement_char]

end Utf8Wasm
