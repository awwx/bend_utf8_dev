/-
ProofLayout.lean -- where the decoder's code points land in memory: facts
about `writeCps` / `endAddr` (defined with the $step model in ProofStep.lean)
and Boundary's `bytesAt` / `textBytes`.  Pure Lean on `Mem`; no Wasm semantics.

The output area may end exactly at 2^32 (Boundary's BufferLayout allows it),
so the lemmas assume only `out + 4 * |cs| ≤ 2^32`: every written byte address
is then below 2^32; only the returned end pointer can wrap (to 0), and Boundary
states it as `UInt32.ofNat (out + 4 * |t|)`, which wraps the same way
(`endAddr_eq`).

EXPORTS
  endAddr_eq        endAddr out cs = ofNat (out + 4 * |cs|)
  endAddr_toNat     (endAddr out cs).toNat = out + 4 * |cs|      (no wrap)
  endAddr_append, writeCps_append                  splitting the written text
  writeCps_pages    writing does not change the page count
  write32_bytes, write32_outside                   one i32.store
  writeCps_outside  bytes outside [out, out + 4 * |cs|) are unchanged
  writeCps_bytes    bytes inside are textBytes cs (Boundary's u32le layout)
  bytesAt_succ, bytesAt_add, bytesAt_congr, bytesAt_length
-/
import ProofStep
import Boundary

namespace Utf8Wasm
open Wasm Utf8Boundary

/-! ## End pointer and splitting -/

theorem endAddr_eq (out : UInt32) (cs : List UInt32) :
    endAddr out cs = UInt32.ofNat (out.toNat + 4 * cs.length) := by
  induction cs generalizing out with
  | nil => simp [endAddr]
  | cons c cs ih =>
    simp only [endAddr, ih]
    apply UInt32.toNat_inj.mp
    simp [UInt32.toNat_add]; omega

theorem endAddr_toNat (out : UInt32) (cs : List UInt32) (h : out.toNat + 4 * cs.length < 2 ^ 32) :
    (endAddr out cs).toNat = out.toNat + 4 * cs.length := by
  rw [endAddr_eq, UInt32.toNat_ofNat_of_lt' h]

theorem endAddr_append (out : UInt32) (t1 t2 : List UInt32) :
    endAddr out (t1 ++ t2) = endAddr (endAddr out t1) t2 := by
  induction t1 generalizing out with
  | nil => rfl
  | cons c cs ih => simp only [List.cons_append, endAddr, ih]

theorem writeCps_append (mem : Mem) (out : UInt32) (t1 t2 : List UInt32) :
    writeCps mem out (t1 ++ t2) = writeCps (writeCps mem out t1) (endAddr out t1) t2 := by
  induction t1 generalizing mem out with
  | nil => rfl
  | cons c cs ih => simp only [List.cons_append, writeCps, endAddr, ih]

theorem writeCps_pages (mem : Mem) (out : UInt32) (cs : List UInt32) :
    (writeCps mem out cs).pages = mem.pages := by
  induction cs generalizing mem out with
  | nil => rfl
  | cons c cs ih => simp [writeCps, ih, Mem.write32]

/-! ## Reading memory back -/

theorem bytesAt_succ (mem : Mem) (p n : Nat) :
    bytesAt mem p (n + 1) = mem.bytes p :: bytesAt mem (p + 1) n := by
  simp [bytesAt, List.range_succ_eq_map, Nat.add_comm, Nat.add_left_comm]

theorem bytesAt_add (mem : Mem) (p n k : Nat) :
    bytesAt mem p (n + k) = bytesAt mem p n ++ bytesAt mem (p + n) k := by
  simp only [bytesAt, List.range_add, List.map_append, List.map_map]
  congr 2
  funext i; simp [Nat.add_assoc]

theorem bytesAt_congr (m1 m2 : Mem) (p n : Nat) (h : ∀ a, a < p + n → m1.bytes a = m2.bytes a) :
    bytesAt m1 p n = bytesAt m2 p n := by
  simp only [bytesAt]
  apply List.map_congr_left
  intro i hi
  simp at hi
  exact h _ (by omega)

theorem bytesAt_length (mem : Mem) (p n : Nat) : (bytesAt mem p n).length = n := by
  simp [bytesAt]

/-! ## Written code points -/

private theorem u8_and255 (x : UInt8) : x &&& 255 = x := by
  apply UInt8.toNat_inj.mp
  rw [UInt8.toNat_and, show (255 : UInt8).toNat = 2 ^ 8 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  exact Nat.mod_eq_of_lt x.toNat_lt

private theorem four_add (out : UInt32) (h : out.toNat + 4 < 2 ^ 32) :
    (4 + out).toNat = out.toNat + 4 := by
  rw [UInt32.toNat_add]; simp; omega

theorem write32_bytes (mem : Mem) (a c : UInt32) :
    bytesAt (mem.write32 a c) a.toNat 4 = u32le c := by
  simp [bytesAt, List.range_succ, Mem.write32, u32le, u8_and255]

theorem write32_outside (mem : Mem) (a c : UInt32) (i : Nat) (h : i < a.toNat ∨ a.toNat + 4 ≤ i) :
    (mem.write32 a c).bytes i = mem.bytes i := by
  simp [Mem.write32, show i ≠ a.toNat by omega, show i ≠ a.toNat + 1 by omega,
    show i ≠ a.toNat + 2 by omega, show i ≠ a.toNat + 3 by omega]

theorem writeCps_outside (mem : Mem) (out : UInt32) (cs : List UInt32) (i : Nat)
    (hfit : out.toNat + 4 * cs.length ≤ 2 ^ 32)
    (h : i < out.toNat ∨ out.toNat + 4 * cs.length ≤ i) :
    (writeCps mem out cs).bytes i = mem.bytes i := by
  induction cs generalizing mem out with
  | nil => rfl
  | cons c cs ih =>
    simp only [List.length_cons] at hfit h
    simp only [writeCps]
    by_cases hcs : cs = []
    · subst hcs; exact write32_outside _ _ _ _ (by simp at h; omega)
    have hl := List.length_pos_iff.mpr hcs
    have h4 := four_add out (by omega)
    rw [ih _ _ (by rw [h4]; omega) (by rw [h4]; omega)]
    exact write32_outside _ _ _ _ (by omega)

theorem writeCps_bytes (mem : Mem) (out : UInt32) (cs : List UInt32)
    (hfit : out.toNat + 4 * cs.length ≤ 2 ^ 32) :
    bytesAt (writeCps mem out cs) out.toNat (4 * cs.length) = textBytes cs := by
  induction cs generalizing mem out with
  | nil => simp [bytesAt, textBytes]
  | cons c cs ih =>
    simp only [List.length_cons] at hfit ⊢
    by_cases hcs : cs = []
    · subst hcs; simpa [writeCps, textBytes] using write32_bytes mem out c
    have hl := List.length_pos_iff.mpr hcs
    have h4 := four_add out (by omega)
    simp only [writeCps, textBytes]
    rw [show 4 * (cs.length + 1) = 4 + 4 * cs.length by omega, bytesAt_add, ← h4,
      ih _ _ (by rw [h4]; omega)]
    congr 1
    rw [← write32_bytes mem out c]
    apply bytesAt_congr
    intro a ha
    exact writeCps_outside _ _ _ _ (by rw [h4]; omega) (by rw [h4]; omega)

end Utf8Wasm
