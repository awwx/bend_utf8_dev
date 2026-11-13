import Interpreter.Wasm.SmallStep

namespace Wasm

/-- Read-after-write, specialized from Talos `CodeLib.RustStd.Frame`. -/
theorem Mem.read32_write32_same (m : Mem) (a v : UInt32) :
    (m.write32 a v).read32 a = v := by
  simp only [Mem.read32, Mem.write32]
  have e1 : a.toNat + 1 ≠ a.toNat := by omega
  have e2 : a.toNat + 2 ≠ a.toNat := by omega
  have e3 : a.toNat + 3 ≠ a.toNat := by omega
  have e21 : a.toNat + 2 ≠ a.toNat + 1 := by omega
  have e31 : a.toNat + 3 ≠ a.toNat + 1 := by omega
  have e32 : a.toNat + 3 ≠ a.toNat + 2 := by omega
  simp only [e1,e2,e3,e21,e31,e32,↓reduceIte]
  apply UInt32.toBitVec_inj.mp
  simp only [UInt32.toBitVec_or, UInt32.toBitVec_shiftLeft,
    UInt8.toBitVec_toUInt32, UInt32.toBitVec_toUInt8,
    UInt32.toBitVec_and, UInt32.toBitVec_shiftRight]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hcases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 ∨ i = 16 ∨ i = 17 ∨ i = 18 ∨ i = 19 ∨ i = 20 ∨ i = 21 ∨ i = 22 ∨ i = 23 ∨ i = 24 ∨ i = 25 ∨ i = 26 ∨ i = 27 ∨ i = 28 ∨ i = 29 ∨ i = 30 ∨ i = 31 := by omega
  rcases hcases with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst i <;> simp

theorem Mem.write32_bytes_out (m : Mem) (a v : UInt32) (i : Nat)
    (h : i < a.toNat ∨ a.toNat + 4 ≤ i) :
    (m.write32 a v).bytes i = m.bytes i := by
  simp only [Mem.write32]
  rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]

theorem Mem.read32_write32_disjoint (m : Mem) (a b v : UInt32)
    (h : b.toNat + 4 ≤ a.toNat ∨ a.toNat + 4 ≤ b.toNat) :
    (m.write32 a v).read32 b = m.read32 b := by
  simp only [Mem.read32]
  rw [Mem.write32_bytes_out m a v b.toNat (by omega),
    Mem.write32_bytes_out m a v (b.toNat+1) (by omega),
    Mem.write32_bytes_out m a v (b.toNat+2) (by omega),
    Mem.write32_bytes_out m a v (b.toNat+3) (by omega)]

theorem Mem.write32_pages (m : Mem) (a v : UInt32) :
    (m.write32 a v).pages = m.pages := rfl

def readWords (m : Mem) (p : Nat) : Nat → List UInt32
  | 0 => []
  | n+1 => m.read32 (UInt32.ofNat p) :: readWords m (p+4) n

def writeWords (m : Mem) (p : Nat) : List UInt32 → Mem
  | [] => m
  | x::xs => writeWords (m.write32 (UInt32.ofNat p) x) (p+4) xs

theorem writeWords_pages (m : Mem) (p : Nat) (xs : List UInt32) :
    (writeWords m p xs).pages = m.pages := by
  induction xs generalizing m p with
  | nil => rfl
  | cons x xs ih =>
      simpa [writeWords, Mem.write32_pages] using
        (ih (m.write32 (UInt32.ofNat p) x) (p+4))

theorem writeWords_read_before (m : Mem) (p q : Nat) (xs : List UInt32)
    (hp : p + 4 ≤ q) (hq : q + 4 * xs.length ≤ 65536) :
    (writeWords m q xs).read32 (UInt32.ofNat p) = m.read32 (UInt32.ofNat p) := by
  induction xs generalizing m q with
  | nil => rfl
  | cons x xs ih =>
      simp only [writeWords]
      rw [ih _ (q+4) (by omega) (by simp_all; omega)]
      apply Mem.read32_write32_disjoint
      left
      rw [UInt32.toNat_ofNat_of_lt' (by simp only [UInt32.size]; simp only [List.length_cons] at hq; omega),
        UInt32.toNat_ofNat_of_lt' (by simp only [UInt32.size]; simp only [List.length_cons] at hq; omega)]
      exact hp

theorem readWords_writeWords (m : Mem) (p : Nat) (xs : List UInt32)
    (hp : p + 4 * xs.length ≤ 65536) :
    readWords (writeWords m p xs) p xs.length = xs := by
  induction xs generalizing m p with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.length_cons, writeWords, readWords]
      rw [writeWords_read_before _ p (p+4) xs (by omega) (by simp_all; omega)]
      rw [Mem.read32_write32_same, ih _ (p+4) (by simp_all; omega)]

theorem readWords_writeWords_before (m : Mem) (p q n : Nat) (xs : List UInt32)
    (hp : p + 4*n ≤ q) (hq : q + 4*xs.length ≤ 65536) :
    readWords (writeWords m q xs) p n = readWords m p n := by
  induction n generalizing p with
  | zero => rfl
  | succ n ih =>
      simp only [readWords]
      rw [writeWords_read_before _ p q xs (by omega) hq,
        ih (p+4) (by omega)]

theorem writeWords_append (m : Mem) (p : Nat) (xs ys : List UInt32) :
    writeWords m p (xs ++ ys) = writeWords (writeWords m p xs) (p + 4*xs.length) ys := by
  induction xs generalizing m p with
  | nil => simp [writeWords]
  | cons x xs ih =>
      simp only [List.cons_append, writeWords, List.length_cons]
      rw [ih]
      congr 1
      omega

theorem readWords_append (m : Mem) (p n k : Nat) :
    readWords m p (n+k) = readWords m p n ++ readWords m (p+4*n) k := by
  induction n generalizing p with
  | zero => simp [readWords]
  | succ n ih =>
      simp only [Nat.succ_add, readWords, List.cons_append]
      rw [ih]
      rw [show p + 4 + 4*n = p + 4*(n+1) by omega]

end Wasm
