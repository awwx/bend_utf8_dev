import WasmMemory
import TextSpec

namespace PrefixWasm
open Wasm LinePrefix

/-- The mathematical memory action corresponding to the loop. -/
def transform (start : Bool) (mem : Mem) (p q : Nat) : Nat → Bool × Mem × Nat
  | 0 => (start, mem, q)
  | n+1 =>
    let cp := mem.read32 (UInt32.ofNat p)
    let ys := emit start cp
    transform (cp == 10) (writeWords mem q ys) (p+4) (q+4*ys.length) n

theorem emit_length (s : Bool) (cp : UInt32) : (emit s cp).length ≤ 3 := by
  cases s <;> simp [emit]

theorem transform_correct (n : Nat) (s : Bool) (mem : Mem) (p q : Nat)
    (hp : p + 4*n ≤ 16384) (hq : 16384 ≤ q) (hend : q+12*n ≤ 65536) :
    transform s mem p q n =
      let result := LinePrefix.run s (readWords mem p n)
      (result.1, writeWords mem q result.2, q+4*result.2.length) := by
  induction n generalizing s mem p q with
  | zero => simp [transform, readWords, LinePrefix.run, writeWords]
  | succ n ih =>
    let cp := mem.read32 (UInt32.ofNat p)
    let ys := emit s cp
    have hlen : ys.length ≤ 3 := emit_length s cp
    have hn : p+4+4*n ≤ 16384 := by omega
    have hq' : 16384 ≤ q+4*ys.length := by omega
    have he : q+4*ys.length+12*n ≤ 65536 := by omega
    have hr : readWords (writeWords mem q ys) (p+4) n = readWords mem (p+4) n :=
      readWords_writeWords_before mem (p+4) q n ys (by omega) (by omega)
    change transform (cp == 10) (writeWords mem q ys) (p+4) (q+4*ys.length) n = _
    rw [ih _ _ _ _ hn hq' he, hr]
    simp only [readWords, LinePrefix.run]
    change ((LinePrefix.run (cp == 10) (readWords mem (p+4) n)).1,
      writeWords (writeWords mem q ys) (q+4*ys.length)
        (LinePrefix.run (cp == 10) (readWords mem (p+4) n)).2,
      q+4*ys.length+4*(LinePrefix.run (cp == 10) (readWords mem (p+4) n)).2.length) = _
    rw [← writeWords_append]
    simp [ys, cp, List.length_append, Nat.mul_add, Nat.add_assoc]

theorem run_length (s : Bool) (text : List UInt32) :
    (LinePrefix.run s text).2.length ≤ 3*text.length := by
  induction text generalizing s with
  | nil => simp [LinePrefix.run]
  | cons cp rest ih =>
    have he := emit_length s cp
    have hr := ih (cp == 10)
    simp only [LinePrefix.run, List.length_append, List.length_cons]
    omega

theorem transform_pages (n : Nat) (s : Bool) (mem : Mem) (p q : Nat) :
    (transform s mem p q n).2.1.pages = mem.pages := by
  induction n generalizing s mem p q with
  | zero => rfl
  | succ n ih =>
    simp only [transform]
    rw [ih, writeWords_pages]

/-- Bridge input preparation followed by the bounded callback's memory action. -/
theorem transform_prepared (s : Bool) (mem : Mem) (chunk : List UInt32)
    (h : chunk.length ≤ 4096) :
    transform s (writeWords mem 0 chunk) 0 16384 chunk.length =
      let result := LinePrefix.run s chunk
      (result.1, writeWords (writeWords mem 0 chunk) 16384 result.2,
        16384+4*result.2.length) := by
  rw [transform_correct _ _ _ _ _ (by omega) (by omega) (by omega),
    readWords_writeWords _ _ _ (by omega)]

/-- The host snapshots exactly the transformed scalar list from output memory. -/
theorem transform_snapshot (s : Bool) (mem : Mem) (chunk : List UInt32)
    (h : chunk.length ≤ 4096) :
    readWords (transform s (writeWords mem 0 chunk) 0 16384 chunk.length).2.1
      16384 (LinePrefix.run s chunk).2.length = (LinePrefix.run s chunk).2 := by
  rw [transform_prepared s mem chunk h]
  apply readWords_writeWords
  have := run_length s chunk
  omega

/-- Arithmetic and memory limits are consequences of the delivery bound. -/
theorem transform_end_bound (s : Bool) (mem : Mem) (chunk : List UInt32)
    (h : chunk.length ≤ 4096) :
    (transform s (writeWords mem 0 chunk) 0 16384 chunk.length).2.2 ≤ 65536 := by
  rw [transform_prepared s mem chunk h]
  have := run_length s chunk
  dsimp
  omega

end PrefixWasm
