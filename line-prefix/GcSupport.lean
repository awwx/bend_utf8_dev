import Interpreter.Wasm.SmallStep

namespace PrefixGc
open Wasm

@[simp] theorem heap_get_first (heap : List GcObject) (a b : GcObject) :
    (heap ++ [a,b])[heap.length]? = some a := by
  rw [List.getElem?_append_right (by omega)]
  simp

@[simp] theorem heap_get_second (heap : List GcObject) (a b : GcObject) :
    (heap ++ [a,b])[heap.length+1]? = some b := by
  rw [List.getElem?_append_right (by omega)]
  simp

@[simp] theorem heap_set_first (heap : List GcObject) (a b c : GcObject) :
    (heap ++ [a,b]).set heap.length c = heap ++ [c,b] := by
  rw [List.set_append_right _ _ (by omega)]
  simp

@[simp] theorem heap_set_second (heap : List GcObject) (a b c : GcObject) :
    (heap ++ [a,b]).set (heap.length+1) c = heap ++ [a,c] := by
  rw [List.set_append_right _ _ (by omega)]
  simp

/-- Appending one output value replaces the next zero slot in a fixed array. -/
theorem padded_set {α : Type} (written : List α) (zero value : α) (capacity : Nat)
    (h : written.length < capacity) :
    (written ++ List.replicate (capacity-written.length) zero).set written.length value =
      (written ++ [value]) ++ List.replicate (capacity-(written.length+1)) zero := by
  have he : capacity-written.length = (capacity-(written.length+1))+1 := by omega
  rw [List.set_append_right _ _ (by omega), Nat.sub_self, he, List.replicate_succ]
  simp

@[simp] theorem padded_take {α : Type} (written : List α) (zero : α) (capacity : Nat) :
    (written ++ List.replicate (capacity-written.length) zero).take written.length = written := by
  simp

@[simp] theorem padded_length {α : Type} (written : List α) (zero : α) (capacity : Nat)
    (h : written.length ≤ capacity) :
    (written ++ List.replicate (capacity-written.length) zero).length = capacity := by
  simp; omega

/-- Packing an already bounded UTF-16 code unit does not alter it. -/
theorem mask16 (cp : UInt32) (h : cp.toNat < 65536) : cp &&& 65535 = cp := by
  apply UInt32.toNat_inj.mp
  rw [UInt32.toNat_and]
  change cp.toNat &&& (2^16-1) = cp.toNat
  exact Nat.and_two_pow_sub_one_of_lt_two_pow h

def arrayHeap (heap : List GcObject) (input output : List UInt32) : List GcObject :=
  heap ++ [.array 0 (input.map Value.i32), .array 0 (output.map Value.i32)]

def padded (capacity : Nat) (written : List UInt32) : List UInt32 :=
  written ++ List.replicate (capacity-written.length) 0

@[simp] theorem arrayHeap_input (heap : List GcObject) (input output : List UInt32) :
    (arrayHeap heap input output)[heap.length]? = some (.array 0 (input.map Value.i32)) := by
  simp [arrayHeap]

@[simp] theorem arrayHeap_output (heap : List GcObject) (input output : List UInt32) :
    (arrayHeap heap input output)[heap.length+1]? = some (.array 0 (output.map Value.i32)) := by
  simp [arrayHeap]

@[simp] theorem arrayHeap_set_output (heap : List GcObject) (input output : List UInt32)
    (i : Nat) (cp : UInt32) :
    (arrayHeap heap input output).set (heap.length+1)
      (.array 0 ((output.map Value.i32).set i (.i32 cp))) =
    arrayHeap heap input (output.set i cp) := by
  simp [arrayHeap, List.map_set]

theorem padded_push (capacity : Nat) (written : List UInt32) (cp : UInt32)
    (h : written.length < capacity) :
    (padded capacity written).set written.length cp = padded capacity (written ++ [cp]) := by
  simpa [padded] using padded_set written 0 cp capacity h

@[simp] theorem mapped_get_next (written remaining : List UInt32) (cp : UInt32) :
    ((written ++ cp :: remaining).map Value.i32)[written.length]? = some (.i32 cp) := by
  simp

end PrefixGc
