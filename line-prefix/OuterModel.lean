import Wasm
import Chunking

namespace PrefixWasm
open Wasm

structure PartResult where
  atStart : Bool
  host : Host
  heap : List GcObject

def processParts (s : Bool) (host : Host) (heap : List GcObject) :
    List (List UInt32) → PartResult
  | [] => ⟨s, host, heap⟩
  | part :: rest => processParts (LinePrefix.run s part).1
      (callbackHost s host part) (callbackHeap s heap part) rest

def partWrites (s : Bool) : List (List UInt32) → List (List UInt32)
  | [] => []
  | part :: rest => (LinePrefix.run s part).2 :: partWrites (LinePrefix.run s part).1 rest

theorem processParts_log (s : Bool) (host : Host) (heap : List GcObject)
    (parts : List (List UInt32)) :
    (processParts s host heap parts).host.log = host.log ++ (partWrites s parts).map (Event.write 1) := by
  induction parts generalizing s host heap with
  | nil => simp [processParts, partWrites]
  | cons part rest ih => simp [processParts, partWrites, ih, callbackHost, List.append_assoc]

theorem processParts_state (s : Bool) (host : Host) (heap : List GcObject)
    (parts : List (List UInt32)) :
    (processParts s host heap parts).atStart = (LinePrefix.run s parts.flatten).1 := by
  induction parts generalizing s host heap with
  | nil => rfl
  | cons part rest ih => simp [processParts, ih, LinePrefix.run_append]

theorem partWrites_flatten (s : Bool) (parts : List (List UInt32)) :
    (partWrites s parts).flatten = (LinePrefix.run s parts.flatten).2 := by
  induction parts generalizing s with
  | nil => rfl
  | cons part rest ih => simp [partWrites, ih, LinePrefix.run_append]

@[simp] theorem partWrites_length (s : Bool) (parts : List (List UInt32)) :
    (partWrites s parts).length = parts.length := by
  induction parts generalizing s with
  | nil => rfl
  | cons part rest ih => simp [partWrites, ih]

def wholeResult (s : Bool) (host : Host) (heap : List GcObject) (units : List UInt32) : PartResult :=
  processParts s (prepareHost host units) heap (LinePrefix.Chunking.chunks units)

def wholeWrites (s : Bool) (units : List UInt32) : List (List UInt32) :=
  partWrites s (LinePrefix.Chunking.chunks units)

theorem partWrites_wellFormed (s : Bool) {parts : List (List UInt32)}
    (h : ∀ p ∈ parts, LinePrefix.Utf16.WellFormed p) :
    ∀ p ∈ partWrites s parts, LinePrefix.Utf16.WellFormed p := by
  induction parts generalizing s with
  | nil => simp [partWrites]
  | cons part rest ih =>
    intro p hp
    simp only [partWrites, List.mem_cons] at hp
    rcases hp with rfl | hp
    · exact LinePrefix.Utf16.run_wellFormed (h part (by simp)) s
    · exact ih _ (fun p hp => h p (by simp [hp])) p hp

theorem wholeResult_state (s : Bool) (host : Host) (heap : List GcObject)
    (units : List UInt32) :
    (wholeResult s host heap units).atStart = (LinePrefix.run s units).1 := by
  simp only [wholeResult, processParts_state, LinePrefix.Chunking.flatten_chunks]

theorem wholeResult_log (s : Bool) (host : Host) (heap : List GcObject)
    (units : List UInt32) :
    (wholeResult s host heap units).host.log = host.log ++ (wholeWrites s units).map (Event.write 1) := by
  simp only [wholeResult, wholeWrites, processParts_log, prepareHost]

theorem wholeWrites_flatten (s : Bool) (units : List UInt32) :
    (wholeWrites s units).flatten = (LinePrefix.run s units).2 := by
  simp only [wholeWrites, partWrites_flatten, LinePrefix.Chunking.flatten_chunks]

theorem wholeWrites_length (s : Bool) (units : List UInt32) :
    (wholeWrites s units).length ≤ units.length := by
  simpa only [wholeWrites, partWrites_length] using LinePrefix.Chunking.chunks_length units

theorem wholeWrites_wellFormed (s : Bool) {units : List UInt32}
    (h : LinePrefix.Utf16.WellFormed units) :
    ∀ p ∈ wholeWrites s units, LinePrefix.Utf16.WellFormed p := by
  apply partWrites_wellFormed
  intro p hp
  exact (LinePrefix.Chunking.chunks_valid h p hp).1

end PrefixWasm
