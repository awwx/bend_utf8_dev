import Utf8Roundtrip

namespace Copier
open Utf8Pure

abbrev Bytes := List UInt8
/-- Ordered nonempty buffers, including the unique empty partition. -/
def Partition (bytes : Bytes) (buffers : List Bytes) : Prop :=
  buffers.flatten = bytes ∧ ∀ b ∈ buffers, b ≠ []

/-- Stateful read-stream delivery. Empty emissions are retained as harmless empty deliveries; the final entry
is decoder finalization, before input close. Entries contain whole scalars. -/
def textEvents : List Bytes → State → List Text
  | [], s => [decodeDone s]
  | b :: bs, s => (decodeBuffer s b).2 :: textEvents bs (decodeBuffer s b).1

theorem textEvents_flatten (bs : List Bytes) (s : State) :
    (textEvents bs s).flatten = (feed RefDecoder bs s).2 ++
      decodeDone (feed RefDecoder bs s).1 := by
  induction bs generalizing s with
  | nil => simp [textEvents, feed]
  | cons b bs ih =>
    simp only [textEvents, List.flatten_cons, ih, feed, feed.then, feed.prepend, RefDecoder]
    simp [List.append_assoc]

theorem textEvents_decode (bs : List Bytes) :
    (textEvents bs []).flatten = decodeAll bs.flatten := by
  rw [textEvents_flatten]
  exact decoded_eq bs

theorem textEvents_scalar (bs : List Bytes) (s : State) :
    ∀ t ∈ textEvents bs s, ∀ c ∈ t, is_unicode_scalar c = true := by
  induction bs generalizing s with
  | nil => simpa [textEvents] using decodeDone_out_scalar s
  | cons b bs ih =>
    intro t ht c hc
    simp only [textEvents, List.mem_cons] at ht
    rcases ht with rfl | ht
    · exact decodeBuffer_out_scalar s b c hc
    · exact ih _ t ht c hc

inductive ReadEncoding where | buffers | utf8 deriving DecidableEq
inductive WriteEncoding where | utf8 deriving DecidableEq
inductive Body where
  | writeArgument
  | letTextToStringThenWrite
  deriving DecidableEq
structure Program where
  readOption : Option ReadEncoding
  writeOption : Option WriteEncoding
  dataBody : Body
  deriving DecidableEq

def good : Program := ⟨some .utf8, some .utf8, .writeArgument⟩
def bad : Program := ⟨none, none, .letTextToStringThenWrite⟩
/-- Defaults of the stream constructors. -/
def readEncoding (p : Program) := p.readOption.getD .buffers
def writeEncoding (p : Program) := p.writeOption.getD .utf8
inductive Argument where | buffer (b : Bytes) | text (t : Text)
/-- Complete-buffer toString is a fresh decode, with immediate finalization. -/
def toString : Argument → Text
  | .buffer b => decodeAll b
  | .text t => t
/-- The local binding has the value returned by toString. Callback execution is
atomic and ordered; the returned text is the argument of output.write. -/
def callback (body : Body) (arg : Argument) : Text :=
  match body with
  | .writeArgument => match arg with | .text t => t | .buffer _ => []
  | .letTextToStringThenWrite => let text := toString arg; text

def arguments (p : Program) (bs : List Bytes) : List Argument :=
  match readEncoding p with
  | .utf8 => (textEvents bs []).map Argument.text
  | .buffers => bs.map Argument.buffer
/-- Stream handles are bound, then the data and close listeners are registered,
then delivery may start. This setup is atomic and has no asynchronous steps. The close listener calls output.close after these events.
This is the elaboration of the tiny callback language into stream actions. -/
def deliveries (p : Program) (bs : List Bytes) : List Text :=
  (arguments p bs).map (callback p.dataBody)

theorem good_deliveries (bs : List Bytes) : deliveries good bs = textEvents bs [] := by
  simp [deliveries, arguments, readEncoding, good, callback, List.map_map, Function.comp_def]

/-- Pending writes are FIFO chunks. A write's Boolean return is deliberately
not part of acceptance: both true and false queue the complete encoded string. -/
structure Machine where
  events : List Text
  pending : List Bytes := []
  output : Bytes := []
  closing : Bool := false
  done : Bool := false
  deriving DecidableEq

def initial (p : Program) (bs : List Bytes) : Machine := ⟨deliveries p bs, [], [], false, false⟩

inductive Step : Machine → Machine → Prop where
  | write (t : Text) (ts : List Text) (q : List Bytes) (out : Bytes)
      (returned : Bool) :
      Step ⟨t :: ts, q, out, false, false⟩
        ⟨ts, q ++ [encodeText t], out, false, false⟩
  | close (q : List Bytes) (out : Bytes) :
      Step ⟨[], q, out, false, false⟩ ⟨[], q, out, true, false⟩
  | flush (ts : List Text) (b : Bytes) (q : List Bytes) (out : Bytes) (closing : Bool) :
      Step ⟨ts, b :: q, out, closing, false⟩ ⟨ts, q, out ++ b, closing, false⟩
  | finish (out : Bytes) :
      Step ⟨[], [], out, true, false⟩ ⟨[], [], out, true, true⟩

/-- Bytes conserved by all queue and callback operations. -/
def remaining (m : Machine) : Bytes :=
  m.output ++ m.pending.flatten ++ encodeText m.events.flatten

theorem step_remaining {m n : Machine} (h : Step m n) : remaining n = remaining m := by
  cases h <;> simp [remaining, encodeText, List.append_assoc]

def rank (m : Machine) : Nat :=
  2 * m.events.length + m.pending.length + (if m.closing then 0 else 1) +
    (if m.done then 0 else 1)

theorem step_rank {m n : Machine} (h : Step m n) : rank n < rank m := by
  cases h <;> simp [rank] <;> omega

/-- Time can stutter arbitrarily. Progress says that from every unfinished time
some subsequent I/O/callback step occurs, rather than assuming completion. -/
structure Execution (start : Machine) where
  state : Nat → Machine
  starts : state 0 = start
  transition : ∀ i, state (i+1) = state i ∨ Step (state i) (state (i+1))
  progress : ∀ i, (state i).done = false → ∃ j, i ≤ j ∧ Step (state j) (state (j+1))

theorem execution_remaining {start : Machine} (e : Execution start) (i : Nat) :
    remaining (e.state i) = remaining start := by
  induction i with
  | zero => rw [e.starts]
  | succ i ih =>
    rcases e.transition i with h | h
    · rw [h]; exact ih
    · exact (step_remaining h).trans ih

theorem rank_nonincreasing {start : Machine} (e : Execution start) {i j : Nat}
    (h : i ≤ j) : rank (e.state j) ≤ rank (e.state i) := by
  induction j with
  | zero =>
    have hi : i = 0 := by omega
    subst i
    exact Nat.le_refl _
  | succ j ih =>
    by_cases heq : i = j+1
    · subst i; exact Nat.le_refl _
    · have hj : i ≤ j := by omega
      apply Nat.le_trans _ (ih hj)
      rcases e.transition j with he | he
      · rw [he]
        exact Nat.le_refl _
      · exact Nat.le_of_lt (step_rank he)

theorem eventually_done {start : Machine} (e : Execution start) :
    ∀ i, ∃ j, i ≤ j ∧ (e.state j).done = true := by
  intro i
  generalize hr : rank (e.state i) = r
  induction r using Nat.strongRecOn generalizing i with
  | ind r ih =>
    cases hd : (e.state i).done with
    | true => exact ⟨i, Nat.le_refl _, hd⟩
    | false =>
      obtain ⟨j, hij, hs⟩ := e.progress i hd
      have hlt : rank (e.state (j+1)) < r := by
        have := rank_nonincreasing e hij
        have := step_rank hs
        omega
      obtain ⟨k, hjk, hk⟩ := ih _ hlt (j+1) rfl
      exact ⟨k, by omega, hk⟩

/-- Finished states have drained all writes and delivered all callbacks. -/
theorem done_empty {start : Machine} (e : Execution start)
    (hstart : start.done = false) (i : Nat) (hd : (e.state i).done = true) :
    (e.state i).events = [] ∧ (e.state i).pending = [] := by
  induction i with
  | zero => rw [e.starts] at hd; simp [hstart] at hd
  | succ i ih =>
    rcases e.transition i with h | h
    · rw [h] at hd ⊢; exact ih hd
    · have hh : ∀ m n, Step m n → n.done = true → n.events = [] ∧ n.pending = [] := by
        intro m n hs hd
        cases hs <;> simp_all
      exact hh _ _ h hd

theorem completed_output {p : Program} {bs : List Bytes} (e : Execution (initial p bs))
    (i : Nat) (hd : (e.state i).done = true) :
    (e.state i).output = encodeText (deliveries p bs).flatten := by
  have hc := execution_remaining e i
  obtain ⟨he, hp⟩ := done_empty e rfl i hd
  simpa [remaining, he, hp, initial, encodeText] using hc

/-- Every valid partition and every successful fair execution eventually finishes
with exactly the input bytes. -/
theorem good_copy {bytes : Bytes} (hv : Valid bytes) {bs : List Bytes}
    (hp : Partition bytes bs) (e : Execution (initial good bs)) :
    ∃ i, (e.state i).done = true ∧ (e.state i).output = bytes := by
  obtain ⟨i, _, hd⟩ := eventually_done e 0
  refine ⟨i, hd, ?_⟩
  rw [completed_output e i hd, good_deliveries, textEvents_decode, hp.1]
  exact valid_roundtrip hv

/-- A concrete eager scheduler demonstrates that successful executions exist for
all partitions; the universal theorem above also allows arbitrary interleavings. -/
def next (m : Machine) : Machine :=
  if m.done then m else
  match m.events with
  | t :: ts => ⟨ts, m.pending ++ [encodeText t], m.output, false, false⟩
  | [] => match m.pending with
    | b :: q => ⟨[], q, m.output ++ b, m.closing, false⟩
    | [] => if m.closing then ⟨[], [], m.output, true, true⟩
            else ⟨[], [], m.output, true, false⟩

def WellFormed (m : Machine) : Prop :=
  (m.closing = true → m.events = []) ∧
  (m.done = true → m.closing = true ∧ m.events = [] ∧ m.pending = [])

theorem next_step (m : Machine) (hw : WellFormed m) (hd : m.done = false) :
    Step m (next m) := by
  rcases m with ⟨events, pending, output, closing, done⟩
  cases done <;> simp_all [WellFormed]
  cases events with
  | cons t ts =>
    cases closing with
    | false => exact Step.write t ts pending output false
    | true => simp_all
  | nil =>
    cases pending with
    | cons b q => exact Step.flush [] b q output closing
    | nil =>
      cases closing with
      | false => exact Step.close [] output
      | true => exact Step.finish output

theorem step_wellFormed {m n : Machine} (hw : WellFormed m) (hs : Step m n) :
    WellFormed n := by
  cases hs <;> simp_all [WellFormed]

def eagerState (start : Machine) : Nat → Machine
  | 0 => start
  | n+1 => next (eagerState start n)

theorem eager_wellFormed {start : Machine} (hw : WellFormed start) (i : Nat) :
    WellFormed (eagerState start i) := by
  induction i with
  | zero => exact hw
  | succ i ih =>
    cases hd : (eagerState start i).done with
    | false => exact step_wellFormed ih (next_step _ ih hd)
    | true => simpa [eagerState, next, hd] using ih

def eager (start : Machine) (hw : WellFormed start) : Execution start where
  state := eagerState start
  starts := rfl
  transition := by
    intro i
    cases hd : (eagerState start i).done with
    | false => exact Or.inr (next_step _ (eager_wellFormed hw i) hd)
    | true => exact Or.inl (by simp [eagerState, next, hd])
  progress := by
    intro i hd
    exact ⟨i, Nat.le_refl _, next_step _ (eager_wellFormed hw i) hd⟩

theorem executions_exist (p : Program) (bs : List Bytes) :
    Nonempty (Execution (initial p bs)) :=
  ⟨eager _ (by simp [WellFormed, initial])⟩

def witnessBytes : Bytes := [0xC2, 0xA9]
def witnessBuffers : List Bytes := [[0xC2], [0xA9]]
def witnessOutput : Bytes := [0xEF, 0xBF, 0xBD, 0xEF, 0xBF, 0xBD]

theorem witness_valid : Valid witnessBytes :=
  Valid.cons (cp := 0xA9) (seq := [0xC2, 0xA9]) (rest := []) (by unfold encodes; decide) Valid.nil

theorem witness_partition : Partition witnessBytes witnessBuffers := by
  unfold Partition witnessBytes witnessBuffers
  simp

theorem witness_decoding :
    decodeAll [0xC2] = [0xFFFD] ∧ decodeAll [0xA9] = [0xFFFD] := by decide

theorem witness_written : encodeText (deliveries bad witnessBuffers).flatten = witnessOutput := by
  decide

theorem bad_counterexample :
    Valid witnessBytes ∧ Partition witnessBytes witnessBuffers ∧
    decodeAll [0xC2] = [0xFFFD] ∧ decodeAll [0xA9] = [0xFFFD] ∧
    ∃ e : Execution (initial bad witnessBuffers), ∃ i,
      (e.state i).done = true ∧ (e.state i).output = witnessOutput ∧
      (e.state i).output ≠ witnessBytes := by
  refine ⟨witness_valid, witness_partition, witness_decoding.1, witness_decoding.2, ?_⟩
  let e := eager (initial bad witnessBuffers) (by simp [WellFormed, initial])
  obtain ⟨i, _, hd⟩ := eventually_done e 0
  have ho : (e.state i).output = witnessOutput :=
    (completed_output e i hd).trans witness_written
  exact ⟨e, i, hd, ho, by rw [ho]; decide⟩

end Copier
