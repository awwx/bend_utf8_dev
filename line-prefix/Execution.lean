import TextSpec
import StreamModel

namespace LinePrefix
open Utf8Pure Copier

/-- The scheduler state between atomic, nonreentrant exported calls. The persistent
line-start bit is the Wasm global; queue entries are complete text writes. -/
structure Machine where
  events : List Text
  atStart : Bool := true
  pending : List Bytes := []
  output : Bytes := []
  closing : Bool := false
  done : Bool := false
  deriving DecidableEq

def initial (chunks : List Text) : Machine := ⟨chunks, true, [], [], false, false⟩

/-- Callback summaries are linked to the actual Talos module in WasmExecution.
Flush and finish are distinct host operations. A write returning false still
queues its text. The complete output chunk is captured before callback return. -/
inductive Step : Machine → Machine → Prop where
  | data (c : Text) (cs : List Text) (s : Bool) (q : List Bytes) (out : Bytes) :
      Step ⟨c::cs, s, q, out, false, false⟩
        ⟨cs, (run s c).1, q ++ [encodeText (run s c).2], out, false, false⟩
  | close (s : Bool) (q : List Bytes) (out : Bytes) :
      Step ⟨[], s, q, out, false, false⟩ ⟨[], s, q, out, true, false⟩
  | flush (cs : List Text) (s : Bool) (b : Bytes) (q : List Bytes) (out : Bytes) (closing : Bool) :
      Step ⟨cs, s, b::q, out, closing, false⟩ ⟨cs, s, q, out++b, closing, false⟩
  | finish (s : Bool) (out : Bytes) :
      Step ⟨[], s, [], out, true, false⟩ ⟨[], s, [], out, true, true⟩

def remaining (m : Machine) : Bytes :=
  m.output ++ m.pending.flatten ++ encodeText (run m.atStart m.events.flatten).2

theorem step_remaining {m n : Machine} (h : Step m n) : remaining n = remaining m := by
  cases h <;> simp [remaining, run, run_append,
    encodeText_append, List.append_assoc]

def rank (m : Machine) : Nat :=
  2 * m.events.length + m.pending.length + (if m.closing then 0 else 1) +
    (if m.done then 0 else 1)

theorem step_rank {m n : Machine} (h : Step m n) : rank n < rank m := by
  cases h with
  | data c cs s q out => simp [rank]; omega
  | close => simp [rank]
  | flush => simp [rank]
  | finish => simp [rank]

/-- Infinite time allows arbitrary finite stuttering. Progress requires some
future operation from every unfinished time, not completion itself. -/
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
      · rw [he]; exact Nat.le_refl _
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

def WellFormed (m : Machine) : Prop :=
  (m.closing = true → m.events = []) ∧
  (m.done = true → m.closing = true ∧ m.events = [] ∧ m.pending = [])

theorem step_wellFormed {m n : Machine} (hw : WellFormed m) (hs : Step m n) :
    WellFormed n := by cases hs <;> simp_all [WellFormed]

theorem execution_wellFormed {start : Machine} (e : Execution start)
    (hw : WellFormed start) (i : Nat) : WellFormed (e.state i) := by
  induction i with
  | zero => simpa [e.starts] using hw
  | succ i ih =>
    rcases e.transition i with h | h
    · simpa [h] using ih
    · exact step_wellFormed ih h

theorem completed_output {chunks : List Text} (e : Execution (initial chunks))
    (i : Nat) (hd : (e.state i).done = true) :
    (e.state i).output = encodeText (prefixLines chunks.flatten) := by
  have hc := execution_remaining e i
  obtain ⟨_, he, hp⟩ := (execution_wellFormed e (by simp [WellFormed, initial]) i).2 hd
  simpa [remaining, he, hp, initial, run, run_correct, encodeText] using hc

/-- A concrete eager scheduler is a witness, not a fairness assumption. -/
def next (m : Machine) : Machine :=
  if m.done then m else
  match m.events with
  | c :: cs => ⟨cs, (run m.atStart c).1, m.pending ++ [encodeText (run m.atStart c).2], m.output, false, false⟩
  | [] => match m.pending with
    | b :: q => ⟨[], m.atStart, q, m.output ++ b, m.closing, false⟩
    | [] => if m.closing then ⟨[], m.atStart, [], m.output, true, true⟩
            else ⟨[], m.atStart, [], m.output, true, false⟩

theorem next_step (m : Machine) (hw : WellFormed m) (hd : m.done = false) :
    Step m (next m) := by
  rcases m with ⟨events, s, pending, output, closing, done⟩
  cases done <;> simp_all [WellFormed]
  cases events with
  | cons c cs =>
    cases closing with
    | false => exact Step.data c cs s pending output
    | true => simp_all
  | nil =>
    cases pending with
    | cons b q => exact Step.flush [] s b q output closing
    | nil =>
      cases closing with
      | false => exact Step.close s [] output
      | true => exact Step.finish s output

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

theorem executions_exist (chunks : List Text) : Nonempty (Execution (initial chunks)) :=
  ⟨eager _ (by simp [WellFormed, initial])⟩

/-- A bridge delivery is any grouping into complete scalars in the same order.
This allows empty deliveries and arbitrary extra splitting. -/
def Delivery (buffers : List Bytes) (chunks : List Text) : Prop :=
  chunks.flatten = (Copier.textEvents buffers []).flatten ∧
  ∀ chunk ∈ chunks, chunk.length ≤ 4096

theorem delivery_decode {bytes : Bytes} {buffers : List Bytes} {chunks : List Text}
    (hp : Partition bytes buffers) (hd : Delivery buffers chunks) :
    chunks.flatten = decodeAll bytes := by
  rw [hd.1, Copier.textEvents_decode, hp.1]

/-- Every completed outcome, not just the first successful outcome. -/
theorem all_completed_outputs {bytes : Bytes} {buffers : List Bytes} {chunks : List Text}
    (hp : Partition bytes buffers) (hd : Delivery buffers chunks)
    (e : Execution (initial chunks)) (i : Nat) (done : (e.state i).done = true) :
    (e.state i).output = encodeText (prefixLines (decodeAll bytes)) := by
  rw [completed_output e i done, delivery_decode hp hd]

/-- Universal progress and exact bytes, for arbitrary raw partitions and scalar
regroupings. Unicode validity is established separately by output_valid. -/
theorem file_correct {bytes : Bytes} {buffers : List Bytes} {chunks : List Text}
    (hp : Partition bytes buffers) (hd : Delivery buffers chunks)
    (e : Execution (initial chunks)) :
    ∃ i, (e.state i).done = true ∧
      (e.state i).output = encodeText (prefixLines (decodeAll bytes)) := by
  obtain ⟨i, _, hi⟩ := eventually_done e 0
  exact ⟨i, hi, all_completed_outputs hp hd e i hi⟩

theorem permitted_delivery_exists (buffers : List Bytes) :
    ∃ chunks, Delivery buffers chunks ∧ Nonempty (Execution (initial chunks)) :=
by
  let chunks := ((Copier.textEvents buffers []).flatten).map (fun c => [c])
  refine ⟨chunks, ⟨?_, ?_⟩, executions_exist _⟩
  · exact List.flatMap_singleton' _
  · intro chunk hc
    obtain ⟨c, _, rfl⟩ := List.mem_map.mp hc
    simp

/-- All permitted callback payloads are complete Unicode scalars. -/
theorem delivery_scalars {buffers : List Bytes} {chunks : List Text}
    (hd : Delivery buffers chunks) : ∀ chunk ∈ chunks, Scalars chunk := by
  intro chunk hc cp hp
  have hm : cp ∈ chunks.flatten := List.mem_flatten.mpr ⟨chunk, hc, hp⟩
  rw [hd.1] at hm
  obtain ⟨t, ht, hcp⟩ := List.mem_flatten.mp hm
  exact Copier.textEvents_scalar buffers [] t ht cp hcp

/-- Completion, correctness and output UTF-8 validity in one statement. -/
theorem file_correct_valid {bytes : Bytes} (_valid : Valid bytes)
    {buffers : List Bytes} {chunks : List Text}
    (hp : Partition bytes buffers) (hd : Delivery buffers chunks)
    (e : Execution (initial chunks)) :
    (∃ i, (e.state i).done = true) ∧
    (∀ i, (e.state i).done = true →
      (e.state i).output = encodeText (prefixLines (decodeAll bytes)) ∧
      Valid (e.state i).output) := by
  obtain ⟨i, hi, _⟩ := file_correct hp hd e
  refine ⟨⟨i, hi⟩, ?_⟩
  intro j hj
  have he := all_completed_outputs hp hd e j hj
  exact ⟨he, he ▸ output_valid bytes⟩


end LinePrefix
