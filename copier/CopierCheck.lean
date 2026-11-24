import StreamModel
import Utf8Check

namespace Copier
open Utf8Pure

theorem encodeText_append (left right : Text) :
    encodeText (left ++ right) = encodeText left ++ encodeText right := by
  simp [encodeText, List.flatMap_append]

private theorem encoding_roundtrip {bytes : Bytes} {text : Text}
    (h : encodes_text bytes text) : decodes bytes text ∧ encodeText text = bytes := by
  induction text generalizing bytes with
  | nil =>
    change bytes = [] at h
    subst bytes
    exact ⟨rfl, rfl⟩
  | cons c more ih =>
    obtain ⟨seq, rest, hseq, rfl, hrest⟩ := h
    obtain ⟨hdecodes, hencode⟩ := ih hrest
    have hfirst : decodes_first (seq ++ rest) (some (c, rest)) := by
      cases seq with
      | nil =>
        rcases Utf8SpecCheck.encoding_cases _ _ hseq.2 with
          ⟨_, heq⟩ | ⟨_, _, heq⟩ | ⟨_, _, heq⟩ | ⟨_, _, heq⟩ <;> cases heq
      | cons b tail =>
        exact Or.inl ⟨c, rest, ⟨b :: tail, hseq, rfl⟩, rfl⟩
    refine ⟨⟨rest, hfirst, hdecodes⟩, ?_⟩
    simp only [encodeText, List.flatMap_cons, hseq.2, Option.getD_some]
    exact congrArg (seq ++ ·) hencode

theorem valid_roundtrip {bytes : Bytes} {text : Text}
    (hv : Valid bytes) (hd : decodes bytes text) : encodeText text = bytes := by
  obtain ⟨original, h⟩ := hv
  obtain ⟨hdecode, hencode⟩ := encoding_roundtrip h
  rw [decodes_unique_proved bytes text original hd hdecode]
  exact hencode

theorem textEvents_scalar (D : Decoder) (bs : List Bytes) (s : D.State) :
    ∀ t ∈ textEvents D bs s, ∀ c ∈ t, is_unicode_scalar c.val = true := by
  intro _ _ c _
  exact (is_unicode_scalar_matches_char_proved c.val).2 c.valid

private theorem textEvents_flatten (D : Decoder) (bs : List Bytes) (s : D.State) :
    (textEvents D bs s).flatten = decoded.text D (feed D bs s) := by
  induction bs generalizing s with
  | nil => simp [textEvents, decoded.text, feed]
  | cons b bs ih =>
    cases h : D.decode_buffer s b with
    | mk state text =>
      simp only [textEvents, h, List.flatten_cons, ih, feed, feed.then]
      cases feed D bs state
      simp [decoded.text, feed.prepend, List.append_assoc]

private theorem good_deliveries (D : Decoder) (bs : List Bytes) :
    deliveries D good bs = textEvents D bs D.start := by
  simp [deliveries, arguments, readEncoding, good, callback, List.map_map, Function.comp_def]

theorem step_remaining {m n : Machine} (h : Step m n) : remaining n = remaining m := by
  cases h <;> simp [remaining, encodeText_append, List.append_assoc]

def rank (m : Machine) : Nat :=
  2 * m.events.length + m.pending.length + (if m.closing then 0 else 1) +
    (if m.done then 0 else 1)

theorem step_rank {m n : Machine} (h : Step m n) : rank n < rank m := by
  cases h <;> simp [rank] <;> omega

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

theorem completed_output {D : Decoder} {p : Program} {bs : List Bytes}
    (e : Execution (initial D p bs))
    (i : Nat) (hd : (e.state i).done = true) :
    (e.state i).output = encodeText (deliveries D p bs).flatten := by
  have hc := execution_remaining e i
  obtain ⟨he, hp⟩ := done_empty e rfl i hd
  simpa [remaining, he, hp, initial, encodeText] using hc

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

theorem executions_exist (D : Decoder) (p : Program) (bs : List Bytes) :
    Nonempty (Execution (initial D p bs)) :=
  ⟨eager _ (by simp [WellFormed, initial])⟩

/-- Every valid partition and every successful fair execution eventually finishes
with exactly the input bytes. The decoding guarantee at EOF suffices. -/
theorem good_copy {D : Decoder} (hnode : node_characterization D)
    {bytes : Bytes} (hv : Valid bytes) {bs : List Bytes}
    (hp : Partition bytes bs) (e : Execution (initial D good bs)) :
    ∃ i, (e.state i).done = true ∧ (e.state i).output = bytes := by
  obtain ⟨i, _, hd⟩ := eventually_done e 0
  refine ⟨i, hd, ?_⟩
  rw [completed_output e i hd, good_deliveries, textEvents_flatten]
  apply valid_roundtrip hv
  rw [← hp.1]
  exact hnode.1 bs

private theorem witness_valid : Valid witnessBytes := by
  refine ⟨['©'], [0xC2, 0xA9], [], ?_, rfl, rfl⟩
  unfold encodes
  decide

private theorem witness_partition : Partition witnessBytes witnessBuffers := by
  simp [Partition, witnessBytes, witnessBuffers]

-- A single non-ASCII byte cannot form a complete UTF-8 sequence. When
-- finalized on its own, it is the only possible maximal subpart.
private theorem decode_non_ascii_singleton (b : UInt8) (hb : 128 ≤ b.toNat) :
    decodes [b] replacement_char_string := by
  have hnone : no_valid_sequence [b] := by
    intro cp rest ⟨seq, he, hbytes⟩
    rcases Utf8SpecCheck.encoding_cases _ _ he.2 with
      ⟨hsmall, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩
    · simp only [List.cons_append, List.nil_append, List.cons.injEq] at hbytes
      have hbyte := congrArg UInt8.toNat hbytes.1
      change cp.toNat % 256 = b.toNat at hbyte
      omega
    all_goals simp at hbytes
  have hmax : maximal_subpart b [] [b] := by
    refine ⟨⟨[], rfl⟩, Or.inr rfl, ?_⟩
    intro c extra ⟨tail, h⟩
    simp at h
  exact ⟨[], Or.inr ⟨hnone, [b], [], hmax, rfl, rfl⟩, rfl⟩

private theorem singleton_toString {D : Decoder} (h : utf8_decodes D)
    (b : UInt8) (hb : 128 ≤ b.toNat) :
    toString D (.buffer [b]) = replacement_char_string :=
  decodes_unique_proved [b] _ _ (h [[b]]) (decode_non_ascii_singleton b hb)

/-- The split of C2 A9 exposes two independently finalized invalid buffers. -/
theorem bad_counterexample {D : Decoder} (hnode : node_characterization D) :
    Valid witnessBytes ∧ Partition witnessBytes witnessBuffers ∧
    toString D (.buffer [0xC2]) = replacement_char_string ∧
    toString D (.buffer [0xA9]) = replacement_char_string ∧
    ∃ e : Execution (initial D bad witnessBuffers), ∃ i,
      (e.state i).done = true ∧ (e.state i).output = witnessOutput ∧
      (e.state i).output ≠ witnessBytes := by
  have hlead := singleton_toString hnode.1 0xC2 (by decide)
  have htrail := singleton_toString hnode.1 0xA9 (by decide)
  refine ⟨witness_valid, witness_partition, hlead, htrail, ?_⟩
  let e := eager (initial D bad witnessBuffers) (by simp [WellFormed, initial])
  obtain ⟨i, _, hd⟩ := eventually_done e 0
  have ho : (e.state i).output = witnessOutput := by
    rw [completed_output e i hd]
    change encodeText (toString D (.buffer [0xC2]) ++
      (toString D (.buffer [0xA9]) ++ [])) = witnessOutput
    rw [hlead, htrail]
    decide
  exact ⟨e, i, hd, ho, by rw [ho]; decide⟩

end Copier
