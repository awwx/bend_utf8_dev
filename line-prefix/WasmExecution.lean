import Execution
import Wasm
import WasmTransform
import WasmDeterminism

namespace PrefixWasm
open Wasm

/-- Callback memory after input preparation and all output writes. -/
def callbackMemory (mem : Mem) (s : Bool) (chunk : List UInt32) : Mem :=
  writeWords (writeWords mem 0 chunk) 16384 (LinePrefix.run s chunk).2

/-- The exact callback obligation, discharged by the instruction-level proof.
The statement quantifies over every persistent memory and operation history. -/
def DataCorrect : Prop := ∀ (s : Bool) (log : Host) (mem : Mem) (chunk : List UInt32),
  mem.pages = 1 → chunk.length ≤ 4096 →
  Runs "data" (store s log (writeWords mem 0 chunk)) [.i32 (UInt32.ofNat chunk.length)]
    (store (LinePrefix.run s chunk).1 (log ++ [.write 1 (LinePrefix.run s chunk).2])
      (callbackMemory mem s chunk))

theorem store_injective {s t : Bool} {a b : Host} {m n : Mem}
    (h : store s a m = store t b n) : s = t ∧ a = b ∧ m = n := by
  have hg := congrArg (fun st : Store Host => st.globals) h
  have hl := congrArg (fun st : Store Host => st.host) h
  have hm := congrArg (fun st : Store Host => st.mem) h
  refine ⟨?_, hl, hm⟩
  cases s <;> cases t <;> simp_all [store]

theorem Runs.unique {op : String} {st a b : Store Host} {args : List Value}
    (ha : Runs op st args a) (hb : Runs op st args b) : a = b := by
  obtain ⟨r, hra, hrb⟩ := Wasm.RunsExportWith.deterministic ha hb
  exact hra.2.symm.trans hrb.2

/-- Every successful actual callback outcome has exactly the proved bit,
write payload and persistent memory, not merely one selected outcome. -/
theorem data_unique (correct : DataCorrect) (s t : Bool) (log : Host)
    (mem mem' : Mem) (chunk output : List UInt32)
    (hp : mem.pages = 1) (hb : chunk.length ≤ 4096)
    (actual : Runs "data" (store s log (writeWords mem 0 chunk))
      [.i32 (UInt32.ofNat chunk.length)] (store t (log ++ [.write 1 output]) mem')) :
    t = (LinePrefix.run s chunk).1 ∧ output = (LinePrefix.run s chunk).2 ∧
      mem' = callbackMemory mem s chunk := by
  obtain ⟨ht, hl, hm⟩ := store_injective (actual.unique (correct s log mem chunk hp hb))
  have ho : output = (LinePrefix.run s chunk).2 := by simpa using hl
  exact ⟨ht, ho, hm⟩

/-- Persistent module state is part of each scheduler state. It is reconstructed
without resetting memory, globals, or operation history between calls. -/
structure Runtime where
  scheduler : LinePrefix.Machine
  log : Host
  memory : Mem

def Runtime.wasm (r : Runtime) : Store Host :=
  store r.scheduler.atStart r.log r.memory

def runtimeInitial (chunks : List (List UInt32)) : Runtime :=
  ⟨LinePrefix.initial chunks, initialization, (prefixModule.initialStore (α := Host)).mem⟩

def Admissible (r : Runtime) : Prop :=
  r.memory.pages = 1 ∧ ∀ chunk ∈ r.scheduler.events, chunk.length ≤ 4096

/-- Concrete calls in Talos, interleaved with FIFO asynchronous host completion.
The data constructor admits arbitrary returned bit, memory and write payload;
the program theorem, rather than this constructor, identifies them. -/
inductive RuntimeStep : Runtime → Runtime → Prop where
  | data (c : List UInt32) (cs : List (List UInt32)) (s t : Bool)
      (q : List (List UInt8)) (out : List UInt8) (log : Host) (mem mem' : Mem)
      (payload : List UInt32)
      (actual : Runs "data" (store s log (writeWords mem 0 c)) [.i32 (UInt32.ofNat c.length)]
        (store t (log ++ [.write 1 payload]) mem')) :
      RuntimeStep ⟨⟨c::cs,s,q,out,false,false⟩,log,mem⟩
        ⟨⟨cs,t,q++[Copier.encodeText payload],out,false,false⟩,log++[.write 1 payload],mem'⟩
  | close (s : Bool) (q : List (List UInt8)) (out : List UInt8) (log : Host) (mem mem' : Mem)
      (actual : Runs "close" (store s log mem) [] (store s (log++[.end 1]) mem')) :
      RuntimeStep ⟨⟨[],s,q,out,false,false⟩,log,mem⟩
        ⟨⟨[],s,q,out,true,false⟩,log++[.end 1],mem'⟩
  | flush (cs : List (List UInt32)) (s : Bool) (b : List UInt8) (q : List (List UInt8))
      (out : List UInt8) (closing : Bool) (log : Host) (mem : Mem) :
      RuntimeStep ⟨⟨cs,s,b::q,out,closing,false⟩,log,mem⟩
        ⟨⟨cs,s,q,out++b,closing,false⟩,log,mem⟩
  | finish (s : Bool) (out : List UInt8) (log : Host) (mem : Mem) :
      RuntimeStep ⟨⟨[],s,[],out,true,false⟩,log,mem⟩
        ⟨⟨[],s,[],out,true,true⟩,log,mem⟩

theorem runtime_step_projects (correct : DataCorrect) {a b : Runtime}
    (ha : Admissible a) (step : RuntimeStep a b) :
    LinePrefix.Step a.scheduler b.scheduler ∧ Admissible b := by
  cases step with
  | data c cs s t q out log mem mem' payload actual =>
    have hb := ha.2 c (by simp)
    obtain ⟨rfl, rfl, rfl⟩ := data_unique correct s t log mem mem' c payload ha.1 hb actual
    refine ⟨LinePrefix.Step.data c cs s q out, ?_, ?_⟩
    · simpa [callbackMemory, writeWords_pages] using ha.1
    · intro chunk hc
      exact ha.2 chunk (by simp [hc])
  | close s q out log mem mem' actual =>
    have he := actual.unique (close_correct s log mem)
    have hm := (store_injective he).2.2
    subst mem'
    exact ⟨LinePrefix.Step.close s q out, ha.1, by simp⟩
  | flush => exact ⟨LinePrefix.Step.flush _ _ _ _ _ _, ha⟩
  | finish => exact ⟨LinePrefix.Step.finish _ _, ha⟩

/-- Fair schedules of actual module calls and host I/O operations. -/
structure RuntimeExecution (start : Runtime) where
  state : Nat → Runtime
  starts : state 0 = start
  transition : ∀ i, state (i+1) = state i ∨ RuntimeStep (state i) (state (i+1))
  progress : ∀ i, (state i).scheduler.done = false →
    ∃ j, i ≤ j ∧ RuntimeStep (state j) (state (j+1))

theorem runtime_admissible (correct : DataCorrect) {start : Runtime}
    (e : RuntimeExecution start) (ha : Admissible start) (i : Nat) :
    Admissible (e.state i) := by
  induction i with
  | zero => simpa [e.starts] using ha
  | succ i ih =>
    rcases e.transition i with hs | hs
    · simpa [hs] using ih
    · exact (runtime_step_projects correct ih hs).2

def RuntimeExecution.project (correct : DataCorrect) {start : Runtime}
    (e : RuntimeExecution start) (ha : Admissible start) :
    LinePrefix.Execution start.scheduler where
  state i := (e.state i).scheduler
  starts := congrArg Runtime.scheduler e.starts
  transition i := by
    rcases e.transition i with hs | hs
    · exact Or.inl (congrArg Runtime.scheduler hs)
    · exact Or.inr (runtime_step_projects correct (runtime_admissible correct e ha i) hs).1
  progress i hi := by
    obtain ⟨j, hij, hs⟩ := e.progress i hi
    exact ⟨j, hij, (runtime_step_projects correct (runtime_admissible correct e ha j) hs).1⟩

theorem runtime_initial_admissible {chunks : List (List UInt32)}
    (hb : ∀ chunk ∈ chunks, chunk.length ≤ 4096) : Admissible (runtimeInitial chunks) := by
  exact ⟨rfl, hb⟩

/-- Whole-file theorem over the concrete persistent Wasm and host execution. -/
theorem runtime_file_correct (correct : DataCorrect) {bytes : List UInt8}
    (valid : Copier.Valid bytes) {buffers : List (List UInt8)} {chunks : List (List UInt32)}
    (partition : Copier.Partition bytes buffers) (delivery : LinePrefix.Delivery buffers chunks)
    (e : RuntimeExecution (runtimeInitial chunks)) :
    (∃ i, (e.state i).scheduler.done = true) ∧
    (∀ i, (e.state i).scheduler.done = true →
      (e.state i).scheduler.output = Copier.encodeText (LinePrefix.prefixLines (Utf8Pure.decodeAll bytes)) ∧
      Copier.Valid (e.state i).scheduler.output) :=
  LinePrefix.file_correct_valid valid partition delivery
    (e.project correct (runtime_initial_admissible delivery.2))

/-- A realizable eager schedule, maintaining memory and operation history. -/
def runtimeNext (r : Runtime) : Runtime :=
  if r.scheduler.done then r else
  match r.scheduler.events with
  | c::cs =>
    let result := LinePrefix.run r.scheduler.atStart c
    ⟨⟨cs,result.1,r.scheduler.pending++[Copier.encodeText result.2],r.scheduler.output,false,false⟩,
      r.log++[.write 1 result.2], callbackMemory r.memory r.scheduler.atStart c⟩
  | [] => match r.scheduler.pending with
    | b::q => ⟨⟨[],r.scheduler.atStart,q,r.scheduler.output++b,r.scheduler.closing,false⟩,r.log,r.memory⟩
    | [] => if r.scheduler.closing then
        ⟨⟨[],r.scheduler.atStart,[],r.scheduler.output,true,true⟩,r.log,r.memory⟩
      else ⟨⟨[],r.scheduler.atStart,[],r.scheduler.output,true,false⟩,r.log++[.end 1],r.memory⟩

theorem runtime_next_step (correct : DataCorrect) (r : Runtime)
    (ha : Admissible r) (hw : LinePrefix.WellFormed r.scheduler)
    (hd : r.scheduler.done = false) : RuntimeStep r (runtimeNext r) := by
  rcases r with ⟨⟨events,s,pending,output,closing,done⟩,log,mem⟩
  cases done <;> simp_all [LinePrefix.WellFormed]
  cases events with
  | cons c cs =>
    cases closing with
    | false =>
      exact RuntimeStep.data c cs s (LinePrefix.run s c).1 pending output log mem
        (callbackMemory mem s c) (LinePrefix.run s c).2
        (correct s log mem c ha.1 (ha.2 c (by simp)))
    | true => simp_all
  | nil =>
    cases pending with
    | cons b q => exact RuntimeStep.flush [] s b q output closing log mem
    | nil =>
      cases closing with
      | false => exact RuntimeStep.close s [] output log mem mem (close_correct s log mem)
      | true => exact RuntimeStep.finish s output log mem

def runtimeEagerState (start : Runtime) : Nat → Runtime
  | 0 => start
  | n+1 => runtimeNext (runtimeEagerState start n)

theorem runtime_eager_invariants (correct : DataCorrect) {start : Runtime}
    (ha : Admissible start) (hw : LinePrefix.WellFormed start.scheduler) (i : Nat) :
    Admissible (runtimeEagerState start i) ∧
      LinePrefix.WellFormed (runtimeEagerState start i).scheduler := by
  induction i with
  | zero => exact ⟨ha,hw⟩
  | succ i ih =>
    cases hd : (runtimeEagerState start i).scheduler.done with
    | true => simpa [runtimeEagerState,runtimeNext,hd] using ih
    | false =>
      have hs := runtime_next_step correct _ ih.1 ih.2 hd
      have hp := runtime_step_projects correct ih.1 hs
      exact ⟨hp.2, LinePrefix.step_wellFormed ih.2 hp.1⟩

def runtimeEager (correct : DataCorrect) (start : Runtime)
    (ha : Admissible start) (hw : LinePrefix.WellFormed start.scheduler) : RuntimeExecution start where
  state := runtimeEagerState start
  starts := rfl
  transition i := by
    cases hd : (runtimeEagerState start i).scheduler.done with
    | true => exact Or.inl (by simp [runtimeEagerState,runtimeNext,hd])
    | false =>
      have hi := runtime_eager_invariants correct ha hw i
      exact Or.inr (runtime_next_step correct _ hi.1 hi.2 hd)
  progress i hd := by
    have hi := runtime_eager_invariants correct ha hw i
    exact ⟨i,Nat.le_refl _,runtime_next_step correct _ hi.1 hi.2 hd⟩

theorem runtime_executions_exist (correct : DataCorrect) {chunks : List (List UInt32)}
    (hb : ∀ chunk ∈ chunks, chunk.length ≤ 4096) :
    Nonempty (RuntimeExecution (runtimeInitial chunks)) :=
  ⟨runtimeEager correct _ (runtime_initial_admissible hb)
    (by simp [LinePrefix.WellFormed,runtimeInitial,LinePrefix.initial])⟩

/-- Total normal return plus a statement about *all* terminal traces, including
potential traps. This justifies the normal-call boundaries in RuntimeStep. -/
def TotalExact (op : String) (st : Store Host) (args : List Value) (final : Store Host) : Prop :=
  Runs op st args final ∧
  PartiallyRunsExportWithOutcome env prefixModule op { initial := st, arguments := args }
    (fun observed => observed.outcome = .done [] ∧ observed.final = final)

theorem Runs.totalExact {op : String} {st final : Store Host} {args : List Value}
    (h : Runs op st args final) : TotalExact op st args final := by
  refine ⟨h, ?_⟩
  obtain ⟨config, hs, hp⟩ := h.outcome_complete
  refine ⟨config, hs, ?_⟩
  intro trace outcome finalState steps
  obtain ⟨values, ho, hv, hf⟩ := hp trace outcome finalState steps
  change values = [] at hv
  rw [hv] at ho
  exact ⟨ho, hf⟩

/-- Every accepted text write uses the output handle and contains only complete
Unicode scalars. This is stronger than validity of the final concatenation. -/
def HistorySafe (log : Host) : Prop :=
  ∀ h text, Event.write h text ∈ log → h = 1 ∧ LinePrefix.Scalars text

def TextSafe (r : Runtime) : Prop :=
  (∀ chunk ∈ r.scheduler.events, LinePrefix.Scalars chunk) ∧ HistorySafe r.log

theorem runtime_step_textSafe (correct : DataCorrect) {a b : Runtime}
    (ha : Admissible a) (ht : TextSafe a) (step : RuntimeStep a b) : TextSafe b := by
  cases step with
  | data c cs s t q out log mem mem' payload actual =>
    obtain ⟨rfl,rfl,rfl⟩ := data_unique correct s t log mem mem' c payload ha.1
      (ha.2 c (by simp)) actual
    refine ⟨?_, ?_⟩
    · intro chunk hc
      exact ht.1 chunk (by simp [hc])
    · intro h text he
      simp only [List.mem_append, List.mem_singleton] at he
      rcases he with he | he
      · exact ht.2 h text he
      · cases he
        exact ⟨rfl, LinePrefix.run_scalar (ht.1 c (by simp)) s⟩
  | close =>
    refine ⟨ht.1, ?_⟩
    intro h text he
    simp only [List.mem_append,List.mem_singleton] at he
    rcases he with he | he
    · exact ht.2 h text he
    · cases he
  | flush => exact ht
  | finish => exact ht

theorem runtime_textSafe (correct : DataCorrect) {buffers : List (List UInt8)}
    {chunks : List (List UInt32)} (delivery : LinePrefix.Delivery buffers chunks)
    (e : RuntimeExecution (runtimeInitial chunks)) (i : Nat) : TextSafe (e.state i) := by
  induction i with
  | zero =>
    rw [e.starts]
    refine ⟨LinePrefix.delivery_scalars delivery, ?_⟩
    intro h text he
    simp [runtimeInitial,initialization] at he
  | succ i ih =>
    rcases e.transition i with hs | hs
    · simpa [hs] using ih
    · exact runtime_step_textSafe correct
        (runtime_admissible correct e (runtime_initial_admissible delivery.2) i) ih hs

/-- Reviewable top-level claim: actual module initialization; total, uniquely
correct callback outcomes; valid complete-scalar writes; and the full fair
execution result for every valid file, raw partition and permitted delivery. -/
def ShippedCorrect : Prop :=
  TotalExact "init" (initial []) [] (runtimeInitial []).wasm ∧
  (∀ s log mem chunk, mem.pages = 1 → chunk.length ≤ 4096 →
    TotalExact "data" (store s log (writeWords mem 0 chunk)) [.i32 (UInt32.ofNat chunk.length)]
      (store (LinePrefix.run s chunk).1 (log ++ [.write 1 (LinePrefix.run s chunk).2])
        (callbackMemory mem s chunk))) ∧
  (∀ s log mem, TotalExact "close" (store s log mem) [] (store s (log++[.end 1]) mem)) ∧
  (∀ s chunk, LinePrefix.Scalars chunk → LinePrefix.Scalars (LinePrefix.run s chunk).2) ∧
  (∀ {buffers : List (List UInt8)} {chunks : List (List UInt32)},
    LinePrefix.Delivery buffers chunks → ∀ e : RuntimeExecution (runtimeInitial chunks),
    ∀ i, HistorySafe (e.state i).log) ∧
  (∀ {bytes : List UInt8}, Copier.Valid bytes →
    ∀ {buffers : List (List UInt8)} {chunks : List (List UInt32)},
    Copier.Partition bytes buffers → LinePrefix.Delivery buffers chunks →
    ∀ e : RuntimeExecution (runtimeInitial chunks),
    (∃ i, (e.state i).scheduler.done = true) ∧
    (∀ i, (e.state i).scheduler.done = true →
      (e.state i).scheduler.output = Copier.encodeText (LinePrefix.prefixLines (Utf8Pure.decodeAll bytes)) ∧
      Copier.Valid (e.state i).scheduler.output))

theorem shipped_correct_of_data (correct : DataCorrect) : ShippedCorrect := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (init_correct []).totalExact
  · intro s log mem chunk hp hb
    exact (correct s log mem chunk hp hb).totalExact
  · intro s log mem
    exact (close_correct s log mem).totalExact
  · intro s chunk hs
    exact LinePrefix.run_scalar hs s
  · intro buffers chunks hd e i
    exact (runtime_textSafe correct hd e i).2
  · intro bytes hv buffers chunks hp hd e
    exact runtime_file_correct correct hv hp hd e

/-- Nonvacuity for every allowed raw partition, using a concrete faithful
complete-scalar delivery and a concrete schedule of the actual callbacks. -/
def ShippedExecutionsExist : Prop :=
  ∀ {bytes : List UInt8}, Copier.Valid bytes →
  ∀ {buffers : List (List UInt8)}, Copier.Partition bytes buffers →
  ∃ chunks, LinePrefix.Delivery buffers chunks ∧
    TotalExact "init" (initial []) [] (runtimeInitial chunks).wasm ∧
    Nonempty (RuntimeExecution (runtimeInitial chunks))

theorem shipped_executions_exist_of_data (correct : DataCorrect) : ShippedExecutionsExist := by
  intro bytes _ buffers _
  obtain ⟨chunks, hd, _⟩ := LinePrefix.permitted_delivery_exists buffers
  exact ⟨chunks, hd, (init_correct []).totalExact, runtime_executions_exist correct hd.2⟩

end PrefixWasm
