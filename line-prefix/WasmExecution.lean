import Execution
import OuterModel
import WasmDeterminism

namespace PrefixWasm
open Wasm
open LinePrefix (Scalars)

def dataArgs (host : Host) (_chunk : List UInt32) : List Value :=
  [.externref (some host.strings.length)]

def dataResult (s : Bool) (host : Host) (heap : List GcObject) (chunk : List UInt32) :=
  wholeResult s host heap (LinePrefix.Utf16.encode chunk)

def resultStore (r : PartResult) : Store Host := store r.atStart r.host r.heap

/-- The public callback takes a whole immutable Node string; its length is
obtained inside Wasm. The only per-string limit is i32 representability. -/
def DataCorrect : Prop := ∀ (s : Bool) (host : Host) (heap : List GcObject)
    (chunk : List UInt32), Scalars chunk → (LinePrefix.Utf16.encode chunk).length < 2^32 →
  Runs "data" (store s (prepareHost host (LinePrefix.Utf16.encode chunk)) heap)
    (dataArgs host chunk) (resultStore (dataResult s host heap chunk))

theorem decoded_writes (s : Bool) {chunk : List UInt32} (hc : Scalars chunk) :
    ((wholeWrites s (LinePrefix.Utf16.encode chunk)).map LinePrefix.Utf16.decode).flatten =
      (LinePrefix.run s chunk).2 := by
  rw [← LinePrefix.Chunking.decode_flatten
    (wholeWrites_wellFormed s ⟨chunk,hc,rfl⟩), wholeWrites_flatten,
    LinePrefix.Utf16.run_encode s hc, LinePrefix.Utf16.decode_encode (LinePrefix.run_scalar hc s)]

theorem store_injective {s t : Bool} {a b : Host} {m n : List GcObject}
    (h : store s a m = store t b n) : s = t ∧ a = b ∧ m = n := by
  have hg := congrArg (fun st : Store Host => st.globals) h
  have hl := congrArg (fun st : Store Host => st.host) h
  have hm := congrArg (fun st : Store Host => st.gcHeap) h
  refine ⟨?_, hl, hm⟩
  cases s <;> cases t <;> simp_all [store]

theorem Runs.unique {op : String} {st a b : Store Host} {args : List Value}
    (ha : Runs op st args a) (hb : Runs op st args b) : a = b := by
  obtain ⟨r, hra, hrb⟩ := Wasm.RunsExportWith.deterministic ha hb
  exact hra.2.symm.trans hrb.2

/-- The complete persistent store is carried between calls; the heap is never
reset. The bridge only introduces the next immutable input string. -/
structure Runtime where
  scheduler : LinePrefix.Machine
  host : Host
  heap : List GcObject

def Runtime.wasm (r : Runtime) : Store Host :=
  store r.scheduler.atStart r.host r.heap

def runtimeInitial (chunks : List (List UInt32)) : Runtime :=
  ⟨LinePrefix.initial chunks, { log := initialization, strings := [] },
    (prefixModule.initialStore (α := Host)).gcHeap⟩

def Admissible (r : Runtime) : Prop :=
  ∀ chunk ∈ r.scheduler.events,
    Scalars chunk ∧ (LinePrefix.Utf16.encode chunk).length < 2^32

/-- A callback may submit several immutable UTF-16 strings. The host queues
all captured writes in order; their contents are determined by actual execution. -/
inductive RuntimeStep : Runtime → Runtime → Prop where
  | data (c : List UInt32) (cs : List (List UInt32)) (s t : Bool)
      (q : List (List UInt8)) (out : List UInt8) (host host' : Host) (heap heap' : List GcObject)
      (payloads : List (List UInt32))
      (valid : ∀ units ∈ payloads, LinePrefix.Utf16.WellFormed units)
      (captured : host'.log = host.log ++ payloads.map (Event.write 1))
      (actual : Runs "data" (store s (prepareHost host (LinePrefix.Utf16.encode c)) heap)
        (dataArgs host c) (store t host' heap')) :
      RuntimeStep ⟨⟨c::cs,s,q,out,false,false⟩,host,heap⟩
        ⟨⟨cs,t,q++(payloads.map LinePrefix.Utf16.decode).map Copier.encodeText,out,false,false⟩,host',heap'⟩
  | close (s : Bool) (q : List (List UInt8)) (out : List UInt8) (host : Host) (heap heap' : List GcObject)
      (actual : Runs "close" (store s host heap) []
        (store s { host with log := host.log++[.end 1] } heap')) :
      RuntimeStep ⟨⟨[],s,q,out,false,false⟩,host,heap⟩
        ⟨⟨[],s,q,out,true,false⟩,{ host with log := host.log++[.end 1] },heap'⟩
  | flush (cs : List (List UInt32)) (s : Bool) (b : List UInt8) (q : List (List UInt8))
      (out : List UInt8) (closing : Bool) (host : Host) (heap : List GcObject) :
      RuntimeStep ⟨⟨cs,s,b::q,out,closing,false⟩,host,heap⟩
        ⟨⟨cs,s,q,out++b,closing,false⟩,host,heap⟩
  | finish (s : Bool) (out : List UInt8) (host : Host) (heap : List GcObject) :
      RuntimeStep ⟨⟨[],s,[],out,true,false⟩,host,heap⟩
        ⟨⟨[],s,[],out,true,true⟩,host,heap⟩

theorem runtime_step_projects (correct : DataCorrect) {a b : Runtime}
    (ha : Admissible a) (step : RuntimeStep a b) :
    LinePrefix.Step a.scheduler b.scheduler ∧ Admissible b := by
  cases step with
  | data c cs s t q out host host' heap heap' payloads valid captured actual =>
    have hc := ha c (by simp)
    obtain ⟨rfl,rfl,rfl⟩ := store_injective (actual.unique (correct s host heap c hc.1 hc.2))
    have hlog := wholeResult_log s host heap (LinePrefix.Utf16.encode c)
    have he : payloads.map (Event.write 1) =
        (wholeWrites s (LinePrefix.Utf16.encode c)).map (Event.write 1) := by
      exact List.append_cancel_left (captured.symm.trans hlog)
    have hp : payloads = wholeWrites s (LinePrefix.Utf16.encode c) :=
      (List.map_inj_right (fun a b h => by simpa using h)).mp he
    subst payloads
    have hs : (dataResult s host heap c).atStart = (LinePrefix.run s c).1 := by
      rw [dataResult, wholeResult_state, LinePrefix.Utf16.run_encode s hc.1]
    refine ⟨?_, ?_⟩
    · rw [hs]
      apply LinePrefix.Step.data
      · exact decoded_writes s hc.1
      · simp only [List.length_map]
        have := wholeWrites_length s (LinePrefix.Utf16.encode c)
        omega
    · intro chunk hm
      exact ha chunk (by simp [hm])
  | close s q out host heap heap' actual =>
    have he := actual.unique (close_correct s host heap)
    have hm := (store_injective he).2.2
    subst heap'
    exact ⟨LinePrefix.Step.close s q out, by intro c hc; simp at hc⟩
  | flush => exact ⟨LinePrefix.Step.flush _ _ _ _ _ _, ha⟩
  | finish => exact ⟨LinePrefix.Step.finish _ _, ha⟩

structure RuntimeExecution (start : Runtime) where
  state : Nat → Runtime
  starts : state 0 = start
  transition : ∀ i, state (i+1) = state i ∨ RuntimeStep (state i) (state (i+1))
  progress : ∀ i, (state i).scheduler.done = false →
    ∃ j, i ≤ j ∧ RuntimeStep (state j) (state (j+1))

theorem runtime_admissible (correct : DataCorrect) {start : Runtime}
    (e : RuntimeExecution start) (ha : Admissible start) (i : Nat) : Admissible (e.state i) := by
  induction i with
  | zero => simpa [e.starts] using ha
  | succ i ih =>
    rcases e.transition i with hs | hs
    · simpa [hs] using ih
    · exact (runtime_step_projects correct ih hs).2

def RuntimeExecution.project (correct : DataCorrect) {start : Runtime}
    (e : RuntimeExecution start) (ha : Admissible start) : LinePrefix.Execution start.scheduler where
  state i := (e.state i).scheduler
  starts := congrArg Runtime.scheduler e.starts
  transition i := by
    rcases e.transition i with hs | hs
    · exact Or.inl (congrArg Runtime.scheduler hs)
    · exact Or.inr (runtime_step_projects correct (runtime_admissible correct e ha i) hs).1
  progress i hi := by
    obtain ⟨j, hij, hs⟩ := e.progress i hi
    exact ⟨j, hij, (runtime_step_projects correct (runtime_admissible correct e ha j) hs).1⟩

theorem runtime_initial_admissible {buffers : List (List UInt8)} {chunks : List (List UInt32)}
    (hd : LinePrefix.Delivery buffers chunks) : Admissible (runtimeInitial chunks) := by
  intro c hc
  exact ⟨LinePrefix.delivery_scalars hd c hc, hd.2 c hc⟩

theorem runtime_file_correct (correct : DataCorrect) {bytes : List UInt8}
    (valid : Copier.Valid bytes) {buffers : List (List UInt8)} {chunks : List (List UInt32)}
    (partition : Copier.Partition bytes buffers) (delivery : LinePrefix.Delivery buffers chunks)
    (e : RuntimeExecution (runtimeInitial chunks)) :
    (∃ i, (e.state i).scheduler.done = true) ∧
    (∀ i, (e.state i).scheduler.done = true →
      (e.state i).scheduler.output = Copier.encodeText (LinePrefix.prefixLines (Utf8Pure.decodeAll bytes)) ∧
      Copier.Valid (e.state i).scheduler.output) :=
  LinePrefix.file_correct_valid valid partition delivery
    (e.project correct (runtime_initial_admissible delivery))

/-- A concrete schedule with actual heap and string-table persistence. -/
def runtimeNext (r : Runtime) : Runtime :=
  if r.scheduler.done then r else
  match r.scheduler.events with
  | c::cs =>
    let result := dataResult r.scheduler.atStart r.host r.heap c
    let payloads := wholeWrites r.scheduler.atStart (LinePrefix.Utf16.encode c)
    ⟨⟨cs,result.atStart,r.scheduler.pending++(payloads.map LinePrefix.Utf16.decode).map Copier.encodeText,
      r.scheduler.output,false,false⟩,result.host,result.heap⟩
  | [] => match r.scheduler.pending with
    | b::q => ⟨⟨[],r.scheduler.atStart,q,r.scheduler.output++b,r.scheduler.closing,false⟩,r.host,r.heap⟩
    | [] => if r.scheduler.closing then
        ⟨⟨[],r.scheduler.atStart,[],r.scheduler.output,true,true⟩,r.host,r.heap⟩
      else ⟨⟨[],r.scheduler.atStart,[],r.scheduler.output,true,false⟩,
        {r.host with log := r.host.log++[.end 1]},r.heap⟩

theorem runtime_next_step (correct : DataCorrect) (r : Runtime)
    (ha : Admissible r) (hw : LinePrefix.WellFormed r.scheduler)
    (hd : r.scheduler.done = false) : RuntimeStep r (runtimeNext r) := by
  rcases r with ⟨⟨events,s,pending,output,closing,done⟩,host,heap⟩
  cases done <;> simp_all [LinePrefix.WellFormed]
  cases events with
  | cons c cs =>
    cases closing with
    | false =>
      have hc := ha c (by simp)
      exact RuntimeStep.data c cs s (dataResult s host heap c).atStart pending output host
        (dataResult s host heap c).host heap (dataResult s host heap c).heap
        (wholeWrites s (LinePrefix.Utf16.encode c))
        (wholeWrites_wellFormed s ⟨c,hc.1,rfl⟩)
        (wholeResult_log s host heap (LinePrefix.Utf16.encode c))
        (correct s host heap c hc.1 hc.2)
    | true => simp_all
  | nil =>
    cases pending with
    | cons b q => exact RuntimeStep.flush [] s b q output closing host heap
    | nil =>
      cases closing with
      | false => exact RuntimeStep.close s [] output host heap heap (close_correct s host heap)
      | true => exact RuntimeStep.finish s output host heap

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

theorem runtime_executions_exist (correct : DataCorrect) {buffers : List (List UInt8)}
    {chunks : List (List UInt32)} (hd : LinePrefix.Delivery buffers chunks) :
    Nonempty (RuntimeExecution (runtimeInitial chunks)) :=
  ⟨runtimeEager correct _ (runtime_initial_admissible hd)
    (by simp [LinePrefix.WellFormed,runtimeInitial,LinePrefix.initial])⟩

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

/-- Every individual write, not just their concatenation, represents complete
Unicode scalars and uses the output handle. -/
def HistorySafe (host : Host) : Prop :=
  ∀ h units, Event.write h units ∈ host.log →
    h = 1 ∧ ∃ text, Scalars text ∧ LinePrefix.Utf16.encode text = units

theorem runtime_step_historySafe {a b : Runtime}
    (ht : HistorySafe a.host) (step : RuntimeStep a b) : HistorySafe b.host := by
  cases step with
  | data c cs s t q out host host' heap heap' payloads valid captured actual =>
    intro h units he
    rw [captured] at he
    rcases List.mem_append.mp he with he | he
    · exact ht h units he
    · obtain ⟨payload,hp,he⟩ := List.mem_map.mp he
      cases he
      exact ⟨rfl, valid units hp⟩
  | close =>
    intro h units he
    simp only [List.mem_append,List.mem_singleton] at he
    rcases he with he | he
    · exact ht h units he
    · cases he
  | flush => exact ht
  | finish => exact ht

theorem runtime_historySafe {chunks : List (List UInt32)}
    (e : RuntimeExecution (runtimeInitial chunks)) (i : Nat) : HistorySafe (e.state i).host := by
  induction i with
  | zero =>
    rw [e.starts]
    intro h units he
    simp [runtimeInitial,initialization] at he
  | succ i ih =>
    rcases e.transition i with hs | hs
    · simpa [hs] using ih
    · exact runtime_step_historySafe ih hs

/-- Total, exact builtin/module behavior and the full scalar-level file theorem.
The normal callback boundary in RuntimeStep is justified by total and universal
terminal-outcome guarantees, rather than excluding traps by assumption. -/
def ShippedCorrect : Prop :=
  TotalExact "init" (initial {}) [] (runtimeInitial []).wasm ∧
  (∀ s host heap chunk, Scalars chunk → (LinePrefix.Utf16.encode chunk).length < 2^32 →
    TotalExact "data" (store s (prepareHost host (LinePrefix.Utf16.encode chunk)) heap)
      (dataArgs host chunk)
      (resultStore (dataResult s host heap chunk))) ∧
  (∀ s host heap, TotalExact "close" (store s host heap) []
    (store s {host with log := host.log++[.end 1]} heap)) ∧
  (∀ s chunk, Scalars chunk →
    ∃ output, Scalars output ∧
      (LinePrefix.run s (LinePrefix.Utf16.encode chunk)).2 = LinePrefix.Utf16.encode output) ∧
  (∀ {chunks}, ∀ e : RuntimeExecution (runtimeInitial chunks), ∀ i, HistorySafe (e.state i).host) ∧
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
  · exact (init_correct {}).totalExact
  · intro s host heap chunk hc hb
    exact (correct s host heap chunk hc hb).totalExact
  · intro s host heap
    exact (close_correct s host heap).totalExact
  · intro s chunk hc
    refine ⟨(LinePrefix.run s chunk).2, LinePrefix.run_scalar hc s, ?_⟩
    rw [LinePrefix.Utf16.run_encode s hc]
  · intro chunks e i
    exact runtime_historySafe e i
  · intro bytes hv buffers chunks hp hd e
    exact runtime_file_correct correct hv hp hd e

/-- Every allowed full-string delivery has a concrete initialized execution.
A faithful abstract delivery also exists for each raw partition; the forwarder
is not assumed to emit that particular witness's singleton events. -/
def ShippedExecutionsExist : Prop :=
  (∀ {bytes : List UInt8}, Copier.Valid bytes →
    ∀ {buffers : List (List UInt8)}, Copier.Partition bytes buffers →
    ∃ chunks, LinePrefix.Delivery buffers chunks ∧
      TotalExact "init" (initial {}) [] (runtimeInitial chunks).wasm ∧
      Nonempty (RuntimeExecution (runtimeInitial chunks))) ∧
  (∀ {buffers : List (List UInt8)} {chunks : List (List UInt32)},
    LinePrefix.Delivery buffers chunks →
    TotalExact "init" (initial {}) [] (runtimeInitial chunks).wasm ∧
    Nonempty (RuntimeExecution (runtimeInitial chunks)))

theorem shipped_executions_exist_of_data (correct : DataCorrect) : ShippedExecutionsExist := by
  constructor
  · intro bytes _ buffers _
    obtain ⟨chunks, hd, _⟩ := LinePrefix.permitted_delivery_exists buffers
    exact ⟨chunks, hd, (init_correct {}).totalExact, runtime_executions_exist correct hd⟩
  · intro buffers chunks hd
    exact ⟨(init_correct {}).totalExact, runtime_executions_exist correct hd⟩

end PrefixWasm
