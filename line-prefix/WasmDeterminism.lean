import Interpreter.Wasm.Host.Run

namespace Wasm

/-- A proved successful export constrains every terminal outcome, including
    structural traps, by deterministic Talos reduction. -/
theorem RunsExportWith.outcome_complete
    {α : Type} [Inhabited α] {env : HostEnv α} {m : Module} {op : String}
    {call : ExportCall α} {post : ExportReturn α → Prop}
    (h : RunsExportWith env m op call post) :
    PartiallyRunsExportWithOutcome env m op call (fun observed =>
      ∃ values, observed.outcome = .done values ∧
        post { values := values, final := observed.final }) := by
  obtain ⟨config, hs, trace, values, final, steps, hp⟩ := h
  refine ⟨config, hs, ?_⟩
  apply SmallStep.TerminatesWithOutcome.toPartiallyMeetsOutcome
  exact ⟨trace, .done values, final, steps, values, rfl, hp⟩

/-- An export whose exact normal result is proved has that result in every
    other successful specification from the same initial call. -/
theorem RunsExportWith.exact_result
    {α : Type} [Inhabited α] {env : HostEnv α} {m : Module} {op : String}
    {call : ExportCall α} {values : List Value} {final : Store α}
    {post : ExportReturn α → Prop}
    (h : RunsExportWith env m op call (fun r => r.values = values ∧ r.final = final))
    (other : RunsExportWith env m op call post) :
    post { values := values, final := final } := by
  obtain ⟨⟨vs, st⟩, ⟨rfl, rfl⟩, hp⟩ := h.deterministic other
  exact hp

/-- Pointwise terminal-trace form, exposing no restriction to successful
    executions: every finite terminal trace returns normally and satisfies
    the established specification. -/
theorem RunsExportWith.every_terminal
    {α : Type} [Inhabited α] {env : HostEnv α} {m : Module} {op : String}
    {call : ExportCall α} {post : ExportReturn α → Prop}
    (h : RunsExportWith env m op call post)
    {config : SmallStep.Config α}
    (hs : startExportConfig? env m op call = some config)
    {trace : List SmallStep.StepKind} {outcome : SmallStep.ObservableOutcome}
    {final : SmallStep.MachineStore α}
    (steps : SmallStep.Steps config trace ⟨SmallStep.ObservableOutcome.toExpr outcome, final⟩) :
    ∃ values, outcome = .done values ∧
      post { values := values, final := final.wasm } := by
  obtain ⟨c, hc, hp⟩ := h.outcome_complete
  rw [hs] at hc
  cases hc
  exact hp _ _ _ steps

/-- No structural trap is reachable from a successfully specified export. -/
theorem RunsExportWith.no_trap
    {α : Type} [Inhabited α] {env : HostEnv α} {m : Module} {op : String}
    {call : ExportCall α} {post : ExportReturn α → Prop}
    (h : RunsExportWith env m op call post)
    {config : SmallStep.Config α}
    (hs : startExportConfig? env m op call = some config)
    {trace : List SmallStep.StepKind} {reason : SmallStep.TrapReason}
    {final : SmallStep.MachineStore α}
    (steps : SmallStep.Steps config trace ⟨.trapped reason, final⟩) : False := by
  obtain ⟨values, he, _⟩ := h.every_terminal hs (outcome := .trapped reason) steps
  cases he

end Wasm
