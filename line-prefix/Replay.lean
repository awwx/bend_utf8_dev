import Lean
open Lean

/-- Recheck imported non-core declarations without trusting stored project
    declarations or elaborator extensions. -/
def main : IO Unit := do
  initSearchPath (← findSysroot)
  let full ← importModules #[{module := `Proof}] {} (loadExts := false)
  let base ← importModules #[{module := `Init}, {module := `Lean}, {module := `Std}]
    {} (loadExts := false)
  let mut declarations : Std.HashMap Name ConstantInfo := {}
  for (name, info) in full.constants.map₁.toList do
    if !base.contains name then declarations := declarations.insert name info
  IO.println s!"Replaying {declarations.size} non-core declarations"
  let checked ← base.toKernelEnv.replay declarations
  for (theoremName, statementName) in
      [(`PrefixWasm.shipped_correct, `PrefixWasm.ShippedCorrect),
       (`PrefixWasm.shipped_executions_exist, `PrefixWasm.ShippedExecutionsExist)] do
    unless declarations.contains theoremName do
      throw <| IO.userError s!"Missing theorem {theoremName} in replay input"
    match checked.find? theoremName with
    | some (.thmInfo theoremInfo) =>
      unless theoremInfo.type == .const statementName [] do
        throw <| IO.userError s!"Unexpected statement for {theoremName}"
    | _ => throw <| IO.userError s!"Missing theorem {theoremName} after kernel replay"
  IO.println "Independent kernel replay OK"
