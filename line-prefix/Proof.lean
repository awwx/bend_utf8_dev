import WasmCallback
import WasmExecution

namespace PrefixWasm

/-- UTF-16 processing in the concrete module realizes the independent scalar
algorithm. The representation change is a theorem, not a builtin contract. -/
theorem scalar_data_correct : DataCorrect := by
  intro s host heap chunk hc hb
  have h := data_correct s host heap (LinePrefix.Utf16.encode chunk) hb
    (fun u hu => LinePrefix.Utf16.unit_bound hc hu)
  simpa only [LinePrefix.Utf16.run_encode s hc, callbackHost, afterDataHost, dataArgs] using h

/-- All callback obligations are discharged for the shipped GC module. -/
theorem shipped_correct : ShippedCorrect :=
  shipped_correct_of_data scalar_data_correct

/-- Every valid input and raw partition admits an initialized fair execution
of this same module, including actual string conversion and GC-array calls. -/
theorem shipped_executions_exist : ShippedExecutionsExist :=
  shipped_executions_exist_of_data scalar_data_correct

end PrefixWasm
