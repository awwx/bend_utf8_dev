import WasmCallback
import WasmExecution

namespace PrefixWasm

/-- All abstract callback obligations are discharged for the shipped module. -/
theorem shipped_correct : ShippedCorrect :=
  shipped_correct_of_data data_correct

/-- Every valid input and raw partition admits an initialized, fair execution
of this same module and bridge model. -/
theorem shipped_executions_exist : ShippedExecutionsExist :=
  shipped_executions_exist_of_data data_correct

end PrefixWasm
