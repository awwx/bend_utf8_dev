import Proof

example : PrefixWasm.ShippedCorrect := PrefixWasm.shipped_correct
example : PrefixWasm.ShippedExecutionsExist := PrefixWasm.shipped_executions_exist
#print axioms PrefixWasm.shipped_correct
#print axioms PrefixWasm.shipped_executions_exist
#print axioms LinePrefix.run_correct
#print axioms LinePrefix.chunks_correct
#print axioms LinePrefix.output_valid
#print axioms PrefixWasm.prefixModule_decodes
