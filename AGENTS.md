Laws must define correctness independently of the implementation. They
may import and reference the implementation, but their preconditions
and expected results must come from the specification, so changing the
implementation cannot change what the laws require.
