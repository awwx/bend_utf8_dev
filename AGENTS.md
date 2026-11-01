Laws must define correctness independently of the implementation. They
may import and reference the implementation, but their preconditions
and expected results must come from the specification, so changing the
implementation cannot change what the laws require.

Define reusable reference specifications independently of the implementation,
and prove that the implementation agrees with them. Higher-level specifications
should reuse those reference definitions.
