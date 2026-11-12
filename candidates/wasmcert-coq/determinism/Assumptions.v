(* Statements and Print Assumptions of the main results (compiled by check.sh, not by make). *)
From Determinism Require Import Fragment ReduceDet Trapped Preservation Focus HeadStep Det Main.
Check Det.reduce_det_fragment_proved.
Print ReduceDet.reduce_det_fragment.
Check Main.fragment_deterministic_outcome.
Print ReduceDet.deterministic_outcome.
Check ReduceDet.still_reaches_stuck_is_target.
Print Assumptions Det.reduce_det_fragment_proved.
Print Assumptions Main.fragment_deterministic_outcome.
Print Assumptions ReduceDet.still_reaches_stuck_is_target.
