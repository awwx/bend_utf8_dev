(* Writes the module bytes, as a hex string, to spike_hex.out (see Makefile). *)
From Stdlib Require Import String.
From Spike Require Import Binary.
Open Scope string_scope.
Set Printing Width 1000000.
Redirect "spike_hex" Eval vm_compute in spike_hex.
