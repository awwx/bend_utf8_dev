(** * The .wasm bytes of [spike_module], printed by WasmCert-Coq's
    (unverified) binary printer, and a check that WasmCert-Coq's
    (unverified) binary parser reads those exact bytes back to the same
    AST term. *)

From Stdlib Require Import String List.
From Wasm Require Import binary_format_printer binary_format_parser bytes_pp.
From Spike Require Import Module.

Definition spike_bytes : list Byte.byte := binary_of_module spike_module.

Lemma spike_bytes_parse_back : run_parse_module spike_bytes = Some spike_module.
Proof. vm_compute. reflexivity. Qed.

Definition spike_hex : string := hex_small_no_prefix_of_bytes_compact spike_bytes.
