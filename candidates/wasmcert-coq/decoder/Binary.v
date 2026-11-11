(** * decoder.wasm printed from [decoder_module] by WasmCert-Coq's
    (unverified) binary printer, and a check that its (unverified)
    parser reads those bytes back to the same term. *)
From Stdlib Require Import String List.
From Wasm Require Import binary_format_printer binary_format_parser bytes_pp.
From Decoder Require Import Module.

Definition decoder_bytes : list Byte.byte := binary_of_module decoder_module.

Lemma decoder_bytes_parse_back : run_parse_module decoder_bytes = Some decoder_module.
Proof. vm_compute. reflexivity. Qed.

Definition decoder_hex : string := hex_small_no_prefix_of_bytes_compact decoder_bytes.
