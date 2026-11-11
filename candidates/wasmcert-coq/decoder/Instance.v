(** * Instantiating [decoder_module] in the empty store (computed by
    [interp_instantiate], lifted to the relational [instantiate] by its
    soundness lemma), as in the spike. *)

From Stdlib Require Import List String NArith.
From Wasm Require Import instantiation_spec instantiation_func interp_instantiate_sound.
From Decoder Require Import Module.
Import ListNotations.

Section Inst.

Context `{ho: host}.

Definition empty_store0 : store_record := Build_store_record nil nil nil nil nil nil.

Definition decoder_exports : list exportinst :=
  [ {| exportinst_name := name "start"; exportinst_val := EV_func 0%N |};
    {| exportinst_name := name "decode"; exportinst_val := EV_func 1%N |};
    {| exportinst_name := name "done"; exportinst_val := EV_func 2%N |};
    {| exportinst_name := name "memory"; exportinst_val := EV_mem 0%N |} ].

Definition inst0 : moduleinst := {|
  inst_types := [ty_start; ty_decode; ty_done];
  inst_funcs := [0%N; 1%N; 2%N];
  inst_tables := [];
  inst_mems := [0%N];
  inst_globals := [];
  inst_elems := [];
  inst_datas := [];
  inst_exports := decoder_exports;
|}.

Definition s0 : store_record := {|
  s_funcs := [FC_func_native ty_start inst0 start_func;
              FC_func_native ty_decode inst0 decode_func;
              FC_func_native ty_done inst0 done_func];
  s_tables := [];
  s_mems := [gen_mem_instance {| lim_min := PAGES; lim_max := Some PAGES |}];
  s_globals := [];
  s_elems := [];
  s_datas := [];
|}.

Lemma interp_instantiate_decoder hs :
  interp_instantiate hs empty_store0 decoder_module [] =
  (Some (hs, s0, Build_frame [] inst0, []), ""%string).
Proof. vm_compute. reflexivity. Qed.

Lemma instantiate_decoder (hs : host_state) :
  instantiate empty_store0 decoder_module [] (s0, Build_frame [] inst0, []).
Proof.
  eapply interp_instantiate_imp_instantiate; exact (interp_instantiate_decoder hs).
Qed.

End Inst.
