(** * Instantiating [spike_module] in the empty store.

    [interp_instantiate] is WasmCert-Coq's executable instantiation; its
    soundness theorem [interp_instantiate_imp_instantiate] turns the
    computed result into the relational spec [instantiate] (module
    typing, allocation, initialisers).  We compute the result once, by
    [vm_compute], and name its parts. *)

From Stdlib Require Import List String NArith.
From Wasm Require Import instantiation_spec instantiation_func interp_instantiate_sound.
From Spike Require Import Module.
Import ListNotations.

Section Inst.

Context `{ho: host}.

Definition empty_store : store_record := Build_store_record nil nil nil nil nil nil.

Definition spike_exports : list exportinst :=
  [ {| exportinst_name := String.list_byte_of_string "is_surrogate_code_point";
       exportinst_val := EV_func 0%N |};
    {| exportinst_name := String.list_byte_of_string "count_non_ascii";
       exportinst_val := EV_func 1%N |};
    {| exportinst_name := String.list_byte_of_string "memory";
       exportinst_val := EV_mem 0%N |} ].

(** The module instance created by instantiation. *)
Definition inst0 : moduleinst := {|
  inst_types := [ty_surrogate; ty_count];
  inst_funcs := [0%N; 1%N];
  inst_tables := [];
  inst_mems := [0%N];
  inst_globals := [];
  inst_elems := [];
  inst_datas := [];
  inst_exports := spike_exports;
|}.

Definition surrogate_closure : funcinst := FC_func_native ty_surrogate inst0 surrogate_func.
Definition count_closure : funcinst := FC_func_native ty_count inst0 count_func.

(** The store right after instantiation (memory: one zeroed page). *)
Definition s0 : store_record := {|
  s_funcs := [surrogate_closure; count_closure];
  s_tables := [];
  s_mems := [gen_mem_instance {| lim_min := 1%N; lim_max := None |}];
  s_globals := [];
  s_elems := [];
  s_datas := [];
|}.

Lemma interp_instantiate_spike hs :
  interp_instantiate hs empty_store spike_module [] =
  (Some (hs, s0, Build_frame [] inst0, []), ""%string).
Proof. vm_compute. reflexivity. Qed.

(** Instantiation in the relational sense of the mechanised spec, with
    no imports and no start/initialisation code left to run. *)
Lemma instantiate_spike (hs : host_state) :
  instantiate empty_store spike_module [] (s0, Build_frame [] inst0, []).
Proof.
  eapply interp_instantiate_imp_instantiate; exact (interp_instantiate_spike hs).
Qed.

End Inst.
