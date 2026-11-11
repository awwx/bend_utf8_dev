(** * [wp] rule for a 16-bit store into memory 0 (uses Mem.v).  Reusable. *)

From Stdlib Require Import ZArith NArith Relations Lia.
From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool eqtype seq.
From Wasm Require Import operations opsem properties.
From Decoder Require Import Steps Control Wp Mem.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section WpMem.

Context `{ho: host}.
Variable hs : host_state.

Definition upd_mem0 (s : store_record) (m' : meminst) : store_record :=
  upd_s_mem s (set_nth m' s.(s_mems) 0 m').

Definition store16_post (m m' : meminst) (a : N) (v : Wasm_int.Int32.int) : Prop :=
  m'.(meminst_type) = m.(meminst_type) /\
  operations.mem_length m' = operations.mem_length m /\
  mem_lookup a m'.(meminst_data) = Some (lo_byte (Wasm_int.Int32.unsigned v)) /\
  mem_lookup (N.add a 1) m'.(meminst_data) = Some (hi_byte (Wasm_int.Int32.unsigned v)) /\
  (forall q, (N.lt q a \/ N.le (N.add a 2) q) ->
     mem_lookup q m'.(meminst_data) = mem_lookup q m.(meminst_data)).

Lemma wp_store16 s f stk (k v : i32) off rest Q m :
  lookup_N f.(f_inst).(inst_mems) 0%num = Some 0%num ->
  lookup_N s.(s_mems) 0%num = Some m ->
  N.le (N.add (N.add (Wasm_int.N_of_uint i32m k) off) 2) (operations.mem_length m) ->
  (forall m', store16_post m m' (N.add (Wasm_int.N_of_uint i32m k) off) v ->
              wp hs (upd_mem0 s m') f stk rest Q) ->
  wp hs s f (VAL_num (VAL_int32 v) :: VAL_num (VAL_int32 k) :: stk)
    (BI_store T_i32 (Some Tp_i16) {| memarg_offset := off; memarg_align := 0%num |} :: rest) Q.
Proof.
  move => Hi Hm Hle HQ.
  case: (store16_spec v Hle) => m' [Hst [H1 [H2 [H3 [H4 H5]]]]].
  apply: (wp_cons (s1 := upd_mem0 s m') (f1 := f) (stk1 := stk)); last first.
  { apply HQ. by repeat split. }
  apply exec_store_packed => //.
  by rewrite /smem_store_packed Hi Hm Hst.
Qed.

Lemma wp_store16_eq s f stk (k v : i32) off rest Q m m' :
  lookup_N f.(f_inst).(inst_mems) 0%num = Some 0%num ->
  lookup_N s.(s_mems) 0%num = Some m ->
  store_packed m (Wasm_int.N_of_uint i32m k) off (serialise_num (VAL_int32 v)) (tp_length Tp_i16) = Some m' ->
  wp hs (upd_mem0 s m') f stk rest Q ->
  wp hs s f (VAL_num (VAL_int32 v) :: VAL_num (VAL_int32 k) :: stk)
    (BI_store T_i32 (Some Tp_i16) {| memarg_offset := off; memarg_align := 0%num |} :: rest) Q.
Proof.
  move => Hi Hm Hst HQ.
  apply: (wp_cons (s1 := upd_mem0 s m') (f1 := f) (stk1 := stk)) => //.
  apply exec_store_packed => //.
  by rewrite /smem_store_packed Hi Hm Hst.
Qed.

End WpMem.
