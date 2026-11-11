(** * Final theorem statements of the spike (see REPORT.md). *)

From Stdlib Require Import ZArith NArith List String.
From Wasm Require Import operations opsem instantiation_spec.
From Spike Require Import Spec Module Instance Surrogate Count.
Import ListNotations.

Section Final.

Context `{ho: host}.

(** [is_surrogate_code_point]:
    1. instantiating [spike_module] (no imports) in the empty store gives
       store [s0] and instance [inst0] (relational spec [instantiate]);
    2. [inst0] exports function address 0 as "is_surrogate_code_point";
    3. on ANY later store whose function table is still that of [s0]
       (memory, globals etc. may have changed arbitrarily), invoking
       address 0 with any i32 [cp] reduces, under the mechanised small-step
       semantics, to exactly the i32 constant 1 if the spec says [cp] is
       a surrogate and 0 otherwise, without changing the store. *)
Theorem is_surrogate_code_point_correct (hs : host_state) :
  instantiate empty_store spike_module [] (s0, Build_frame [] inst0, []) /\
  In {| exportinst_name := String.list_byte_of_string "is_surrogate_code_point";
        exportinst_val := EV_func 0%N |} inst0.(inst_exports) /\
  forall s f (cp : i32),
    s.(s_funcs) = s0.(s_funcs) ->
    reduce_trans
      (hs, s, f, [AI_basic (BI_const_num (VAL_int32 cp)); AI_invoke 0%N])
      (hs, s, f, [AI_basic (BI_const_num (VAL_int32
         (if is_surrogate_code_point (Z.to_N (Wasm_int.Int32.unsigned cp))
          then Wasm_int.Int32.one else Wasm_int.Int32.zero)))]).
Proof.
  split; [exact (instantiate_spike hs) |].
  split; [left; reflexivity |].
  intros s f cp Hfuncs.
  apply is_surrogate_code_point_invoke.
  rewrite Hfuncs; reflexivity.
Qed.

(** [count_non_ascii]:
    1. as above, instantiation gives [s0]/[inst0];
    2. [inst0] exports function address 1 as "count_non_ascii" and
       memory address 0 as "memory";
    3. on ANY later store whose function table is still that of [s0] and
       whose memory 0 is ANY memory [m] (any contents, any size; e.g.
       after the host wrote the input and/or grew it), if the bytes [bs]
       are stored in [m] at address [ptr], [len] = number of bytes, and
       [ptr + len <= 2^32], then invoking address 1 with [ptr], [len]
       reduces to the i32 constant [count_non_ascii bs], and the final
       store is the same store [s] (memory unchanged). *)
Theorem count_non_ascii_correct (hs : host_state) :
  instantiate empty_store spike_module [] (s0, Build_frame [] inst0, []) /\
  In {| exportinst_name := String.list_byte_of_string "count_non_ascii";
        exportinst_val := EV_func 1%N |} inst0.(inst_exports) /\
  In {| exportinst_name := String.list_byte_of_string "memory";
        exportinst_val := EV_mem 0%N |} inst0.(inst_exports) /\
  forall s f m (ptr len : i32) (bs : list byte),
    s.(s_funcs) = s0.(s_funcs) ->
    List.nth_error s.(s_mems) 0 = Some m ->
    bytes_at m (Z.to_N (Wasm_int.Int32.unsigned ptr)) bs ->
    Z.of_nat (List.length bs) = Wasm_int.Int32.unsigned len ->
    (Wasm_int.Int32.unsigned ptr + Wasm_int.Int32.unsigned len <= Wasm_int.Int32.modulus)%Z ->
    reduce_trans
      (hs, s, f, [AI_basic (BI_const_num (VAL_int32 ptr));
                  AI_basic (BI_const_num (VAL_int32 len)); AI_invoke 1%N])
      (hs, s, f, [AI_basic (BI_const_num
                    (VAL_int32 (Wasm_int.Int32.repr (Z.of_nat (count_non_ascii bs)))))]).
Proof.
  split; [exact (instantiate_spike hs) |].
  split; [right; left; reflexivity |].
  split; [right; right; left; reflexivity |].
  intros s f m ptr len bs Hfuncs Hmem Hbytes Hlen Hbound.
  apply count_non_ascii_invoke with (m := m); auto.
  - rewrite Hfuncs; reflexivity.
Qed.

End Final.
