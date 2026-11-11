(** * Proofs for the [start] and [done] exports, and shared lemmas for
    invoking exports on a store like the instantiated one. *)

From Stdlib Require Import ZArith NArith List Lia.
From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool eqtype seq.
From Wasm Require Import datatypes operations opsem properties.
From Utf8 Require Import Utf8Laws Utf8Ref Utf8Proofs.
From Decoder Require Import Module Steps Control Wp Mem WpMem Instance Boundary Repr.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Ltac unfold_code :=
  cbv [lg ls i32c bin rel i_add i_sub i_and i_or i_shl i_shr i_eq i_ltu i_leu i_geu
       load8 store16 if_ ma adv_o emit_fffd emit_cp empty_code range_code len_code
       low6_of_st cp_code pending_code step_code loop_body decode_body done_body start_body BTn
       app cat];
  cbn [f_locs f_inst].

Section Exports.

Context `{ho: host}.
Variable hs : host_state.

Lemma upd_mem0_same s m : nth_error s.(s_mems) 0 = Some m -> upd_mem0 s m = s.
Proof.
  case: s => fs ts ms gs es ds /=.
  case: ms => [|m0 ms] //= [->] //.
Qed.

Lemma store_with_mem0 s m : store_with_mem s 0%num m = upd_mem0 s m.
Proof. by []. Qed.

(** Wrap a [wp] proof of a function body into a call. *)
Lemma call_of_wp s a ts1 ts2 x ts body args defs s' res :
  lookup_N s.(s_funcs) a = Some (FC_func_native (Tf ts1 ts2) inst0 (Build_module_func x ts body)) ->
  length args = length ts1 -> length res = length ts2 ->
  default_vals ts = Some defs ->
  wp hs s (Build_frame (args ++ defs) inst0) [::] body
     (fun s1 f1 stk1 => s1 = s' /\ stk1 = rev res) ->
  call_returns hs s a args s' res.
Proof.
  move => Hl Ha Hr Hd [s1 [f1 [stk1 [Hx [E1 E2]]]]] f; subst.
  by apply: invoke_rule; eauto.
Qed.


Lemma mem_bytes_needed_val : mem_bytes_needed = 327684%num.
Proof. by vm_compute. Qed.
Lemma OUT_addr_val : OUT_addr = 65536%num.
Proof. by vm_compute. Qed.
Lemma out_area0 : out_area 0 = 4%num.
Proof. by vm_compute. Qed.
Lemma N_of_uint_OUT : Wasm_int.N_of_uint i32m (Wasm_int.Int32.repr OUT) = 65536%num.
Proof. by vm_compute. Qed.

Variable s : store_record.
Variable m : meminst.
Hypothesis Hfuncs : s.(s_funcs) = s0.(s_funcs).
Hypothesis Hmem : nth_error s.(s_mems) 0 = Some m.
Hypothesis Hlen : (mem_bytes_needed <= operations.mem_length m)%num.

Lemma start_correct :
  Rst [::] (Wasm_int.Int32.repr 0) /\
  call_returns hs s 0%num [::] s [:: i32v (Wasm_int.Int32.repr 0)].
Proof.
  split; first by split; [left|].
  apply: (call_of_wp (ts1 := [::]) (ts2 := [:: T32]) (x := 0%num) (ts := [::]) (body := start_body)
            (defs := [::])) => //.
  - by rewrite Hfuncs.
  - unfold_code. repeat wp_step. by [].
Qed.

Lemma FFFD_units : utf16le [:: FFFD] = [:: 0xFD; 0xFF]%num.
Proof. by vm_compute. Qed.

Lemma done_correct st v :
  Rst st v ->
  exists m',
    mem_frame m m' OUT_addr (out_area 0) /\
    mem_holds m' OUT_addr (utf16le (ref_done st)) /\
    call_returns hs s 2%num [:: i32v v]
      (store_with_mem s 0%num m') [:: i32_of_nat (List.length (utf16le (ref_done st)))].
Proof.
  move => [HI ->].
  have Hr := enc_range st. have Hz := enc_zero st HI.
  case Est: st => [|b r].
  - (* no pending bytes: no output *)
    exists m; split; [|split].
    + split; [by []|split; [by []|by []]].
    + by move => [|i] n.
    + rewrite store_with_mem0 (upd_mem0_same Hmem).
      apply: (call_of_wp (ts1 := [:: T32]) (ts2 := [:: T32]) (x := 2%num) (ts := [::])
                (body := done_body) (defs := [::])) => //.
      * by rewrite Hfuncs.
      * unfold_code. wp_step.
        apply: wp_if1 => Hc; last first.
        { repeat wp_step. eexists; split; first by [].
          repeat wp_step. by []. }
        exfalso; apply: Hc. by [].
  - (* pending bytes: one U+FFFD *)
    have Hne : enc st <> 0%Z by move => /Hz; rewrite Est.
    rewrite -Est in HI *.
    have Hd : ref_done st = [:: FFFD] by rewrite Est.
    rewrite Hd FFFD_units.
    have Hb : (N.add (N.add (Wasm_int.N_of_uint i32m (Wasm_int.Int32.repr OUT)) 0) 2 <=
               operations.mem_length m)%num.
    { move: Hlen. rewrite mem_bytes_needed_val N_of_uint_OUT. lia. }
    have [m' Hm'] := store16_spec (Wasm_int.Int32.repr 0xFFFD) Hb.
    move: Hm' => [Hst [H1 [H2 [H3 [H4 H5]]]]].
    exists m'; split; [|split].
    + split; [by []|split; [by []|]].
      move => q Hq. apply: H5. move: Hq. rewrite OUT_addr_val out_area0 N_of_uint_OUT. lia.
    + move => [|[|i]] n; cbn [nth_error]; last by case: i.
      * move => [<-]. eexists; split.
        { have -> : (OUT_addr + N.of_nat 0 = N.add (Wasm_int.N_of_uint i32m (Wasm_int.Int32.repr OUT)) 0)%num
            by vm_compute.
          exact H3. }
        by vm_compute.
      * move => [<-]. eexists; split.
        { have -> : (OUT_addr + N.of_nat 1 = N.add (N.add (Wasm_int.N_of_uint i32m (Wasm_int.Int32.repr OUT)) 0) 1)%num
            by vm_compute.
          exact H4. }
        by vm_compute.
    + rewrite store_with_mem0.
      apply: (call_of_wp (ts1 := [:: T32]) (ts2 := [:: T32]) (x := 2%num) (ts := [::])
                (body := done_body) (defs := [::])) => //.
      * by rewrite Hfuncs.
      * unfold_code. wp_step.
        apply: wp_if1 => Hc.
        2: { exfalso. apply: Hne.
             have Hu : Wasm_int.Int32.unsigned (Wasm_int.Int32.repr (enc st)) = enc st.
             { apply Wasm_int.Int32.unsigned_repr. rewrite /Wasm_int.Int32.max_unsigned /=. lia. }
             by rewrite -Hu Hc. }
        repeat wp_step.
        apply: (wp_store16_eq (m := m) (m' := m')) => //.
        repeat wp_step.
        eexists; split; first by []. apply wp_nil. by [].
Qed.

End Exports.
