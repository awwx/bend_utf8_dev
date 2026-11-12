(** * Fragment.v: a decidable fragment of WasmCert-Coq 2.2.1 configurations
    on which [reduce] is meant to be deterministic.

    Exports:
    - [bi_ok b]      : basic instruction [b] (recursively through block,
                       loop and if bodies) is in the fragment.
    - [ai_ok e]      : administrative instruction [e] is in the fragment
                       (recursively through labels and frames).  [AI_trap]
                       and [AI_return_invoke] are NOT in it.
    - [es_ok es]     : every instruction of [es] is [ai_ok].
    - [funcs_ok s]   : every function closure of store [s] is native and
                       its body is [bi_ok] (so no host function exists).
    - [cfg_ok s es]  : [funcs_ok s && es_ok es].
    - [trapped es]   : [es] has an [AI_trap] at the first non-value
                       position, possibly under labels and frames.  This
                       is the shape a configuration has after a fragment
                       step that traps.
    - [lfill_es_ok]  : [es_ok (lfill lh es) -> es_ok es].

    Why these choices (see REPORT.txt):
    - Values of every type are allowed (they never step).
    - In the fragment: numeric const/unop/binop/testop/relop/cvtop on the
      INTEGER types, drop, select, nop, unreachable, local.get/set/tee,
      global.get/set, non-vector load/store, memory.size, block, loop, if,
      br, br_if, br_table, return, call.
    - Not in it: host functions (genuinely nondeterministic in [reduce]),
      [AI_trap] (trap propagation [rs_trap] overlaps other redexes, so a
      configuration containing a trap may step in several ways: the
      results are all trap configurations, but not equal), and, to keep
      the proof small, everything else: floats, SIMD, references, tables,
      call_indirect, tail calls, memory.grow and bulk memory.  Note that
      floats, SIMD and memory.grow are NOT nondeterministic in this
      mechanisation (their semantics are functions); they are left out
      only to keep the case analysis small. *)

From Stdlib Require Import NArith List.
From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool eqtype seq.
From Wasm Require Import datatypes operations opsem properties.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Fragment.

Context `{ho: host}.

Definition int_type (t : number_type) : bool :=
  match t with T_i32 | T_i64 => true | _ => false end.

Fixpoint bi_ok (b : basic_instruction) : bool :=
  match b with
  (* values *)
  | BI_const_num _ | BI_const_vec _ | BI_ref_null _ => true
  (* integer arithmetic *)
  | BI_unop t _ | BI_binop t _ | BI_testop t _ | BI_relop t _ => int_type t
  | BI_cvtop t2 _ t1 _ => int_type t1 && int_type t2
  (* parametric, variables *)
  | BI_drop | BI_select _ => true
  | BI_local_get _ | BI_local_set _ | BI_local_tee _ => true
  | BI_global_get _ | BI_global_set _ => true
  (* memory, without grow / bulk operations / vectors *)
  | BI_load t _ _ | BI_store t _ _ => int_type t
  | BI_memory_size => true
  (* control *)
  | BI_nop | BI_unreachable => true
  | BI_block _ bs | BI_loop _ bs => List.forallb bi_ok bs
  | BI_if _ bs1 bs2 => List.forallb bi_ok bs1 && List.forallb bi_ok bs2
  | BI_br _ | BI_br_if _ | BI_br_table _ _ | BI_return => true
  | BI_call _ => true
  | _ => false
  end.

Fixpoint ai_ok (e : administrative_instruction) : bool :=
  match e with
  | AI_basic b => bi_ok b
  | AI_ref _ | AI_ref_extern _ => true
  | AI_invoke _ => true
  | AI_label _ es LI => List.forallb ai_ok es && List.forallb ai_ok LI
  | AI_frame _ _ es => List.forallb ai_ok es
  | AI_trap | AI_return_invoke _ => false
  end.

Definition es_ok (es : seq administrative_instruction) : bool := List.forallb ai_ok es.

Definition func_ok (cl : funcinst) : bool :=
  match cl with
  | FC_func_native _ _ mf => List.forallb bi_ok mf.(modfunc_body)
  | FC_func_host _ _ => false
  end.

Definition funcs_ok (s : store_record) : bool := List.forallb func_ok s.(s_funcs).

Definition cfg_ok (s : store_record) (es : seq administrative_instruction) : bool :=
  funcs_ok s && es_ok es.

(** [trapped es]: the first non-value instruction of [es] is [AI_trap],
    or a label or frame whose body is [trapped]. *)
Inductive trapped : seq administrative_instruction -> Prop :=
| trapped_here : forall vs rest,
    trapped (v_to_e_list vs ++ AI_trap :: rest)
| trapped_label : forall vs n cont es rest,
    trapped es -> trapped (v_to_e_list vs ++ AI_label n cont es :: rest)
| trapped_frame : forall vs n f es rest,
    trapped es -> trapped (v_to_e_list vs ++ AI_frame n f es :: rest).

(** ** Basic facts *)

Lemma es_ok_cat es1 es2 : es_ok (es1 ++ es2) = es_ok es1 && es_ok es2.
Proof. by rewrite /es_ok List.forallb_app. Qed.

Lemma es_ok_cons e es : es_ok (e :: es) = ai_ok e && es_ok es.
Proof. by []. Qed.

Lemma es_ok_v_to_e vs : es_ok (v_to_e_list vs).
Proof.
  elim: vs => [//|v vs IH]. rewrite /= /es_ok /= in IH *. rewrite IH andbT.
  by case: v => [?|?|[?|?|?]].
Qed.

Lemma es_ok_to_e_list bs : es_ok (to_e_list bs) = List.forallb bi_ok bs.
Proof. by elim: bs => [//|b bs IH] /=; rewrite -IH. Qed.

(** A fragment property of a filled context is a property of its hole. *)
Lemma lfill_es_ok k (lh : lholed k) es : es_ok (lfill lh es) -> es_ok es.
Proof.
  elim: lh => [vs es'|k' vs n es' lh IH es''] /=.
  - by rewrite !es_ok_cat => /andP [_ /andP [H _]].
  - rewrite es_ok_cat es_ok_cons => /andP [_ /andP [/= /andP [_ H] _]].
    exact: IH.
Qed.

Lemma trapped_not_const es : trapped es -> const_list es = false.
Proof.
  case => [vs rest|vs n cont es0 rest _|vs n f es0 rest _];
  by rewrite /const_list List.forallb_app /= andbF.
Qed.

Lemma trapped_not_es_ok es : trapped es -> es_ok es = false.
Proof.
  elim => [vs rest|vs n cont es0 rest _ IH|vs n f es0 rest _ IH];
  rewrite es_ok_cat es_ok_v_to_e /= //.
  - by rewrite /es_ok in IH; rewrite IH andbF.
  - by rewrite /es_ok in IH; rewrite IH.
Qed.

End Fragment.
