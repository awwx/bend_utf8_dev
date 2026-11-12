(** * HeadStep.v: the steps of [ves ++ [e]] (values, then one instruction
    [e] of the fragment), listed explicitly.

    Exports:
    - [head_step hs s f ves e hs' s' f' X]: an explicit, per-rule list of
      the ways [ves ++ [e]] can step to [X].  Every constructor takes an
      arbitrary prefix [ves0] of values that the rule does not consume.
    - [head_step_complete] (PROVED): in a store without host functions, if
      [e] is a fragment instruction (not a value) and [ves] is a value list,
      every [reduce] step of [ves ++ [e]] is a [head_step].
    This turns reasoning about the context rule [r_label] into inversion
    on [head_step]; see Det.v for determinism of [head_step]. *)

From Stdlib Require Import NArith ZArith List.
From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool eqtype seq.
From Wasm Require Import datatypes operations opsem properties contexts.
From Determinism Require Import Fragment ReduceDet Trapped Preservation Focus.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section HeadStep.

Context `{ho: host}.

Notation ais := (seq administrative_instruction).

Inductive head_step (hs : host_state) (s : store_record) (f : frame) :
  ais -> administrative_instruction -> host_state -> store_record -> frame -> ais -> Prop :=
| hs_unop : forall ves0 v op t, unop_typecheck v t op ->
    head_step hs s f (ves0 ++ [:: $VN v]) (AI_basic (BI_unop t op)) hs s f (ves0 ++ [:: $VN (app_unop op v)])
| hs_binop_success : forall ves0 v1 v2 v op t, binop_typecheck v1 v2 t op -> app_binop op v1 v2 = Some v ->
    head_step hs s f (ves0 ++ [:: $VN v1; $VN v2]) (AI_basic (BI_binop t op)) hs s f (ves0 ++ [:: $VN v])
| hs_binop_failure : forall ves0 v1 v2 op t, binop_typecheck v1 v2 t op -> app_binop op v1 v2 = None ->
    head_step hs s f (ves0 ++ [:: $VN v1; $VN v2]) (AI_basic (BI_binop t op)) hs s f (ves0 ++ [:: AI_trap])
| hs_testop_i32 : forall ves0 c op,
    head_step hs s f (ves0 ++ [:: $VN (VAL_int32 c)]) (AI_basic (BI_testop T_i32 op)) hs s f
      (ves0 ++ [:: $VN (VAL_int32 (wasm_bool (app_testop_i i32m op c)))])
| hs_testop_i64 : forall ves0 c op,
    head_step hs s f (ves0 ++ [:: $VN (VAL_int64 c)]) (AI_basic (BI_testop T_i64 op)) hs s f
      (ves0 ++ [:: $VN (VAL_int32 (wasm_bool (app_testop_i i64m op c)))])
| hs_relop : forall ves0 v1 v2 t op, relop_typecheck v1 v2 t op ->
    head_step hs s f (ves0 ++ [:: $VN v1; $VN v2]) (AI_basic (BI_relop t op)) hs s f
      (ves0 ++ [:: $VN (VAL_int32 (wasm_bool (app_relop op v1 v2)))])
| hs_convert_success : forall ves0 t1 t2 v v' op sx,
    typeof_num v = t1 -> cvtop_valid t2 op t1 sx -> eval_cvt t2 op sx v = Some v' ->
    head_step hs s f (ves0 ++ [:: $VN v]) (AI_basic (BI_cvtop t2 op t1 sx)) hs s f (ves0 ++ [:: $VN v'])
| hs_convert_failure : forall ves0 t1 t2 v op sx,
    typeof_num v = t1 -> cvtop_valid t2 op t1 sx -> eval_cvt t2 op sx v = None ->
    head_step hs s f (ves0 ++ [:: $VN v]) (AI_basic (BI_cvtop t2 op t1 sx)) hs s f (ves0 ++ [:: AI_trap])
| hs_unreachable : forall ves0,
    head_step hs s f ves0 (AI_basic BI_unreachable) hs s f (ves0 ++ [:: AI_trap])
| hs_nop : forall ves0, head_step hs s f ves0 (AI_basic BI_nop) hs s f ves0
| hs_drop : forall ves0 v, head_step hs s f (ves0 ++ [:: v_to_e v]) (AI_basic BI_drop) hs s f ves0
| hs_select_false : forall ves0 n v1 v2 ot, n = Wasm_int.int_zero i32m ->
    head_step hs s f (ves0 ++ [:: v_to_e v1; v_to_e v2; $VN (VAL_int32 n)]) (AI_basic (BI_select ot)) hs s f
      (ves0 ++ [:: v_to_e v2])
| hs_select_true : forall ves0 n v1 v2 ot, n <> Wasm_int.int_zero i32m ->
    head_step hs s f (ves0 ++ [:: v_to_e v1; v_to_e v2; $VN (VAL_int32 n)]) (AI_basic (BI_select ot)) hs s f
      (ves0 ++ [:: v_to_e v1])
| hs_if_false : forall ves0 c tb es1 es2, c = Wasm_int.int_zero i32m ->
    head_step hs s f (ves0 ++ [:: $VN (VAL_int32 c)]) (AI_basic (BI_if tb es1 es2)) hs s f
      (ves0 ++ [:: AI_basic (BI_block tb es2)])
| hs_if_true : forall ves0 c tb es1 es2, c <> Wasm_int.int_zero i32m ->
    head_step hs s f (ves0 ++ [:: $VN (VAL_int32 c)]) (AI_basic (BI_if tb es1 es2)) hs s f
      (ves0 ++ [:: AI_basic (BI_block tb es1)])
| hs_br_if_false : forall ves0 n i, n = Wasm_int.int_zero i32m ->
    head_step hs s f (ves0 ++ [:: $VN (VAL_int32 n)]) (AI_basic (BI_br_if i)) hs s f ves0
| hs_br_if_true : forall ves0 n i, n <> Wasm_int.int_zero i32m ->
    head_step hs s f (ves0 ++ [:: $VN (VAL_int32 n)]) (AI_basic (BI_br_if i)) hs s f
      (ves0 ++ [:: AI_basic (BI_br i)])
| hs_br_table : forall ves0 iss c i j,
    N.lt (Wasm_int.N_of_uint i32m c) (N.of_nat (length iss)) ->
    lookup_N iss (Wasm_int.N_of_uint i32m c) = Some j ->
    head_step hs s f (ves0 ++ [:: $VN (VAL_int32 c)]) (AI_basic (BI_br_table iss i)) hs s f
      (ves0 ++ [:: AI_basic (BI_br j)])
| hs_br_table_length : forall ves0 iss c i,
    N.le (N.of_nat (length iss)) (Wasm_int.N_of_uint i32m c) ->
    head_step hs s f (ves0 ++ [:: $VN (VAL_int32 c)]) (AI_basic (BI_br_table iss i)) hs s f
      (ves0 ++ [:: AI_basic (BI_br i)])
| hs_local_tee : forall ves0 i v,
    head_step hs s f (ves0 ++ [:: v_to_e v]) (AI_basic (BI_local_tee i)) hs s f
      (ves0 ++ [:: v_to_e v; v_to_e v; AI_basic (BI_local_set i)])
| hs_block : forall ves0 vs es n m tb t1s t2s,
    expand f.(f_inst) tb = Some (Tf t1s t2s) -> const_list vs -> length vs = n -> length t1s = n -> length t2s = m ->
    head_step hs s f (ves0 ++ vs) (AI_basic (BI_block tb es)) hs s f
      (ves0 ++ [:: AI_label m [::] (vs ++ to_e_list es)])
| hs_loop : forall ves0 vs es n m tb t1s t2s,
    expand f.(f_inst) tb = Some (Tf t1s t2s) -> const_list vs -> length vs = n -> length t1s = n -> length t2s = m ->
    head_step hs s f (ves0 ++ vs) (AI_basic (BI_loop tb es)) hs s f
      (ves0 ++ [:: AI_label n [:: AI_basic (BI_loop tb es)] (vs ++ to_e_list es)])
| hs_call : forall ves0 i a, lookup_N f.(f_inst).(inst_funcs) i = Some a ->
    head_step hs s f ves0 (AI_basic (BI_call i)) hs s f (ves0 ++ [:: AI_invoke a])
| hs_invoke_native : forall ves0 addr ts1 ts2 inst x ts es vs n m k defaults,
    lookup_N s.(s_funcs) addr = Some (FC_func_native (Tf ts1 ts2) inst (Build_module_func x ts es)) ->
    length vs = n -> length ts = k -> length ts1 = n -> length ts2 = m -> default_vals ts = Some defaults ->
    head_step hs s f (ves0 ++ v_to_e_list vs) (AI_invoke addr) hs s f
      (ves0 ++ [:: AI_frame m (Build_frame (vs ++ defaults) inst) [:: AI_label m [::] (to_e_list es)]])
| hs_local_get : forall ves0 v j, lookup_N f.(f_locs) j = Some v ->
    head_step hs s f ves0 (AI_basic (BI_local_get j)) hs s f (ves0 ++ [:: v_to_e v])
| hs_local_set : forall ves0 f' i v vd,
    f'.(f_inst) = f.(f_inst) -> N.to_nat i < length f.(f_locs) ->
    f'.(f_locs) = set_nth vd f.(f_locs) (N.to_nat i) v ->
    head_step hs s f (ves0 ++ [:: v_to_e v]) (AI_basic (BI_local_set i)) hs s f' ves0
| hs_global_get : forall ves0 i v, sglob_val s f.(f_inst) i = Some v ->
    head_step hs s f ves0 (AI_basic (BI_global_get i)) hs s f (ves0 ++ [:: v_to_e v])
| hs_global_set : forall ves0 i v s', supdate_glob s f.(f_inst) i v = Some s' ->
    head_step hs s f (ves0 ++ [:: v_to_e v]) (AI_basic (BI_global_set i)) hs s' f ves0
| hs_load_success : forall ves0 t bs k marg m,
    smem s f.(f_inst) = Some m ->
    load m (Wasm_int.N_of_uint i32m k) marg.(memarg_offset) (tnum_length t) = Some bs ->
    head_step hs s f (ves0 ++ [:: $VN (VAL_int32 k)]) (AI_basic (BI_load t None marg)) hs s f
      (ves0 ++ [:: $VN (wasm_deserialise bs t)])
| hs_load_failure : forall ves0 t k marg m,
    smem s f.(f_inst) = Some m ->
    load m (Wasm_int.N_of_uint i32m k) marg.(memarg_offset) (tnum_length t) = None ->
    head_step hs s f (ves0 ++ [:: $VN (VAL_int32 k)]) (AI_basic (BI_load t None marg)) hs s f
      (ves0 ++ [:: AI_trap])
| hs_load_packed_success : forall ves0 t tp k marg m bs sx,
    smem s f.(f_inst) = Some m ->
    load_packed sx m (Wasm_int.N_of_uint i32m k) marg.(memarg_offset) (tp_length tp) (tnum_length t) = Some bs ->
    head_step hs s f (ves0 ++ [:: $VN (VAL_int32 k)]) (AI_basic (BI_load t (Some (tp, sx)) marg)) hs s f
      (ves0 ++ [:: $VN (wasm_deserialise bs t)])
| hs_load_packed_failure : forall ves0 t tp k marg m sx,
    smem s f.(f_inst) = Some m ->
    load_packed sx m (Wasm_int.N_of_uint i32m k) marg.(memarg_offset) (tp_length tp) (tnum_length t) = None ->
    head_step hs s f (ves0 ++ [:: $VN (VAL_int32 k)]) (AI_basic (BI_load t (Some (tp, sx)) marg)) hs s f
      (ves0 ++ [:: AI_trap])
| hs_store_success : forall ves0 t v k marg s',
    smem_store s f.(f_inst) (Wasm_int.N_of_uint i32m k) marg.(memarg_offset) v t = Some s' ->
    head_step hs s f (ves0 ++ [:: $VN (VAL_int32 k); $VN v]) (AI_basic (BI_store t None marg)) hs s' f ves0
| hs_store_failure : forall ves0 t v k marg,
    smem_store s f.(f_inst) (Wasm_int.N_of_uint i32m k) marg.(memarg_offset) v t = None ->
    head_step hs s f (ves0 ++ [:: $VN (VAL_int32 k); $VN v]) (AI_basic (BI_store t None marg)) hs s f
      (ves0 ++ [:: AI_trap])
| hs_store_packed_success : forall ves0 t v k marg tp s',
    smem_store_packed s f.(f_inst) (Wasm_int.N_of_uint i32m k) marg.(memarg_offset) v tp = Some s' ->
    typeof_num v = t ->
    head_step hs s f (ves0 ++ [:: $VN (VAL_int32 k); $VN v]) (AI_basic (BI_store t (Some tp) marg)) hs s' f ves0
| hs_store_packed_failure : forall ves0 t v k marg tp,
    smem_store_packed s f.(f_inst) (Wasm_int.N_of_uint i32m k) marg.(memarg_offset) v tp = None ->
    typeof_num v = t ->
    head_step hs s f (ves0 ++ [:: $VN (VAL_int32 k); $VN v]) (AI_basic (BI_store t (Some tp) marg)) hs s f
      (ves0 ++ [:: AI_trap])
| hs_memory_size : forall ves0 m n,
    smem s f.(f_inst) = Some m -> mem_size m = n ->
    head_step hs s f ves0 (AI_basic BI_memory_size) hs s f
      (ves0 ++ [:: $VN (VAL_int32 (Wasm_int.int_of_Z i32m (Z.of_N n)))])
| hs_label_const : forall ves0 n es vs, const_list vs ->
    head_step hs s f ves0 (AI_label n es vs) hs s f (ves0 ++ vs)
| hs_label_br : forall ves0 n es vs i (lh : lholed i) LI,
    const_list vs -> length vs = n -> lfill lh (vs ++ [:: AI_basic (BI_br (N.of_nat i))]) = LI ->
    head_step hs s f ves0 (AI_label n es LI) hs s f (ves0 ++ (vs ++ es))
| hs_label_inner : forall ves0 n es LI hs' s' f' LI',
    reduce hs s f LI hs' s' f' LI' ->
    head_step hs s f ves0 (AI_label n es LI) hs' s' f' (ves0 ++ [:: AI_label n es LI'])
| hs_frame_const : forall ves0 n f0 es, const_list es -> length es = n ->
    head_step hs s f ves0 (AI_frame n f0 es) hs s f (ves0 ++ es)
| hs_frame_return : forall ves0 n f0 vs es i (lh : lholed i),
    const_list vs -> length vs = n -> lfill lh (vs ++ [:: AI_basic BI_return]) = es ->
    head_step hs s f ves0 (AI_frame n f0 es) hs s f (ves0 ++ vs)
| hs_frame_inner : forall ves0 n f0 es hs' s' f0' es',
    reduce hs s f0 es hs' s' f0' es' ->
    head_step hs s f ves0 (AI_frame n f0 es) hs' s' f (ves0 ++ [:: AI_frame n f0' es']).

(** Try every constructor (econstructor does not backtrack). *)
Ltac hs_constr :=
  first [
    solve [eapply hs_unop; eauto] |
    solve [eapply hs_binop_success; eauto] |
    solve [eapply hs_binop_failure; eauto] |
    solve [eapply hs_testop_i32; eauto] |
    solve [eapply hs_testop_i64; eauto] |
    solve [eapply hs_relop; eauto] |
    solve [eapply hs_convert_success; eauto] |
    solve [eapply hs_convert_failure; eauto] |
    solve [eapply hs_unreachable; eauto] |
    solve [eapply hs_nop; eauto] |
    solve [eapply hs_drop; eauto] |
    solve [eapply hs_select_false; eauto] |
    solve [eapply hs_select_true; eauto] |
    solve [eapply hs_if_false; eauto] |
    solve [eapply hs_if_true; eauto] |
    solve [eapply hs_br_if_false; eauto] |
    solve [eapply hs_br_if_true; eauto] |
    solve [eapply hs_br_table; eauto] |
    solve [eapply hs_br_table_length; eauto] |
    solve [eapply hs_local_tee; eauto] |
    solve [eapply hs_block; eauto] |
    solve [eapply hs_loop; eauto] |
    solve [eapply hs_call; eauto] |
    solve [eapply hs_invoke_native; eauto] |
    solve [eapply hs_local_get; eauto] |
    solve [eapply hs_local_set; eauto] |
    solve [eapply hs_global_get; eauto] |
    solve [eapply hs_global_set; eauto] |
    solve [eapply hs_load_success; eauto] |
    solve [eapply hs_load_failure; eauto] |
    solve [eapply hs_load_packed_success; eauto] |
    solve [eapply hs_load_packed_failure; eauto] |
    solve [eapply hs_store_success; eauto] |
    solve [eapply hs_store_failure; eauto] |
    solve [eapply hs_store_packed_success; eauto] |
    solve [eapply hs_store_packed_failure; eauto] |
    solve [eapply hs_memory_size; eauto] |
    solve [eapply hs_label_const; eauto] |
    solve [eapply hs_label_br; eauto] |
    solve [eapply hs_label_inner; eauto] |
    solve [eapply hs_frame_const; eauto] |
    solve [eapply hs_frame_return; eauto] |
    solve [eapply hs_frame_inner; eauto] ].

(** Values in front are carried along. *)
Lemma head_step_prefix hs s f ves e hs' s' f' X pre :
  head_step hs s f ves e hs' s' f' X ->
  head_step hs s f (pre ++ ves) e hs' s' f' (pre ++ X).
Proof.
  case => *; rewrite ?catA; first [hs_constr | rewrite -catA; hs_constr].
Qed.

Lemma head_step_nil hs s f ves e hs' s' f' X :
  head_step hs s f ([::] ++ ves) e hs' s' f' ([::] ++ X) -> head_step hs s f ves e hs' s' f' X.
Proof. by []. Qed.

Lemma rcons_split (Y ves : ais) x e : Y ++ [:: x] = ves ++ [:: e] -> Y = ves /\ x = e.
Proof. rewrite !cats1 => /rcons_inj [-> ->]. by []. Qed.

Ltac split_lhs HX :=
  first [ apply rcons_split in HX
        | match type of HX with
          | [:: ?x] = ?R => change ([::] ++ [:: x] = R) in HX
          | [:: ?a; ?x] = ?R => change ([:: a] ++ [:: x] = R) in HX
          | [:: ?a; ?b; ?x] = ?R => change ([:: a; b] ++ [:: x] = R) in HX
          | [:: ?a; ?b; ?c; ?x] = ?R => change ([:: a; b; c] ++ [:: x] = R) in HX
          end; apply rcons_split in HX ].

Ltac base_tac :=
  subst;
  match goal with H : _ = _ ++ [:: _] |- _ => split_lhs H; case: H => ? ?; subst end;
  first [ apply: head_step_nil; hs_constr | by []
        | match goal with H : is_true (ai_ok _) |- _ => move: H; rewrite /= ?andbF; by [] end ].

Lemma cat_nil_inv (A : Type) (l1 l2 : seq A) : l1 ++ l2 = [::] -> l1 = [::] /\ l2 = [::].
Proof. by case: l1. Qed.

Lemma head_step_complete_gen hs s f X hs' s' f' X' :
  reduce hs s f X hs' s' f' X' -> funcs_ok s ->
  forall ves e, const_list ves -> is_const e = false -> ai_ok e -> X = ves ++ [:: e] ->
  head_step hs s f ves e hs' s' f' X'.
Proof.
  elim => {hs s f X hs' s' f' X'}.
  1: { move => X X' s f hs Hs Hf ves e Hves He Hok HX.
       case: Hs HX => //; intros;
         try base_tac.
       (* rs_trap *)
       all: exfalso; subst.
       all: match goal with
            | HX : lfill ?lh _ = _ ++ _ |- _ =>
                move: (lfill0_trap_first lh erefl); rewrite HX first_nc_const_cat // /= He => - [E];
                by subst
            end. }
  all: intros;
    try base_tac.
  (* host functions: excluded by funcs_ok *)
  all: try (subst; match goal with
                   | Hf : is_true (funcs_ok ?s), Hl : lookup_N (s_funcs ?s) _ = Some _ |- _ =>
                       by move: (funcs_ok_lookup Hf Hl)
                   end).
  (* r_return_invoke: the frame body is not in the fragment *)
  all: try (subst; match goal with H : _ = _ ++ [:: _] |- _ => split_lhs H; case: H => ? ? end; subst;
            match goal with
            | H : is_true (ai_ok (AI_frame _ _ (lfill ?lh _))) |- _ =>
                move: (lfill_es_ok (es := _ ++ _) H); by rewrite es_ok_cat /= andbF
            end).
  (* r_label *)
  match goal with
  | Hred : reduce _ _ _ ?es0 _ _ _ ?es0', IH : is_true (funcs_ok _) -> forall _ _, _,
    H1 : lfill ?lh ?es0 = ?les, H2 : lfill ?lh ?es0' = ?les', HX : ?les = _ ++ _,
    Hf : is_true (funcs_ok _), Hves : is_true (const_list _), He : is_const _ = false,
    Hok : is_true (ai_ok _) |- _ =>
      rename Hred into Hr; rename IH into IHr; rename HX into HX0; rename Hf into Hf0;
      rename Hves into Hves0; rename He into He0; rename Hok into Hok0; subst les les'
  end.
  have Hnc : const_list es = false.
  { case Hc: (const_list es) => //. case: (const_irreducible_gen Hr Hc). }
  case: (const_es_exists Hves0) => vv Evv. subst ves.
  move: HX0. case: lh => [vs1 es''|k' vs1 n c lh' es''] /= HX.
  - case: (first_nc_not_const Hnc) => e1 /first_nc_some [He1 [vs2 [r1 Ees0]]]. subst es.
    rewrite -catA /= catA v_to_e_cat in HX.
    case: (v_to_e_split_eq (e1 := e1) (e2 := e) (ltac:(by rewrite He1)) (ltac:(by rewrite He0)) HX)
      => Evs [Ee Er]. subst.
    case: (cat_nil_inv Er) => ? ?. subst.
    have Hh := IHr Hf0 (v_to_e_list vs2) e (v_to_e_const _) He0 Hok0 erefl.
    rewrite cats0 -v_to_e_cat. exact: head_step_prefix.
  - case: (v_to_e_split_eq (e1 := AI_label n c (lfill lh' es)) (e2 := e) (ltac:(by [])) (ltac:(by rewrite He0)) HX)
      => Evs [Ee Er]. subst.
    apply: hs_label_inner. eapply r_label; [exact: Hr | reflexivity | reflexivity].
Qed.

Lemma head_step_complete hs s f ves e hs' s' f' X' :
  funcs_ok s -> const_list ves -> is_const e = false -> ai_ok e ->
  reduce hs s f (ves ++ [:: e]) hs' s' f' X' ->
  head_step hs s f ves e hs' s' f' X'.
Proof. move => Hf Hv He Hok Hr. exact: (head_step_complete_gen Hr Hf Hv He Hok erefl). Qed.

End HeadStep.
