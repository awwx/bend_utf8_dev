(** * A small reusable symbolic-execution layer over WasmCert-Coq's [reduce].

    Everything here is proved from the small-step relation [reduce] of
    [Wasm.opsem]; nothing is assumed.  The layer has three levels:

    - [steps]: [reduce_trans] at a fixed host state, plus lifting lemmas
      through value/instruction contexts, labels and frames.
    - [exec s f stk bes s' f' stk']: running the basic instructions [bes]
      from operand stack [stk] completes normally with stack [stk'].
      Stacks are written TOP FIRST, so instruction rules unify on [::].
    - [exec_br ... k]: running [bes] ends at a [br k] (any operands
      below it, any instructions after it are discarded by the branch).

    Structured control is handled by rules for the specific shapes used
    ([block (loop body)] with empty block types, and function invocation).
*)

From Stdlib Require Import ZArith NArith Relations.
From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool eqtype seq.
From Wasm Require Import operations opsem properties.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Steps.

Context `{ho: host}.

Variable hs : host_state.

Definition steps s f es s' f' es' : Prop :=
  reduce_trans (hs, s, f, es) (hs, s', f', es').

Lemma steps_refl s f es : steps s f es s f es.
Proof. by apply rt_refl. Qed.

Lemma steps_trans s f es s1 f1 es1 s2 f2 es2 :
  steps s f es s1 f1 es1 -> steps s1 f1 es1 s2 f2 es2 -> steps s f es s2 f2 es2.
Proof. by apply rt_trans. Qed.

Lemma steps_one s f es s' f' es' :
  reduce hs s f es hs s' f' es' -> steps s f es s' f' es'.
Proof. by move => H; apply rt_step. Qed.

Lemma steps_simple s f es es' : reduce_simple es es' -> steps s f es s f es'.
Proof. by move => H; apply steps_one; apply r_simple. Qed.

(** Generic: a map that preserves single steps preserves [reduce_trans]. *)
Lemma rt_map {A} (R : A -> A -> Prop) (g : A -> A) :
  (forall x y, R x y -> R (g x) (g y)) ->
  forall x y, clos_refl_trans _ R x y -> clos_refl_trans _ R (g x) (g y).
Proof.
  move => Hg x y H; induction H; [by apply rt_step, Hg | by apply rt_refl |].
  by eapply rt_trans; eauto.
Qed.

Definition ctx_cfg (vs : seq value) (rest : seq administrative_instruction)
  (c : host_state * store_record * frame * seq administrative_instruction) :=
  let '(h, s, f, es) := c in (h, s, f, v_to_e_list vs ++ es ++ rest).

Lemma steps_ctx vs rest s f es s' f' es' :
  steps s f es s' f' es' ->
  steps s f (v_to_e_list vs ++ es ++ rest) s' f' (v_to_e_list vs ++ es' ++ rest).
Proof.
  move => H.
  apply (rt_map (g := ctx_cfg vs rest)) in H; first by [].
  move => [[[h1 s1] f1] e1] [[[h2 s2] f2] e2] /= Hr.
  by eapply r_label with (lh := LH_base vs rest); eauto.
Qed.

Lemma steps_suffix rest s f es s' f' es' :
  steps s f es s' f' es' -> steps s f (es ++ rest) s' f' (es' ++ rest).
Proof. by move => H; apply (steps_ctx [::] rest) in H. Qed.

Definition label_cfg n (cont : seq administrative_instruction)
  (c : host_state * store_record * frame * seq administrative_instruction) :=
  let '(h, s, f, es) := c in (h, s, f, [:: AI_label n cont es]).

Lemma steps_label n cont s f es s' f' es' :
  steps s f es s' f' es' ->
  steps s f [:: AI_label n cont es] s' f' [:: AI_label n cont es'].
Proof.
  move => H.
  apply (rt_map (g := label_cfg n cont)) in H; first by [].
  move => [[[h1 s1] f1] e1] [[[h2 s2] f2] e2] /= Hr.
  eapply r_label with (lh := LH_rec [::] n cont (LH_base [::] [::]) [::]); eauto => /=;
    by rewrite cats0.
Qed.

Definition frame_cfg n (f0 : frame)
  (c : host_state * store_record * frame * seq administrative_instruction) :=
  let '(h, s, f, es) := c in (h, s, f0, [:: AI_frame n f es]).

Lemma steps_frame n f0 s f es s' f' es' :
  steps s f es s' f' es' ->
  steps s f0 [:: AI_frame n f es] s' f0 [:: AI_frame n f' es'].
Proof.
  move => H.
  apply (rt_map (g := frame_cfg n f0)) in H; first by [].
  move => [[[h1 s1] f1] e1] [[[h2 s2] f2] e2] /= Hr.
  by apply r_frame.
Qed.

(** ** Normal completion of basic instruction sequences *)

Definition exec s f (stk : seq value) (bes : seq basic_instruction) s' f' (stk' : seq value) :=
  steps s f (v_to_e_list (rev stk) ++ to_e_list bes) s' f' (v_to_e_list (rev stk')).

Lemma exec_nil s f stk : exec s f stk [::] s f stk.
Proof. by rewrite /exec /= cats0; apply steps_refl. Qed.

(** Used to finish a symbolic run: the computed stack equals the claimed one. *)
Lemma exec_nil_eq s f stk stk' : stk = stk' -> exec s f stk [::] s f stk'.
Proof. by move => ->; apply exec_nil. Qed.

Lemma exec_app s f stk b1 s1 f1 stk1 b2 s2 f2 stk2 :
  exec s f stk b1 s1 f1 stk1 -> exec s1 f1 stk1 b2 s2 f2 stk2 ->
  exec s f stk (b1 ++ b2) s2 f2 stk2.
Proof.
  rewrite /exec to_e_list_cat catA => H1 H2.
  eapply steps_trans; last by apply H2.
  by apply steps_suffix.
Qed.

Lemma exec_cons s f stk b s1 f1 stk1 bes s2 f2 stk2 :
  exec s f stk [:: b] s1 f1 stk1 -> exec s1 f1 stk1 bes s2 f2 stk2 ->
  exec s f stk (b :: bes) s2 f2 stk2.
Proof. by move => H1 H2; apply (exec_app H1 H2). Qed.

(** Lifting a rule about the top [args] (top first) of the stack. *)
Lemma exec_top s f s' f' args res stk b :
  steps s f (v_to_e_list (rev args) ++ [:: AI_basic b]) s' f' (v_to_e_list (rev res)) ->
  exec s f (args ++ stk) [:: b] s' f' (res ++ stk).
Proof.
  move => H; move: (steps_ctx (rev stk) [::] H).
  by rewrite /exec !rev_cat /v_to_e_list !map_cat -!catA !cats0.
Qed.

Lemma exec_const s f stk c :
  exec s f stk [:: BI_const_num c] s f (VAL_num c :: stk).
Proof.
  rewrite /exec rev_cons -cats1 /v_to_e_list map_cat /=; apply steps_refl.
Qed.

Lemma exec_local_get s f stk j v :
  lookup_N f.(f_locs) j = Some v ->
  exec s f stk [:: BI_local_get j] s f (v :: stk).
Proof.
  move => H; apply (exec_top (args := [::]) (res := [:: v])).
  by apply steps_one; apply r_local_get.
Qed.

Lemma exec_local_set s f stk i v :
  N.to_nat i < length f.(f_locs) ->
  exec s f (v :: stk) [:: BI_local_set i] s
    (Build_frame (set_nth v f.(f_locs) (N.to_nat i) v) f.(f_inst)) stk.
Proof.
  move => H; apply (exec_top (args := [:: v]) (res := [::])).
  by apply steps_one; eapply r_local_set; eauto.
Qed.

Lemma exec_binop s f stk t op v1 v2 v :
  binop_typecheck v1 v2 t op ->
  app_binop op v1 v2 = Some v ->
  exec s f (VAL_num v2 :: VAL_num v1 :: stk) [:: BI_binop t op] s f (VAL_num v :: stk).
Proof.
  move => Ht Hv; apply (exec_top (args := [:: VAL_num v2; VAL_num v1]) (res := [:: VAL_num v])).
  by apply steps_simple; apply rs_binop_success.
Qed.

Lemma exec_relop s f stk t op v1 v2 :
  relop_typecheck v1 v2 t op ->
  exec s f (VAL_num v2 :: VAL_num v1 :: stk) [:: BI_relop t op] s f
    (VAL_num (VAL_int32 (wasm_bool (app_relop op v1 v2))) :: stk).
Proof.
  move => Ht; apply (exec_top (args := [:: VAL_num v2; VAL_num v1])
                      (res := [:: VAL_num (VAL_int32 (wasm_bool (app_relop op v1 v2)))])).
  by apply steps_simple; apply rs_relop.
Qed.

Lemma exec_testop_i32 s f stk c op :
  exec s f (VAL_num (VAL_int32 c) :: stk) [:: BI_testop T_i32 op] s f
    (VAL_num (VAL_int32 (wasm_bool (app_testop_i i32m op c))) :: stk).
Proof.
  apply (exec_top (args := [:: VAL_num (VAL_int32 c)])
           (res := [:: VAL_num (VAL_int32 (wasm_bool (app_testop_i i32m op c)))])).
  by apply steps_simple; apply rs_testop_i32.
Qed.

Lemma exec_load_packed s f stk t tp sx marg k m bs :
  smem s f.(f_inst) = Some m ->
  load_packed sx m (Wasm_int.N_of_uint i32m k) marg.(memarg_offset) (tp_length tp) (tnum_length t) = Some bs ->
  exec s f (VAL_num (VAL_int32 k) :: stk) [:: BI_load t (Some (tp, sx)) marg] s f
    (VAL_num (wasm_deserialise bs t) :: stk).
Proof.
  move => Hm Hl; apply (exec_top (args := [:: VAL_num (VAL_int32 k)])
                         (res := [:: VAL_num (wasm_deserialise bs t)])).
  by apply steps_one; eapply r_load_packed_success; eauto.
Qed.

(** Not used by the spike; included to check that memory writes fit the
    same pattern (the real decoder writes its output). *)
Lemma exec_store_packed s f stk t tp marg k v s' :
  smem_store_packed s f.(f_inst) (Wasm_int.N_of_uint i32m k) marg.(memarg_offset) v tp = Some s' ->
  typeof_num v = t ->
  exec s f (VAL_num v :: VAL_num (VAL_int32 k) :: stk) [:: BI_store t (Some tp) marg] s' f stk.
Proof.
  move => Hs Ht; apply (exec_top (args := [:: VAL_num v; VAL_num (VAL_int32 k)]) (res := [::])).
  by apply steps_one; eapply r_store_packed_success; eauto.
Qed.

Lemma exec_br_if_false s f stk i :
  exec s f (VAL_num (VAL_int32 (Wasm_int.int_zero i32m)) :: stk) [:: BI_br_if i] s f stk.
Proof.
  apply (exec_top (args := [:: VAL_num (VAL_int32 (Wasm_int.int_zero i32m))]) (res := [::])).
  by apply steps_simple; apply rs_br_if_false.
Qed.

(** ** Ending at a branch *)

Definition exec_br s f (stk : seq value) (bes : seq basic_instruction) s' f' (k : N) :=
  exists below rest,
    steps s f (v_to_e_list (rev stk) ++ to_e_list bes) s' f'
      (v_to_e_list below ++ [:: AI_basic (BI_br k)] ++ rest).

Lemma exec_br_br s f stk k : exec_br s f stk [:: BI_br k] s f k.
Proof. by exists (rev stk), [::]; apply steps_refl. Qed.

Lemma exec_br_if_true s f stk c k :
  c <> Wasm_int.int_zero i32m ->
  exec_br s f (VAL_num (VAL_int32 c) :: stk) [:: BI_br_if k] s f k.
Proof.
  move => Hc; exists (rev stk), [::].
  have H := steps_ctx (rev stk) [::] (steps_simple s f (rs_br_if_true k Hc)).
  by move: H; rewrite /= rev_cons -cats1 /v_to_e_list map_cat -catA ?cats0.
Qed.

Lemma exec_then_br s f stk b1 s1 f1 stk1 b2 s2 f2 k :
  exec s f stk b1 s1 f1 stk1 -> exec_br s1 f1 stk1 b2 s2 f2 k ->
  exec_br s f stk (b1 ++ b2) s2 f2 k.
Proof.
  move => H1 [below [rest H2]]; exists below, rest.
  rewrite to_e_list_cat catA.
  eapply steps_trans; last by apply H2.
  by apply steps_suffix.
Qed.

Lemma exec_br_prefix s f stk b1 b2 s' f' k :
  exec_br s f stk b1 s' f' k -> exec_br s f stk (b1 ++ b2) s' f' k.
Proof.
  move => [below [rest H]]; exists below, (rest ++ to_e_list b2).
  rewrite to_e_list_cat catA.
  move: (steps_suffix (to_e_list b2) H).
  by rewrite -!catA.
Qed.

(** ** [block (loop body)] with empty block types

    [P n s f] is a loop invariant indexed by a decreasing measure [n].
    Each iteration of [body] (from an empty operand stack) must either
    branch back to the loop ([br 0]) re-establishing the invariant at a
    smaller measure, or leave the block ([br 1]) establishing [Q]. *)

Definition BT_none : block_type := BT_valtype None.

Lemma block_loop_rule body (P : nat -> store_record -> frame -> Prop)
      (Q : store_record -> frame -> Prop) :
  (forall n s f, P n s f ->
     (exists n' s' f', (n' < n)%coq_nat /\ exec_br s f [::] body s' f' (0 : N) /\ P n' s' f') \/
     (exists s' f', exec_br s f [::] body s' f' (1 : N) /\ Q s' f')) ->
  forall n s f stk, P n s f ->
  exists s' f', exec s f stk [:: BI_block BT_none [:: BI_loop BT_none body]] s' f' stk /\ Q s' f'.
Proof.
  move => Hbody.
  (* the label configuration [label0 [] [loop body]] runs to [::] *)
  have Hinner : forall n s f, P n s f -> exists s' f',
      steps s f [:: AI_label 0 [::] [:: AI_basic (BI_loop BT_none body)]] s' f' [::] /\ Q s' f'.
  { elim/(well_founded_induction lt_wf) => n IH s f HP.
    have Hloop : steps s f [:: AI_basic (BI_loop BT_none body)] s f
                   [:: AI_label 0 [:: AI_basic (BI_loop BT_none body)] (to_e_list body)].
    { apply steps_one.
      by eapply r_loop with (vs := [::]) (t1s := [::]) (t2s := [::]). }
    case: (Hbody n s f HP) => [[n' [s' [f' [Hlt [[below [rest Hrun]] HP']]]]] |
                               [s' [f' [[below [rest Hrun]] HQ]]]].
    - (* continue: br 0 restarts the loop *)
      case: (IH n' Hlt s' f' HP') => [s'' [f'' [Hrest HQ]]].
      exists s'', f''; split => //.
      eapply steps_trans; first by apply steps_label, Hloop.
      eapply steps_trans; first by apply steps_label, steps_label, Hrun.
      eapply steps_trans; last by apply Hrest.
      apply steps_label, steps_simple.
      by eapply rs_br with (vs := [::]) (lh := LH_base below rest).
    - (* exit: br 1 leaves the enclosing block *)
      exists s', f'; split => //.
      eapply steps_trans; first by apply steps_label, Hloop.
      eapply steps_trans; first by apply steps_label, steps_label, Hrun.
      apply steps_simple.
      by eapply rs_br with (vs := [::]) (es := [::])
                  (lh := LH_rec [::] 0 [:: AI_basic (BI_loop BT_none body)] (LH_base below rest) [::]).
  }
  move => n s f stk HP.
  case: (Hinner n s f HP) => [s' [f' [Hrun HQ]]].
  exists s', f'; split => //.
  have Hblk : steps s f [:: AI_basic (BI_block BT_none [:: BI_loop BT_none body])] s f
                 [:: AI_label 0 [::] [:: AI_basic (BI_loop BT_none body)]].
  { apply steps_one.
    by eapply r_block with (vs := [::]) (t1s := [::]) (t2s := [::]). }
  move: (steps_trans Hblk Hrun) => H.
  move: (steps_ctx (rev stk) [::] H).
  by rewrite /exec /= !cats0.
Qed.

(** ** Invoking a native function *)

Lemma invoke_rule s f0 a ts1 ts2 inst x ts body args defs s' f' res :
  lookup_N s.(s_funcs) a = Some (FC_func_native (Tf ts1 ts2) inst (Build_module_func x ts body)) ->
  length args = length ts1 ->
  length res = length ts2 ->
  default_vals ts = Some defs ->
  exec s (Build_frame (args ++ defs) inst) [::] body s' f' (rev res) ->
  steps s f0 (v_to_e_list args ++ [:: AI_invoke a]) s' f0 (v_to_e_list res).
Proof.
  move => Hcl Hargs Hres Hdef Hbody.
  eapply steps_trans.
  { apply steps_one. eapply r_invoke_native; eauto. }
  eapply steps_trans.
  { apply steps_frame, steps_label. rewrite /exec /= revK in Hbody. by apply Hbody. }
  eapply steps_trans.
  { apply steps_frame, steps_simple, rs_label_const. by apply v_to_e_const. }
  apply steps_simple, rs_local_const; first by apply v_to_e_const.
  by rewrite /v_to_e_list length_is_size size_map -length_is_size.
Qed.

End Steps.
