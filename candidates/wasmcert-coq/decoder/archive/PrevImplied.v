(* ARCHIVED 2026-11-12 (improvement pass): no longer built or checked.
   It compared the claim with two superseded statements that were vacuous for
   the real module, so the comparison guarded nothing; the shadow / extra-premise
   checks it was credited with in the re-audit are done by check.sh's CheckTop.v
   (fully qualified, @-explicit type checks against Boundary.v).  Kept only as a
   record; it would need the session-5 Boundary.v to compile. *)
(** * PrevImplied.v: how the current claim relates to the earlier
    versions of Boundary.v.

    Versions:
    - v1 (sha256 65cc3b6a...c6d6): [call_returns] said only that SOME
      reduction sequence reaches the result;
    - prev (sha256 d7d6ac94...c646, session 4): added the unique-outcome
      guarantee; output area 4 * len + 4 bytes, so memories of at least
      327684 bytes -- MORE than the module's fixed 5 pages (327680), which
      made every per-call guarantee of v1 and prev vacuous for the real
      module (audit 2026-11-12);
    - current: output area 2 * len + 2 bytes (memories of at least 196610
      bytes), plus [decoder_module_applies] (the real memory is that large).

    The prev and v1 texts are copied below with their constants renamed
    [out_area_prev] / [mem_bytes_needed_prev] (everything else they use is
    unchanged in Boundary.v).  The current claim implies prev: a smaller
    memory requirement is a weaker hypothesis, and a smaller frame area is
    a stronger promise; the other components are identical.  Because prev
    and v1 are vacuous for the real module, these implications only show
    that no component of the statement was weakened; they say nothing
    about the real module.

    Exports (PROVED):
    - [decoder_module_correct_implies_prev] : decoder_module_correct -> decoder_module_correct_prev;
    - [decoder_module_correct_prev_implies_v1] : decoder_module_correct_prev -> decoder_module_correct_v1;
    - [decoder_module_correct_prev_proved], [decoder_module_correct_v1_proved]. *)

From Stdlib Require Import ZArith NArith List String Lia.
From Stdlib Require Strings.Byte.
From mathcomp Require seq.
From Wasm Require Import datatypes operations opsem instantiation_spec.
From Utf8 Require Import Utf8Laws.
From Decoder Require Import Module Boundary Theorems.
Import ListNotations.

Section Prev.

Context `{ho: host}.

(* ---- prev text (Boundary.v d7d6ac94..., constants renamed _prev) ---- *)

Definition out_area_prev (len : nat) : N := (4 * N.of_nat len + 4)%N.
Definition mem_bytes_needed_prev : N := (OUT_addr + out_area_prev IN_max)%N.

Definition Realizes_prev (hs : host_state) (D : Decoder) : Prop :=
  exists (R : DecodeState D -> Wasm_int.Int32.int -> Prop)
         (s0 : store_record) (inst : moduleinst) (a_start a_dec a_done a_mem : N),
    instantiate empty_store decoder_module [] (s0, Build_frame [] inst, []) /\
    export_named inst "start" (EV_func a_start) /\
    export_named inst "decode" (EV_func a_dec) /\
    export_named inst "done" (EV_func a_done) /\
    export_named inst "memory" (EV_mem a_mem) /\
    forall (s : store_record) (m : meminst),
      s.(s_funcs) = s0.(s_funcs) ->
      nth_error s.(s_mems) (N.to_nat a_mem) = Some m ->
      (mem_bytes_needed_prev <= mem_length m)%N ->
      (* start: returns a representation of the start state, store unchanged *)
      (exists v, R (decode_start_state D) v /\ call_returns hs s a_start [] s [i32v v]) /\
      (* decode: input bytes [bs] at IN_addr; returns the new state and the
         number of output bytes; the output text is at OUT_addr *)
      (forall st v bs,
         R st v ->
         (List.length bs <= IN_max)%nat ->
         mem_holds m IN_addr (byte_values bs) ->
         let '(st', t) := decode_buffer D st bs in
         exists v' m',
           R st' v' /\
           mem_frame m m' OUT_addr (out_area_prev (List.length bs)) /\
           mem_holds m' OUT_addr (utf16le t) /\
           call_returns hs s a_dec [i32v v; i32_of_nat (List.length bs)]
             (store_with_mem s a_mem m') [i32v v'; i32_of_nat (List.length (utf16le t))]) /\
      (* done: the final text is at OUT_addr *)
      (forall st v,
         R st v ->
         let t := decode_done D st in
         exists m',
           mem_frame m m' OUT_addr (out_area_prev 0) /\
           mem_holds m' OUT_addr (utf16le t) /\
           call_returns hs s a_done [i32v v]
             (store_with_mem s a_mem m') [i32_of_nat (List.length (utf16le t))]).

Definition decoder_module_correct_prev : Prop :=
  exists D : Decoder, Decoder_correct D /\ forall hs : host_state, Realizes_prev hs D.

(* ---- end of prev text ---- *)

(* ---- v1 text (verbatim from v1 Boundary.v, names suffixed _v1) ---- *)

(** Calling function address [a] with arguments [args] in store [s]
    (any host state, any caller frame) returns [res] with store [s']. *)
Definition call_returns_v1 hs (s : store_record) (a : N) (args : list value)
           (s' : store_record) (res : list value) : Prop :=
  forall f, reduce_trans (hs, s, f, v_to_e_list args ++ [AI_invoke a])
                         (hs, s', f, v_to_e_list res).

Definition Realizes_v1 (hs : host_state) (D : Decoder) : Prop :=
  exists (R : DecodeState D -> Wasm_int.Int32.int -> Prop)
         (s0 : store_record) (inst : moduleinst) (a_start a_dec a_done a_mem : N),
    instantiate empty_store decoder_module [] (s0, Build_frame [] inst, []) /\
    export_named inst "start" (EV_func a_start) /\
    export_named inst "decode" (EV_func a_dec) /\
    export_named inst "done" (EV_func a_done) /\
    export_named inst "memory" (EV_mem a_mem) /\
    forall (s : store_record) (m : meminst),
      s.(s_funcs) = s0.(s_funcs) ->
      nth_error s.(s_mems) (N.to_nat a_mem) = Some m ->
      (mem_bytes_needed_prev <= mem_length m)%N ->
      (* start: returns a representation of the start state, store unchanged *)
      (exists v, R (decode_start_state D) v /\ call_returns_v1 hs s a_start [] s [i32v v]) /\
      (* decode: input bytes [bs] at IN_addr; returns the new state and the
         number of output bytes; the output text is at OUT_addr *)
      (forall st v bs,
         R st v ->
         (List.length bs <= IN_max)%nat ->
         mem_holds m IN_addr (byte_values bs) ->
         let '(st', t) := decode_buffer D st bs in
         exists v' m',
           R st' v' /\
           mem_frame m m' OUT_addr (out_area_prev (List.length bs)) /\
           mem_holds m' OUT_addr (utf16le t) /\
           call_returns_v1 hs s a_dec [i32v v; i32_of_nat (List.length bs)]
             (store_with_mem s a_mem m') [i32v v'; i32_of_nat (List.length (utf16le t))]) /\
      (* done: the final text is at OUT_addr *)
      (forall st v,
         R st v ->
         let t := decode_done D st in
         exists m',
           mem_frame m m' OUT_addr (out_area_prev 0) /\
           mem_holds m' OUT_addr (utf16le t) /\
           call_returns_v1 hs s a_done [i32v v]
             (store_with_mem s a_mem m') [i32_of_nat (List.length (utf16le t))]).

Definition decoder_module_correct_v1 : Prop :=
  exists D : Decoder, Decoder_correct D /\ forall hs : host_state, Realizes_v1 hs D.

(* ---- end of v1 text ---- *)

Lemma mem_frame_widen m m' p l1 l2 :
  (l1 <= l2)%N -> mem_frame m m' p l1 -> mem_frame m m' p l2.
Proof.
  intros Hl [T [L O]]. split; [exact T|split; [exact L|]].
  intros q Hq. apply O. lia.
Qed.

Lemma out_area_le_prev len : (out_area len <= out_area_prev len)%N.
Proof. unfold out_area, out_area_prev. lia. Qed.

Lemma mem_bytes_needed_le_prev : (mem_bytes_needed <= mem_bytes_needed_prev)%N.
Proof. vm_compute. discriminate. Qed.

Lemma Realizes_implies_prev hs D : Realizes hs D -> Realizes_prev hs D.
Proof.
  intros [R [s0 [inst [a1 [a2 [a3 [a4 [Hi [E1 [E2 [E3 [E4 H]]]]]]]]]]]].
  exists R, s0, inst, a1, a2, a3, a4.
  do 5 (split; [assumption|]).
  intros s m Hf Hm Hl.
  assert (Hl' : (mem_bytes_needed <= mem_length m)%N)
    by (pose proof mem_bytes_needed_le_prev; lia).
  destruct (H s m Hf Hm Hl') as [Hst [Hdec Hdone]].
  split; [exact Hst|split].
  - intros st v' bs HR' Hb Hin. specialize (Hdec st v' bs HR' Hb Hin).
    destruct (decode_buffer D st bs) as [st' t].
    destruct Hdec as [v'' [m' [H1 [H2 [H3 H4]]]]].
    exists v'', m'. split; [exact H1|split; [|split; [exact H3|exact H4]]].
    eapply mem_frame_widen; [apply out_area_le_prev|exact H2].
  - intros st v' HR'. specialize (Hdone st v' HR'). cbv zeta in Hdone |- *.
    destruct Hdone as [m' [H1 [H2 H3]]].
    exists m'. split; [|split; [exact H2|exact H3]].
    eapply mem_frame_widen; [apply out_area_le_prev|exact H1].
Qed.

Theorem decoder_module_correct_implies_prev :
  decoder_module_correct -> decoder_module_correct_prev.
Proof.
  intros [D [HD H]]. exists D. split; [exact HD|]. intro hs. apply Realizes_implies_prev, H.
Qed.

Lemma call_returns_implies_v1 hs s a args s' res :
  call_returns hs s a args s' res -> call_returns_v1 hs s a args s' res.
Proof. intros H f. exact (proj1 (H f)). Qed.

Lemma Realizes_prev_implies_v1 hs D : Realizes_prev hs D -> Realizes_v1 hs D.
Proof.
  intros [R [s0 [inst [a1 [a2 [a3 [a4 [Hi [E1 [E2 [E3 [E4 H]]]]]]]]]]]].
  exists R, s0, inst, a1, a2, a3, a4.
  do 5 (split; [assumption|]).
  intros s m Hf Hm Hl. destruct (H s m Hf Hm Hl) as [[v [HR Hc]] [Hdec Hdone]].
  split; [|split].
  - exists v. split; [exact HR | apply call_returns_implies_v1; exact Hc].
  - intros st v' bs HR' Hb Hin. specialize (Hdec st v' bs HR' Hb Hin).
    destruct (decode_buffer D st bs) as [st' t].
    destruct Hdec as [v'' [m' [H1 [H2 [H3 H4]]]]].
    exists v'', m'. split; [exact H1|split; [exact H2|split; [exact H3|]]].
    apply call_returns_implies_v1; exact H4.
  - intros st v' HR'. specialize (Hdone st v' HR'). cbv zeta in Hdone |- *.
    destruct Hdone as [m' [H1 [H2 H3]]].
    exists m'. split; [exact H1|split; [exact H2|]].
    apply call_returns_implies_v1; exact H3.
Qed.

Theorem decoder_module_correct_prev_implies_v1 :
  decoder_module_correct_prev -> decoder_module_correct_v1.
Proof.
  intros [D [HD H]]. exists D. split; [exact HD|]. intro hs. apply Realizes_prev_implies_v1, H.
Qed.

Theorem decoder_module_correct_prev_proved : decoder_module_correct_prev.
Proof. exact (decoder_module_correct_implies_prev decoder_module_correct_proved). Qed.

Theorem decoder_module_correct_v1_proved : decoder_module_correct_v1.
Proof. exact (decoder_module_correct_prev_implies_v1 decoder_module_correct_prev_proved). Qed.

End Prev.
