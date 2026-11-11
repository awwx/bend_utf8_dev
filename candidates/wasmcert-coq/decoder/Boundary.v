(** * Boundary.v: what is claimed about the Wasm module [decoder_module].

    Read together with Utf8Laws.v (the decoder spec) and Module.v (the
    module term, of which decoder.wasm is the printed binary).  This file
    contains definitions and statements only; the proofs are elsewhere.

    The claim, [decoder_module_correct] at the end, is: there is a
    [Decoder] (in the sense of Utf8Laws.v) that satisfies the three
    streaming laws and that the module's exports implement, through the
    data representation defined below.

    Semantics: WasmCert-Coq 2.2.1, the mechanised Wasm 2.0 semantics.
    [instantiate] is its relational instantiation predicate and
    [reduce_trans] the reflexive-transitive closure of its small-step
    relation [reduce].

    CAVEAT (no determinism): "the call reduces to configuration C" means
    that SOME finite reduction sequence ends in C (a list of constants,
    which cannot reduce further).  WasmCert-Coq 2.2.1 has no determinism
    theorem, so this does not by itself exclude other reduction paths
    (e.g. one that traps).  See REPORT.txt. *)

From Stdlib Require Import ZArith NArith List String.
From Stdlib Require Strings.Byte.
From mathcomp Require seq.
From Wasm Require Import datatypes operations opsem instantiation_spec.
From Utf8 Require Import Utf8Laws.
From Decoder Require Import Module.
Import ListNotations.

Section Boundary.

Context `{ho: host}.

(** ** How spec values appear in Wasm *)

(** A spec byte (stdlib [Byte.byte]) is stored as the Wasm memory byte
    (CompCert [Integers.byte]) with the same value 0..255. *)
Definition byte_as_mem (b : Byte.byte) (wb : bytes.byte) : Prop :=
  Integers.Byte.unsigned wb = Z.of_N (Byte.to_N b).

(** [mem_holds m p ns]: memory [m] holds the byte values [ns] (each
    0..255) at addresses [p], [p+1], ... *)
Definition mem_holds (m : meminst) (p : N) (ns : list N) : Prop :=
  forall i n, nth_error ns i = Some n ->
    exists wb, mem_lookup (p + N.of_nat i)%N m.(meminst_data) = Some wb /\
               Integers.Byte.unsigned wb = Z.of_N n.

(** The input bytes, as values. *)
Definition byte_values (bs : list Byte.byte) : list N := map Byte.to_N bs.

(** Text is passed out as UTF-16 code units: a code point below 0x10000
    is one unit; any other is a surrogate pair.  (Every code point in a
    decoder's output is a Unicode scalar value or U+FFFD, by the spec's
    [decodes], so this is the standard UTF-16 encoding.) *)
Definition utf16_units (cp : U32) : list N :=
  let n := U32_to_N cp in
  if (n <? 0x10000)%N then [n]
  else [(0xD800 + (n - 0x10000) / 0x400)%N; (0xDC00 + (n - 0x10000) mod 0x400)%N].

(** Code units are stored little-endian, two bytes each. *)
Definition utf16le (t : Text) : list N :=
  flat_map (fun u => [(u mod 256)%N; (u / 256)%N]) (flat_map utf16_units t).

(** ** Memory layout and the exports *)

(** Input at [IN_addr], at most [IN_MAX] bytes per call; output at
    [OUT_addr].  A call may overwrite [OUT_addr, OUT_addr + out_area len)
    and nothing else. *)
Definition IN_addr : N := Z.to_N IN.
Definition OUT_addr : N := Z.to_N OUT.
Definition IN_max : nat := Z.to_nat IN_MAX.
Definition out_area (len : nat) : N := (4 * N.of_nat len + 4)%N.
Definition mem_bytes_needed : N := (OUT_addr + out_area IN_max)%N.

Definition i32_of_nat (n : nat) : value :=
  VAL_num (VAL_int32 (Wasm_int.Int32.repr (Z.of_nat n))).
Definition i32v (v : Wasm_int.Int32.int) : value := VAL_num (VAL_int32 v).

Definition empty_store : store_record := Build_store_record nil nil nil nil nil nil.

Definition export_named (inst : moduleinst) (nm : string) (v : extern_value) : Prop :=
  In {| exportinst_name := String.list_byte_of_string nm; exportinst_val := v |}
     inst.(inst_exports).

(** [s'] is [s] with memory [a] replaced by [m']. *)
Definition store_with_mem (s : store_record) (a : N) (m' : meminst) : store_record :=
  upd_s_mem s (seq.set_nth m' s.(s_mems) (N.to_nat a) m').

(** [m'] is [m] changed at most in [p, p + len). *)
Definition mem_frame (m m' : meminst) (p len : N) : Prop :=
  m'.(meminst_type) = m.(meminst_type) /\
  mem_length m' = mem_length m /\
  forall q, (q < p \/ p + len <= q)%N ->
    mem_lookup q m'.(meminst_data) = mem_lookup q m.(meminst_data).

(** Calling function address [a] with arguments [args] in store [s]
    (any host state, any caller frame) returns [res] with store [s']. *)
Definition call_returns hs (s : store_record) (a : N) (args : list value)
           (s' : store_record) (res : list value) : Prop :=
  forall f, reduce_trans (hs, s, f, v_to_e_list args ++ [AI_invoke a])
                         (hs, s', f, v_to_e_list res).

(** ** The module realizes a decoder *)

(** [R] relates decoder states to the i32 values that represent them.
    [hs] is the host state of the configurations considered.
    The stores considered are all stores with the function list made by
    instantiation and with the module's memory (any contents) of at
    least [mem_bytes_needed] bytes; each call below returns such a store
    again, so the statements apply to every sequence of calls, with any
    host writes to the input area in between. *)
Definition Realizes (hs : host_state) (D : Decoder) : Prop :=
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
      (mem_bytes_needed <= mem_length m)%N ->
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
           mem_frame m m' OUT_addr (out_area (List.length bs)) /\
           mem_holds m' OUT_addr (utf16le t) /\
           call_returns hs s a_dec [i32v v; i32_of_nat (List.length bs)]
             (store_with_mem s a_mem m') [i32v v'; i32_of_nat (List.length (utf16le t))]) /\
      (* done: the final text is at OUT_addr *)
      (forall st v,
         R st v ->
         let t := decode_done D st in
         exists m',
           mem_frame m m' OUT_addr (out_area 0) /\
           mem_holds m' OUT_addr (utf16le t) /\
           call_returns hs s a_done [i32v v]
             (store_with_mem s a_mem m') [i32_of_nat (List.length (utf16le t))]).

(** ** The top-level claim *)

(** For every host state [hs] (the host part of a Wasm configuration;
    the decoder never calls the host). *)
Definition decoder_module_correct : Prop :=
  exists D : Decoder, Decoder_correct D /\ forall hs : host_state, Realizes hs D.

End Boundary.
