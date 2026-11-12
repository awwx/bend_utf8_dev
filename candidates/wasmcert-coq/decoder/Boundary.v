(** * Boundary.v: what is claimed about the Wasm module [decoder_module].

    Read together with Utf8Laws.v (the decoder spec) and Module.v (the
    module term, of which decoder.wasm is the printed binary).  This file
    contains definitions and statements only; the proofs are elsewhere.

    There are two claims, both at the end:
    - [decoder_module_correct]: there is a [Decoder] (in the sense of
      Utf8Laws.v) that satisfies the three streaming laws and that the
      module's exports implement, through the data representation and
      memory layout defined below;
    - [decoder_module_applies]: those guarantees are not vacuous: the
      store made by instantiating the module meets their store condition
      (its memory is large enough for the layout), the largest call
      (64 KiB of input) fits, and instantiation has exactly one possible
      result, so that store is the one the guarantees speak about.

    Semantics: WasmCert-Coq 2.2.1, the mechanised Wasm 2.0 semantics.
    [instantiate] is its relational instantiation predicate and
    [reduce_trans] the reflexive-transitive closure of its small-step
    relation [reduce].

    Each call statement ([call_returns]) says that the call reaches the
    stated result and that this result is its only possible outcome: no
    trap or other result is reachable, and execution cannot run forever. *)

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

(** The layout, in plain words:
    - input: at most 64 KiB ([IN_max] = 65536 bytes) per call, at address
      0 ([IN_addr]);
    - output: at most 2 bytes per input byte, plus 2, at address 64 KiB
      ([OUT_addr] = 65536).  A call with [len] input bytes may overwrite
      [OUT_addr, OUT_addr + out_area len) and nothing else.  (Over a
      call, the output has at most one UTF-16 code unit, 2 bytes, per input
      byte, plus one unit for bytes left pending by an earlier call: a
      U+FFFD, or the second half of a surrogate pair.  OutBound.v proves
      this of the decoder; the proof of the main claim shows the module
      writes nothing else.)  [done] has [len] = 0, so it may write 2 bytes;
    - memory: the module's memory is fixed at 5 pages (327680 bytes) and
      cannot grow.  The guarantees below are stated for memories of at
      least [mem_bytes_needed] = 65536 + 2 * 65536 + 2 = 196610 bytes;
      the last section of this file states that the module's real memory
      is that large, so the largest call fits. *)
Definition IN_addr : N := Z.to_N IN.
Definition OUT_addr : N := Z.to_N OUT.
Definition IN_max : nat := Z.to_nat IN_MAX.
Definition out_area (len : nat) : N := (2 * N.of_nat len + 2)%N.
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
    (any host state, any caller frame) returns [res] with store [s'],
    and that is the only possible outcome.  With [c] the call
    configuration and [d] the result configuration:
    - [c] reduces to [d] (in finitely many steps);
    - every configuration reachable from [c] can still reach [d], so no
      trap and no other result is reachable;
    - there is no infinite reduction sequence starting at [c], so
      execution cannot run forever.
    It follows from the second point that the only place execution can
    stop (a reachable configuration that cannot reduce) is [d]. *)
Definition call_returns hs (s : store_record) (a : N) (args : list value)
           (s' : store_record) (res : list value) : Prop :=
  forall f,
    let c := (hs, s, f, v_to_e_list args ++ [AI_invoke a]) in
    let d := (hs, s', f, v_to_e_list res) in
    reduce_trans c d /\
    (forall c', reduce_trans c c' -> reduce_trans c' d) /\
    (forall run : nat -> host_state * store_record * frame * list administrative_instruction,
       run 0 = c -> ~ (forall n, reduce_tuple (run n) (run (S n)))).

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

(** ** The guarantees apply to the real module

    [Realizes] promises something only for stores whose memory has at
    least [mem_bytes_needed] bytes.  This section states that the store
    made by instantiating the module meets that condition, that the
    largest call the wrapper makes (64 KiB of input) fits the layout, and
    that instantiation has only one possible result.
    (Without this, a too-large layout would make every guarantee above
    hold vacuously; an earlier version of this file had that defect.) *)

(** The layout fits: the input area [IN_addr, IN_addr + IN_max) ends
    where the output area begins, so a full-size input never overlaps the
    output; and the input and output areas of the largest call end within
    the module's 5 pages. *)
Definition layout_fits : Prop :=
  (IN_addr + N.of_nat IN_max <= OUT_addr)%N /\
  (mem_bytes_needed <= 5 * 65536)%N.

(** Instantiating the module in the empty store succeeds, and EVERY
    possible result (so also the one [Realizes] speaks about) has an
    exported memory of exactly 5 pages, fixed (minimum = maximum = 5), and
    at least [mem_bytes_needed] bytes long: the result store itself meets
    the store conditions of [Realizes].
    ([hs] is not used: WasmCert's instantiation predicate mentions some
    host state, so instantiation can succeed only if one exists; the main
    claim likewise speaks of every host state [hs].) *)
Definition instance_memory_fits : Prop :=
  (forall hs : host_state,   (* see below *)
   exists (s0 : store_record) (inst : moduleinst),
     instantiate empty_store decoder_module [] (s0, Build_frame [] inst, [])) /\
  forall (s0 : store_record) (inst : moduleinst) (a_mem : N),
    instantiate empty_store decoder_module [] (s0, Build_frame [] inst, []) ->
    export_named inst "memory" (EV_mem a_mem) ->
    exists m : meminst,
      nth_error s0.(s_mems) (N.to_nat a_mem) = Some m /\
      m.(meminst_type) = {| lim_min := 5%N; lim_max := Some 5%N |} /\
      mem_length m = (5 * 65536)%N /\
      (mem_bytes_needed <= mem_length m)%N.

(** Instantiating the module has exactly one possible result, so the
    memory this claim talks about is the memory the guarantees are about.
    ([instantiate] is a relation, so in principle it could relate the
    module to several result stores; [Realizes] picks one of them.  Any
    two results are equal: the store, the instance's frame, and the
    initialisation code, which is empty for this module, are all the
    same.) *)
Definition instantiation_unique : Prop :=
  forall z1 z2 : store_record * frame * list basic_instruction,
    instantiate empty_store decoder_module [] z1 ->
    instantiate empty_store decoder_module [] z2 ->
    z1 = z2.

(** The second top-level claim: the guarantees of [decoder_module_correct]
    are not vacuous for the real module. *)
Definition decoder_module_applies : Prop :=
  layout_fits /\ instance_memory_fits /\ instantiation_unique.

End Boundary.
