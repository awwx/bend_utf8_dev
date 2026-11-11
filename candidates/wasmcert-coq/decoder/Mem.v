(** * Memory lemmas: a 16-bit store, its effect on [mem_lookup], and
    framing.  Reusable; nothing decoder-specific. *)

From Stdlib Require Import ZArith NArith Lia.
From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool eqtype seq.
From compcert Require Import Integers.
From Wasm Require Import operations opsem properties memory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Mem.

Context `{ho: host}.

(** Length is preserved by a block update (derived from the lookup laws). *)
Lemma mem_update_gen_length n len gen (d d' : mem_t) :
  mem_update_gen n len gen d = Some d' -> mem_length d' = mem_length d.
Proof.
  move => H.
  have Hle : N.le (N.add n len) (mem_length d).
  { apply: (mem_update_gen_some_length (gen := gen)). by rewrite H. }
  have Hin : forall i, N.lt i (mem_length d) -> mem_lookup i d' <> None.
  { move => i Hi.
    case: (N.lt_ge_cases i n) => Hn.
    - rewrite (mem_update_gen_lookup_lt H Hn). by apply mem_lookup_ib.
    - case: (N.lt_ge_cases i (N.add n len)) => Hl.
      + have -> : i = N.add n (N.sub i n) by lia.
        rewrite (mem_update_gen_lookup H) //; lia.
      + have Hg : N.ge i (N.add n len) by lia.
        rewrite (mem_update_gen_lookup_ge H Hg). by apply mem_lookup_ib. }
  have Hout : forall i, N.ge i (mem_length d) -> mem_lookup i d' = None.
  { move => i Hi. have Hg : N.ge i (N.add n len) by lia.
    rewrite (mem_update_gen_lookup_ge H Hg). by apply mem_lookup_oob. }
  apply N.le_antisymm.
  - case: (N.le_gt_cases (mem_length d') (mem_length d)) => // Hgt.
    exfalso. have := mem_lookup_ib (mem := d') (i := mem_length d) Hgt.
    by rewrite Hout //; lia.
  - case: (N.le_gt_cases (mem_length d) (mem_length d')) => // Hgt.
    exfalso. have := Hin (mem_length d') Hgt. by rewrite mem_lookup_oob //; lia.
Qed.

Definition lo_byte (v : Z) : byte := Byte.repr v.
Definition hi_byte (v : Z) : byte := Byte.repr (v / 256).

(** A 16-bit store of [v] at address [k + off] in memory [m]. *)
Lemma store16_spec (m : meminst) (k off : N) (v : Wasm_int.Int32.int) :
  N.le (N.add (N.add k off) 2) (operations.mem_length m) ->
  exists m',
    store_packed m k off (serialise_num (VAL_int32 v)) (tp_length Tp_i16) = Some m' /\
    m'.(meminst_type) = m.(meminst_type) /\
    operations.mem_length m' = operations.mem_length m /\
    mem_lookup (N.add k off) m'.(meminst_data) = Some (lo_byte (Wasm_int.Int32.unsigned v)) /\
    mem_lookup (N.add (N.add k off) 1) m'.(meminst_data) = Some (hi_byte (Wasm_int.Int32.unsigned v)) /\
    (forall q, (N.lt q (N.add k off) \/ N.le (N.add (N.add k off) 2) q) ->
       mem_lookup q m'.(meminst_data) = mem_lookup q m.(meminst_data)).
Proof.
  move => Hle.
  rewrite /store_packed /store.
  have -> : (k + off + N.of_nat (N.to_nat (tp_length Tp_i16)) <=? operations.mem_length m)%num = true.
  { apply N.leb_le. rewrite /=. lia. }
  rewrite /write_bytes_meminst /write_bytes /write_bytes_gen /serialise_num /serialise_i32.
  rewrite /bytes_takefill /common.Memdata.encode_int /common.Memdata.rev_if_be.
  Local Transparent Archi.big_endian.
  rewrite /Archi.big_endian /=.
  set gen := (fun n0 : N => _).
  case E: (mem_update_gen (k + off) 2 gen (meminst_data m)) => [d'|].
  - exists (Build_meminst (meminst_type m) d'); split => //=.
    split => //. split; first by rewrite /operations.mem_length /= (mem_update_gen_length E).
    split; [|split].
    + have := mem_update_gen_lookup (i := 0%num) E. rewrite N.add_0_r => -> //; lia.
    + have := mem_update_gen_lookup (i := 1%num) E. move => -> //; lia.
    + move => q [Hq|Hq].
      * by rewrite (mem_update_gen_lookup_lt E Hq).
      * have Hg : N.ge q (N.add (N.add k off) 2) by lia. by rewrite (mem_update_gen_lookup_ge E Hg).
  - exfalso. apply: (mem_update_gen_ib (n := (k + off)%num) (len := 2%num) (gen := gen) (m := meminst_data m)); last by rewrite E.
    rewrite /operations.mem_length in Hle. exact Hle.
Qed.

End Mem.
