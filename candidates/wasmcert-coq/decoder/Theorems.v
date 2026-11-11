(** * The top-level statement of Boundary.v, proved CONDITIONALLY on the
    per-byte lemma [step_spec] (Decode.v), with RefDecoder as witness. *)

From Stdlib Require Import ZArith NArith List Lia.
From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool eqtype seq.
From Wasm Require Import datatypes operations opsem properties.
From Utf8 Require Import Utf8Laws Utf8Ref Utf8Proofs.
From Decoder Require Import Module Steps Wp WpMem Instance Boundary Repr Exports Decode.

Section Top.

Context `{ho: host}.

Theorem decoder_module_correct_if_step :
  (forall hs, step_spec hs) -> decoder_module_correct.
Proof.
  move => Hstep.
  exists RefDecoder; split; first by apply RefDecoder_correct.
  move => hs.
  exists Rst, s0, inst0, 0%num, 1%num, 2%num, 0%num.
  split; first by apply: (instantiate_decoder hs).
  split; first by rewrite /export_named /=; left.
  split; first by rewrite /export_named /=; right; left.
  split; first by rewrite /export_named /=; right; right; left.
  split; first by rewrite /export_named /=; right; right; right; left.
  move => s m Hf Hm Hlen.
  split; [|split].
  - case: (start_correct hs Hf) => HR Hc. by exists (Wasm_int.Int32.repr 0).
  - move => st v bs [HI ->] Hbs Hin.
    case: (decode_correct (Hstep hs) Hf Hm Hlen HI Hbs Hin) => st' [t [m' [Hdec [HI' [Hfr [Hho Hc]]]]]].
    rewrite /= Hdec.
    exists (Wasm_int.Int32.repr (enc st')), m'.
    by do 3 (split; first by []).
  - move => st v HR.
    case: (done_correct hs Hf Hm Hlen HR) => m' H. by exists m'.
Qed.

End Top.
