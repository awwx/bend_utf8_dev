(** * NonVacuity.v: proof of [decoder_module_applies] (Boundary.v): the
    store made by instantiation has a fixed 5-page exported memory, which
    is at least [mem_bytes_needed] bytes; and the layout fits.

    Exports: [decoder_module_applies_proved : decoder_module_applies]
    (with [layout_fits_proved], [instance_memory_fits_proved],
    [instantiation_unique_proved], and [instantiate_decoder_result]: every
    instantiation result is the computed [(s0, Build_frame [] inst0, [])]
    of Instance.v).

    The universal half inspects the relational [instantiate] directly: its
    [alloc_module] conjunct fixes the result store's memory list (the
    module has no imports, so only the module's own memory is allocated)
    and the instance's export list. *)

From Stdlib Require Import ZArith NArith List String Lia.
From Wasm Require Import datatypes operations opsem memory instantiation_spec.
From mathcomp Require Import ssreflect.
From Decoder Require Import Module Instance Boundary.
Import ListNotations.

Section NonVacuity.

Context `{ho: host}.

Lemma layout_fits_proved : layout_fits.
Proof. split; vm_compute; discriminate. Qed.

(** Every result of [instantiate] is [(s0, Build_frame [] inst0, [])]:
    [alloc_module] fixes the store and the instance, and the frame and
    initialisation code are given by [instantiate] itself (the module has
    no elements, data segments or start function). *)
Lemma instantiate_decoder_result z :
  instantiate empty_store decoder_module [] z -> z = (s0, Build_frame [] inst0, []).
Proof.
  case: z => [[s f] bes] Hi.
  destruct Hi as [timps [ti [te [hs' [inst [gi [ri [Ht [Hti [Hsub [Ha [_ [_ [Hf Hbes]]]]]]]]]]]]]].
  unfold alloc_module in Ha. cbn in Ha.
  destruct Ha as [Es [Ety [Efu [Eta [Em [Eg [Ee [Ed Hex]]]]]]]].
  have Hi0 : inst = inst0 by destruct inst; cbn in *; subst; rewrite Hex.
  by subst f bes s inst.
Qed.

Lemma instance_memory_fits_proved : instance_memory_fits.
Proof.
  split.
  - intro hs. exists s0, inst0. exact (instantiate_decoder hs).
  - move => s inst a /instantiate_decoder_result [-> ->] He.
    have -> : a = 0%N.
    { move: He. rewrite /export_named /=.
      by do 3 (case => [//|]); case => [[]|]. }
    exists (gen_mem_instance {| lim_min := 5%N; lim_max := Some 5%N |}).
    do 2 (split; first reflexivity).
    rewrite /operations.mem_length /gen_mem_instance /= mem_make_length.
    split; vm_compute; [reflexivity|discriminate].
Qed.

Lemma instantiation_unique_proved : instantiation_unique.
Proof.
  move => z1 z2 H1 H2.
  by rewrite (instantiate_decoder_result _ H1) (instantiate_decoder_result _ H2).
Qed.

Theorem decoder_module_applies_proved : decoder_module_applies.
Proof.
  split; [exact layout_fits_proved|split];
    [exact instance_memory_fits_proved | exact instantiation_unique_proved].
Qed.

End NonVacuity.
