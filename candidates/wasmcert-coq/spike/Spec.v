(** * Specifications (the part a human reviews).

    These definitions mention no WebAssembly at all.  The theorems in
    [Surrogate.v] and [Count.v] connect them to the Wasm module term. *)

From Stdlib Require Import ZArith NArith List.
From compcert Require Import Integers.
Import ListNotations.
Open Scope N_scope.

(** ** Surrogate code points (LAWS.bend lines 117-131)

    Surrogate code points are U+D800..U+DFFF.  A code point is given as
    an unsigned 32-bit number, i.e. an [N] below 2^32 (the Wasm side
    passes an i32 that is read as unsigned). *)

Definition is_surrogate_code_point (cp : N) : bool :=
  (0xD800 <=? cp) && (cp <=? 0xDFFF).

Lemma is_surrogate_code_point_examples :
  is_surrogate_code_point 0x0000 = false /\
  is_surrogate_code_point 0xD7FF = false /\
  is_surrogate_code_point 0xD800 = true /\
  is_surrogate_code_point 0xDC00 = true /\
  is_surrogate_code_point 0xDFFF = true /\
  is_surrogate_code_point 0xE000 = false.
Proof. repeat split. Qed.

(** ** Counting non-ASCII bytes

    A byte is non-ASCII when its unsigned value is at least 0x80.  The
    count is defined by recursion over the byte list. *)

Definition is_non_ascii (b : byte) : bool :=
  (128 <=? Byte.unsigned b)%Z.

Fixpoint count_non_ascii (bs : list byte) : nat :=
  match bs with
  | [] => 0
  | b :: rest => (if is_non_ascii b then 1 else 0) + count_non_ascii rest
  end%nat.
