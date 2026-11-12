(** * The streaming UTF-8 decoder module, as a WasmCert-Coq AST term.

    This term is the single source of truth: the theorems are about it,
    and [Binary.v] prints decoder.wasm from it.

    State (an i32 value): bits 0..7 = first pending byte b1, 8..15 = b2,
    16..23 = b3, 24..25 = number n of pending bytes (0..3).  The start
    state is 0.  This is RefDecoder's pending-byte list, packed.

    Memory (5 pages, not growable by the module):
      input area   [IN, IN + len)            IN = 0, len <= IN_MAX = 65536
      output area  [OUT, OUT + 2*len + 2)    OUT = 65536 (UTF-16LE code units;
                                             Boundary.v's out_area)

    Exports:
      start  () -> i32                    the start state (0)
      decode (st len : i32) -> (i32 i32)  new state, number of output BYTES at OUT
      done   (st : i32) -> i32            number of output bytes at OUT
      memory

    Locals of [decode]: 0 st, 1 len, 2 i, 3 o (output byte address),
    4 b (current byte), 5 n, 6 b1, 7 cp, 8 lo, 9 hi, 10 L. *)

From Stdlib Require Import ZArith NArith List String.
From Wasm Require Import datatypes numerics.
Import ListNotations.

Definition i32c (z : Z) : basic_instruction :=
  BI_const_num (VAL_int32 (Wasm_int.Int32.repr z)).
Definition T32 : value_type := T_num T_i32.
Definition BTn : block_type := BT_valtype None.

Definition lg (n : N) := BI_local_get n.
Definition ls (n : N) := BI_local_set n.
Definition bin op := BI_binop T_i32 (Binop_i op).
Definition rel op := BI_relop T_i32 (Relop_i op).
Definition i_add := bin BOI_add.
Definition i_sub := bin BOI_sub.
Definition i_and := bin BOI_and.
Definition i_or := bin BOI_or.
Definition i_shl := bin BOI_shl.
Definition i_shr := bin (BOI_shr SX_U).
Definition i_eq := rel ROI_eq.
Definition i_ltu := rel (ROI_lt SX_U).
Definition i_leu := rel (ROI_le SX_U).
Definition i_geu := rel (ROI_ge SX_U).
Definition ma (off : N) := {| memarg_offset := off; memarg_align := 0%N |}.
Definition load8 := BI_load T_i32 (Some (Tp_i8, SX_U)) (ma 0).
Definition store16 (off : N) := BI_store T_i32 (Some Tp_i16) (ma off).
Definition if_ thn els := BI_if BTn thn els.

Definition IN : Z := 0.
Definition IN_MAX : Z := 65536.
Definition OUT : Z := 65536.
Definition PAGES : N := 5.

(** o += k *)
Definition adv_o (k : Z) := [lg 3; i32c k; i_add; ls 3].

(** Write U+FFFD at o. *)
Definition emit_fffd := [lg 3; i32c 0xFFFD; store16 0] ++ adv_o 2.

(** Write the scalar in local 7 at o, as one or two UTF-16 code units. *)
Definition emit_cp :=
  [lg 7; i32c 0x10000; i_ltu;
   if_ ([lg 3; lg 7; store16 0] ++ adv_o 2)
       ([lg 3; lg 7; i32c 10; i_shr; i32c 0xD7C0; i_add; store16 0;
         lg 3; lg 7; i32c 0x3FF; i_and; i32c 0xDC00; i_or; store16 2] ++ adv_o 4)].

(** RefDecoder's [step_empty] on byte b (local 4); st (local 0) is 0. *)
Definition empty_code :=
  [lg 4; i32c 0x80; i_ltu;
   if_ ([lg 3; lg 4; store16 0] ++ adv_o 2)
       [lg 4; i32c 0xC2; i_sub; i32c 0x32; i_leu;
        if_ [lg 4; i32c 0x1000000; i_or; ls 0]
            emit_fffd]].

(** Allowed range [lo, hi] (locals 8, 9) for the next byte. *)
Definition range_code :=
  [i32c 0x80; ls 8; i32c 0xBF; ls 9;
   lg 5; i32c 1; i_eq;
   if_ [lg 6; i32c 0xE0; i_eq; if_ [i32c 0xA0; ls 8] [];
        lg 6; i32c 0xF0; i_eq; if_ [i32c 0x90; ls 8] [];
        lg 6; i32c 0xED; i_eq; if_ [i32c 0x9F; ls 9] [];
        lg 6; i32c 0xF4; i_eq; if_ [i32c 0x8F; ls 9] []] []].

(** Sequence length L (local 10) from the lead byte b1. *)
Definition len_code :=
  [i32c 4; ls 10;
   lg 6; i32c 0xF0; i_ltu; if_ [i32c 3; ls 10] [];
   lg 6; i32c 0xE0; i_ltu; if_ [i32c 2; ls 10] []].

(** (st >> sh) & 0x3F *)
Definition low6_of_st (sh : Z) := [lg 0; i32c sh; i_shr; i32c 0x3F; i_and].

(** The code point (local 7) of the completed sequence b1 [b2 [b3]] b. *)
Definition cp_code :=
  [lg 4; i32c 0x3F; i_and; ls 7;
   lg 10; i32c 2; i_eq;
   if_ [lg 7; lg 6; i32c 0x1F; i_and; i32c 6; i_shl; i_or; ls 7]
       [lg 10; i32c 3; i_eq;
        if_ ([lg 7; lg 6; i32c 0x0F; i_and; i32c 12; i_shl; i_or] ++
             low6_of_st 8 ++ [i32c 6; i_shl; i_or; ls 7])
            ([lg 7; lg 6; i32c 0x07; i_and; i32c 18; i_shl; i_or] ++
             low6_of_st 8 ++ [i32c 12; i_shl; i_or] ++
             low6_of_st 16 ++ [i32c 6; i_shl; i_or; ls 7])]].

(** RefDecoder's [step] for a non-empty pending state. *)
Definition pending_code :=
  [lg 0; i32c 0xFF; i_and; ls 6] ++ range_code ++
  [lg 4; lg 8; i_geu; lg 4; lg 9; i_leu; i_and;
   if_ (len_code ++
        [lg 5; i32c 1; i_add; lg 10; i_eq;
         if_ (cp_code ++ emit_cp ++ [i32c 0; ls 0])
             [lg 0; lg 4; lg 5; i32c 3; i_shl; i_shl; i_or; i32c 0x1000000; i_add; ls 0]])
       (emit_fffd ++ [i32c 0; ls 0] ++ empty_code)].

(** One byte: RefDecoder's [step]. *)
Definition step_code :=
  [lg 2; load8; ls 4;
   lg 0; i32c 24; i_shr; ls 5;
   lg 5; BI_testop T_i32 TO_eqz;
   if_ empty_code pending_code].

Definition loop_body :=
  [lg 2; lg 1; i_geu; BI_br_if 1%N] ++ step_code ++ [lg 2; i32c 1; i_add; ls 2; BI_br 0%N].

Definition decode_body : expr :=
  [i32c OUT; ls 3;
   BI_block BTn [BI_loop BTn loop_body];
   lg 0; lg 3; i32c OUT; i_sub].

Definition done_body : expr :=
  [lg 0; BI_if (BT_valtype (Some T32)) [i32c OUT; i32c 0xFFFD; store16 0; i32c 2] [i32c 0]].

Definition start_body : expr := [i32c 0].

Definition ty_start : function_type := Tf [] [T32].
Definition ty_decode : function_type := Tf [T32; T32] [T32; T32].
Definition ty_done : function_type := Tf [T32] [T32].

Definition start_func : module_func :=
  {| modfunc_type := 0%N; modfunc_locals := []; modfunc_body := start_body |}.
Definition decode_func : module_func :=
  {| modfunc_type := 1%N; modfunc_locals := repeat T32 9; modfunc_body := decode_body |}.
Definition done_func : module_func :=
  {| modfunc_type := 2%N; modfunc_locals := []; modfunc_body := done_body |}.

Definition name := String.list_byte_of_string.

Definition decoder_module : module := {|
  mod_types := [ty_start; ty_decode; ty_done];
  mod_funcs := [start_func; decode_func; done_func];
  mod_tables := [];
  mod_mems := [ {| modmem_type := {| lim_min := PAGES; lim_max := Some PAGES |} |} ];
  mod_globals := [];
  mod_elems := [];
  mod_datas := [];
  mod_start := None;
  mod_imports := [];
  mod_exports := [
    {| modexp_name := name "start"; modexp_desc := MED_func 0%N |};
    {| modexp_name := name "decode"; modexp_desc := MED_func 1%N |};
    {| modexp_name := name "done"; modexp_desc := MED_func 2%N |};
    {| modexp_name := name "memory"; modexp_desc := MED_mem 0%N |} ];
|}.
