(** * The spike module, as a WasmCert-Coq AST term.

    This term is the single source of truth: the theorems are about it,
    and [Binary.v] prints the .wasm bytes from it.

    Equivalent WAT:
<<
  (module
    (type (func (param i32) (result i32)))
    (type (func (param i32 i32) (result i32)))
    (func $is_surrogate_code_point (type 0)
      local.get 0  i32.const 0xD800  i32.ge_u
      local.get 0  i32.const 0xDFFF  i32.le_u
      i32.and)
    (func $count_non_ascii (type 1) (local i32)   ;; 0=ptr 1=len 2=acc
      block
        loop
          local.get 1  i32.eqz  br_if 1
          local.get 2  local.get 0  i32.load8_u  i32.const 0x80  i32.ge_u
          i32.add  local.set 2
          local.get 0  i32.const 1  i32.add  local.set 0
          local.get 1  i32.const 1  i32.sub  local.set 1
          br 0
        end
      end
      local.get 2)
    (memory 1)
    (export "is_surrogate_code_point" (func 0))
    (export "count_non_ascii" (func 1))
    (export "memory" (memory 0)))
>>
*)

From Stdlib Require Import ZArith NArith List String.
From Wasm Require Import datatypes numerics.
Import ListNotations.

Definition i32c (z : Z) : basic_instruction :=
  BI_const_num (VAL_int32 (Wasm_int.Int32.repr z)).

Definition T32 : value_type := T_num T_i32.

Definition surrogate_body : expr :=
  [ BI_local_get 0%N; i32c 0xD800; BI_relop T_i32 (Relop_i (ROI_ge SX_U));
    BI_local_get 0%N; i32c 0xDFFF; BI_relop T_i32 (Relop_i (ROI_le SX_U));
    BI_binop T_i32 (Binop_i BOI_and) ].

(** The loop body, split into the exit test and the rest so that proofs
    can refer to the pieces. *)
Definition count_exit_test : expr :=
  [ BI_local_get 1%N; BI_testop T_i32 TO_eqz; BI_br_if 1%N ].

Definition count_step : expr :=
  [ BI_local_get 2%N; BI_local_get 0%N;
    BI_load T_i32 (Some (Tp_i8, SX_U)) {| memarg_offset := 0%N; memarg_align := 0%N |};
    i32c 0x80; BI_relop T_i32 (Relop_i (ROI_ge SX_U));
    BI_binop T_i32 (Binop_i BOI_add); BI_local_set 2%N;
    BI_local_get 0%N; i32c 1; BI_binop T_i32 (Binop_i BOI_add); BI_local_set 0%N;
    BI_local_get 1%N; i32c 1; BI_binop T_i32 (Binop_i BOI_sub); BI_local_set 1%N ].

Definition count_loop_body : expr :=
  count_exit_test ++ count_step ++ [ BI_br 0%N ].

Definition count_body : expr :=
  [ BI_block (BT_valtype None) [ BI_loop (BT_valtype None) count_loop_body ];
    BI_local_get 2%N ].

Definition ty_surrogate : function_type := Tf [T32] [T32].
Definition ty_count : function_type := Tf [T32; T32] [T32].

Definition surrogate_func : module_func :=
  {| modfunc_type := 0%N; modfunc_locals := []; modfunc_body := surrogate_body |}.

Definition count_func : module_func :=
  {| modfunc_type := 1%N; modfunc_locals := [T32]; modfunc_body := count_body |}.

Definition spike_module : module := {|
  mod_types := [ty_surrogate; ty_count];
  mod_funcs := [surrogate_func; count_func];
  mod_tables := [];
  mod_mems := [ {| modmem_type := {| lim_min := 1%N; lim_max := None |} |} ];
  mod_globals := [];
  mod_elems := [];
  mod_datas := [];
  mod_start := None;
  mod_imports := [];
  mod_exports := [
    {| modexp_name := String.list_byte_of_string "is_surrogate_code_point";
       modexp_desc := MED_func 0%N |};
    {| modexp_name := String.list_byte_of_string "count_non_ascii";
       modexp_desc := MED_func 1%N |};
    {| modexp_name := String.list_byte_of_string "memory";
       modexp_desc := MED_mem 0%N |} ];
|}.
