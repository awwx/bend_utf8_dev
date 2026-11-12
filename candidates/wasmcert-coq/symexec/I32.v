(** * I32.v: i32 arithmetic on values that fit (reusable; nothing
    decoder-specific).

    WasmCert-Coq's i32 operations are CompCert's [Int32] on [repr]s.  For
    operands known to lie in [0, 2^32) ([small]), these lemmas turn each
    operation into plain [Z] arithmetic, so that after symbolic execution
    (Steps.v / Wp.v) the goals are [lia] goals.

    Exports:
    - [modulus_val] (2^32), [small] (0 <= a < 2^32), [small_const],
      [unsigned_small] (unsigned (repr z) = z).
    - comparisons: [ltu_val], [leu_val], [geu_val], [eq_val]
      (app_relop of reprs = the Z test); [wasm_bool_nz], [wasm_bool_z],
      [wasm_bool_true_nz], [and_bool].
    - arithmetic: [i32_iadd_repr] / [iadd_val], [i32_isub_repr],
      [i32_or_repr] / [or_val], [shl_val] (a * 2^k), [shru_val] (a / 2^k),
      [and_val] / [low_bits_val] / [mask_val] (a mod 2^k), [modu32].
    - bit fields: [Z_lor_disjoint] (a | c*2^k = a + c*2^k for a < 2^k),
      [lor_pack], [lor_mid], [lor_swap], [or_count], [mod_bound].
    - bytes: [byte_unsigned_repr]. *)

From Stdlib Require Import ZArith NArith Lia.
From mathcomp Require Import ssreflect ssrfun ssrbool.
From compcert Require Import Integers Coqlib.
From Wasm Require Import numerics datatypes operations.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma modulus_val : Wasm_int.Int32.modulus = 4294967296%Z.
Proof. by []. Qed.

Definition small (a : Z) := (0 <= a < Wasm_int.Int32.modulus)%Z.

Lemma small_const z : (0 <= z < 4294967296)%Z -> small z.
Proof. by rewrite /small modulus_val. Qed.

Lemma unsigned_small z : (0 <= z < Wasm_int.Int32.modulus)%Z ->
  Wasm_int.Int32.unsigned (Wasm_int.Int32.repr z) = z.
Proof.
  move => H; apply Wasm_int.Int32.unsigned_repr. rewrite /Wasm_int.Int32.max_unsigned. lia.
Qed.

Lemma geu_val a b : (0 <= a < Wasm_int.Int32.modulus)%Z -> (0 <= b < Wasm_int.Int32.modulus)%Z ->
  app_relop (Relop_i (ROI_ge SX_U)) (VAL_int32 (Wasm_int.Int32.repr a)) (VAL_int32 (Wasm_int.Int32.repr b))
  = (b <=? a)%Z.
Proof.
  move => Ha Hb. rewrite /app_relop /= /Wasm_int.Int32.ltu !unsigned_small //.
  case: Coqlib.zlt => H; case: Z.leb_spec => H' //=; lia.
Qed.

Lemma i32_iadd_repr a b :
  Wasm_int.Int32.iadd (Wasm_int.Int32.repr a) (Wasm_int.Int32.repr b) = Wasm_int.Int32.repr (a + b).
Proof.
  rewrite /Wasm_int.Int32.iadd /Wasm_int.Int32.add.
  apply Wasm_int.Int32.eqm_samerepr, Wasm_int.Int32.eqm_add;
    apply Wasm_int.Int32.eqm_sym, Wasm_int.Int32.eqm_unsigned_repr.
Qed.

Lemma i32_isub_repr a b :
  Wasm_int.Int32.isub (Wasm_int.Int32.repr a) (Wasm_int.Int32.repr b) = Wasm_int.Int32.repr (a - b).
Proof.
  rewrite /Wasm_int.Int32.isub /Wasm_int.Int32.sub.
  apply Wasm_int.Int32.eqm_samerepr, Wasm_int.Int32.eqm_sub;
    apply Wasm_int.Int32.eqm_sym, Wasm_int.Int32.eqm_unsigned_repr.
Qed.

Lemma wasm_bool_true_nz : wasm_bool true <> Wasm_int.int_zero i32m.
Proof. by []. Qed.

Lemma ltu_val a b : (0 <= a < Wasm_int.Int32.modulus)%Z -> (0 <= b < Wasm_int.Int32.modulus)%Z ->
  app_relop (Relop_i (ROI_lt SX_U)) (VAL_int32 (Wasm_int.Int32.repr a)) (VAL_int32 (Wasm_int.Int32.repr b))
  = (a <? b)%Z.
Proof.
  move => Ha Hb. rewrite /app_relop /= /Wasm_int.Int32.ltu !unsigned_small //.
  case: Coqlib.zlt => H; case: Z.ltb_spec => H' //=; lia.
Qed.

Lemma leu_val a b : (0 <= a < Wasm_int.Int32.modulus)%Z -> (0 <= b < Wasm_int.Int32.modulus)%Z ->
  app_relop (Relop_i (ROI_le SX_U)) (VAL_int32 (Wasm_int.Int32.repr a)) (VAL_int32 (Wasm_int.Int32.repr b))
  = (a <=? b)%Z.
Proof.
  move => Ha Hb. rewrite /app_relop /= /Wasm_int.Int32.ltu !unsigned_small //.
  case: Coqlib.zlt => H; case: Z.leb_spec => H' //=; lia.
Qed.

Lemma wasm_bool_nz b : wasm_bool b <> Wasm_int.int_zero i32m -> b = true.
Proof. by case: b. Qed.

Lemma wasm_bool_z b : wasm_bool b = Wasm_int.int_zero i32m -> b = false.
Proof. by case: b. Qed.

Lemma Z_lor_disjoint a c k : (0 <= k)%Z -> (0 <= a < 2 ^ k)%Z -> (0 <= c)%Z ->
  Z.lor a (c * 2 ^ k) = (a + c * 2 ^ k)%Z.
Proof.
  move => Hk Ha Hc.
  have H0 : Z.land a (c * 2 ^ k) = 0%Z.
  { apply Z.bits_inj' => i Hi. rewrite Z.land_spec Z.bits_0.
    case: (Z.lt_ge_cases i k) => Hik.
    - by rewrite Z.mul_pow2_bits_low // andbF.
    - have -> : Z.testbit a i = false; last by [].
      case: (Z.eq_dec a 0) => [->|Ha0]; first by rewrite Z.bits_0.
      apply: (Z.bits_above_log2 a i); first lia.
      have : (Z.log2 a < k)%Z by apply Z.log2_lt_pow2; lia. lia. }
  by rewrite -Z.lxor_lor // -Z.add_nocarry_lxor.
Qed.

Lemma byte_unsigned_repr z : (0 <= z < 256)%Z -> Integers.Byte.unsigned (Integers.Byte.repr z) = z.
Proof. move => H. apply Integers.Byte.unsigned_repr. rewrite /Integers.Byte.max_unsigned /=. lia. Qed.

Lemma i32_or_repr a b : (0 <= a < Wasm_int.Int32.modulus)%Z -> (0 <= b < Wasm_int.Int32.modulus)%Z ->
  Wasm_int.Int32.or (Wasm_int.Int32.repr a) (Wasm_int.Int32.repr b) = Wasm_int.Int32.repr (Z.lor a b).
Proof. move => Ha Hb. by rewrite /Wasm_int.Int32.or !unsigned_small. Qed.

Lemma or_count a k : (0 <= a < 16777216)%Z -> (0 <= k < 256)%Z ->
  Wasm_int.int_or i32m (Wasm_int.Int32.repr a) (Wasm_int.Int32.repr (k * 16777216)) =
  Wasm_int.Int32.repr (a + k * 16777216).
Proof.
  move => Ha Hk. have Hm := modulus_val.
  change (Wasm_int.Int32.or (Wasm_int.Int32.repr a) (Wasm_int.Int32.repr (k * 16777216)) =
          Wasm_int.Int32.repr (a + k * 16777216)).
  rewrite i32_or_repr; try lia.
  have E : (16777216 = 2 ^ 24)%Z by [].
  by rewrite E Z_lor_disjoint; try lia.
Qed.

Lemma modu32 k : (0 <= k < 32)%Z ->
  Wasm_int.Int32.modu (Wasm_int.Int32.repr k) Wasm_int.Int32.iwordsize = Wasm_int.Int32.repr k.
Proof.
  move => Hk. have Hm := modulus_val.
  rewrite /Wasm_int.Int32.modu unsigned_small; first lia.
  have -> : Wasm_int.Int32.unsigned Wasm_int.Int32.iwordsize = 32%Z by [].
  by rewrite Z.mod_small.
Qed.

Lemma shl_val a k : small a -> (0 <= k < 32)%Z ->
  Wasm_int.int_shl i32m (Wasm_int.Int32.repr a) (Wasm_int.Int32.repr k) = Wasm_int.Int32.repr (a * 2 ^ k).
Proof.
  move => Ha Hk. have Hm := modulus_val.
  change (Wasm_int.Int32.shl (Wasm_int.Int32.repr a)
            (Wasm_int.Int32.modu (Wasm_int.Int32.repr k) Wasm_int.Int32.iwordsize) =
          Wasm_int.Int32.repr (a * 2 ^ k)).
  rewrite modu32 // /Wasm_int.Int32.shl !unsigned_small; try (rewrite /small in Ha; lia).
  by rewrite Z.shiftl_mul_pow2; first lia.
Qed.

Lemma shru_val a k : small a -> (0 <= k < 32)%Z ->
  Wasm_int.int_shr_u i32m (Wasm_int.Int32.repr a) (Wasm_int.Int32.repr k) = Wasm_int.Int32.repr (a / 2 ^ k).
Proof.
  move => Ha Hk. have Hm := modulus_val.
  change (Wasm_int.Int32.shru (Wasm_int.Int32.repr a)
            (Wasm_int.Int32.modu (Wasm_int.Int32.repr k) Wasm_int.Int32.iwordsize) =
          Wasm_int.Int32.repr (a / 2 ^ k)).
  rewrite modu32 // /Wasm_int.Int32.shru !unsigned_small; try (rewrite /small in Ha; lia).
  by rewrite Z.shiftr_div_pow2; first lia.
Qed.

Lemma and_val a k : small a -> (0 <= k < 32)%Z ->
  Wasm_int.int_and i32m (Wasm_int.Int32.repr a) (Wasm_int.Int32.repr (2 ^ k - 1)) = Wasm_int.Int32.repr (a mod 2 ^ k).
Proof.
  move => Ha Hk. have Hm := modulus_val.
  have Hp : (0 < 2 ^ k <= 2 ^ 32)%Z by split; [apply Z.pow_pos_nonneg|apply Z.pow_le_mono_r]; lia.
  change (Wasm_int.Int32.and (Wasm_int.Int32.repr a) (Wasm_int.Int32.repr (2 ^ k - 1)) =
          Wasm_int.Int32.repr (a mod 2 ^ k)).
  rewrite /Wasm_int.Int32.and !unsigned_small; try (rewrite /small in Ha; lia).
  have -> : (2 ^ k - 1 = Z.ones k)%Z by rewrite Z.ones_equiv; lia.
  by rewrite Z.land_ones; first lia.
Qed.

Lemma eq_val a b : small a -> small b ->
  app_relop (Relop_i ROI_eq) (VAL_int32 (Wasm_int.Int32.repr a)) (VAL_int32 (Wasm_int.Int32.repr b))
  = (a =? b)%Z.
Proof.
  move => Ha Hb. rewrite /app_relop /= /Wasm_int.Int32.eq !unsigned_small //.
  case: Coqlib.zeq => H; case: Z.eqb_spec => H' //=.
Qed.

Lemma and_bool x y :
  Wasm_int.int_and i32m (wasm_bool x) (wasm_bool y) = wasm_bool (x && y).
Proof. by case: x; case: y. Qed.

Lemma lor_pack x c k n : (0 <= k)%Z -> (k + 8 <= 24)%Z -> (0 <= x < 2 ^ k)%Z -> (0 <= c < 256)%Z -> (0 <= n)%Z ->
  Z.lor (x + n * 2 ^ 24) (c * 2 ^ k) = (x + c * 2 ^ k + n * 2 ^ 24)%Z.
Proof.
  move => Hk Hk8 Hx Hc Hn.
  have Hp : (2 ^ k * 256 <= 2 ^ 24)%Z.
  { have -> : (256 = 2 ^ 8)%Z by []. rewrite -Z.pow_add_r; try lia. apply Z.pow_le_mono_r; lia. }
  have Hx24 : (0 <= x < 2 ^ 24)%Z by lia.
  have Hck : (c * 2 ^ k <= 255 * 2 ^ k)%Z by apply Z.mul_le_mono_nonneg_r; lia.
  have Hc0 : (0 <= c * 2 ^ k)%Z by apply Z.mul_nonneg_nonneg; lia.
  rewrite -(Z_lor_disjoint (c := n) _ Hx24) // -Z.lor_assoc (Z.lor_comm (n * 2 ^ 24)) Z.lor_assoc.
  have Hx' : (0 <= x < 2 ^ k)%Z by lia.
  rewrite (Z_lor_disjoint Hk Hx' (ltac:(lia) : (0 <= c)%Z)).
  have Hy : (0 <= x + c * 2 ^ k < 2 ^ 24)%Z by lia.
  by rewrite (Z_lor_disjoint (ltac:(lia) : (0 <= 24)%Z) Hy Hn).
Qed.

(* [int_add i32m] is the form the semantics produces after a step;
   [rewrite] does not see through it to [Int32.iadd]. *)
Lemma iadd_val a c :
  Wasm_int.int_add i32m (Wasm_int.Int32.repr a) (Wasm_int.Int32.repr c) = Wasm_int.Int32.repr (a + c).
Proof. exact: i32_iadd_repr. Qed.

Lemma lor_swap x y z : Z.lor (Z.lor x y) z = Z.lor (Z.lor x z) y.
Proof. by rewrite -!Z.lor_assoc (Z.lor_comm y z). Qed.

(* [and_val] for a byte value, and with the mask given as an equation. *)
Lemma low_bits_val a k : (0 <= a < 256)%Z -> (0 <= k < 32)%Z ->
  Wasm_int.int_and i32m (Wasm_int.Int32.repr a) (Wasm_int.Int32.repr (2 ^ k - 1)) = Wasm_int.Int32.repr (a mod 2 ^ k).
Proof. move => Ha Hk. apply: and_val => //. apply small_const. lia. Qed.

Lemma mod_bound a k : (0 <= k)%Z -> (0 <= a mod 2 ^ k < 2 ^ k)%Z.
Proof. move => Hk. apply Z.mod_pos_bound. apply Z.pow_pos_nonneg; lia. Qed.

(* The [int_or i32m] form of [i32_or_repr]. *)
Lemma or_val a c : small a -> small c ->
  Wasm_int.int_or i32m (Wasm_int.Int32.repr a) (Wasm_int.Int32.repr c) = Wasm_int.Int32.repr (Z.lor a c).
Proof. exact: i32_or_repr. Qed.

Lemma mask_val a m k : small a -> m = (2 ^ k - 1)%Z -> (0 <= k < 32)%Z ->
  Wasm_int.int_and i32m (Wasm_int.Int32.repr a) (Wasm_int.Int32.repr m) = Wasm_int.Int32.repr (a mod 2 ^ k).
Proof. move => Ha -> Hk. exact: and_val. Qed.

Lemma lor_mid a c h j k : (0 <= j)%Z -> (j <= k)%Z -> (0 <= a < 2 ^ j)%Z -> (0 <= c)%Z -> (0 <= h)%Z ->
  (a + c * 2 ^ j < 2 ^ k)%Z ->
  Z.lor (a + h * 2 ^ k) (c * 2 ^ j) = (a + c * 2 ^ j + h * 2 ^ k)%Z.
Proof.
  move => Hj Hjk Ha Hc Hh Hfit.
  have Hpj : (0 <= c * 2 ^ j)%Z by apply Z.mul_nonneg_nonneg; [lia|apply Z.pow_nonneg; lia].
  have Hak : (0 <= a < 2 ^ k)%Z by lia.
  rewrite -(Z_lor_disjoint (ltac:(lia) : (0 <= k)%Z) Hak Hh) -Z.lor_assoc (Z.lor_comm (h * 2 ^ k)) Z.lor_assoc.
  rewrite (Z_lor_disjoint Hj Ha Hc).
  have Hy : (0 <= a + c * 2 ^ j < 2 ^ k)%Z by lia.
  by rewrite (Z_lor_disjoint (ltac:(lia) : (0 <= k)%Z) Hy Hh).
Qed.
