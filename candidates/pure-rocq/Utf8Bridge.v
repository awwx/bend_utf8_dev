(* Utf8Bridge.v: from the bit-level spec (U32 = 32 booleans, encoding by
   bit shapes) to arithmetic on N and to the byte-range table of Utf8Ref.v.
   Everything is proved symbolically (lia and N.testbit lemmas); there is
   no enumeration of code points or byte sequences.

   Exports:
   - U32 and N:  U32_to_N_bound, U32_to_of (U32_to_N (U32_of_N n) = n for
       n < 2^32), U32_of_to, U32_to_N_inj, scalar_N (arithmetic scalar
       test), is_unicode_scalar_iff.
   - Bytes:  bN_inj, bN_bound, bN_byte_of (byte_of: N -> byte).
   - utf8_form s n: s is the UTF-8 bit layout of n (length chosen by the
       range of n, continuation bytes 80..BF, value as a base-64 sum).
       encoding_form (what `encoding` computes, as a utf8_form),
       utf8_form_unique.
   - Byte-range table:  seq_len_cases, lo2_hi2_cases, vp_one_iff,
       vs_one_iff, vp_cons2, vs_vp_len, vp_len_lead, seq_len_le4, vp_len,
       vp_app, vs_vp, vs_prefix_free.
   - Central characterization:  vs_form (a valid sequence is the
       utf8_form of its seq_value, which is a scalar), form_vs (converse),
       encodes_iff, seq_cp_value, seq_value_scalar.
   - completion s (bytes completing a pending prefix), pending_completion. *)

From Stdlib Require Import List NArith Arith Bool Lia.
From Stdlib Require Strings.Byte.
Import Corelib.Init.Byte ListNotations.
From Utf8 Require Import Utf8Laws Utf8Ref.

Local Open Scope N_scope.

(** * U32 and N *)

Lemma b2n_le1 b : N.b2n b <= 1.
Proof. destruct b; simpl; lia. Qed.

(* Replace every N.b2n of a variable by a fresh N in 0..1, for lia. *)
Ltac b2n_bounds :=
  repeat match goal with
  | |- context [N.b2n ?b] =>
      lazymatch b with
      | true => fail | false => fail
      | _ => pose proof (b2n_le1 b); generalize dependent (N.b2n b); intros
      end
  end.

Lemma U32_to_N_bound x : U32_to_N x < 2 ^ 32.
Proof. destruct x; unfold U32_to_N; b2n_bounds; cbn [N.pow]; lia. Qed.

(* Value of bits j .. j+k-1 of n. *)
Fixpoint low_bits (k : nat) (j n : N) : N :=
  match k with
  | O => 0
  | S k => N.b2n (N.testbit n j) + 2 * low_bits k (N.succ j) n
  end.

Lemma low_bits_mod k j n : low_bits k j n = (n / 2 ^ j) mod 2 ^ N.of_nat k.
Proof.
  revert j; induction k as [|k IH]; intros j; cbn [low_bits].
  - now rewrite N.mod_1_r.
  - set (m := n / 2 ^ j). rewrite IH.
    replace (n / 2 ^ N.succ j) with (m / 2)
      by (unfold m; now rewrite N.Div0.div_div, N.pow_succ_r', N.mul_comm).
    replace (N.testbit n j) with (N.testbit m 0) by (unfold m; now rewrite N.div_pow2_bits).
    now rewrite N.bit0_mod, Nat2N.inj_succ, N.pow_succ_r', N.Div0.mod_mul_r.
Qed.

Lemma U32_to_of n : n < 2 ^ 32 -> U32_to_N (U32_of_N n) = n.
Proof.
  intros H. transitivity (low_bits 32 0 n).
  { cbn [low_bits]. rewrite N.mul_0_r, N.add_0_r. reflexivity. }
  rewrite low_bits_mod, N.div_1_r. now apply N.mod_small.
Qed.

Lemma b2n_double_inj b c x y : N.b2n b + 2 * x = N.b2n c + 2 * y -> b = c /\ x = y.
Proof. destruct b, c; cbn [N.b2n]; intros; split; lia || reflexivity. Qed.

Lemma U32_to_N_inj x y : U32_to_N x = U32_to_N y -> x = y.
Proof.
  destruct x, y; unfold U32_to_N; intros H;
  repeat (apply b2n_double_inj in H as [-> H]).
  destruct (N.b2n_inj _ _ H). reflexivity.
Qed.

Lemma U32_of_to x : U32_of_N (U32_to_N x) = x.
Proof. apply U32_to_N_inj, U32_to_of, U32_to_N_bound. Qed.

Definition scalar_N (n : N) : Prop := n <= 0x10FFFF /\ ~ (0xD800 <= n <= 0xDFFF).

Lemma is_unicode_scalar_iff cp : is_unicode_scalar cp = true <-> scalar_N (U32_to_N cp).
Proof.
  unfold is_unicode_scalar, is_surrogate_code_point, U32_is_ge, U32_is_le, scalar_N.
  rewrite !U32_to_of by (cbn; lia).
  rewrite !andb_true_iff, negb_true_iff, andb_false_iff, !N.leb_le, !N.leb_gt. lia.
Qed.

(** * Bytes as N *)

Lemma bN_inj a b : bN a = bN b -> a = b.
Proof.
  unfold bN; intros H. apply (f_equal Byte.of_N) in H. rewrite !Byte.of_to_N in H.
  now injection H.
Qed.

Lemma bN_bound b : bN b <= 255.
Proof. apply Byte.to_N_bounded. Qed.

Definition byte_of (n : N) : byte :=
  match Byte.of_N n with Some b => b | None => x00 end.

Lemma bN_byte_of n : n <= 255 -> bN (byte_of n) = n.
Proof.
  intros H. unfold byte_of. destruct (Byte.of_N n) eqn:E.
  - now apply Byte.to_of_N in E.
  - apply Byte.of_N_None_iff in E. lia.
Qed.

Lemma bN_bit8 b7 b6 b5 b4 b3 b2 b1 b0 :
  bN (bit8_value (b7, b6, b5, b4, b3, b2, b1, b0)) =
  N.b2n b7 * 128 + N.b2n b6 * 64 + N.b2n b5 * 32 + N.b2n b4 * 16 +
  N.b2n b3 * 8 + N.b2n b2 * 4 + N.b2n b1 * 2 + N.b2n b0.
Proof. destruct b7, b6, b5, b4, b3, b2, b1, b0; reflexivity. Qed.

(** * The UTF-8 layout of a number *)

Definition cont (b : byte) : Prop := 0x80 <= bN b <= 0xBF.

(* `s` is the UTF-8 bit layout of `n`: the length is chosen by the range
   of `n`, the lead byte carries the high bits after its length marker,
   each continuation byte carries 6 bits after its 10 marker. *)
Definition utf8_form (s : list byte) (n : N) : Prop :=
  match s with
  | [b1] => n < 0x80 /\ bN b1 = n
  | [b1; b2] => 0x80 <= n < 0x800 /\ 0xC0 <= bN b1 /\ cont b2 /\
      n = (bN b1 - 0xC0) * 64 + (bN b2 - 0x80)
  | [b1; b2; b3] => 0x800 <= n < 0x10000 /\ 0xE0 <= bN b1 /\ cont b2 /\ cont b3 /\
      n = ((bN b1 - 0xE0) * 64 + (bN b2 - 0x80)) * 64 + (bN b3 - 0x80)
  | [b1; b2; b3; b4] =>
      0x10000 <= n < 0x200000 /\ 0xF0 <= bN b1 /\ cont b2 /\ cont b3 /\ cont b4 /\
      n = (((bN b1 - 0xF0) * 64 + (bN b2 - 0x80)) * 64 + (bN b3 - 0x80)) * 64 + (bN b4 - 0x80)
  | _ => False
  end.

Ltac shape_reduce :=
  cbn [one_byte_shape_bits two_byte_shape_bits three_byte_shape_bits four_byte_shape_bits].

(* Case split on exactly the bits that the shape patterns test, in the
   order the compiled matches test them, until every match is decided. *)
Ltac shape_split :=
  shape_reduce;
  repeat match goal with
  | |- context [if ?b then _ else _] => is_var b; destruct b; shape_reduce
  end.

(* What `encoding` computes, in arithmetic terms (about 30 cases). *)
Lemma encoding_form cp :
  match encoding cp with
  | Some s => utf8_form s (U32_to_N cp)
  | None => 0x200000 <= U32_to_N cp
  end.
Proof.
  destruct cp.
  unfold encoding, encoding_if, encoding_two, encoding_three, encoding_four,
    one_byte_shape, two_byte_shape, three_byte_shape, four_byte_shape, U32_to_N.
  cbn [u32_byte4].
  shape_split; cbn [N.b2n utf8_form]; unfold cont; rewrite ?bN_bit8; cbn [N.b2n];
    b2n_bounds; lia.
Qed.

Lemma utf8_form_unique s t n : utf8_form s n -> utf8_form t n -> s = t.
Proof.
  destruct s as [|a1 [|a2 [|a3 [|a4 [|? ?]]]]], t as [|b1 [|b2 [|b3 [|b4 [|? ?]]]]];
    cbn [utf8_form]; unfold cont; try tauto; intros; try lia;
  repeat match goal with a : byte |- _ => pose proof (bN_bound a); generalize dependent a end;
  intros; repeat f_equal; apply bN_inj; lia.
Qed.

(** * The byte-range table of Utf8Ref.v as arithmetic *)

Lemma seq_len_cases n :
  (n <= 0x7F /\ seq_len n = 1%nat) \/
  (0xC2 <= n <= 0xDF /\ seq_len n = 2%nat) \/
  (0xE0 <= n <= 0xEF /\ seq_len n = 3%nat) \/
  (0xF0 <= n <= 0xF4 /\ seq_len n = 4%nat) \/
  (((0x80 <= n <= 0xC1) \/ 0xF5 <= n) /\ seq_len n = 0%nat).
Proof.
  unfold seq_len.
  destruct (N.leb_spec n 0x7F), (N.leb_spec 0xC2 n), (N.leb_spec n 0xDF),
    (N.leb_spec 0xE0 n), (N.leb_spec n 0xEF), (N.leb_spec 0xF0 n), (N.leb_spec n 0xF4);
    cbn [andb]; lia.
Qed.

Lemma lo2_hi2_cases n :
  (n = 0xE0 /\ lo2 n = 0xA0 /\ hi2 n = 0xBF) \/
  (n = 0xED /\ lo2 n = 0x80 /\ hi2 n = 0x9F) \/
  (n = 0xF0 /\ lo2 n = 0x90 /\ hi2 n = 0xBF) \/
  (n = 0xF4 /\ lo2 n = 0x80 /\ hi2 n = 0x8F) \/
  (n <> 0xE0 /\ n <> 0xED /\ n <> 0xF0 /\ n <> 0xF4 /\ lo2 n = 0x80 /\ hi2 n = 0xBF).
Proof.
  unfold lo2, hi2.
  destruct (N.eqb_spec n 0xE0), (N.eqb_spec n 0xED), (N.eqb_spec n 0xF0), (N.eqb_spec n 0xF4);
    lia.
Qed.

Lemma seq_len_le4 n : (seq_len n <= 4)%nat.
Proof. destruct (seq_len_cases n) as [[_ ->]|[[_ ->]|[[_ ->]|[[_ ->]|[_ ->]]]]]; lia. Qed.

Lemma vp_one b : vp [b] = Nat.ltb 0 (seq_len (bN b)).
Proof. unfold vp. cbn [length]. destruct (seq_len (bN b)) as [|[|k]]; reflexivity. Qed.

Lemma vp_one_iff b : vp [b] = true <-> bN b <= 0x7F \/ 0xC2 <= bN b <= 0xF4.
Proof.
  rewrite vp_one, Nat.ltb_lt.
  destruct (seq_len_cases (bN b)) as [[A ->]|[[A ->]|[[A ->]|[[A ->]|[A ->]]]]]; lia.
Qed.

Lemma vs_one_iff b : vs [b] = true <-> bN b <= 0x7F.
Proof.
  unfold vs. rewrite vp_one. cbn [length].
  destruct (seq_len_cases (bN b)) as [[A ->]|[[A ->]|[[A ->]|[[A ->]|[A ->]]]]];
    cbn; split; intros; lia || discriminate || reflexivity.
Qed.

Lemma vp_cons2 b1 b2 r :
  vp (b1 :: b2 :: r) = true <->
  (2 + length r <= seq_len (bN b1))%nat /\
  lo2 (bN b1) <= bN b2 <= hi2 (bN b1) /\
  Forall (fun b => 0x80 <= bN b <= 0xBF) r.
Proof.
  unfold vp, second_ok, is_cont. cbn [length].
  rewrite !andb_true_iff, Nat.ltb_lt, Nat.leb_le, !N.leb_le, forallb_forall, Forall_forall.
  setoid_rewrite andb_true_iff. setoid_rewrite N.leb_le.
  assert (forall k, (0 < k /\ 2 + length r <= k <-> 2 + length r <= k)%nat) as -> by lia.
  reflexivity.
Qed.

Lemma vs_vp_len s : vs s = true <-> vp s = true /\
  match s with [] => False | b1 :: _ => length s = seq_len (bN b1) end.
Proof.
  unfold vs. destruct s as [|b1 r]; [cbn; split; [discriminate|tauto]|].
  rewrite andb_true_iff, Nat.eqb_eq; tauto.
Qed.

Lemma vp_len_lead b1 r : vp (b1 :: r) = true -> (length (b1 :: r) <= seq_len (bN b1))%nat.
Proof. unfold vp. rewrite !andb_true_iff, Nat.leb_le. tauto. Qed.

Lemma vp_len s : vp s = true -> (length s <= 4)%nat.
Proof.
  destruct s as [|b1 r]; [discriminate|]. intros H.
  pose proof (vp_len_lead _ _ H). pose proof (seq_len_le4 (bN b1)). lia.
Qed.

Lemma vp_app s t : vp (s ++ t) = true -> s <> [] -> vp s = true.
Proof.
  destruct s as [|b1 [|b2 r]]; [congruence| |]; intros H _.
  - apply vp_one_iff. cbn [app] in H. pose proof (vp_len_lead _ _ H).
    destruct (seq_len_cases (bN b1)) as [[A E]|[[A E]|[[A E]|[[A E]|[A E]]]]];
      rewrite E in *; cbn [length] in *; lia.
  - cbn [app] in H. rewrite vp_cons2, Forall_app, length_app in H. apply vp_cons2.
    destruct H as (A & B & C & _). repeat split; auto; lia.
Qed.

Lemma vs_vp s : vs s = true -> vp s = true.
Proof. rewrite vs_vp_len; tauto. Qed.

Lemma vs_prefix_free s t : vs s = true -> vs (s ++ t) = true -> t = [].
Proof.
  rewrite !vs_vp_len. destruct s as [|b1 m]; [tauto|]. cbn [app length].
  rewrite length_app. destruct t; cbn [length]; [reflexivity|lia].
Qed.

(** * Valid sequences are the UTF-8 layouts of scalars *)

Lemma mod_offset x c k : c <= x < c + k -> c mod k = 0 -> x mod k = x - c.
Proof.
  intros H E. replace x with ((x - c) + c) at 1 by lia.
  rewrite N.Div0.add_mod, E, N.add_0_r, N.Div0.mod_mod. apply N.mod_small. lia.
Qed.

(* seq_value takes the low bits with mod; once the byte classes are
   known (table_arith), each mod is a subtraction and lia finishes. *)
Ltac lia_mod :=
  repeat match goal with
  | |- context [?x mod 64] => rewrite (mod_offset x 0x80 64) by (reflexivity || lia)
  | |- context [?x mod 32] => rewrite (mod_offset x 0xC0 32) by (reflexivity || lia)
  | |- context [?x mod 16] => rewrite (mod_offset x 0xE0 16) by (reflexivity || lia)
  | |- context [?x mod 8] => rewrite (mod_offset x 0xF0 8) by (reflexivity || lia)
  end; lia.

(* Turn the byte-range table and seq_value into linear arithmetic:
   explicit length, range facts per byte, the lo2/hi2 case. *)
Ltac table_arith b1 :=
  repeat match goal with a : byte |- _ => pose proof (bN_bound a); generalize dependent a end;
  intros;
  destruct (seq_len_cases (bN b1)) as [[? E]|[[? E]|[[? E]|[[? E]|[? E]]]]];
    rewrite ?E in *; cbn [length] in *;
  destruct (lo2_hi2_cases (bN b1)) as [(? & E2 & E3)|[(? & E2 & E3)|[(? & E2 & E3)|
    [(? & E2 & E3)|(? & ? & ? & ? & E2 & E3)]]]]; rewrite ?E2, ?E3 in *;
  try (exfalso; lia).

Lemma vs_form s : vs s = true -> utf8_form s (seq_value s) /\ scalar_N (seq_value s).
Proof.
  rewrite vs_vp_len. intros [H L]. pose proof (vp_len s H).
  destruct s as [|b1 [|b2 [|b3 [|b4 [|? ?]]]]]; cbn [length] in *; try lia;
    (rewrite vp_one_iff in H || rewrite vp_cons2, ?Forall_cons_iff in H);
    cbn [utf8_form seq_value length] in *; unfold scalar_N, cont;
    table_arith b1; lia_mod.
Qed.

Lemma form_vs s n : utf8_form s n -> scalar_N n -> vs s = true /\ seq_value s = n.
Proof.
  unfold scalar_N. rewrite vs_vp_len.
  destruct s as [|b1 [|b2 [|b3 [|b4 [|? ?]]]]]; cbn [utf8_form]; unfold cont; try tauto;
    intros; cbn [seq_value length];
    rewrite ?vp_one_iff, ?vp_cons2, ?Forall_cons_iff; cbn [length];
    table_arith b1; repeat split; try constructor; lia_mod.
Qed.

Theorem encodes_iff s cp : encodes s cp <-> vs s = true /\ cp = seq_cp s.
Proof.
  unfold encodes, seq_cp. rewrite is_unicode_scalar_iff. split.
  - intros [Hsc Hen]. pose proof (encoding_form cp) as F; rewrite Hen in F.
    destruct (form_vs _ _ F Hsc) as [V ->]. split; [exact V|]. symmetry; apply U32_of_to.
  - intros [V ->]. destruct (vs_form s V) as [F Hsc].
    assert (E : U32_to_N (U32_of_N (seq_value s)) = seq_value s)
      by (apply U32_to_of; unfold scalar_N in Hsc; cbn; lia).
    rewrite E. split; [exact Hsc|].
    pose proof (encoding_form (U32_of_N (seq_value s))) as G; rewrite E in G.
    destruct (encoding _) as [t|]; [|unfold scalar_N in Hsc; lia].
    now rewrite (utf8_form_unique _ _ _ F G).
Qed.

Lemma seq_value_scalar s : vs s = true ->
  seq_value s <= 0x10FFFF /\ ~ (0xD800 <= seq_value s <= 0xDFFF).
Proof. apply vs_form. Qed.

Lemma seq_cp_value s : vs s = true -> U32_to_N (seq_cp s) = seq_value s.
Proof.
  intros H. apply U32_to_of. destruct (seq_value_scalar s H). cbn; lia.
Qed.

(** * Completing a pending prefix *)

(* Bytes that complete a valid sequence prefix to a valid sequence. *)
Definition completion (s : list byte) : list byte :=
  match s with
  | [] => []
  | [b1] => match seq_len (bN b1) with
            | 2%nat => [x80]
            | 3%nat => [byte_of (lo2 (bN b1)); x80]
            | 4%nat => [byte_of (lo2 (bN b1)); x80; x80]
            | _ => []
            end
  | b1 :: _ => repeat x80 (seq_len (bN b1) - length s)
  end.

Lemma pending_completion s : vp s = true -> vs s = false ->
  vs (s ++ completion s) = true /\ seq_value (s ++ completion s) <> 0xFFFD.
Proof.
  intros H1 H2. pose proof (vp_len s H1) as L.
  assert (L2 : match s with [] => False | b1 :: _ => (length s < seq_len (bN b1))%nat end).
  { destruct s as [|b1 r]; [discriminate|]. pose proof (vp_len_lead _ _ H1).
    destruct (Nat.eq_dec (length (b1 :: r)) (seq_len (bN b1))) as [E|]; [|lia].
    assert (vs (b1 :: r) = true) by (apply vs_vp_len; auto). congruence. }
  clear H2. rewrite vs_vp_len.
  destruct s as [|b1 [|b2 [|b3 [|b4 [|? ?]]]]]; cbn [length] in *; try tauto; try lia;
    (rewrite vp_one_iff in H1 || rewrite vp_cons2, ?Forall_cons_iff in H1);
    cbn [completion app]; table_arith b1; cbn [repeat Nat.sub length app] in *;
    rewrite vp_cons2, ?Forall_cons_iff; cbn [seq_value length];
    rewrite ?E, ?E2, ?E3, ?bN_byte_of by lia; change (bN x80) with 128;
    repeat split; try constructor; lia_mod.
Qed.
