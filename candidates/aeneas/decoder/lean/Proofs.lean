/-
Proofs.lean -- proof of `Boundary.Verified` with `Utf8Pure.RefDecoder` as the
witness.  Structure:
  1. byte/code-point conversions; `spec_ok` (spec form -> `= ok`)
  2. byte predicates: each Rust predicate `= ok` the Utf8Ref Bool function
  3. cp2/cp3/cp4 compute `cpOf`
  4. step_fresh / bad_pending / step refine `stepFresh` / `step` (OutRel)
  5. unpack/pack and the state relation `StRel`
  6. the decode_buffer loop (loop.spec_decr_nat), decode_buffer, decode_done
  7. the top-level theorem `verified : Boundary.Verified`
-/
import Boundary
import Utf8Proofs
open Aeneas Aeneas.Std Result Boundary Utf8Pure

namespace DecoderProofs

/-! ## 1. Conversions -/

theorem byte_toNat (x : U8) : (byte x).toNat = x.val := by
  have := x.hBounds
  simp [byte]

theorem codePoint_toNat (x : U32) : (codePoint x).toNat = x.val := by
  have := x.hBounds
  simp [codePoint]

theorem byte_le (x : U8) (c : UInt8) : (c ≤ byte x) ↔ c.toNat ≤ x.val := by
  rw [UInt8.le_iff_toNat_le, byte_toNat]
theorem le_byte (x : U8) (c : UInt8) : (byte x ≤ c) ↔ x.val ≤ c.toNat := by
  rw [UInt8.le_iff_toNat_le, byte_toNat]
theorem byte_eq (x : U8) (c : UInt8) : (byte x = c) ↔ x.val = c.toNat := by
  rw [← UInt8.toNat_inj, byte_toNat]

theorem cp_eq_of (c : U32) (x : UInt32) (h : c.val = x.toNat) : codePoint c = x := by
  rw [← UInt32.toNat_inj, codePoint_toNat, h]

theorem spec_ok {α} {m : Result α} {P : α → Prop} (h : m ⦃ r => P r ⦄) : ∃ r, m = ok r ∧ P r := by
  generalize m = r at h ⊢
  cases r with
  | ret v => exact ⟨v, rfl, by simpa using h⟩
  | vis e k => simp [WP.spec_vis] at h
  | div => simp at h

/-! ## 2. Byte predicates -/

theorem is_cont_eq (b : U8) : decoder.is_cont b = ok (isCont (byte b)) := by
  unfold decoder.is_cont isCont
  split <;> simp [byte_le, le_byte] <;> scalar_tac
theorem is_lead1_eq (b : U8) : decoder.is_lead1 b = ok (isLead1 (byte b)) := by
  unfold decoder.is_lead1 isLead1
  simp [le_byte]
theorem is_lead2_eq (b : U8) : decoder.is_lead2 b = ok (isLead2 (byte b)) := by
  unfold decoder.is_lead2 isLead2
  split <;> simp [byte_le, le_byte] <;> scalar_tac
theorem is_lead3_eq (b : U8) : decoder.is_lead3 b = ok (isLead3 (byte b)) := by
  unfold decoder.is_lead3 isLead3
  split <;> simp [byte_le, le_byte] <;> scalar_tac
theorem is_lead4_eq (b : U8) : decoder.is_lead4 b = ok (isLead4 (byte b)) := by
  unfold decoder.is_lead4 isLead4
  split <;> simp [byte_le, le_byte] <;> scalar_tac

theorem second_ok_eq (b1 b2 : U8) : decoder.second_ok b1 b2 = ok (secondOk (byte b1) (byte b2)) := by
  unfold decoder.second_ok secondOk
  simp only [byte_eq]
  split_ifs <;> simp_all [byte_le, le_byte]

theorem is_lead_multi_eq (b : U8) :
    decoder.is_lead_multi b = ok (isLead2 (byte b) || isLead3 (byte b) || isLead4 (byte b)) := by
  unfold decoder.is_lead_multi
  simp only [is_lead2_eq, is_lead3_eq, is_lead4_eq, bind_ok]
  cases isLead2 (byte b) <;> cases isLead3 (byte b) <;> simp

theorem vs2_eq (b0 b1 : U8) : decoder.vs2 b0 b1 = ok (isVS [byte b0, byte b1]) := by
  unfold decoder.vs2
  simp only [is_lead2_eq, second_ok_eq, bind_ok, isVS]
  cases isLead2 (byte b0) <;> simp

theorem vsp2_eq (b0 b1 : U8) : decoder.vsp2 b0 b1 = ok (isVSP [byte b0, byte b1]) := by
  unfold decoder.vsp2
  simp only [is_lead_multi_eq, second_ok_eq, bind_ok, isVSP]
  cases (isLead2 (byte b0) || isLead3 (byte b0) || isLead4 (byte b0)) <;> simp

theorem vs3_eq (b0 b1 b2 : U8) : decoder.vs3 b0 b1 b2 = ok (isVS [byte b0, byte b1, byte b2]) := by
  unfold decoder.vs3
  simp only [is_lead3_eq, second_ok_eq, is_cont_eq, bind_ok, isVS]
  cases isLead3 (byte b0) <;> cases secondOk (byte b0) (byte b1) <;> simp

theorem vsp3_eq (b0 b1 b2 : U8) : decoder.vsp3 b0 b1 b2 = ok (isVSP [byte b0, byte b1, byte b2]) := by
  unfold decoder.vsp3
  simp only [is_lead3_eq, is_lead4_eq, second_ok_eq, is_cont_eq, bind_ok, isVSP]
  cases isLead3 (byte b0) <;> cases isLead4 (byte b0) <;> cases secondOk (byte b0) (byte b1) <;> simp

theorem vs4_eq (b0 b1 b2 b3 : U8) :
    decoder.vs4 b0 b1 b2 b3 = ok (isVS [byte b0, byte b1, byte b2, byte b3]) := by
  unfold decoder.vs4
  simp only [is_lead4_eq, second_ok_eq, is_cont_eq, bind_ok, isVS]
  cases isLead4 (byte b0) <;> cases secondOk (byte b0) (byte b1) <;> cases isCont (byte b2) <;> simp

/-! ## 3. Code points -/

theorem cp2_spec (b0 b1 : U8) : decoder.cp2 b0 b1 ⦃ c => codePoint c = cpOf [byte b0, byte b1] ⦄ := by
  unfold decoder.cp2
  step*
  apply cp_eq_of
  rw [cpOf_two, byte_toNat, byte_toNat]
  scalar_tac

theorem cp3_spec (b0 b1 b2 : U8) :
    decoder.cp3 b0 b1 b2 ⦃ c => codePoint c = cpOf [byte b0, byte b1, byte b2] ⦄ := by
  unfold decoder.cp3
  step*
  apply cp_eq_of
  rw [cpOf_three, byte_toNat, byte_toNat, byte_toNat]
  scalar_tac

theorem cp4_spec (b0 b1 b2 b3 : U8) :
    decoder.cp4 b0 b1 b2 b3 ⦃ c => codePoint c = cpOf [byte b0, byte b1, byte b2, byte b3] ⦄ := by
  unfold decoder.cp4
  step*
  apply cp_eq_of
  rw [cpOf_four, byte_toNat, byte_toNat, byte_toNat, byte_toNat]
  scalar_tac

theorem codePoint_cast (b : U8) : codePoint (UScalar.cast .U32 b) = cpOf [byte b] := by
  apply cp_eq_of
  rw [cpOf_one, byte_toNat]
  scalar_tac

theorem codePoint_replacement : codePoint decoder.REPLACEMENT = replacement_char := by
  unfold decoder.REPLACEMENT; rfl

theorem byte_zero : byte 0#u8 = 0 := rfl


/-! ## 4. One step -/

/-- The Rust pending-bytes record holds the list `s` (unused bytes are 0). -/
def PendRel (p : decoder.Pend) (s : List UInt8) : Prop :=
  p.n.val = s.length ∧ [byte p.b0, byte p.b1, byte p.b2] = s ++ List.replicate (3 - s.length) 0

/-- The code points a Rust `Out` emits. -/
def outText (o : decoder.Out) : Text := [codePoint o.c0, codePoint o.c1].take o.n.val

def OutRel (o : decoder.Out) (r : State × Text) : Prop :=
  PendRel o.p r.1 ∧ o.n.val ≤ 2 ∧ outText o = r.2

theorem empty_eq : decoder.EMPTY = { n := 0#u8, b0 := 0#u8, b1 := 0#u8, b2 := 0#u8 } := by
  unfold decoder.EMPTY; rfl

theorem step_fresh_eq (b : U8) :
    ∃ o, decoder.step_fresh b = ok o ∧ OutRel o (stepFresh (byte b)) ∧ o.n.val ≤ 1 := by
  unfold decoder.step_fresh stepFresh
  simp only [is_lead1_eq, is_lead_multi_eq, bind_ok, lift, decoder.emit, decoder.hold]
  have e1 : isVS [byte b] = isLead1 (byte b) := rfl
  have e2 : isVSP [byte b] = (isLead1 (byte b) || (isLead2 (byte b) || isLead3 (byte b) || isLead4 (byte b))) := by
    simp [isVSP, Bool.or_assoc]
  rw [e1, e2]
  cases h1 : isLead1 (byte b) <;> cases h2 : (isLead2 (byte b) || isLead3 (byte b) || isLead4 (byte b)) <;>
    simp [OutRel, PendRel, outText, empty_eq, codePoint_cast, codePoint_replacement, byte_zero]


theorem bad_pending_eq (b : U8) :
    ∃ o, decoder.bad_pending b = ok o ∧
      OutRel o ((stepFresh (byte b)).1, replacement_char :: (stepFresh (byte b)).2) := by
  obtain ⟨f, hf, ⟨hp, _, ht⟩, hn⟩ := step_fresh_eq b
  unfold decoder.bad_pending
  rw [hf, bind_ok]
  have := spec_ok (m := f.n + 1#u8) (P := fun i => i.val = f.n.val + 1) (by step*)
  obtain ⟨i, hi, hiv⟩ := this
  rw [hi, bind_ok]
  refine ⟨_, rfl, hp, by simp; omega, ?_⟩
  rw [← ht]
  simp only [outText, hiv, codePoint_replacement]
  rcases Nat.lt_or_ge f.n.val 1 with h | h
  · have : f.n.val = 0 := by omega
    simp [this]
  · have : f.n.val = 1 := by omega
    simp [this]


theorem emit_rel (c : U32) (x : UInt32) (h : codePoint c = x) :
    OutRel { p := decoder.EMPTY, n := 1#u8, c0 := c, c1 := 0#u32 } ([], [x]) := by
  simp [OutRel, PendRel, outText, empty_eq, byte_zero, h]

theorem step_eq (p : decoder.Pend) (s : State) (hs : PendRel p s) (b : U8) :
    ∃ o, decoder.step p b = ok o ∧ OutRel o (Utf8Pure.step s (byte b)) := by
  unfold PendRel at hs
  obtain ⟨hn, hb⟩ := hs
  rcases s with _ | ⟨a, _ | ⟨a2, _ | ⟨a3, _ | ⟨a4, t⟩⟩⟩⟩
  · -- no pending bytes
    have h0 : p.n = 0#u8 := by simp at hn; scalar_tac
    unfold decoder.step
    rw [step_nil]
    simp only [h0, ↓reduceIte]
    obtain ⟨o, ho, hr, _⟩ := step_fresh_eq b
    exact ⟨o, ho, hr⟩
  · -- one pending byte
    simp at hn hb
    obtain ⟨rfl, h1, h2⟩ := hb
    have h0 : ¬ p.n = 0#u8 := by scalar_tac
    have h1' : p.n = 1#u8 := by scalar_tac
    unfold decoder.step Utf8Pure.step
    simp only [h0, h1', ↓reduceIte, vs2_eq, vsp2_eq, bind_ok, List.cons_append, List.nil_append]
    cases hv : isVS [byte p.b0, byte b]
    · cases hp : isVSP [byte p.b0, byte b]
      · simp only [Bool.false_eq_true, ↓reduceIte, List.isEmpty_cons]
        exact bad_pending_eq b
      · simp only [Bool.false_eq_true, ↓reduceIte, decoder.hold]
        refine ⟨_, rfl, ?_⟩
        simp [OutRel, PendRel, outText, byte_zero]
    · obtain ⟨c, hc, hcv⟩ := spec_ok (cp2_spec p.b0 b)
      simp only [↓reduceIte, hc, bind_ok, decoder.emit]
      exact ⟨_, rfl, emit_rel c _ hcv⟩
  · -- two pending bytes
    simp at hn hb
    obtain ⟨rfl, rfl, h2⟩ := hb
    have h0 : ¬ p.n = 0#u8 := by scalar_tac
    have h1' : ¬ p.n = 1#u8 := by scalar_tac
    have h2' : p.n = 2#u8 := by scalar_tac
    unfold decoder.step Utf8Pure.step
    simp only [h0, h1', h2', ↓reduceIte, vs3_eq, vsp3_eq, bind_ok, List.cons_append, List.nil_append]
    cases hv : isVS [byte p.b0, byte p.b1, byte b]
    · cases hp : isVSP [byte p.b0, byte p.b1, byte b]
      · simp only [Bool.false_eq_true, ↓reduceIte, List.isEmpty_cons]
        exact bad_pending_eq b
      · simp only [Bool.false_eq_true, ↓reduceIte, decoder.hold]
        refine ⟨_, rfl, ?_⟩
        simp [OutRel, PendRel, outText, byte_zero]
    · obtain ⟨c, hc, hcv⟩ := spec_ok (cp3_spec p.b0 p.b1 b)
      simp only [↓reduceIte, hc, bind_ok, decoder.emit]
      exact ⟨_, rfl, emit_rel c _ hcv⟩
  · -- three pending bytes
    simp at hn hb
    obtain ⟨rfl, rfl, rfl⟩ := hb
    have h0 : ¬ p.n = 0#u8 := by scalar_tac
    have h1' : ¬ p.n = 1#u8 := by scalar_tac
    have h2' : ¬ p.n = 2#u8 := by scalar_tac
    unfold decoder.step Utf8Pure.step
    simp only [h0, h1', h2', ↓reduceIte, vs4_eq, bind_ok, List.cons_append, List.nil_append]
    have e : isVSP [byte p.b0, byte p.b1, byte p.b2, byte b] = isVS [byte p.b0, byte p.b1, byte p.b2, byte b] := rfl
    rw [e]
    cases hv : isVS [byte p.b0, byte p.b1, byte p.b2, byte b]
    · simp only [Bool.false_eq_true, ↓reduceIte, List.isEmpty_cons]
      exact bad_pending_eq b
    · obtain ⟨c, hc, hcv⟩ := spec_ok (cp4_spec p.b0 p.b1 p.b2 b)
      simp only [↓reduceIte, hc, bind_ok, decoder.emit]
      exact ⟨_, rfl, emit_rel c _ hcv⟩
  · -- four or more: impossible
    simp at hb


/-! ## 5. Output writes -/

theorem writes_nil (out : Slice U32) : WritesText out out 0#usize [] := by
  simp [WritesText]

theorem writes_one (out0 out1 : Slice U32) (k : Usize) (t : Text) (h : WritesText out0 out1 k t)
    (hk : k.val < out1.length) (c : U32) (k' : Usize) (hk' : k'.val = k.val + 1) :
    WritesText out0 (out1.set k c) k' (t ++ [codePoint c]) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  have hl : out1.val.length = out1.length := rfl
  refine ⟨by simp [hk', h1], ?_, ?_, ?_⟩
  · simp [Slice.length, Slice.set_val_eq] at *; omega
  · rw [Slice.set_val_eq, List.set_eq_take_append_cons_drop, if_pos (by omega)]
    rw [List.length_append, List.length_singleton, ← h1, List.take_append]
    have hA : (out1.val.take k.val).length = k.val := by simp; omega
    rw [hA, List.take_of_length_le (by omega), Nat.add_sub_cancel_left]
    simp [h1, h3]
  · rw [Slice.set_val_eq, List.length_append, ← h1, List.length_singleton, List.drop_set_of_lt (by omega)]
    have := congrArg (List.drop 1) h4
    simpa [List.drop_drop, h1, Nat.add_comm] using this


/-! ## 6. The decode_buffer loop -/

theorem decodeBuffer_snoc (s : State) (l : List UInt8) (b : UInt8) :
    decodeBuffer s (l ++ [b]) =
      ((step (decodeBuffer s l).1 b).1, (decodeBuffer s l).2 ++ (step (decodeBuffer s l).1 b).2) := by
  simp [decodeBuffer, List.foldl_append, stepAcc]

theorem bytes_take_succ (input : Slice U8) (i : Nat) (h : i < input.length) :
    (bytes input).take (i + 1) = (bytes input).take i ++ [byte (input.val[i]'h)] := by
  have h' : i < (bytes input).length := by simp [bytes, Slice.length] at *; exact h
  rw [List.take_succ, List.getElem?_eq_getElem h']
  simp [bytes]

/-- Loop invariant: after `i` bytes, the Rust state holds the reference state
and `out` holds the reference text so far. -/
def LoopInv (input : Slice U8) (out0 : Slice U32) (s0 : State)
    (x : Slice U32 × decoder.Pend × Usize × Usize) : Prop :=
  x.2.2.1.val ≤ input.length ∧ x.2.2.2.val ≤ 2 * x.2.2.1.val ∧
  PendRel x.2.1 (decodeBuffer s0 ((bytes input).take x.2.2.1.val)).1 ∧
  WritesText out0 x.1 x.2.2.2 (decodeBuffer s0 ((bytes input).take x.2.2.1.val)).2

theorem loop_spec (input : Slice U8) (out0 : Slice U32) (s0 : State)
    (hout : 2 * input.length ≤ out0.length)
    (x : Slice U32 × decoder.Pend × Usize × Usize) (hx : LoopInv input out0 s0 x) :
    decoder.decode_buffer_loop input x.1 x.2.1 x.2.2.1 x.2.2.2 ⦃ r =>
      PendRel r.2.1 (decodeBuffer s0 (bytes input)).1 ∧
      WritesText out0 r.1 r.2.2 (decodeBuffer s0 (bytes input)).2 ⦄ := by
  unfold decoder.decode_buffer_loop
  apply loop.spec_decr_nat (measure := fun x => input.length - x.2.2.1.val) (inv := LoopInv input out0 s0)
  · rintro ⟨out1, p1, i1, k1⟩ ⟨hi, hk, hp, hw⟩
    simp only at hi hk hp hw
    simp only [decoder.decode_buffer_loop.body]
    split
    · rename_i hlt
      have hlt' : i1.val < input.length := by scalar_tac
      step as ⟨x, hx⟩
      obtain ⟨o, ho, hrel⟩ := step_eq p1 _ hp x
      simp only [ho, bind_ok]
      have hl := hw.2.1
      have hx' : byte x = byte (input.val[i1.val]'hlt') := by rw [hx]
      have hnext : decodeBuffer s0 ((bytes input).take (i1.val + 1)) =
          ((step (decodeBuffer s0 (List.take (↑i1) (bytes input))).1 (byte x)).1,
           (decodeBuffer s0 (List.take (↑i1) (bytes input))).2 ++
             (step (decodeBuffer s0 (List.take (↑i1) (bytes input))).1 (byte x)).2) := by
        rw [bytes_take_succ input _ hlt', decodeBuffer_snoc, hx']
      generalize decodeBuffer s0 (List.take (↑i1) (bytes input)) = R at hp hw hrel hnext
      obtain ⟨hop, hon, hot⟩ := hrel
      generalize step R.1 (byte x) = st at hop hot hnext
      have hkl : k1.val + o.n.val ≤ out1.length := by omega
      rcases (by omega : o.n.val = 0 ∨ o.n.val = 1 ∨ o.n.val = 2) with h0 | h1 | h2
      · have : ¬ (o.n ≥ 1#u8) := by scalar_tac
        simp only [this, ↓reduceIte, bind_ok]
        step*
        unfold LoopInv
        simp only [i3_post, hnext]
        simp [outText, h0] at hot
        rw [hot, List.append_nil]
        refine ⟨⟨by omega, by omega, hop, hw⟩, by omega⟩
      · have : (o.n ≥ 1#u8) := by scalar_tac
        have : ¬ (o.n ≥ 2#u8) := by scalar_tac
        simp only [*, ↓reduceIte, bind_ok]
        step*
        rcases x with ⟨xa, back⟩
        simp only at x_post1
        subst x_post1
        step as ⟨k2, hk2⟩
        step as ⟨i3, i3_post⟩
        unfold LoopInv
        simp only [i3_post, hnext]
        simp [outText, h1] at hot
        rw [← hot]
        refine ⟨⟨by omega, by omega, hop, writes_one _ _ _ _ hw (by omega) _ _ hk2⟩, by omega⟩
      · have : (o.n ≥ 1#u8) := by scalar_tac
        have : (o.n ≥ 2#u8) := by scalar_tac
        simp only [*, ↓reduceIte, bind_ok]
        step*
        rcases x with ⟨xa, back⟩
        simp only at x_post1
        subst x_post1
        step as ⟨k2, hk2⟩
        have hlen : (out1.set k1 o.c0).length = out1.length := by
          simp [Slice.length, Slice.set_val_eq]
        step as ⟨s2, hs2⟩
        step as ⟨k3, hk3⟩
        step as ⟨i3, i3_post⟩
        unfold LoopInv
        simp only [i3_post, hnext, hs2]
        simp [outText, h2] at hot
        rw [← hot]
        have w1 := writes_one _ _ _ _ hw (by omega) o.c0 k2 hk2
        have w2 := writes_one _ _ _ _ w1 (by omega) o.c1 k3 hk3
        rw [List.append_assoc] at w2
        refine ⟨⟨by omega, by omega, hop, w2⟩, by omega⟩
    · rename_i hge
      have hi' : i1.val = input.length := by scalar_tac
      have htk : (bytes input).take i1.val = bytes input := by
        rw [hi']; apply List.take_of_length_le; simp [bytes, Slice.length]
      rw [htk] at hp hw
      simp only [WP.spec_ok]
      exact ⟨hp, hw⟩
  · exact hx


/-! ## 7. State packing and the entry points -/

/-- The Rust `u32` state `v` holds the reference state `s`. -/
def StRel (s : State) (v : U32) : Prop :=
  Pending s ∧ ∃ p : decoder.Pend, PendRel p s ∧
    v.val = p.n.val + 256 * p.b0.val + 65536 * p.b1.val + 16777216 * p.b2.val

theorem unpack_spec (v : U32) : decoder.unpack v ⦃ q =>
    q.n.val = v.val % 256 ∧ q.b0.val = v.val / 256 % 256 ∧ q.b1.val = v.val / 65536 % 256 ∧
    q.b2.val = v.val / 16777216 ⦄ := by
  unfold decoder.unpack
  step*
  simp only [*]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> scalar_tac

theorem pack_spec (q : decoder.Pend) : decoder.pack q ⦃ v =>
    v.val = q.n.val + 256 * q.b0.val + 65536 * q.b1.val + 16777216 * q.b2.val ⦄ := by
  unfold decoder.pack
  step*

theorem pendRel_congr (p q : decoder.Pend) (s : State) (h : PendRel p s)
    (hn : q.n.val = p.n.val) (h0 : q.b0.val = p.b0.val) (h1 : q.b1.val = p.b1.val)
    (h2 : q.b2.val = p.b2.val) : PendRel q s := by
  unfold PendRel byte at *
  rw [hn, h0, h1, h2]; exact h

theorem decode_buffer_eq (s : State) (v : U32) (input : Slice U8) (out : Slice U32)
    (hR : StRel s v) (hout : 2 * input.length ≤ out.length) :
    ∃ (v' : U32) (k : Usize) (out' : Slice U32),
      decoder.decode_buffer v input out = ok ((v', k), out') ∧
      StRel (decodeBuffer s (bytes input)).1 v' ∧
      WritesText out out' k (decodeBuffer s (bytes input)).2 := by
  obtain ⟨hpend, p, hp, hv⟩ := hR
  have hpb := p.n.hBounds; have h0b := p.b0.hBounds; have h1b := p.b1.hBounds; have h2b := p.b2.hBounds
  obtain ⟨q, hq, hqn, hq0, hq1, hq2⟩ := spec_ok (unpack_spec v)
  have hqp : PendRel q s := pendRel_congr p q s hp (by scalar_tac) (by scalar_tac) (by scalar_tac) (by scalar_tac)
  have inv0 : LoopInv input out s (out, q, 0#usize, 0#usize) := by
    refine ⟨by simp, by simp, ?_, ?_⟩
    · simpa [decodeBuffer] using hqp
    · simpa [decodeBuffer] using writes_nil out
  obtain ⟨r, hr, hrp, hrw⟩ := spec_ok (loop_spec input out s hout _ inv0)
  obtain ⟨v', hv', hv'v⟩ := spec_ok (pack_spec r.2.1)
  refine ⟨v', r.2.2, r.1, ?_, ⟨decodeBuffer_pending s _ hpend, r.2.1, hrp, hv'v⟩, hrw⟩
  unfold decoder.decode_buffer
  rw [hq, bind_ok, hr, bind_ok]
  rcases r with ⟨o1, p1, k1⟩
  show (do let i ← decoder.pack p1; ok ((i, k1), o1)) = _
  rw [hv']
  simp

theorem decode_done_eq (s : State) (v : U32) (out : Slice U32) (hR : StRel s v)
    (hout : 1 ≤ out.length) :
    ∃ (k : Usize) (out' : Slice U32),
      decoder.decode_done v out = ok (k, out') ∧ WritesText out out' k (decodeDone s) := by
  obtain ⟨hpend, p, hp, hv⟩ := hR
  have hpb := p.n.hBounds; have h0b := p.b0.hBounds; have h1b := p.b1.hBounds; have h2b := p.b2.hBounds
  have hmod : v.val % 256 = s.length := by rw [← hp.1]; scalar_tac
  have key : decoder.decode_done v out ⦃ r => WritesText out r.2 r.1 (decodeDone s) ⦄ := by
    unfold decoder.decode_done
    step*
    · have : s = [] := by
        apply List.eq_nil_of_length_eq_zero; scalar_tac
      subst this
      simp [decodeDone, writes_nil]
    · have : s ≠ [] := by
        intro h; subst h; simp at hmod; scalar_tac
      rw [decodeDone_pending s this]
      have := writes_one out out 0#usize [] (writes_nil out) (by simp; scalar_tac) decoder.REPLACEMENT 1#usize (by simp)
      rw [out1_post]
      simpa [codePoint_replacement] using this
  obtain ⟨r, hr, hw⟩ := spec_ok key
  exact ⟨r.1, r.2, hr, hw⟩

theorem start_eq : decoder.decode_start_state = ok 0#u32 ∧ StRel [] 0#u32 := by
  refine ⟨rfl, Or.inl rfl, { n := 0#u8, b0 := 0#u8, b1 := 0#u8, b2 := 0#u8 }, ?_, by simp⟩
  simp [PendRel, byte_zero]

/-! ## 8. The top-level theorem -/

theorem realizes : Realizes RefDecoder :=
  ⟨StRel, ⟨0#u32, start_eq.1, start_eq.2⟩,
   fun s v input out hR hout => decode_buffer_eq s v input out hR hout,
   fun s v out hR hout => decode_done_eq s v out hR hout⟩

theorem verified : Verified := ⟨RefDecoder, RefDecoder_correct, realizes⟩

end DecoderProofs
