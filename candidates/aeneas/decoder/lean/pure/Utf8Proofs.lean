/-
Utf8Proofs.lean -- main file of the shared pure layer (namespace `Utf8Pure`).

Files (import order): Utf8Laws (the spec, byte-identical copy of
../spec-lean/Utf8Laws.lean) -> Utf8Bits -> Utf8Ref -> Utf8Table -> Utf8Proofs.

EXPORTED DEFINITIONS (Utf8Ref.lean; stable)
  isCont isLead1 isLead2 isLead3 isLead4 : UInt8 -> Bool   byte-range classes
  secondOk b1 b2 : Bool       restricted second byte after E0/ED/F0/F4
  isVS  : List UInt8 -> Bool  whole valid sequence (Unicode Table 3-7)
  isVSP : List UInt8 -> Bool  valid sequence prefix
  cpOf  : List UInt8 -> UInt32  code point of a valid sequence, shift/mask form
  State := List UInt8         pending bytes ([] or a VSP that is not a VS)
  stepFresh, step : State -> UInt8 -> State x Text
  stepAcc, decodeBuffer (List.foldl stepAcc), decodeDone
  RefDecoder : Decoder
 (Utf8Proofs.lean)
  run       right-recursive form of decodeBuffer (decodeBuffer_eq)
  decodeAll pure whole-buffer decoder (decodes_iff)
  Pending   state invariant
 (Utf8Bits.lean) enc32, encoding_eq : encoding cp = if cp.toNat < 0x200000 then some (enc32 cp) else none
 (Utf8Table.lean) completion (bytes completing a pending state)
 Each file's header lists its own exports.

SPEC LAWS (each `<law>_proved : <law>`)
  bit8_value_sum_proved bit8_value_word_proved u32_byte4_bits_proved
  is_surrogate_code_point_examples_proved begins_with_scalar_unique_proved
  not_valid_sequence_prefix_extended_proved maximal_subpart_exists_proved
  maximal_subpart_unique_proved decodes_first_exists_proved
  decodes_first_unique_proved decodes_first_empty_proved
  decodes_first_nonempty_proved decodes_exists_proved decodes_unique_proved
  decodes_examples_proved
STREAMING
  utf8_decodes_RefDecoder utf8_decode_buffer_safe_RefDecoder
  utf8_decode_buffer_prompt_RefDecoder
  RefDecoder_correct : Decoder.Correct RefDecoder

SUPPORTING LEMMAS
  table:   encodes_iff (encodes seq cp <-> isVS seq ∧ cp = cpOf seq),
           isVS_iff (is_valid_sequence), isVSP_iff (is_valid_sequence_prefix),
           encodes_one/two/three/four (ranges + shift/mask value per length),
           is_unicode_scalar_iff (toNat form), cpOf_one..four (toNat form),
           secondOk_iff, isCont_iff, isLead1..4_iff, lead1_not..lead3_not, isVS_isVSP, isVSP_prefix, isVS_not_proper,
           isVSP_of_isVS_append, isVSP_extends, completion_spec, isVS_length
  step:    step_nil, step_complete, step_extend, step_bad_fresh,
           step_bad_pending, decodeBuffer_nil, decodeBuffer_cons,
           decodeBuffer_eq, run_append, feed_eq, decoded_eq, decoded_so_far_eq
  state:   step_pending, run_pending, decodeBuffer_pending, pending_length (≤ 3)
  output:  step_out_scalar, run_out_scalar, decodeBuffer_out_scalar,
           decodeDone_out_scalar, decoded_scalar (every output code point is a
           Unicode scalar; U+FFFD is one: replacement_char_scalar)
  decoding: decodes_decodeAll, decodes_iff, run_decodes, run_complete,
           df_scalar, df_fresh_bad, df_pending_bad, df_pending_end

TRUST: everything is kernel-checked (decide, omega, simp); no bv_decide or
native code.  Axioms: at most propext, Classical.choice, Quot.sound.
Arithmetic bridges: Utf8Bits one/two/three/four_shape (tuple-of-bools shapes
-> Nat arithmetic on cp.toNat), Utf8Table cpOf_one/two/three/four
(shift/mask cpOf -> Nat arithmetic), secondOk_iff, isLead*_iff, isCont_iff.
CHECK TIME: about 6 s per Lean version for the whole layer (was 57 s); see
IMPROVEMENT.txt for what made the first version slow.
-/
import Utf8Table

namespace Utf8Pure

/-! ## Spec-internal bit laws -/

theorem bit8_value_sum_proved : bit8_value_sum := by
  unfold bit8_value_sum; decide

theorem bit8_value_word_proved : bit8_value_word := by
  unfold bit8_value_word; decide

theorem u32_byte4_bits_proved : u32_byte4_bits := by
  intro b31 b30 b29 b28 b27 b26 b25 b24 b23 b22 b21 b20 b19 b18 b17 b16 b15 b14 b13 b12 b11 b10 b9 b8
    b7 b6 b5 b4 b3 b2 b1 b0
  simp only [u32_byte4, BitVec.getLsbD_ofBoolListLE]
  rfl

theorem is_surrogate_code_point_examples_proved : is_surrogate_code_point_examples := by
  unfold is_surrogate_code_point_examples; decide

/-! ## Spec predicates ⇔ table predicates -/

theorem isVS_iff (seq : List UInt8) : is_valid_sequence seq ↔ isVS seq = true :=
  ⟨fun ⟨_, h⟩ => (isVS_of_encodes _ _ h).1, fun h => ⟨_, encodes_of_isVS _ h⟩⟩

theorem isVSP_iff (l : List UInt8) : is_valid_sequence_prefix l ↔ isVSP l = true := by
  cases l with
  | nil => simp [is_valid_sequence_prefix, isVSP]
  | cons b more =>
    simp only [is_valid_sequence_prefix, isVS_iff]
    exact ⟨fun ⟨r, h⟩ => isVSP_of_isVS_append _ r (by simp) h, fun h => isVSP_extends _ h⟩

theorem isVSP_prefix (l m : List UInt8) (hne : l ≠ []) (h : isVSP (l ++ m) = true) :
    isVSP l = true := by
  obtain ⟨r, hr⟩ := isVSP_extends _ h
  exact isVSP_of_isVS_append l (m ++ r) hne (by simpa using hr)

/-- Two valid sequences at the front of the same bytes are equal. -/
theorem vs_front_eq (s1 s2 r1 r2 : List UInt8) (h1 : isVS s1 = true) (h2 : isVS s2 = true)
    (h : s1 ++ r1 = s2 ++ r2) : s1 = s2 := by
  rcases List.append_eq_append_iff.mp h with ⟨a, hs, _⟩ | ⟨c, hs, _⟩
  · cases a with
    | nil => simpa using hs.symm
    | cons x e =>
      have := isVS_not_proper s1 x e h1
      rw [← hs, isVS_isVSP _ h2] at this; cases this
  · cases c with
    | nil => simpa using hs
    | cons x e =>
      have := isVS_not_proper s2 x e h2
      rw [← hs, isVS_isVSP _ h1] at this; cases this

theorem begins_with_scalar_unique_proved : begins_with_scalar_unique := by
  intro bytes cp1 r1 cp2 r2 ⟨s1, e1, h1⟩ ⟨s2, e2, h2⟩
  rw [encodes_iff] at e1 e2
  have hs := vs_front_eq s1 s2 r1 r2 e1.1 e2.1 (h1.trans h2.symm)
  subst hs
  exact ⟨e1.2.trans e2.2.symm, List.append_cancel_left (h1.trans h2.symm)⟩

theorem not_valid_sequence_prefix_extended_proved : not_valid_sequence_prefix_extended := by
  intro b1 more extra h hext
  rw [isVSP_iff] at h hext
  exact h (isVSP_prefix _ _ (by simp) hext)

theorem maximal_subpart_lt (b1 : UInt8) (more s : List UInt8) (x : UInt8) (e : List UInt8)
    (h1 : maximal_subpart b1 more s) (h2 : maximal_subpart b1 more (s ++ x :: e)) : False := by
  obtain ⟨_, v1, m1⟩ := h1
  obtain ⟨p2, v2, _⟩ := h2
  have hn := m1 x e p2
  rcases v2 with v2 | v2
  · exact hn v2
  · have : s = [] := by
      cases s with
      | nil => rfl
      | cons y t => simp at v2
    subst this
    rcases v1 with v1 | v1
    · simp [is_valid_sequence_prefix] at v1
    · cases v1

theorem maximal_subpart_unique_proved : maximal_subpart_unique := by
  intro b1 more s1 s2 h1 h2
  obtain ⟨t1, ht1⟩ := h1.1
  obtain ⟨t2, ht2⟩ := h2.1
  rcases List.append_eq_append_iff.mp (ht1.trans ht2.symm) with ⟨a, hs, _⟩ | ⟨c, hs, _⟩
  · cases a with
    | nil => simpa using hs.symm
    | cons x e => subst hs; exact (maximal_subpart_lt b1 more s1 x e h1 h2).elim
  · cases c with
    | nil => simpa using hs
    | cons x e => subst hs; exact (maximal_subpart_lt b1 more s2 x e h2 h1).elim

/-! ## The four ways the first code point is decided -/

theorem df_replaced (b1 : UInt8) (more s rest : List UInt8) (hs : s ++ rest = b1 :: more)
    (hv : isVSP s = true ∨ s = [b1])
    (hlong : ∀ c extra, is_prefix (s ++ c :: extra) (b1 :: more) → isVSP (s ++ c :: extra) = false)
    (hno : ∀ seq rest', seq ++ rest' = b1 :: more → isVS seq = false) :
    decodes_first (b1 :: more) (some (replacement_char, rest)) := by
  refine Or.inr ⟨?_, s, rest, ⟨⟨rest, hs⟩, ?_, ?_⟩, hs, rfl⟩
  · intro cp rest' ⟨seq, enc, eq⟩
    have := (encodes_iff _ _).1 enc
    rw [hno seq rest' eq] at this; cases this.1
  · rw [isVSP_iff]; exact hv
  · intro c extra hp; rw [isVSP_iff, hlong c extra hp]; simp

theorem df_scalar (q r : List UInt8) (h : isVS q = true) :
    decodes_first (q ++ r) (some (cpOf q, r)) := by
  cases q with
  | nil => cases h
  | cons a q' => exact Or.inl ⟨cpOf (a :: q'), r, ⟨a :: q', encodes_of_isVS _ h, rfl⟩, rfl⟩

theorem df_fresh_bad (b : UInt8) (r : List UInt8) (h : isVSP [b] = false) :
    decodes_first (b :: r) (some (replacement_char, r)) := by
  apply df_replaced b r [b] r rfl (Or.inr rfl)
  · intro c extra _
    apply Bool.eq_false_iff.mpr; intro hv
    rw [isVSP_prefix [b] _ (by simp) hv] at h; cases h
  · intro seq rest' eq
    cases seq with
    | nil => rfl
    | cons x e =>
      simp only [List.cons_append, List.cons.injEq] at eq
      obtain ⟨rfl, _⟩ := eq
      apply Bool.eq_false_iff.mpr; intro hv
      rw [isVSP_of_isVS_append [x] e (by simp) hv] at h; cases h

theorem df_pending_bad (p : List UInt8) (b : UInt8) (r : List UInt8) (hne : p ≠ [])
    (hp : isVSP p = true) (hpv : isVS p = false) (hb : isVSP (p ++ [b]) = false) :
    decodes_first (p ++ b :: r) (some (replacement_char, b :: r)) := by
  obtain ⟨a, p', rfl⟩ := List.exists_cons_of_ne_nil hne
  rw [List.cons_append]
  apply df_replaced a (p' ++ b :: r) (a :: p') (b :: r) rfl (Or.inl hp)
  · intro c extra ⟨t, ht⟩
    rw [← List.cons_append, List.append_assoc] at ht
    have ht := List.append_cancel_left ht
    simp only [List.cons_append, List.cons.injEq] at ht
    obtain ⟨rfl, _⟩ := ht
    apply Bool.eq_false_iff.mpr; intro hv
    rw [isVSP_prefix (a :: p' ++ [c]) extra (by simp) (by simpa using hv)] at hb; cases hb
  · intro seq rest' eq
    rw [← List.cons_append] at eq
    apply Bool.eq_false_iff.mpr; intro hs
    rcases List.append_eq_append_iff.mp eq with ⟨a', hp', _⟩ | ⟨c', hseq, h2⟩
    · cases a' with
      | nil => simp at hp'; subst hp'; rw [hs] at hpv; cases hpv
      | cons x e =>
        have := isVS_not_proper seq x e hs
        rw [← hp', hp] at this; cases this
    · cases c' with
      | nil => simp at hseq; rw [hseq, hpv] at hs; cases hs
      | cons x e =>
        simp only [List.cons_append, List.cons.injEq] at h2
        obtain ⟨hbx, _⟩ := h2
        rw [← hbx] at hseq
        rw [hseq] at hs
        have := isVSP_of_isVS_append (a :: p' ++ [b]) e (by simp) (by simpa using hs)
        rw [this] at hb; cases hb

theorem df_pending_end (p : List UInt8) (hne : p ≠ [])
    (hp : isVSP p = true) (hpv : isVS p = false) :
    decodes_first p (some (replacement_char, [])) := by
  obtain ⟨a, p', rfl⟩ := List.exists_cons_of_ne_nil hne
  apply df_replaced a p' (a :: p') [] (by simp) (Or.inl hp)
  · intro c extra ⟨t, ht⟩
    have := congrArg List.length ht
    (simp at this) <;> omega
  · intro seq rest' eq
    apply Bool.eq_false_iff.mpr; intro hs
    cases rest' with
    | nil => simp at eq; rw [eq, hpv] at hs; cases hs
    | cons x e =>
      have := isVS_not_proper seq x e hs
      rw [eq, hp] at this; cases this


/-! ## The decoder as a right-recursive run, and its equations -/

/-- `run p bytes`: final state and output of stepping through `bytes`
from pending state `p` (equal to `decodeBuffer`, see `decodeBuffer_eq`). -/
def run : State → List UInt8 → State × Text
  | p, [] => (p, [])
  | p, b :: bs => ((run (step p b).1 bs).1, (step p b).2 ++ (run (step p b).1 bs).2)

theorem foldl_stepAcc (bs : List UInt8) : ∀ (p : State) (acc : Text),
    bs.foldl stepAcc (p, acc) = ((run p bs).1, acc ++ (run p bs).2) := by
  induction bs with
  | nil => intro p acc; simp [run]
  | cons b bs ih => intro p acc; simp [List.foldl, stepAcc, ih, run, List.append_assoc]

theorem decodeBuffer_eq (s : State) (buf : List UInt8) : decodeBuffer s buf = run s buf := by
  simp [decodeBuffer, foldl_stepAcc]

theorem run_append (xs : List UInt8) : ∀ (p : State) (ys : List UInt8),
    run p (xs ++ ys) = ((run (run p xs).1 ys).1, (run p xs).2 ++ (run (run p xs).1 ys).2) := by
  induction xs with
  | nil => intro p ys; simp [run]
  | cons b xs ih => intro p ys; simp [run, ih, List.append_assoc]

theorem feed_eq (bufs : List (List UInt8)) : ∀ s : State,
    feed RefDecoder bufs s = run s bufs.flatten := by
  induction bufs with
  | nil => intro s; rfl
  | cons buf rest ih =>
    intro s
    simp only [feed, feed.then, feed.prepend, List.flatten_cons, run_append]
    show feed.prepend RefDecoder _ _ = _
    have e := ih (run s buf).1
    simp only [RefDecoder] at e
    simp only [RefDecoder, decodeBuffer_eq, feed.prepend, e]

theorem step_nil (b : UInt8) : step [] b = stepFresh b := by
  simp [step, stepFresh]

/-- The invariant on the decoder state. -/
def Pending (p : State) : Prop := p = [] ∨ (isVSP p = true ∧ isVS p = false)

theorem step_pending (p : State) (b : UInt8) (_hp : Pending p) : Pending (step p b).1 := by
  unfold step
  by_cases h1 : isVS (p ++ [b]) = true
  · simp [h1, Pending]
  by_cases h2 : isVSP (p ++ [b]) = true
  · simp [h1, h2, Pending]
  by_cases h3 : p.isEmpty = true
  · simp [h1, h2, h3, Pending]
  simp only [h1, h2, h3, Bool.false_eq_true, ↓reduceIte, stepFresh]
  by_cases g1 : isVS [b] = true
  · simp [g1, Pending]
  by_cases g2 : isVSP [b] = true
  · simp [g1, g2, Pending]
  · simp [g1, g2, Pending]

theorem run_pending (bs : List UInt8) : ∀ p, Pending p → Pending (run p bs).1 := by
  induction bs with
  | nil => intro p hp; exact hp
  | cons b bs ih => intro p hp; exact ih _ (step_pending p b hp)

theorem decodeDone_pending (p : State) (hne : p ≠ []) : decodeDone p = [replacement_char] := by
  cases p with
  | nil => exact absurd rfl hne
  | cons _ _ => rfl

/-! ## The decoder output satisfies `decodes` -/

theorem decodes_cons (cp : UInt32) (t : Text) (bytes rest : List UInt8)
    (h1 : decodes_first bytes (some (cp, rest))) (h2 : decodes rest t) :
    decodes bytes (cp :: t) := ⟨rest, h1, h2⟩

theorem run_decodes (bytes : List UInt8) : ∀ p, Pending p →
    decodes (p ++ bytes) ((run p bytes).2 ++ decodeDone (run p bytes).1) := by
  induction bytes with
  | nil =>
    intro p hp
    rcases hp with rfl | ⟨hp, hpv⟩
    · show decodes_first [] none; rfl
    · have hne : p ≠ [] := by rintro rfl; cases hp
      simp only [run, List.append_nil, List.nil_append, decodeDone_pending p hne]
      exact decodes_cons _ _ _ [] (df_pending_end p hne hp hpv) rfl
  | cons b r ih =>
    have fresh : decodes (b :: r)
        ((stepFresh b).2 ++ ((run (stepFresh b).1 r).2 ++ decodeDone (run (stepFresh b).1 r).1)) := by
      unfold stepFresh
      by_cases g1 : isVS [b] = true
      · simp only [g1, ↓reduceIte, List.singleton_append]
        exact decodes_cons _ _ _ r (df_scalar [b] r g1) (ih [] (Or.inl rfl))
      by_cases g2 : isVSP [b] = true
      · simp only [g1, g2, Bool.false_eq_true, ↓reduceIte, List.nil_append]
        exact ih [b] (Or.inr ⟨g2, by simpa using g1⟩)
      · simp only [g1, g2, Bool.false_eq_true, ↓reduceIte, List.singleton_append]
        exact decodes_cons _ _ _ r (df_fresh_bad b r (by simpa using g2)) (ih [] (Or.inl rfl))
    intro p hp
    by_cases hp0 : p = []
    · subst hp0
      simp only [run, step_nil, List.nil_append, List.append_assoc]
      exact fresh
    rcases hp with hp | ⟨hp, hpv⟩
    · exact absurd hp hp0
    simp only [run, step]
    have hq : p ++ b :: r = (p ++ [b]) ++ r := by simp
    by_cases h1 : isVS (p ++ [b]) = true
    · simp only [h1, ↓reduceIte, List.cons_append]
      rw [hq]
      exact decodes_cons _ _ _ r (df_scalar _ r h1) (ih [] (Or.inl rfl))
    by_cases h2 : isVSP (p ++ [b]) = true
    · simp only [h1, h2, Bool.false_eq_true, ↓reduceIte, List.nil_append]
      rw [hq]
      exact ih _ (Or.inr ⟨h2, by simpa using h1⟩)
    have h3 : p.isEmpty = false := by cases p <;> simp_all
    simp only [h1, h2, h3, Bool.false_eq_true, ↓reduceIte, List.cons_append, List.append_assoc]
    exact decodes_cons _ _ _ (b :: r) (df_pending_bad p b r hp0 hp hpv (by simpa using h2)) fresh


/-! ## Whole-buffer decoding laws -/

/-- The pure whole-buffer decoder: run the streaming decoder on one buffer. -/
def decodeAll (bytes : List UInt8) : Text :=
  (run [] bytes).2 ++ decodeDone (run [] bytes).1

theorem decodes_decodeAll (bytes : List UInt8) : decodes bytes (decodeAll bytes) := by
  have := run_decodes bytes [] (Or.inl rfl)
  simpa [decodeAll] using this

theorem decodes_exists_proved : decodes_exists :=
  fun bytes => ⟨_, decodes_decodeAll bytes⟩

theorem decodes_first_exists_proved : decodes_first_exists := by
  intro bytes
  have h := decodes_decodeAll bytes
  unfold decodes at h
  cases ht : decodeAll bytes with
  | nil => rw [ht] at h; exact ⟨_, h⟩
  | cons cp t => rw [ht] at h; obtain ⟨rest, h1, _⟩ := h; exact ⟨_, h1⟩

theorem decodes_first_empty_proved : decodes_first_empty :=
  fun _ h => h

theorem decodes_first_nonempty_proved : decodes_first_nonempty := by
  intro b1 more result h
  rcases h with ⟨_, _, _, rfl⟩ | ⟨_, _, _, _, _, rfl⟩ <;> rfl

theorem maximal_subpart_exists_proved : maximal_subpart_exists := by
  intro b1 more hno
  obtain ⟨r, h⟩ := decodes_first_exists_proved (b1 :: more)
  rcases h with ⟨cp, rest, hb, _⟩ | ⟨_, s, _, hs, _, _⟩
  · exact (hno cp rest hb).elim
  · exact ⟨s, hs⟩

theorem decodes_first_unique_proved : decodes_first_unique := by
  intro bytes r1 r2 h1 h2
  cases bytes with
  | nil => exact h1.trans h2.symm
  | cons b1 more =>
    rcases h1 with ⟨cp1, rest1, hb1, rfl⟩ | ⟨hn1, s1, rest1, hs1, he1, rfl⟩ <;>
    rcases h2 with ⟨cp2, rest2, hb2, rfl⟩ | ⟨hn2, s2, rest2, hs2, he2, rfl⟩
    · obtain ⟨rfl, rfl⟩ := begins_with_scalar_unique_proved _ _ _ _ _ hb1 hb2; rfl
    · exact (hn2 _ _ hb1).elim
    · exact (hn1 _ _ hb2).elim
    · have := maximal_subpart_unique_proved _ _ _ _ hs1 hs2
      subst this
      rw [List.append_cancel_left (he1.trans he2.symm)]

theorem decodes_unique_proved : decodes_unique := by
  intro bytes t1 t2 h1 h2
  unfold decodes at h1 h2
  induction t1 generalizing bytes t2 with
  | nil =>
    cases t2 with
    | nil => rfl
    | cons c t2 =>
      obtain ⟨_, h, _⟩ := h2
      cases decodes_first_unique_proved _ _ _ h1 h
  | cons c t1 ih =>
    obtain ⟨rest1, d1, g1⟩ := h1
    cases t2 with
    | nil => cases decodes_first_unique_proved _ _ _ d1 h2
    | cons c2 t2 =>
      obtain ⟨rest2, d2, g2⟩ := h2
      have e := decodes_first_unique_proved _ _ _ d1 d2
      simp only [Option.some.injEq, Prod.mk.injEq] at e
      obtain ⟨rfl, rfl⟩ := e
      rw [ih rest1 t2 g1 g2]

theorem decodes_iff (bytes : List UInt8) (t : Text) : decodes bytes t ↔ t = decodeAll bytes :=
  ⟨fun h => decodes_unique_proved _ _ _ h (decodes_decodeAll bytes),
   fun h => h ▸ decodes_decodeAll bytes⟩

theorem decodes_examples_proved : decodes_examples := by
  unfold decodes_examples
  simp only [decodes_iff]
  decide

/-! ## The streaming laws for `RefDecoder` -/

theorem decoded_eq (bufs : List (List UInt8)) :
    decoded RefDecoder bufs = decodeAll bufs.flatten := by
  show decoded.text RefDecoder (feed RefDecoder bufs []) = _
  rw [feed_eq]; rfl

theorem decoded_so_far_eq (bufs : List (List UInt8)) :
    decoded_so_far RefDecoder bufs = (run [] bufs.flatten).2 := by
  show decoded_so_far.text RefDecoder (feed RefDecoder bufs []) = _
  rw [feed_eq]; rfl

theorem decodeAll_append (xs ys : List UInt8) :
    decodeAll (xs ++ ys) = (run [] xs).2 ++ ((run (run [] xs).1 ys).2 ++
      decodeDone (run (run [] xs).1 ys).1) := by
  simp [decodeAll, run_append, List.append_assoc]

theorem utf8_decodes_RefDecoder : utf8_decodes RefDecoder := by
  intro bufs; rw [decoded_eq]; exact decodes_decodeAll _

theorem utf8_decode_buffer_safe_RefDecoder : utf8_decode_buffer_safe RefDecoder := by
  intro bufs rest full h
  rw [decodes_iff, decodeAll_append] at h
  rw [decoded_so_far_eq, h]
  exact ⟨_, rfl⟩

/-- From a pending state, feeding the rest of a valid sequence emits
exactly its code point and returns to the empty state. -/
theorem run_complete (r : List UInt8) : ∀ p : State, r ≠ [] → isVS (p ++ r) = true →
    run p r = ([], [cpOf (p ++ r)]) := by
  induction r with
  | nil => intro p h; exact absurd rfl h
  | cons b r ih =>
    intro p _ hv
    cases r with
    | nil =>
      simp [run, step, hv]
    | cons x e =>
      have hq : isVS (p ++ [b]) = false := by
        apply Bool.eq_false_iff.mpr; intro hq
        have := isVS_not_proper (p ++ [b]) x e hq
        rw [show p ++ [b] ++ x :: e = p ++ b :: x :: e by simp, isVS_isVSP _ hv] at this
        cases this
      have hq2 : isVSP (p ++ [b]) = true :=
        isVSP_of_isVS_append (p ++ [b]) (x :: e) (by simp) (by simpa using hv)
      have := ih (p ++ [b]) (by simp) (by simpa using hv)
      have hs : step p b = (p ++ [b], []) := by simp [step, hq, hq2]
      show ((run (step p b).1 (x :: e)).1, (step p b).2 ++ (run (step p b).1 (x :: e)).2) = _
      rw [hs, this]; simp

theorem not_prefix_longer (o : Text) (c : UInt32) : ¬ is_text_prefix (o ++ [c]) o := by
  intro ⟨m, h⟩
  have := congrArg List.length h
  (simp at this) <;> omega

theorem utf8_decode_buffer_prompt_RefDecoder : utf8_decode_buffer_prompt RefDecoder := by
  intro bufs c
  rw [decoded_so_far_eq]
  have hP := run_pending bufs.flatten [] (Or.inl rfl)
  generalize hO : run [] bufs.flatten = R at hP
  obtain ⟨P, O⟩ := R
  rcases hP with hP | ⟨hP, hPv⟩
  · subst hP
    refine ⟨[], _, decodes_decodeAll _, ?_⟩
    rw [decodeAll_append, hO]
    simpa [run, decodeDone, code_point_to_string] using not_prefix_longer O c
  have hne : P ≠ [] := by rintro rfl; cases hP
  by_cases hc : c = replacement_char
  · subst hc
    obtain ⟨hv, hcp⟩ := completion_spec P hP hPv
    refine ⟨completion P, _, decodes_decodeAll _, ?_⟩
    rw [decodeAll_append, hO]
    have hcne : completion P ≠ [] := by
      intro h; rw [h] at hv; simp at hv; rw [hv] at hPv; cases hPv
    simp only [run_complete _ P hcne hv]
    intro ⟨m, h⟩
    simp [code_point_to_string, decodeDone] at h
    exact hcp h.1.symm
  · refine ⟨[], _, decodes_decodeAll _, ?_⟩
    rw [decodeAll_append, hO]
    simp only [run, decodeDone_pending P hne]
    intro ⟨m, h⟩
    simp [code_point_to_string] at h
    exact hc h.1

theorem RefDecoder_correct : Decoder.Correct RefDecoder :=
  ⟨utf8_decodes_RefDecoder, utf8_decode_buffer_safe_RefDecoder, utf8_decode_buffer_prompt_RefDecoder⟩


/-! ## Supporting lemmas for downstream refinement proofs -/

/-! ### Equations for `step` -/

theorem step_complete (p : State) (b : UInt8) (h : isVS (p ++ [b]) = true) :
    step p b = ([], [cpOf (p ++ [b])]) := by simp [step, h]

theorem step_extend (p : State) (b : UInt8) (h1 : isVS (p ++ [b]) = false)
    (h2 : isVSP (p ++ [b]) = true) : step p b = (p ++ [b], []) := by simp [step, h1, h2]

theorem step_bad_fresh (b : UInt8) (h : isVSP [b] = false) :
    step [] b = ([], [replacement_char]) := by
  have h1 : isVS [b] = false := by
    apply Bool.eq_false_iff.mpr; intro hv; rw [isVS_isVSP _ hv] at h; cases h
  simp [step, h, h1]

theorem step_bad_pending (p : State) (b : UInt8) (hne : p ≠ []) (h : isVSP (p ++ [b]) = false) :
    step p b = ((stepFresh b).1, replacement_char :: (stepFresh b).2) := by
  have h1 : isVS (p ++ [b]) = false := by
    apply Bool.eq_false_iff.mpr; intro hv; rw [isVS_isVSP _ hv] at h; cases h
  have h3 : p.isEmpty = false := by cases p <;> simp_all
  simp [step, h, h1, h3]

theorem decodeBuffer_nil (s : State) : decodeBuffer s [] = (s, []) := rfl

theorem decodeBuffer_cons (s : State) (b : UInt8) (bs : List UInt8) :
    decodeBuffer s (b :: bs) =
      ((decodeBuffer (step s b).1 bs).1, (step s b).2 ++ (decodeBuffer (step s b).1 bs).2) := by
  simp only [decodeBuffer_eq]; rfl

/-- The state is always empty or a valid sequence prefix that is not a
whole valid sequence (hence 1..3 bytes). -/
theorem decodeBuffer_pending (s : State) (buf : List UInt8) (h : Pending s) :
    Pending (decodeBuffer s buf).1 := by
  rw [decodeBuffer_eq]; exact run_pending buf s h

theorem pending_length (p : State) (h : Pending p) : p.length ≤ 3 := by
  rcases h with rfl | ⟨h1, h2⟩
  · simp
  · rcases p with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, _ | ⟨e, l⟩⟩⟩⟩⟩ <;> simp_all [isVSP, isVS]

/-! ### Code point value in shift/mask form, per length -/

theorem encodes_one (b1 : UInt8) (cp : UInt32) :
    encodes [b1] cp ↔ b1 ≤ 0x7F ∧ cp = b1.toUInt32 := by
  rw [encodes_iff]; simp [isVS, isLead1, cpOf]

theorem encodes_two (b1 b2 : UInt8) (cp : UInt32) :
    encodes [b1, b2] cp ↔ (0xC2 ≤ b1 ∧ b1 ≤ 0xDF) ∧ (0x80 ≤ b2 ∧ b2 ≤ 0xBF) ∧
      cp = ((b1.toUInt32 &&& 0x1F) <<< 6) ||| (b2.toUInt32 &&& 0x3F) := by
  rw [encodes_iff]
  simp only [isVS, isLead2_iff, secondOk_iff, cpOf, Bool.and_eq_true, UInt8.le_iff_toNat_le,
    UInt8.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
  constructor
  · intro ⟨⟨h1, h2⟩, h3⟩; exact ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩, h3⟩
  · intro ⟨h1, h2, h3⟩; exact ⟨⟨⟨by omega, by omega⟩, by omega⟩, h3⟩

theorem encodes_three (b1 b2 b3 : UInt8) (cp : UInt32) :
    encodes [b1, b2, b3] cp ↔ (0xE0 ≤ b1 ∧ b1 ≤ 0xEF) ∧ secondOk b1 b2 = true ∧
      (0x80 ≤ b3 ∧ b3 ≤ 0xBF) ∧
      cp = ((b1.toUInt32 &&& 0x0F) <<< 12) ||| ((b2.toUInt32 &&& 0x3F) <<< 6) |||
        (b3.toUInt32 &&& 0x3F) := by
  rw [encodes_iff]
  simp only [isVS, isLead3, isCont, cpOf, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · intro ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩; exact ⟨h1, h2, h3, h4⟩
  · intro ⟨h1, h2, h3, h4⟩; exact ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩

theorem encodes_four (b1 b2 b3 b4 : UInt8) (cp : UInt32) :
    encodes [b1, b2, b3, b4] cp ↔ (0xF0 ≤ b1 ∧ b1 ≤ 0xF4) ∧ secondOk b1 b2 = true ∧
      (0x80 ≤ b3 ∧ b3 ≤ 0xBF) ∧ (0x80 ≤ b4 ∧ b4 ≤ 0xBF) ∧
      cp = ((b1.toUInt32 &&& 0x07) <<< 18) ||| ((b2.toUInt32 &&& 0x3F) <<< 12) |||
        ((b3.toUInt32 &&& 0x3F) <<< 6) ||| (b4.toUInt32 &&& 0x3F) := by
  rw [encodes_iff]
  simp only [isVS, isLead4, isCont, cpOf, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · intro ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩; exact ⟨h1, h2, h3, h4, h5⟩
  · intro ⟨h1, h2, h3, h4, h5⟩; exact ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩

/-- No valid sequence is longer than four bytes. -/
theorem isVS_length (seq : List UInt8) (h : isVS seq = true) : 1 ≤ seq.length ∧ seq.length ≤ 4 := by
  rcases seq with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, _ | ⟨e, l⟩⟩⟩⟩⟩ <;> simp_all [isVS]

/-! ### Every output code point is a Unicode scalar (so UTF-16-encodable) -/

theorem replacement_char_scalar : is_unicode_scalar replacement_char = true := by decide

theorem step_out_scalar (p : State) (b : UInt8) :
    ∀ c ∈ (step p b).2, is_unicode_scalar c = true := by
  have hq : ∀ q : List UInt8, isVS q = true → is_unicode_scalar (cpOf q) = true :=
    fun q h => (encodes_of_isVS q h).1
  unfold step stepFresh
  by_cases h1 : isVS (p ++ [b]) = true
  · simp [h1, hq _ h1]
  by_cases h2 : isVSP (p ++ [b]) = true
  · simp [h1, h2]
  by_cases h3 : p.isEmpty = true
  · simp [h1, h2, h3, replacement_char_scalar]
  by_cases g1 : isVS [b] = true
  · simp [h1, h2, h3, g1, replacement_char_scalar, hq _ g1]
  by_cases g2 : isVSP [b] = true
  · simp [h1, h2, h3, g1, g2, replacement_char_scalar]
  · simp [h1, h2, h3, g1, g2, replacement_char_scalar]

theorem run_out_scalar (bs : List UInt8) : ∀ (p : State),
    ∀ c ∈ (run p bs).2, is_unicode_scalar c = true := by
  induction bs with
  | nil => intro p c h; simp [run] at h
  | cons b bs ih =>
    intro p c h
    simp only [run, List.mem_append] at h
    rcases h with h | h
    · exact step_out_scalar p b c h
    · exact ih _ c h

theorem decodeBuffer_out_scalar (s : State) (buf : List UInt8) :
    ∀ c ∈ (decodeBuffer s buf).2, is_unicode_scalar c = true := by
  rw [decodeBuffer_eq]; exact run_out_scalar buf s

theorem decodeDone_out_scalar (s : State) : ∀ c ∈ decodeDone s, is_unicode_scalar c = true := by
  intro c h; unfold decodeDone at h; split at h <;> simp_all [replacement_char_scalar]

theorem decoded_scalar (bufs : List (List UInt8)) :
    ∀ c ∈ decoded RefDecoder bufs, is_unicode_scalar c = true := by
  rw [decoded_eq]; intro c h
  simp only [decodeAll, List.mem_append] at h
  rcases h with h | h
  · exact run_out_scalar _ [] c h
  · exact decodeDone_out_scalar _ c h

end Utf8Pure
