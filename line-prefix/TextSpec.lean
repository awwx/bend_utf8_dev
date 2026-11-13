import Utf8Roundtrip

namespace LinePrefix
open Utf8Pure

/-- Specification: pair every scalar with its actual predecessor, using `none`
    only for the first position. This construction does not carry a line bit. -/
def preceded (previous : Option UInt32) (text : Text) : Text :=
  ((previous :: text.map some).zip text).flatMap fun (p, cp) =>
    (if p = none ∨ p = some 10 then [62, 32] else []) ++ [cp]

def prefixLines (text : Text) : Text := preceded none text

def emit (atStart : Bool) (cp : UInt32) : Text :=
  (if atStart then [62, 32] else []) ++ [cp]

def run : Bool → Text → Bool × Text
  | s, [] => (s, [])
  | s, cp :: rest =>
      let r := run (cp == 10) rest
      (r.1, emit s cp ++ r.2)

theorem preceded_cons (p : Option UInt32) (cp : UInt32) (rest : Text) :
    preceded p (cp :: rest) =
      (if p = none ∨ p = some 10 then [62,32] else []) ++ [cp] ++
        preceded (some cp) rest := by
  simp [preceded, List.zip_cons_cons, List.flatMap_cons, List.append_assoc]

theorem run_preceded (p : Option UInt32) (text : Text) :
    (run (decide (p = none ∨ p = some 10)) text).2 = preceded p text := by
  induction text generalizing p with
  | nil => simp [run, preceded]
  | cons cp rest ih =>
      rw [preceded_cons]
      simp only [run, emit, decide_eq_true_eq]
      have h := ih (some cp)
      simp only [Option.some.injEq, reduceCtorEq, false_or] at h
      have hb : (cp == 10) = decide (cp = 10) := by
        apply Bool.eq_iff_iff.mpr
        simp
      rw [hb, h]

theorem run_correct (text : Text) : (run true text).2 = prefixLines text := by
  simpa [prefixLines] using run_preceded none text

theorem emit_length (s : Bool) (cp : UInt32) : (emit s cp).length ≤ 3 := by
  cases s <;> simp [emit]

theorem run_length (s : Bool) (text : Text) : (run s text).2.length ≤ 3*text.length := by
  induction text generalizing s with
  | nil => simp [run]
  | cons cp rest ih =>
      have he := emit_length s cp
      have hr := ih (cp == 10)
      simp only [run, List.length_append, List.length_cons]
      omega

theorem run_append (s : Bool) (a b : Text) :
    run s (a ++ b) =
      let x := run s a
      let y := run x.1 b
      (y.1, x.2 ++ y.2) := by
  induction a generalizing s with
  | nil => simp [run]
  | cons cp rest ih => simp [run, ih, List.append_assoc]

def runChunks : Bool → List Text → Bool × Text
  | s, [] => (s, [])
  | s, chunk :: rest =>
      let x := run s chunk
      let y := runChunks x.1 rest
      (y.1, x.2 ++ y.2)

theorem runChunks_eq (s : Bool) (chunks : List Text) :
    runChunks s chunks = run s chunks.flatten := by
  induction chunks generalizing s with
  | nil => rfl
  | cons chunk rest ih => simp [runChunks, ih, run_append]

theorem chunks_correct (chunks : List Text) :
    (runChunks true chunks).2 = prefixLines chunks.flatten := by
  rw [runChunks_eq, run_correct]

def Scalars (text : Text) : Prop := ∀ cp ∈ text, is_unicode_scalar cp = true

theorem run_scalar {text : Text} (h : Scalars text) (s : Bool) :
    Scalars (run s text).2 := by
  suffices ∀ s, Scalars (run s text).2 from this s
  induction text with
  | nil => simp [run, Scalars]
  | cons cp rest ih =>
      intro s c hc
      have hr : Scalars rest := fun x hx => h x (by simp [hx])
      have hp := h cp (by simp)
      simp only [run, List.mem_append] at hc
      rcases hc with hc | hc
      · cases s <;> simp [emit] at hc
        · subst c; exact hp
        · rcases hc with rfl | rfl | rfl <;> first | decide | exact hp
      · exact ih hr _ c hc

theorem prefix_scalar {text : Text} (h : Scalars text) : Scalars (prefixLines text) := by
  rw [← run_correct]
  exact run_scalar h true

/-- The decoded scalar contract holds even for replacement decoding. -/
theorem decode_scalar (bytes : List UInt8) : Scalars (decodeAll bytes) := by
  have h := decoded_scalar [bytes]
  simpa [decoded_eq, Scalars] using h

theorem scalar_encoding {cp : UInt32} (h : is_unicode_scalar cp = true) :
    encodes ((encoding cp).getD []) cp := by
  have hb := (is_unicode_scalar_iff cp).mp h
  have hl : cp.toNat < 0x200000 := by omega
  exact ⟨h, by simp [encoding_eq, hl]⟩

theorem encode_valid {text : Text} (h : Scalars text) :
    Copier.Valid (Copier.encodeText text) := by
  induction text with
  | nil => exact .nil
  | cons cp rest ih =>
      have hp := h cp (by simp)
      have hr : Scalars rest := fun c hc => h c (by simp [hc])
      exact Copier.Valid.cons (scalar_encoding hp) (ih hr)

theorem decode_encode {text : Text} (h : Scalars text) :
    decodeAll (Copier.encodeText text) = text := by
  induction text with
  | nil => rfl
  | cons cp rest ih =>
      have hp := h cp (by simp)
      have hr : Scalars rest := fun c hc => h c (by simp [hc])
      change decodeAll (((encoding cp).getD []) ++ Copier.encodeText rest) = _
      rw [Copier.decodeAll_scalar_append (scalar_encoding hp), ih hr]

theorem output_valid (bytes : List UInt8) :
    Copier.Valid (Copier.encodeText (prefixLines (decodeAll bytes))) :=
  encode_valid (prefix_scalar (decode_scalar bytes))

theorem output_roundtrip (bytes : List UInt8) :
    decodeAll (Copier.encodeText (prefixLines (decodeAll bytes))) =
      prefixLines (decodeAll bytes) :=
  decode_encode (prefix_scalar (decode_scalar bytes))

/-- Buffered scalar writes encode compositionally, including empty buffers. -/
theorem encode_chunks (chunks : List Text) :
    Copier.encodeText chunks.flatten =
      (chunks.map Copier.encodeText).flatten := by
  induction chunks with
  | nil => rfl
  | cons chunk rest ih => simp [Copier.encodeText_append, ih]

/-- Every scalar fits the unsigned i32 callback/array representation. -/
theorem scalar_i32_bound {cp : UInt32} (h : is_unicode_scalar cp = true) :
    cp.toNat ≤ 0x10FFFF ∧ cp.toNat < 2^32 := by
  exact ⟨((is_unicode_scalar_iff cp).mp h).1, cp.toNat_lt⟩

example : prefixLines [] = [] := by decide
example : prefixLines [10] = [62,32,10] := by decide
example : prefixLines [10,10] = [62,32,10,62,32,10] := by decide
example : prefixLines [97,13,10,0x1F642] = [62,32,97,13,10,62,32,0x1F642] := by decide
example : prefixLines [97,10] = [62,32,97,10] := by decide

end LinePrefix
