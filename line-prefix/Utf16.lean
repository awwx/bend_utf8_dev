import TextSpec

set_option maxRecDepth 100000
namespace LinePrefix.Utf16
open Utf8Pure

/-- UTF-16 encoding, with the supplementary scalar represented by its two
surrogate code units in high-then-low order. -/
def encodeScalar (cp : UInt32) : Text :=
  if cp.toNat < 0x10000 then [cp]
  else [UInt32.ofNat (0xD800 + (cp.toNat - 0x10000) / 1024),
        UInt32.ofNat (0xDC00 + (cp.toNat - 0x10000) % 1024)]

def encode (text : Text) : Text := text.flatMap encodeScalar

/-- A code-unit sequence represents complete Unicode text, so its endpoints
cannot lie inside a surrogate pair. -/
def WellFormed (units : Text) : Prop :=
  ∃ text, Scalars text ∧ encode text = units

@[simp] theorem encode_nil : encode [] = [] := rfl
@[simp] theorem encode_cons (cp : UInt32) (text : Text) :
    encode (cp :: text) = encodeScalar cp ++ encode text := by
  simp [encode]
@[simp] theorem encode_append (a b : Text) :
    encode (a ++ b) = encode a ++ encode b := by simp [encode]

 theorem scalar_nonempty (cp : UInt32) : encodeScalar cp ≠ [] := by
  unfold encodeScalar; split <;> simp

theorem scalar_length (cp : UInt32) : (encodeScalar cp).length ≤ 2 := by
  unfold encodeScalar; split <;> simp

theorem encode_length (text : Text) : (encode text).length ≤ 2 * text.length := by
  induction text with
  | nil => simp
  | cons cp rest ih =>
    simp only [encode_cons, List.length_append, List.length_cons]
    have := scalar_length cp
    omega

theorem supplementary_bounds {cp : UInt32} (h : is_unicode_scalar cp = true)
    (hs : ¬ cp.toNat < 0x10000) :
    let hi := 0xD800 + (cp.toNat - 0x10000) / 1024
    let lo := 0xDC00 + (cp.toNat - 0x10000) % 1024
    0xD800 ≤ hi ∧ hi < 0xDC00 ∧ 0xDC00 ≤ lo ∧ lo < 0xE000 ∧
      0x10000 + (hi - 0xD800) * 1024 + (lo - 0xDC00) = cp.toNat := by
  have hb := ((is_unicode_scalar_iff cp).mp h).1
  have hd := Nat.mod_add_div (cp.toNat - 0x10000) 1024
  have hm := Nat.mod_lt (cp.toNat - 0x10000) (by decide : 0 < 1024)
  dsimp
  omega

theorem scalar_unit_bound {cp u : UInt32} (h : is_unicode_scalar cp = true)
    (hu : u ∈ encodeScalar cp) : u.toNat < 65536 := by
  unfold encodeScalar at hu
  split at hu
  · simp only [List.mem_singleton] at hu; subst u; assumption
  · have hb := supplementary_bounds h (by assumption)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl
    · change _ % 4294967296 < 65536; dsimp at hb; omega
    · change _ % 4294967296 < 65536; dsimp at hb; omega

theorem unit_bound {text : Text} (h : Scalars text) {u : UInt32}
    (hu : u ∈ encode text) : u.toNat < 65536 := by
  simp only [encode, List.mem_flatMap] at hu
  obtain ⟨cp, hc, hu⟩ := hu
  exact scalar_unit_bound (h cp hc) hu

@[simp] theorem encode_ascii (cp : UInt32) (h : cp.toNat < 0x10000) :
    encodeScalar cp = [cp] := by simp [encodeScalar, h]

 theorem run_scalar_encode {cp : UInt32} (h : is_unicode_scalar cp = true) (s : Bool) :
    run s (encodeScalar cp) = (cp == 10, encode (emit s cp)) := by
  by_cases hs : cp.toNat < 0x10000
  · cases s <;> simp [encodeScalar, hs, run, emit, encode]
  · have hb := supplementary_bounds h hs
    have hi : (UInt32.ofNat (0xD800 + (cp.toNat - 0x10000) / 1024) == 10) = false := by
      simp only [beq_eq_false_iff_ne]
      intro he
      have he' := congrArg UInt32.toNat he
      rw [UInt32.toNat_ofNat] at he'
      dsimp at hb
      change _ % 4294967296 = 10 at he'
      omega
    have lo : (UInt32.ofNat (0xDC00 + (cp.toNat - 0x10000) % 1024) == 10) = false := by
      simp only [beq_eq_false_iff_ne]
      intro he
      have he' := congrArg UInt32.toNat he
      rw [UInt32.toNat_ofNat] at he'
      dsimp at hb
      change _ % 4294967296 = 10 at he'
      omega
    have hc : (cp == 10) = false := by
      simp only [beq_eq_false_iff_ne]
      intro he; subst cp; exact hs (by decide)
    cases s <;> simp only [encodeScalar, hs, ↓reduceIte, run, hi, lo, hc, emit, Bool.false_eq_true, encode, List.flatMap_cons, List.flatMap_nil, List.nil_append, List.append_nil, List.cons_append] <;> rfl

/-- Processing code units preserves both scalar output and the persistent LF
state. The output is a concatenation of complete scalar encodings. -/
theorem run_encode (s : Bool) {text : Text} (h : Scalars text) :
    run s (encode text) = ((run s text).1, encode (run s text).2) := by
  induction text generalizing s with
  | nil => simp [run]
  | cons cp rest ih =>
    have hp := h cp (by simp)
    have hr : Scalars rest := fun c hc => h c (by simp [hc])
    rw [encode_cons, run_append, run_scalar_encode hp]
    simp only
    rw [ih _ hr]
    simp [run]

theorem run_wellFormed {units : Text} (h : WellFormed units) (s : Bool) :
    WellFormed (run s units).2 := by
  obtain ⟨text, ht, rfl⟩ := h
  rw [run_encode s ht]
  exact ⟨(run s text).2, run_scalar ht s, rfl⟩

/-- Total UTF-16 reader. Its behavior on malformed unit sequences is irrelevant
for the representation relation; on valid encodings it recovers every scalar. -/
def decode : Text → Text
  | [] => []
  | u :: rest =>
    if 0xD800 ≤ u.toNat ∧ u.toNat < 0xDC00 then
      match rest with
      | [] => [u]
      | v :: tail =>
        UInt32.ofNat (0x10000 + (u.toNat - 0xD800) * 1024 +
          (v.toNat - 0xDC00)) :: decode tail
    else u :: decode rest

theorem decode_scalar_append {cp : UInt32} (h : is_unicode_scalar cp = true)
    (rest : Text) : decode (encodeScalar cp ++ rest) = cp :: decode rest := by
  have hb := (is_unicode_scalar_iff cp).mp h
  by_cases hs : cp.toNat < 0x10000
  · have hn : ¬ (0xD800 ≤ cp.toNat ∧ cp.toNat < 0xDC00) := by omega
    rw [encodeScalar, if_pos hs]
    cases rest <;> simp only [List.cons_append, List.nil_append, decode, hn, ↓reduceIte]
  · have hp := supplementary_bounds h hs
    dsimp at hp
    have hhi : (UInt32.ofNat (0xD800 + (cp.toNat - 0x10000) / 1024)).toNat =
        0xD800 + (cp.toNat - 0x10000) / 1024 := by
      apply UInt32.toNat_ofNat_of_lt'; change _ < 4294967296; omega
    have hlo : (UInt32.ofNat (0xDC00 + (cp.toNat - 0x10000) % 1024)).toNat =
        0xDC00 + (cp.toNat - 0x10000) % 1024 := by
      apply UInt32.toNat_ofNat_of_lt'; change _ < 4294967296; omega
    have hr : UInt32.ofNat (0x10000 +
        ((0xD800 + (cp.toNat - 0x10000) / 1024) - 0xD800) * 1024 +
        ((0xDC00 + (cp.toNat - 0x10000) % 1024) - 0xDC00)) = cp := by
      apply UInt32.toNat_inj.mp
      rw [UInt32.toNat_ofNat_of_lt']
      · exact hp.2.2.2.2
      · change _ < 4294967296; omega
    simp only [encodeScalar, hs, ↓reduceIte, List.cons_append, List.nil_append,
      decode, hhi, hlo]
    rw [if_pos ⟨hp.1, hp.2.1⟩, hr]

theorem decode_encode {text : Text} (h : Scalars text) : decode (encode text) = text := by
  induction text with
  | nil => rfl
  | cons cp rest ih =>
    rw [encode_cons, decode_scalar_append (h cp (by simp)), ih]
    exact fun c hc => h c (by simp [hc])

theorem encode_injective {a b : Text} (ha : Scalars a) (hb : Scalars b)
    (he : encode a = encode b) : a = b := by
  have hh := congrArg decode he
  simpa only [decode_encode ha, decode_encode hb] using hh

end LinePrefix.Utf16
