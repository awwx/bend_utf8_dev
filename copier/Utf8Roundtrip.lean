import Utf8Proofs

namespace Copier
open Utf8Pure

/-- Encoding each complete scalar separately models a UTF-8 string write. -/
def encodeText (text : Text) : List UInt8 :=
  text.flatMap (fun cp => (encoding cp).getD [])

theorem encodeText_append (left right : Text) :
    encodeText (left ++ right) = encodeText left ++ encodeText right := by
  simp [encodeText, List.flatMap_append]

/-- Valid files are concatenations of sequences from the encoding specification.
    In particular, the empty file is valid. -/
inductive Valid : List UInt8 → Prop where
  | nil : Valid []
  | cons {seq rest : List UInt8} {cp : UInt32} :
      encodes seq cp → Valid rest → Valid (seq ++ rest)

theorem decodeAll_scalar_append {seq : List UInt8} {cp : UInt32}
    (h : encodes seq cp) (rest : List UInt8) :
    decodeAll (seq ++ rest) = cp :: decodeAll rest := by
  obtain ⟨hv, hc⟩ := (encodes_iff seq cp).mp h
  have hd := decodes_cons cp (decodeAll rest) (seq ++ rest) rest
    (hc ▸ df_scalar seq rest hv) (decodes_decodeAll rest)
  exact ((decodes_iff _ _).mp hd).symm

/-- The copying round trip follows from validity, independently of streams. -/
theorem valid_roundtrip {bytes : List UInt8} (h : Valid bytes) :
    encodeText (decodeAll bytes) = bytes := by
  induction h with
  | nil => rfl
  | @cons seq rest cp he _ ih =>
      rw [decodeAll_scalar_append he]
      simp only [encodeText, List.flatMap_cons, he.2, Option.getD_some]
      exact congrArg (seq ++ ·) ih

end Copier
