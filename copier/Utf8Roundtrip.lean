import Utf8Laws

namespace Copier

/-- Encoding each complete scalar separately models a UTF-8 string write. -/
def encodeText (text : Text) : List UInt8 :=
  text.flatMap (fun c => (encoding c.val).getD [])

/-- A valid file is a complete UTF-8 encoding of some text, possibly empty. -/
def Valid (bytes : List UInt8) : Prop :=
  ∃ text : Text, encodes_text bytes text

end Copier
