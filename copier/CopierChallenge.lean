import StreamModel

namespace Copier

theorem valid_roundtrip {bytes : Bytes} {text : Text}
    (hv : Valid bytes) (hd : decodes bytes text) : encodeText text = bytes := by sorry

theorem textEvents_scalar (D : Decoder) (bs : List Bytes) (s : D.State) :
    ∀ t ∈ textEvents D bs s, ∀ c ∈ t, is_unicode_scalar c.val = true := by sorry

theorem good_copy {D : Decoder} (hnode : node_characterization D)
    {bytes : Bytes} (hv : Valid bytes) {bs : List Bytes}
    (hp : Partition bytes bs) (e : Execution (initial D good bs)) :
    ∃ i, (e.state i).done = true ∧ (e.state i).output = bytes := by sorry

theorem executions_exist (D : Decoder) (p : Program) (bs : List Bytes) :
    Nonempty (Execution (initial D p bs)) := by sorry

theorem bad_counterexample {D : Decoder} (hnode : node_characterization D) :
    Valid witnessBytes ∧ Partition witnessBytes witnessBuffers ∧
    toString D (.buffer [0xC2]) = replacement_char_string ∧
    toString D (.buffer [0xA9]) = replacement_char_string ∧
    ∃ e : Execution (initial D bad witnessBuffers), ∃ i,
      (e.state i).done = true ∧ (e.state i).output = witnessOutput ∧
      (e.state i).output ≠ witnessBytes := by sorry

end Copier
