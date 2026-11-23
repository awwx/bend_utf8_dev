/- Trusted challenge: review this file together with Utf8Laws.lean and the
comparator configurations. The holes are intentional: comparator requires the
untrusted solution to fill them, preserving the statements and all spec definitions.
This module must never import the solution or its proofs. -/
import Utf8Laws

namespace Utf8Pure

theorem bit8_value_sum_proved : bit8_value_sum := by sorry
theorem bit8_value_word_proved : bit8_value_word := by sorry
theorem u32_byte4_bits_proved : u32_byte4_bits := by sorry
theorem is_surrogate_code_point_examples_proved : is_surrogate_code_point_examples := by sorry
theorem is_unicode_scalar_matches_char_proved : is_unicode_scalar_matches_char := by sorry
theorem begins_with_scalar_unique_proved : begins_with_scalar_unique := by sorry
theorem not_valid_sequence_prefix_extended_proved : not_valid_sequence_prefix_extended := by sorry
theorem maximal_subpart_unique_proved : maximal_subpart_unique := by sorry
theorem maximal_subpart_exists_proved : maximal_subpart_exists := by sorry
theorem decodes_first_exists_proved : decodes_first_exists := by sorry
theorem decodes_exists_proved : decodes_exists := by sorry
theorem decodes_first_empty_proved : decodes_first_empty := by sorry
theorem decodes_first_nonempty_proved : decodes_first_nonempty := by sorry
theorem decodes_first_unique_proved : decodes_first_unique := by sorry
theorem decodes_unique_proved : decodes_unique := by sorry
theorem decodes_examples_proved : decodes_examples := by sorry

-- The solution supplies this definition; no implementation is trusted here.
def RefDecoder : Decoder := by sorry

theorem RefDecoder_correct : Decoder.Correct RefDecoder := by sorry

end Utf8Pure
