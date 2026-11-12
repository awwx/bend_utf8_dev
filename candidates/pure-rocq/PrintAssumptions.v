From Utf8 Require Import Utf8Laws Utf8Ref Utf8Proofs Utf8StepFacts.
Check bit8_value_sum_proved : bit8_value_sum. Print Assumptions bit8_value_sum_proved.
Check bit8_value_word_proved : bit8_value_word. Print Assumptions bit8_value_word_proved.
Check u32_byte4_bits_proved : u32_byte4_bits. Print Assumptions u32_byte4_bits_proved.
Check is_surrogate_code_point_examples_proved : is_surrogate_code_point_examples. Print Assumptions is_surrogate_code_point_examples_proved.
Check begins_with_scalar_unique_proved : begins_with_scalar_unique. Print Assumptions begins_with_scalar_unique_proved.
Check not_valid_sequence_prefix_extended_proved : not_valid_sequence_prefix_extended. Print Assumptions not_valid_sequence_prefix_extended_proved.
Check maximal_subpart_exists_proved : maximal_subpart_exists. Print Assumptions maximal_subpart_exists_proved.
Check maximal_subpart_unique_proved : maximal_subpart_unique. Print Assumptions maximal_subpart_unique_proved.
Check decodes_first_exists_proved : decodes_first_exists. Print Assumptions decodes_first_exists_proved.
Check decodes_first_unique_proved : decodes_first_unique. Print Assumptions decodes_first_unique_proved.
Check decodes_first_empty_proved : decodes_first_empty. Print Assumptions decodes_first_empty_proved.
Check decodes_first_nonempty_proved : decodes_first_nonempty. Print Assumptions decodes_first_nonempty_proved.
Check decodes_exists_proved : decodes_exists. Print Assumptions decodes_exists_proved.
Check decodes_unique_proved : decodes_unique. Print Assumptions decodes_unique_proved.
Check decodes_examples_proved : decodes_examples. Print Assumptions decodes_examples_proved.
Check RefDecoder_correct : Decoder_correct RefDecoder. Print Assumptions RefDecoder_correct.
Print Assumptions Utf8.Utf8Ref.bN.
Print Assumptions Utf8.Utf8Ref.seq_len.
Print Assumptions Utf8.Utf8Ref.lo2.
Print Assumptions Utf8.Utf8Ref.hi2.
Print Assumptions Utf8.Utf8Ref.is_cont.
Print Assumptions Utf8.Utf8Ref.second_ok.
Print Assumptions Utf8.Utf8Ref.vp.
Print Assumptions Utf8.Utf8Ref.vs.
Print Assumptions Utf8.Utf8Ref.seq_value.
Print Assumptions Utf8.Utf8Ref.seq_cp.
Print Assumptions Utf8.Utf8Ref.FFFD.
Print Assumptions Utf8.Utf8Ref.State.
Print Assumptions Utf8.Utf8Ref.step_empty.
Print Assumptions Utf8.Utf8Ref.step.
Print Assumptions Utf8.Utf8Ref.step_acc.
Print Assumptions Utf8.Utf8Ref.ref_decode_buffer.
Print Assumptions Utf8.Utf8Ref.ref_done.
Print Assumptions Utf8.Utf8Ref.RefDecoder.
Print Assumptions Utf8.Utf8Ref.ref_decode.
Print Assumptions Utf8.Utf8Bridge.b2n_le1.
Print Assumptions Utf8.Utf8Bridge.U32_to_N_bound.
Print Assumptions Utf8.Utf8Bridge.low_bits.
Print Assumptions Utf8.Utf8Bridge.low_bits_mod.
Print Assumptions Utf8.Utf8Bridge.U32_to_of.
Print Assumptions Utf8.Utf8Bridge.b2n_double_inj.
Print Assumptions Utf8.Utf8Bridge.U32_to_N_inj.
Print Assumptions Utf8.Utf8Bridge.U32_of_to.
Print Assumptions Utf8.Utf8Bridge.scalar_N.
Print Assumptions Utf8.Utf8Bridge.is_unicode_scalar_iff.
Print Assumptions Utf8.Utf8Bridge.bN_inj.
Print Assumptions Utf8.Utf8Bridge.bN_bound.
Print Assumptions Utf8.Utf8Bridge.byte_of.
Print Assumptions Utf8.Utf8Bridge.bN_byte_of.
Print Assumptions Utf8.Utf8Bridge.bN_bit8.
Print Assumptions Utf8.Utf8Bridge.cont.
Print Assumptions Utf8.Utf8Bridge.utf8_form.
Print Assumptions Utf8.Utf8Bridge.encoding_form.
Print Assumptions Utf8.Utf8Bridge.utf8_form_unique.
Print Assumptions Utf8.Utf8Bridge.seq_len_cases.
Print Assumptions Utf8.Utf8Bridge.lo2_hi2_cases.
Print Assumptions Utf8.Utf8Bridge.lead_cases.
Print Assumptions Utf8.Utf8Bridge.seq_len_le4.
Print Assumptions Utf8.Utf8Bridge.vp_one.
Print Assumptions Utf8.Utf8Bridge.vp_one_iff.
Print Assumptions Utf8.Utf8Bridge.vs_one_iff.
Print Assumptions Utf8.Utf8Bridge.vp_cons2.
Print Assumptions Utf8.Utf8Bridge.vs_vp_len.
Print Assumptions Utf8.Utf8Bridge.vp_len_lead.
Print Assumptions Utf8.Utf8Bridge.vp_len.
Print Assumptions Utf8.Utf8Bridge.vp_app.
Print Assumptions Utf8.Utf8Bridge.vs_vp.
Print Assumptions Utf8.Utf8Bridge.vs_prefix_free.
Print Assumptions Utf8.Utf8Bridge.mod_offset.
Print Assumptions Utf8.Utf8Bridge.vs_form.
Print Assumptions Utf8.Utf8Bridge.form_vs.
Print Assumptions Utf8.Utf8Bridge.encodes_iff.
Print Assumptions Utf8.Utf8Bridge.seq_value_scalar.
Print Assumptions Utf8.Utf8Bridge.seq_cp_value.
Print Assumptions Utf8.Utf8Bridge.completion.
Print Assumptions Utf8.Utf8Bridge.pending_completion.
Print Assumptions Utf8.Utf8Proofs.bit8_value_sum_proved.
Print Assumptions Utf8.Utf8Proofs.bit8_value_word_proved.
Print Assumptions Utf8.Utf8Proofs.u32_byte4_bits_proved.
Print Assumptions Utf8.Utf8Proofs.is_surrogate_code_point_examples_proved.
Print Assumptions Utf8.Utf8Proofs.encodes_vs.
Print Assumptions Utf8.Utf8Proofs.vs_encodes.
Print Assumptions Utf8.Utf8Proofs.valid_sequence_iff.
Print Assumptions Utf8.Utf8Proofs.valid_sequence_prefix_iff.
Print Assumptions Utf8.Utf8Proofs.pending_no_valid_prefix.
Print Assumptions Utf8.Utf8Proofs.begins_with_scalar_unique_proved.
Print Assumptions Utf8.Utf8Proofs.not_valid_sequence_prefix_extended_proved.
Print Assumptions Utf8.Utf8Proofs.ms_le.
Print Assumptions Utf8.Utf8Proofs.maximal_subpart_unique_proved.
Print Assumptions Utf8.Utf8Proofs.df_valid.
Print Assumptions Utf8.Utf8Proofs.bws_vs.
Print Assumptions Utf8.Utf8Proofs.df_bad_lead.
Print Assumptions Utf8.Utf8Proofs.df_replaced.
Print Assumptions Utf8.Utf8Proofs.df_stuck.
Print Assumptions Utf8.Utf8Proofs.df_pending_end.
Print Assumptions Utf8.Utf8Proofs.decodes_first_unique_proved.
Print Assumptions Utf8.Utf8Proofs.decodes_first_empty_proved.
Print Assumptions Utf8.Utf8Proofs.decodes_first_nonempty_proved.
Print Assumptions Utf8.Utf8Proofs.Inv.
Print Assumptions Utf8.Utf8Proofs.run.
Print Assumptions Utf8.Utf8Proofs.fold_run.
Print Assumptions Utf8.Utf8Proofs.ref_decode_buffer_run.
Print Assumptions Utf8.Utf8Proofs.run_app.
Print Assumptions Utf8.Utf8Proofs.step_empty_inv.
Print Assumptions Utf8.Utf8Proofs.step_inv.
Print Assumptions Utf8.Utf8Proofs.run_inv.
Print Assumptions Utf8.Utf8Proofs.decodes_cons.
Print Assumptions Utf8.Utf8Proofs.step_empty_dec.
Print Assumptions Utf8.Utf8Proofs.step_dec.
Print Assumptions Utf8.Utf8Proofs.run_dec.
Print Assumptions Utf8.Utf8Proofs.done_dec.
Print Assumptions Utf8.Utf8Proofs.ref_decode_run.
Print Assumptions Utf8.Utf8Proofs.ref_decode_ok.
Print Assumptions Utf8.Utf8Proofs.decodes_first_exists_proved.
Print Assumptions Utf8.Utf8Proofs.maximal_subpart_exists_proved.
Print Assumptions Utf8.Utf8Proofs.decodes_exists_proved.
Print Assumptions Utf8.Utf8Proofs.decodes_unique_proved.
Print Assumptions Utf8.Utf8Proofs.decodes_examples_proved.
Print Assumptions Utf8.Utf8Proofs.feed_run.
Print Assumptions Utf8.Utf8Proofs.decoded_run.
Print Assumptions Utf8.Utf8Proofs.decoded_so_far_run.
Print Assumptions Utf8.Utf8Proofs.RefDecoder_decodes.
Print Assumptions Utf8.Utf8Proofs.RefDecoder_safe.
Print Assumptions Utf8.Utf8Proofs.U32_eq_dec.
Print Assumptions Utf8.Utf8Proofs.RefDecoder_prompt.
Print Assumptions Utf8.Utf8Proofs.RefDecoder_correct.
Print Assumptions Utf8.Utf8Proofs.output_ok.
Print Assumptions Utf8.Utf8Proofs.FFFD_value.
Print Assumptions Utf8.Utf8Proofs.seq_cp_ok.
Print Assumptions Utf8.Utf8Proofs.step_empty_output_ok.
Print Assumptions Utf8.Utf8Proofs.step_output_ok.
Print Assumptions Utf8.Utf8Proofs.ref_done_output_ok.
Print Assumptions Utf8.Utf8Proofs.Inv_len.
Print Assumptions Utf8.Utf8Proofs.seq_cp_value1.
Print Assumptions Utf8.Utf8Proofs.seq_cp_value2.
Print Assumptions Utf8.Utf8Proofs.seq_cp_value3.
Print Assumptions Utf8.Utf8Proofs.seq_cp_value4.
Print Assumptions Utf8.Utf8Proofs.step_empty_ascii.
Print Assumptions Utf8.Utf8Proofs.step_empty_lead.
Print Assumptions Utf8.Utf8Proofs.step_empty_bad.
Print Assumptions Utf8.Utf8Proofs.step_pending.
Print Assumptions Utf8.Utf8StepFacts.step_reject.
Print Assumptions Utf8.Utf8StepFacts.step_extend.
Print Assumptions Utf8.Utf8StepFacts.step_complete.
Print Assumptions Utf8.Utf8StepFacts.pending_lead.
Print Assumptions Utf8.Utf8StepFacts.lo_next.
Print Assumptions Utf8.Utf8StepFacts.hi_next.
Print Assumptions Utf8.Utf8StepFacts.pending_vp.
Print Assumptions Utf8.Utf8StepFacts.pending_vs.
Print Assumptions Utf8.Utf8StepFacts.seq_cp_bound.
Print Assumptions Utf8.Utf8StepFacts.ref_decode_buffer_snoc.
Print Assumptions Utf8.Utf8StepFacts.cp_units.
Print Assumptions Utf8.Utf8StepFacts.text_units.
Print Assumptions Utf8.Utf8StepFacts.pending_units.
Print Assumptions Utf8.Utf8StepFacts.text_units_app.
Print Assumptions Utf8.Utf8StepFacts.cp_units_le2.
Print Assumptions Utf8.Utf8StepFacts.FFFD_units1.
Print Assumptions Utf8.Utf8StepFacts.step_empty_units_bound.
Print Assumptions Utf8.Utf8StepFacts.step_units_bound.
Print Assumptions Utf8.Utf8StepFacts.fold_units_bound.
Print Assumptions Utf8.Utf8StepFacts.decode_units_bound.
Print Assumptions Utf8.Utf8StepFacts.ref_done_units_bound.
