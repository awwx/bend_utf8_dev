/-
ProofMain.lean -- the whole-buffer refinement, the three exports in
Boundary's form, and the top-level theorem
`Utf8Wasm.shippedModuleCorrect : Utf8Boundary.ShippedModuleCorrect`.

Witnesses for Boundary's existentials: D := Utf8Pure.RefDecoder, R := Rel
(ProofDone.lean: at most three pending bytes, packed by `enc`).

The output area may end exactly at 2^32; see ProofLayout.lean for why that
case needs no extra hypothesis.

EXPORTS
  Calls_mono                         weaken the postcondition of a `Calls`
  runM_enc                           runM on enc p = enc / endAddr / writeCps of decodeBuffer p
  start_ok', buffer_ok, done_ok      Boundary's StartOk / BufferOk / DoneOk with R := Rel
  shippedModuleCorrect               the top-level claim
  ShippedModuleCorrect_v1, shippedModuleCorrect_implies_v1, shippedModuleCorrect_v1
                                     the pre-audit statement, implied by the current one
Memory-layout lemmas (writeCps_bytes, writeCps_outside, endAddr_eq, ...) are in
ProofLayout.lean; decodeBuffer_bounds is in the pure layer (Utf8StepFacts.lean).
-/
import ProofBuffer
import ProofDone
import ProofRefine

namespace Utf8Wasm
open Wasm Utf8Boundary Utf8Pure

theorem Calls_mono {m : Module} {op : String} {mem : Mem} {args : List UInt32}
    {P Q : List UInt32 → Store Unit → Prop} (h : ∀ ws f, P ws f → Q ws f)
    (hc : Calls m op mem args P) : Calls m op mem args Q := by
  obtain ⟨c, hc1, tr, vals, st, hs, ws, hws, hp⟩ := hc
  exact ⟨c, hc1, tr, vals, st, hs, ws, hws, h _ _ hp⟩

/-! ## Whole buffer -/

theorem runM_enc (bs : List UInt8) : ∀ (p : List UInt8) (out : UInt32) (mem : Mem), p.length ≤ 3 →
    runM (enc p) out mem bs =
      (enc (decodeBuffer p bs).1, endAddr out (decodeBuffer p bs).2,
        writeCps mem out (decodeBuffer p bs).2) := by
  induction bs with
  | nil => intro p out mem _; rfl
  | cons b bs ih =>
    intro p out mem hp
    simp only [runM, stepM_enc p hp b]
    rw [ih _ _ _ (step_length p hp b), decodeBuffer_cons, writeCps_append, endAddr_append]

/-! ## The three exports in Boundary's form -/

theorem start_ok' : StartOk decoderModule RefDecoder Rel := start_ok

theorem buffer_ok : BufferOk decoderModule RefDecoder Rel := by
  intro s v mem inp len out ⟨hs, hv⟩ ⟨hw, hio, hb⟩
  subst hv
  unfold inMem at hb
  refine Calls_mono ?_ (buffer_runs mem (enc s) inp len out hw hio hb)
  rintro ws final ⟨rfl, rfl⟩
  obtain ⟨hs', ht⟩ := decodeBuffer_bounds (bytesAt mem inp.toNat len.toNat) s hs
  simp only [bytesAt_length] at ht
  have hfit : out.toNat + 4 * (decodeBuffer s (bytesAt mem inp.toNat len.toNat)).2.length ≤ 2 ^ 32 := by
    omega
  rw [runM_enc _ s out mem hs]
  exact ⟨_, _, by rw [endAddr_eq]; rfl, ⟨hs', rfl⟩, ht, writeCps_bytes _ _ _ hfit,
    ⟨writeCps_pages _ _ _, fun i hi => writeCps_outside _ _ _ _ hfit hi⟩, rfl⟩

theorem done_ok : DoneOk decoderModule RefDecoder Rel := by
  intro s v mem out ⟨hs, hv⟩ hw hb
  subst hv
  unfold inMem at hb
  refine Calls_mono ?_ (done_runs mem (enc s) out hb)
  rintro ws final ⟨h0, h1⟩
  by_cases hs0 : s = []
  · subst hs0
    obtain ⟨rfl, rfl⟩ := h0 rfl
    exact ⟨mem, by simp [RefDecoder, decodeDone], by simp [RefDecoder, decodeDone],
      by simp [RefDecoder, decodeDone, bytesAt, textBytes], ⟨rfl, fun _ _ => rfl⟩, rfl⟩
  · obtain ⟨rfl, rfl⟩ := h1 (fun h => hs0 ((enc_eq_zero hs).mp h))
    have he : s.isEmpty = false := by
      cases s with
      | nil => exact absurd rfl hs0
      | cons _ _ => rfl
    have ht : RefDecoder.decode_done s = [65533] := by
      simp [RefDecoder, decodeDone, he, replacement_char]
    have hfit : out.toNat + 4 * [(65533 : UInt32)].length ≤ 2 ^ 32 := by simp; omega
    simp only [ht]
    refine ⟨writeCps mem out [65533], ?_, by simp, writeCps_bytes _ _ _ hfit,
      ⟨writeCps_pages _ _ _, fun i hi => writeCps_outside _ _ _ _ hfit hi⟩, rfl⟩
    rw [← endAddr_eq]; rfl

/-! ## The top-level claim -/

theorem shippedModuleCorrect : ShippedModuleCorrect :=
  ⟨decoderModule, decoderModule_decodes,
    RefDecoder, RefDecoder_correct, Rel, start_ok', buffer_ok, done_ok⟩

/-! ## Sanity check: the current claim implies the earlier one

`ShippedModuleCorrect_v1` is the text of `Utf8Boundary.ShippedModuleCorrect`
before the audit fix (AUDIT.txt M2): a universal statement over decoded
modules, vacuously true if decoding failed.  The current Boundary statement
(existence of the decoded module plus its correctness) implies it, so the
change dropped nothing. -/

def ShippedModuleCorrect_v1 : Prop :=
  ∀ m : Module, Decoder.Wat.decodeForVerification Utf8Boundary.printedWat = .ok m →
    ∃ D : Decoder, D.Correct ∧ Realizes m D

theorem shippedModuleCorrect_implies_v1 :
    Utf8Boundary.ShippedModuleCorrect → ShippedModuleCorrect_v1 := by
  rintro ⟨m, hm, hc⟩ m' hm'
  rw [hm] at hm'
  cases hm'
  exact hc

theorem shippedModuleCorrect_v1 : ShippedModuleCorrect_v1 :=
  shippedModuleCorrect_implies_v1 shippedModuleCorrect

end Utf8Wasm
