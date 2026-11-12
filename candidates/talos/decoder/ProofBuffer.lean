/-
ProofBuffer.lean -- the decode_buffer export call, against the Wasm-level
model `runM` (Boundary's `Calls` form): block + loop entry, then loop_correct.

EXPORTS
  reach_terminates       a `Reach` to a `.done` configuration gives `TerminatesWith`
  buffer_runs            decode_buffer(v, inp, len, out) returns and writes as runM says
-/
import ProofLoop

namespace Utf8Wasm
open Wasm SmallStep Utf8Boundary

theorem reach_terminates {c : Cfg} {vals : List Value} {st : MachineStore Unit}
    {post : List Value → MachineStore Unit → Prop}
    (h : Reach c ⟨.done vals, st⟩) (hp : post vals st) : TerminatesWith c post :=
  let ⟨tr, ht⟩ := h; ⟨tr, vals, st, ht, hp⟩

theorem buffer_runs (mem : Mem) (v inp len out : UInt32) (hw : mem.pages ≤ 65536)
    (hio : inp.toNat + len.toNat ≤ out.toNat)
    (hb : out.toNat + 8 * len.toNat ≤ mem.pages * 65536) :
    Calls decoderModule "decode_buffer" mem [v, inp, len, out] fun ws final =>
      ws = [(runM v out mem (bytesAt mem inp.toNat len.toNat)).1,
            (runM v out mem (bytesAt mem inp.toNat len.toNat)).2.1] ∧
      final = storeWith decoderModule (runM v out mem (bytesAt mem inp.toNat len.toNat)).2.2 := by
  refine ⟨⟨.running
      { locals := { params := [.i32 v, .i32 inp, .i32 len, .i32 out], locals := [] }
        code := bufBody, resultArity := 2, callerRemainder := [] },
     ⟨rt0, storeWith decoderModule mem⟩⟩, rfl, ?_⟩
  have h := loop_correct len.toNat (storeWith decoderModule mem) v inp len out rfl hw hio hb
  refine reach_terminates (Reach.cons .block (Reach.cons .loop h)) ?_
  refine ⟨_, rfl, rfl, ?_⟩
  rfl

end Utf8Wasm
