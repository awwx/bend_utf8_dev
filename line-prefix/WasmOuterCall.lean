import WasmOuter

namespace PrefixWasm
open Wasm SmallStep PrefixGc

def outerCaller (ref len pos stop : Nat) (unit : UInt32) : CallFrame :=
  { locals := { params := [.externref (some ref)]
                locals := [.i32 (UInt32.ofNat len), .i32 (UInt32.ofNat pos),
                  .i32 (UInt32.ofNat stop), .i32 unit] }
    continuation := outerTail, resultArity := 0, callerRemainder := []
    control := outerControls, returningInstance := ⟨0⟩ }

/-- The substring builtin snapshots one bounded piece. The helper transforms
that piece and returns to the outer loop, which advances its input position. -/
theorem outer_call_steps (s : Bool) (host : Host) (heap : List GcObject)
    (ref pos stop : Nat) (unit : UInt32) (all : List UInt32)
    (hr : host.strings[ref]? = some all) (hp : pos ≤ stop)
    (he : stop ≤ all.length) (hlen : all.length < 2^32)
    (hb : stop-pos ≤ 4096)
    (hu : ∀ u ∈ (all.drop pos).take (stop-pos), u.toNat < 65536) :
    ∃ trace, Steps (outerConfig s host heap ref all.length pos stop unit outerCallBody) trace
      (outerHead (LinePrefix.run s ((all.drop pos).take (stop-pos))).1
        (callbackHost s host ((all.drop pos).take (stop-pos)))
        (callbackHeap s heap ((all.drop pos).take (stop-pos)))
        ref all.length stop stop unit) := by
  let part := (all.drop pos).take (stop-pos)
  have hpart : part.length = stop-pos := by
    simp only [part, List.length_take, List.length_drop]
    omega
  have hs : UInt32.ofNat stop - UInt32.ofNat pos = UInt32.ofNat part.length := by
    rw [← UInt32.ofNat_sub hp, hpart]
  obtain ⟨callTrace, hcall⟩ := chunk_call s host heap part (by omega) hu
    (outerCaller ref all.length pos stop unit) [] rfl
  have hsub := sub_invoke s host heap ref all pos stop hr hp he hlen
  have hentry : Steps (outerConfig s host heap ref all.length pos stop unit outerCallBody)
      (([.localGet 0, .localGet 2, .localGet 3] : Program).map StepKind.instruction ++
        [.host 9] ++ ([.localGet 3, .localGet 2, .sub] : Program).map StepKind.instruction)
      (chunkCall s host heap part (outerCaller ref all.length pos stop unit) []) := by
    wasm_steps [(.localGet rfl), (.localGet rfl), (.localGet rfl),
      (.callHostReturn (by change 9 < 11; decide) rfl rfl hsub),
      (.localGet rfl), (.localGet rfl), .sub]
    rw [hs]
    exact Steps.refl _
  have htail : Steps
      (resumeConfig (outerCaller ref all.length pos stop unit) []
        (LinePrefix.run s part).1 (callbackHost s host part) (callbackHeap s heap part))
      (outerTail.map StepKind.instruction)
      (outerHead (LinePrefix.run s part).1 (callbackHost s host part)
        (callbackHeap s heap part) ref all.length stop stop unit) := by
    wasm_steps [(.localGet rfl), (.localSet rfl)]
    exact Steps.single (.br rfl)
  exact ⟨_, Steps.trans hentry (Steps.trans hcall htail)⟩

end PrefixWasm
