import WasmLoop

namespace PrefixWasm
open Wasm SmallStep

def dataEntry (s : Bool) (log : Host) (mem : Mem) (n : Nat) : Config Host :=
  ⟨.running
    { locals := { params := [.i32 (UInt32.ofNat n)],
                  locals := [.i32 0, .i32 0, .i32 0] }
      code := [.const 16384, .localSet 2, .block 0 0 [.loop 0 0 loopBody]] ++ afterLoop
      resultArity := 0, callerRemainder := [] }, machine s log mem⟩

theorem data_entry (s : Bool) (log : Host) (mem : Mem) (n : Nat) :
    startExportConfig? env prefixModule "data"
      { initial := store s log mem, arguments := [.i32 (UInt32.ofNat n)] } =
      some (dataEntry s log mem n) := rfl

theorem data_entry_steps (s : Bool) (log : Host) (mem : Mem) (n : Nat) :
    Steps (dataEntry s log mem n)
      [.instruction (.const 16384), .instruction (.localSet 2),
        .instruction (.block 0 0 [.loop 0 0 loopBody]), .instruction (.loop 0 0 loopBody)]
      (loopHead s log mem 0 n 16384 0) := by
  wasm_steps [.const, (.localSet rfl), .block, .loop]
  exact Steps.refl _

/-- The actual bounded Wasm callback, for arbitrary persistent memory and log. -/
theorem data_correct (s : Bool) (log : Host) (mem : Mem) (chunk : List UInt32)
    (hp : mem.pages = 1) (hb : chunk.length ≤ 4096) :
    Runs "data" (store s log (writeWords mem 0 chunk)) [.i32 (UInt32.ofNat chunk.length)]
      (store (LinePrefix.run s chunk).1 (log ++ [.write 1 (LinePrefix.run s chunk).2])
        (writeWords (writeWords mem 0 chunk) 16384 (LinePrefix.run s chunk).2)) := by
  let prepared := writeWords mem 0 chunk
  let result := LinePrefix.run s chunk
  let finalMem := writeWords prepared 16384 result.2
  have hpages : prepared.pages = 1 := by simpa [prepared, writeWords_pages] using hp
  obtain ⟨p', c', trace, hloop⟩ := loop_correct chunk.length s log prepared 0 16384 0
    (by omega) (by omega) hpages
  have heq := transform_prepared s mem chunk hb
  change transform s prepared 0 16384 chunk.length =
    (result.1, finalMem, 16384+4*result.2.length) at heq
  rw [heq] at hloop
  have hbound : 16384+4*result.2.length ≤ 65536 := by
    have hl := run_length s chunk
    change result.2.length ≤ 3*chunk.length at hl
    omega
  have hfinalpages : finalMem.pages = 1 := by
    simpa [finalMem, writeWords_pages] using hpages
  have hout : exitOutput (16384+4*result.2.length) finalMem = result.2 := by
    unfold exitOutput
    rw [exit_count _ (by omega) hbound]
    rw [show (16384+4*result.2.length-16384)/4 = result.2.length by omega]
    exact readWords_writeWords prepared 16384 result.2 hbound
  have hexit := exit_correct result.1 log finalMem p' (16384+4*result.2.length) c'
    (by omega) hbound hfinalpages
  rw [hout] at hexit
  refine ⟨dataEntry s log prepared chunk.length, data_entry s log prepared chunk.length, ?_⟩
  obtain ⟨exitTrace, values, final, exitSteps, post⟩ := hexit
  exact ⟨_, values, final,
    Steps.trans (data_entry_steps s log prepared chunk.length) (Steps.trans hloop exitSteps), post⟩

end PrefixWasm
#print axioms PrefixWasm.data_correct
