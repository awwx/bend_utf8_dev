/-
ProofLoop.lean -- the decode_buffer loop (func 7) against the Wasm-level
model `runM` (a left fold of `stepM`), spike style: explicit loop-head
configuration, induction on the remaining length.
-/
import ProofStep
import Boundary

namespace Utf8Wasm
open Wasm SmallStep

set_option maxHeartbeats 0

/-- Model of the loop: fold `stepM` over the bytes, writing code points. -/
def runM : UInt32 → UInt32 → Mem → List UInt8 → UInt32 × UInt32 × Mem
  | s, out, mem, [] => (s, out, mem)
  | s, out, mem, b :: bs =>
    runM (stepM s b.toUInt32).1 (endAddr out (stepM s b.toUInt32).2)
      (writeCps mem out (stepM s b.toUInt32).2) bs

theorem stepA0_len (b : UInt32) : (stepA 0 b (0, [])).2.length ≤ 1 := by
  unfold stepA; split <;> (try split) <;> (try split) <;> simp

theorem stepA_len (s b : UInt32) (k : UInt32 × List UInt32) :
    (stepA s b k).2.length ≤ 1 ∨ stepA s b k = k := by
  unfold stepA; split <;> (try split) <;> (try split) <;> simp

theorem stepM_len (s b : UInt32) : (stepM s b).2.length ≤ 2 := by
  have h0 := stepA0_len b
  unfold stepM
  rcases stepA_len s b ((stepA 0 b (0, [])).1, 65533 :: (stepA 0 b (0, [])).2) with h | h
  · omega
  · rw [h]; simp; omega

theorem endAddr_toNat (out : UInt32) (cs : List UInt32) (h : out.toNat + 4 * cs.length < 2 ^ 32) :
    (endAddr out cs).toNat = out.toNat + 4 * cs.length := by
  induction cs generalizing out with
  | nil => simp [endAddr]
  | cons c cs ih =>
    simp only [endAddr, List.length_cons] at *
    rw [ih _ (by rw [UInt32.toNat_add]; simp; omega)]
    rw [UInt32.toNat_add]; simp; omega

theorem writeCps_pages (mem : Mem) (out : UInt32) (cs : List UInt32) :
    (writeCps mem out cs).pages = mem.pages := by
  induction cs generalizing mem out with
  | nil => rfl
  | cons c cs ih => simp [writeCps, ih, Mem.write32]

theorem writeCps_below (mem : Mem) (out : UInt32) (cs : List UInt32) (a : Nat) :
    out.toNat + 4 * cs.length < 2 ^ 32 → a < out.toNat →
    (writeCps mem out cs).bytes a = mem.bytes a := by
  induction cs generalizing mem out with
  | nil => intro _ _; rfl
  | cons c cs ih =>
    intro h ha
    simp only [List.length_cons] at h
    have h4 : (4 + out).toNat = out.toNat + 4 := by rw [UInt32.toNat_add]; simp; omega
    simp only [writeCps]
    rw [ih (mem.write32 out c) (4 + out) (by rw [h4]; omega) (by rw [h4]; omega)]
    simp only [Mem.write32]
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]

def loopBody : Program := [
  .localGet 2, .eqz, .br_if 1, .localGet 0, .localGet 1, .load8U 0, .localGet 3, .call 5,
  .localSet 3, .localSet 0, .localGet 1, .const 1, .add, .localSet 1,
  .localGet 2, .const 1, .sub, .localSet 2, .br 0]

def bufBody : Program := [.block 0 0 [.loop 0 0 loopBody], .localGet 0, .localGet 3]

theorem buf_body_eq : (decoderModule.funcs[7]?.map (·.body)) = some bufBody := by rfl

def blockFrame : ControlFrame :=
  { kind := .block, paramArity := 0, resultArity := 0,
    body := [.loop 0 0 loopBody], continuation := [.localGet 0, .localGet 3], belowStack := [] }

def loopFrame : ControlFrame :=
  { kind := .loop, paramArity := 0, resultArity := 0,
    body := loopBody, continuation := [], belowStack := [] }

def loopHead (w : Store Unit) (s inp len out : UInt32) : Cfg :=
  ⟨.running
    { locals := { params := [.i32 s, .i32 inp, .i32 len, .i32 out], locals := [], values := [] }
      code := loopBody, resultArity := 2, callerRemainder := []
      control := [loopFrame, blockFrame] }, ⟨rt0, w⟩⟩

theorem loop_exit (w : Store Unit) (s inp out : UInt32) :
    Reach (loopHead w s inp 0 out) ⟨.done [.i32 out, .i32 s], ⟨rt0, w⟩⟩ := by
  unfold loopHead loopBody
  refine Reach.cons (Step.localGet rfl) ?_
  refine Reach.cons (Step.eqz rfl) ?_
  refine Reach.cons (Step.brIf (by decide) rfl) ?_
  refine Reach.cons (Step.localGet rfl) ?_
  refine Reach.cons (Step.localGet rfl) ?_
  exact Reach.cons .finish (Reach.refl _)

theorem loop_iter (w : Store Unit) (s inp len out : UInt32) (hl : len ≠ 0)
    (hw : w.mem.pages ≤ 65536) (hp : inp.toNat + 1 ≤ w.mem.pages * 65536)
    (hb : out.toNat + 8 ≤ w.mem.pages * 65536) :
    Reach (loopHead w s inp len out)
      (loopHead { w with mem := writeCps w.mem out (stepM s (w.mem.read8 inp).toUInt32).2 }
        (stepM s (w.mem.read8 inp).toUInt32).1 (1 + inp) (len - 1)
        (endAddr out (stepM s (w.mem.read8 inp).toUInt32).2)) := by
  unfold loopHead loopBody
  refine Reach.cons (Step.localGet rfl) ?_
  refine Reach.cons (Step.eqz (result := 0) (by simp [hl])) ?_
  refine Reach.cons .brIfZero ?_
  refine Reach.cons (Step.localGet rfl) ?_
  refine Reach.cons (Step.localGet rfl) ?_
  refine Reach.cons (Step.load8U rfl (by simpa using hp)) ?_
  refine Reach.cons (Step.localGet rfl) ?_
  refine Reach.trans (call_step hw hb) ?_
  refine Reach.cons (Step.localSet rfl) ?_
  refine Reach.cons (Step.localSet rfl) ?_
  refine Reach.cons (Step.localGet rfl) ?_
  refine Reach.cons Step.const ?_
  refine Reach.cons Step.add ?_
  refine Reach.cons (Step.localSet rfl) ?_
  refine Reach.cons (Step.localGet rfl) ?_
  refine Reach.cons Step.const ?_
  refine Reach.cons Step.sub ?_
  refine Reach.cons (Step.localSet rfl) ?_
  refine Reach.cons (Step.br rfl) ?_
  simp
  exact Reach.refl _

open Utf8Boundary in
theorem bytesAt_succ (mem : Mem) (p n : Nat) :
    bytesAt mem p (n + 1) = mem.bytes p :: bytesAt mem (p + 1) n := by
  simp [bytesAt, List.range_succ_eq_map, Nat.add_comm, Nat.add_left_comm]

open Utf8Boundary in
theorem bytesAt_congr (m1 m2 : Mem) (p n : Nat) (h : ∀ a, a < p + n → m1.bytes a = m2.bytes a) :
    bytesAt m1 p n = bytesAt m2 p n := by
  simp only [bytesAt]
  apply List.map_congr_left
  intro i hi
  simp at hi
  exact h _ (by omega)

open Utf8Boundary in
theorem loop_correct (n : Nat) : ∀ (w : Store Unit) (s inp len out : UInt32),
    len.toNat = n → w.mem.pages ≤ 65536 → inp.toNat + n ≤ out.toNat →
    out.toNat + 8 * n ≤ w.mem.pages * 65536 → out.toNat + 8 * n < 2 ^ 32 →
    Reach (loopHead w s inp len out)
      ⟨.done [.i32 (runM s out w.mem (bytesAt w.mem inp.toNat n)).2.1,
              .i32 (runM s out w.mem (bytesAt w.mem inp.toNat n)).1],
        ⟨rt0, { w with mem := (runM s out w.mem (bytesAt w.mem inp.toNat n)).2.2 }⟩⟩ := by
  induction n with
  | zero =>
    intro w s inp len out hl _ _ _ _
    have : len = 0 := UInt32.toNat_inj.mp (by simpa using hl)
    subst this
    simpa [bytesAt, runM] using loop_exit w s inp out
  | succ n ih =>
    intro w s inp len out hl hw hio hb hlt
    have hl0 : len ≠ 0 := by intro h; subst h; simp at hl
    have h1 := loop_iter w s inp len out hl0 hw (by omega) (by omega)
    have hlen := stepM_len s (w.mem.read8 inp).toUInt32
    have hpg : w.mem.pages * 65536 ≤ 2 ^ 32 := by omega
    have hend := endAddr_toNat out (stepM s (w.mem.read8 inp).toUInt32).2 (by omega)
    have hinp : (1 + inp).toNat = inp.toNat + 1 := by
      rw [UInt32.toNat_add]; simp; omega
    have hl1 : (len - 1).toNat = n := by
      rw [UInt32.toNat_sub_one_eq (by omega)]; omega
    have h2 := ih { w with mem := writeCps w.mem out (stepM s (w.mem.read8 inp).toUInt32).2 }
      (stepM s (w.mem.read8 inp).toUInt32).1 (1 + inp) (len - 1)
      (endAddr out (stepM s (w.mem.read8 inp).toUInt32).2) hl1 (by simpa [writeCps_pages] using hw)
      (by rw [hinp, hend]; omega)
      (by simp only [writeCps_pages]; rw [hend]; omega) (by rw [hend]; omega)
    have hbytes : bytesAt (writeCps w.mem out (stepM s (w.mem.read8 inp).toUInt32).2) (1 + inp).toNat n =
        bytesAt w.mem (inp.toNat + 1) n := by
      rw [hinp]
      apply bytesAt_congr
      intro a ha
      exact writeCps_below _ _ _ _ (by omega) (by omega)
    simp only [hbytes] at h2
    rw [bytesAt_succ]
    simp only [runM]
    simp only [Mem.read8] at h1 h2
    simpa using Reach.trans h1 h2

end Utf8Wasm
