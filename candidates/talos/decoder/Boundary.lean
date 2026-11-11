/-
Boundary.lean -- what is claimed about the shipped Wasm module.

Reviewed together with Utf8Laws.lean (the spec); nothing else needs to be
read to know what is proved.  Definitions and `Prop` statements only.

The claim, in words: for the module that Talos's WAT decoder produces from
`decoder.printed.wat` (the output of `wasm-tools print decoder.wasm`), there
is a decoder `D` satisfying the spec's three streaming laws (`D.Correct`)
whose behaviour the module's three exports realize:

  * the decoder state is one i32 value (related to `D.State` by some
    relation `R`, which is existential: its encoding is the module's choice);
  * input bytes are `len` bytes of linear memory at address `inp`;
  * output text is written as little-endian 32-bit code points at address
    `out`, and the export returns the end address of what it wrote;
  * each call terminates without trapping (total correctness in Talos's
    small-step semantics), and changes no memory byte outside the written
    output, nor anything else in the store.

Instantiation is not modelled by Talos.  A call starts from the store
`storeWith m mem`: the store Talos's `Module.initialStore` builds for the
module, with its memory replaced by an arbitrary memory `mem` (any contents,
any page count up to the Wasm 32-bit limit of 65536 pages).  Because the
module has no globals, tables or imports, and every export leaves the store
in this form again (see the postconditions), this covers every call in any
sequence of calls on one instance, including after the host writes to
memory or grows it.
-/
import Utf8Laws
import Interpreter.Wasm.Host.Run
import Interpreter.Wasm.Decoder.Wat

namespace Utf8Boundary
open Wasm

/-- The text `wasm-tools print decoder.wasm` printed; `check.sh` regenerates
it from the shipped bytes and fails if it differs. -/
def printedWat : String := include_str "decoder.printed.wat"

/-! ## Memory layout -/

/-- One code point as four bytes, little-endian. -/
def u32le (c : UInt32) : List UInt8 :=
  [c.toUInt8, (c >>> 8).toUInt8, (c >>> 16).toUInt8, (c >>> 24).toUInt8]

/-- How a text is laid out in memory: its code points as consecutive
little-endian u32 values. -/
def textBytes : Text → List UInt8
  | [] => []
  | c :: t => u32le c ++ textBytes t

/-- The `len` bytes of `mem` starting at address `ptr`. -/
def bytesAt (mem : Mem) (ptr len : Nat) : List UInt8 :=
  (List.range len).map fun i => mem.bytes (ptr + i)

/-- Address `a` is a valid byte address of `mem`. -/
def inMem (mem : Mem) (a : Nat) : Prop := a ≤ mem.pages * 65536

/-- `mem'` has the same size as `mem` and the same bytes outside
`[lo, lo + len)`. -/
def sameOutside (mem mem' : Mem) (lo len : Nat) : Prop :=
  mem'.pages = mem.pages ∧
  ∀ a, (a < lo ∨ lo + len ≤ a) → mem'.bytes a = mem.bytes a

/-! ## Calls -/

/-- No imports: the empty host environment. -/
abbrev env : HostEnv Unit := {}

/-- The store a call starts from (see the header). -/
def storeWith (m : Module) (mem : Mem) : Store Unit :=
  { (m.initialStore : Store Unit) with mem := mem }

/-- Call export `op` with i32 arguments `args` (in source order) on the store
`storeWith m mem`; it terminates without trapping and `post` holds of the
returned i32 values (in source order) and the final store. -/
def Calls (m : Module) (op : String) (mem : Mem) (args : List UInt32)
    (post : List UInt32 → Store Unit → Prop) : Prop :=
  RunsExportWith env m op
    { initial := storeWith m mem, arguments := (args.map Value.i32).reverse }
    (fun r => post' r.values.reverse r.final)
where
  post' (vs : List Value) (final : Store Unit) : Prop :=
    ∃ ws : List UInt32, vs = ws.map Value.i32 ∧ post ws final

/-! ## The three exports -/

/-- `decode_start_state()` returns a value related to `D.start`. -/
def StartOk (m : Module) (D : Decoder) (R : D.State → UInt32 → Prop) : Prop :=
  ∀ mem : Mem, mem.pages ≤ 65536 →
    Calls m "decode_start_state" mem [] fun ws final =>
      ∃ v, ws = [v] ∧ R D.start v ∧ final = storeWith m mem

/-- Layout contract for `decode_buffer(state, inp, len, out)`: the input
`[inp, inp + len)` lies before an output area `[out, out + 8 * len)`
(room for two code points per input byte) that fits in memory. -/
def BufferLayout (mem : Mem) (inp len out : UInt32) : Prop :=
  mem.pages ≤ 65536 ∧
  inp.toNat + len.toNat ≤ out.toNat ∧
  inMem mem (out.toNat + 8 * len.toNat)

/-- `decode_buffer(v, inp, len, out)`, with `R s v` and `bs` the input bytes,
returns `(v', end)` where `R s' v'`, `(s', t) = D.decode_buffer s bs`, the
encoding of `t` is at `[out, end)` with `end = out + 4 * |t|`, `t` fits in the
output area, and nothing else in the store changed. -/
def BufferOk (m : Module) (D : Decoder) (R : D.State → UInt32 → Prop) : Prop :=
  ∀ (s : D.State) (v : UInt32) (mem : Mem) (inp len out : UInt32),
    R s v → BufferLayout mem inp len out →
    Calls m "decode_buffer" mem [v, inp, len, out] fun ws final =>
      let bs := bytesAt mem inp.toNat len.toNat
      let s' := (D.decode_buffer s bs).1
      let t := (D.decode_buffer s bs).2
      ∃ v' mem',
        ws = [v', UInt32.ofNat (out.toNat + 4 * t.length)] ∧
        R s' v' ∧
        t.length ≤ 2 * len.toNat ∧
        bytesAt mem' out.toNat (4 * t.length) = textBytes t ∧
        sameOutside mem mem' out.toNat (4 * t.length) ∧
        final = storeWith m mem'

/-- `decode_done(v, out)`, with `R s v` and room for one code point at `out`,
returns `end` where the encoding of `t = D.decode_done s` is at `[out, end)`,
`end = out + 4 * |t|`, `|t| ≤ 1`, and nothing else in the store changed. -/
def DoneOk (m : Module) (D : Decoder) (R : D.State → UInt32 → Prop) : Prop :=
  ∀ (s : D.State) (v : UInt32) (mem : Mem) (out : UInt32),
    R s v → mem.pages ≤ 65536 → inMem mem (out.toNat + 4) →
    Calls m "decode_done" mem [v, out] fun ws final =>
      let t := D.decode_done s
      ∃ mem',
        ws = [UInt32.ofNat (out.toNat + 4 * t.length)] ∧
        t.length ≤ 1 ∧
        bytesAt mem' out.toNat (4 * t.length) = textBytes t ∧
        sameOutside mem mem' out.toNat (4 * t.length) ∧
        final = storeWith m mem'

/-- The module realizes `D`: some relation `R` between decoder states and
i32 values makes all three exports behave as `D` does. -/
def Realizes (m : Module) (D : Decoder) : Prop :=
  ∃ R : D.State → UInt32 → Prop, StartOk m D R ∧ BufferOk m D R ∧ DoneOk m D R

/-! ## The top-level claim -/

/-- Whatever module Talos's verification decoder produces from the printed
text of the shipped bytes realizes a decoder that satisfies the spec. -/
def ShippedModuleCorrect : Prop :=
  ∀ m : Module, Decoder.Wat.decodeForVerification printedWat = .ok m →
    ∃ D : Decoder, D.Correct ∧ Realizes m D

end Utf8Boundary
