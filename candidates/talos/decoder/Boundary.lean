/-
Boundary.lean -- what is claimed about the shipped Wasm module.

Reviewed together with Utf8Laws.lean (the spec); nothing else needs to be
read to know what is proved.  Definitions and `Prop` statements only.

The claim, in words: Talos's WAT decoder accepts `decoder.printed.wat` (the
output of `wasm-tools print decoder.wasm`) and produces a module, and for
that module there is a decoder `D` satisfying the spec's three streaming laws
(`D.Correct`) whose behaviour the module's three exports realize:

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

/-- Talos's verification decoder succeeds on the printed text of the shipped
bytes, producing a module `m`, and `m` realizes a decoder that satisfies the
spec.  (The decoder is a function, so `m` is the only module it produces.) -/
def ShippedModuleCorrect : Prop :=
  ∃ m : Module, Decoder.Wat.decodeForVerification printedWat = .ok m ∧
    ∃ D : Decoder, D.Correct ∧ Realizes m D

/-! ## The guarantees apply to the shipped wrapper (non-vacuity)

The guarantees above hold only for calls that meet their conditions (memory
size, where the input and output areas are, the state value).  This section
says that every call the shipped JavaScript wrapper `decoder.mjs` makes meets
all of them, so the guarantees are not empty for the real module as it is
used.

The wrapper's choices, as numbers (`check.sh` reads them from the marked lines
of `decoder.mjs`, and the memory size from the module text, and fails if they
differ from the numbers here):

  * it copies each piece of input (at most `wrapperMaxChunk` bytes; longer
    input is split) to address `wrapperInputAddr`;
  * it asks for the output at address `wrapperOutputAddr`, for both
    `decode_buffer` and `decode_done`;
  * it never grows the module's memory, which has `shippedMemoryPages` pages
    of 64 KiB each.

The state condition (`R s v`) needs nothing here: the wrapper only passes
state values that `decode_start_state` or `decode_buffer` returned, and their
guarantees say exactly that such a value is related to the decoder's state.
-/

/-- Where the wrapper puts the input bytes. -/
def wrapperInputAddr : Nat := 0
/-- The most input bytes the wrapper passes in one call. -/
def wrapperMaxChunk : Nat := 1048576
/-- Where the wrapper asks for the output. -/
def wrapperOutputAddr : Nat := 1048576
/-- The size of the module's memory, in 64 KiB pages. -/
def shippedMemoryPages : Nat := 160

/-- A memory as the wrapper's instance has it: the module's size. -/
def WrapperMem (mem : Mem) : Prop := mem.pages = shippedMemoryPages

/-- For module `m`, every call the wrapper makes meets the conditions above:

  1. the instance starts with a memory of the module's size, and its initial
     store is the store the guarantees start from (`storeWith`), so the start
     guarantee applies to it;
  2. the input area and the largest output area (two code points of four
     bytes per input byte) lie inside that memory and do not overlap;
  3. on any memory of that size (any contents), decode_start_state's memory
     condition holds; decode_buffer's layout condition holds for every input
     length up to the maximum, with input and output at the wrapper's
     addresses; decode_done has room for one code point at the output address;
  4. a guarantee that changes memory only in place (`sameOutside`, which all
     three guarantees state) leaves a memory of the same size, so the next call
     again meets the conditions. -/
def WrapperCallsCovered (m : Module) : Prop :=
  WrapperMem (m.initialStore : Store Unit).mem ∧
  storeWith m (m.initialStore : Store Unit).mem = m.initialStore ∧
  wrapperInputAddr + wrapperMaxChunk ≤ wrapperOutputAddr ∧
  wrapperOutputAddr + 8 * wrapperMaxChunk ≤ shippedMemoryPages * 65536 ∧
  (∀ mem : Mem, WrapperMem mem →
    mem.pages ≤ 65536 ∧
    (∀ len : UInt32, len.toNat ≤ wrapperMaxChunk →
      BufferLayout mem (UInt32.ofNat wrapperInputAddr) len (UInt32.ofNat wrapperOutputAddr)) ∧
    inMem mem ((UInt32.ofNat wrapperOutputAddr).toNat + 4)) ∧
  (∀ (mem mem' : Mem) (lo len : Nat), WrapperMem mem → sameOutside mem mem' lo len →
    WrapperMem mem')

/-- Second top-level claim: the module Talos decodes from the shipped bytes
(the same `m` as in `ShippedModuleCorrect`) is used by the wrapper only in
calls its guarantees cover. -/
def ShippedWrapperCovered : Prop :=
  ∃ m : Module, Decoder.Wat.decodeForVerification printedWat = .ok m ∧
    WrapperCallsCovered m

end Utf8Boundary
