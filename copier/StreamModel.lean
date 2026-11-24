import Utf8Roundtrip

namespace Copier

abbrev Bytes := List UInt8
/-- Ordered nonempty buffers, including the unique empty partition. -/
def Partition (bytes : Bytes) (buffers : List Bytes) : Prop :=
  buffers.flatten = bytes ∧ ∀ b ∈ buffers, b ≠ []

/-- Stateful read-stream delivery. Empty emissions are retained as harmless empty deliveries; the final entry
is decoder finalization, before input close. Entries contain whole scalars. -/
def textEvents (D : Decoder) : List Bytes → D.State → List Text
  | [], s => [D.decode_done s]
  | b :: bs, s =>
    let (state, text) := D.decode_buffer s b
    text :: textEvents D bs state

inductive ReadEncoding where | buffers | utf8 deriving DecidableEq
inductive WriteEncoding where | utf8 deriving DecidableEq
inductive Body where
  | writeArgument
  | letTextToStringThenWrite
  deriving DecidableEq
structure Program where
  readOption : Option ReadEncoding
  writeOption : Option WriteEncoding
  dataBody : Body
  deriving DecidableEq

def good : Program := ⟨some .utf8, some .utf8, .writeArgument⟩
def bad : Program := ⟨none, none, .letTextToStringThenWrite⟩
/-- Defaults of the stream constructors. -/
def readEncoding (p : Program) := p.readOption.getD .buffers
def writeEncoding (p : Program) := p.writeOption.getD .utf8
inductive Argument where | buffer (b : Bytes) | text (t : Text)
/-- A fresh singleton run gives the complete-buffer decoding for `toString`
when `D` satisfies `utf8_decodes`. This models its result. -/
def toString (D : Decoder) : Argument → Text
  | .buffer b => decoded D [b]
  | .text t => t
/-- The local binding has the value returned by toString. Callback execution is
atomic and ordered; the returned text is the argument of output.write. -/
def callback (D : Decoder) (body : Body) (arg : Argument) : Text :=
  match body with
  | .writeArgument => match arg with | .text t => t | .buffer _ => []
  | .letTextToStringThenWrite => let text := toString D arg; text

def arguments (D : Decoder) (p : Program) (bs : List Bytes) : List Argument :=
  match readEncoding p with
  | .utf8 => (textEvents D bs D.start).map Argument.text
  | .buffers => bs.map Argument.buffer
/-- Stream handles are bound, then the data and close listeners are registered,
then delivery may start. This setup is atomic and has no asynchronous steps. The close listener calls output.close after these events.
This is the elaboration of the tiny callback language into stream actions. -/
def deliveries (D : Decoder) (p : Program) (bs : List Bytes) : List Text :=
  (arguments D p bs).map (callback D p.dataBody)

/-- Pending writes are FIFO chunks. A write's Boolean return is deliberately
not part of acceptance: both true and false queue the complete encoded string. -/
structure Machine where
  events : List Text
  pending : List Bytes := []
  output : Bytes := []
  closing : Bool := false
  done : Bool := false
  deriving DecidableEq

def initial (D : Decoder) (p : Program) (bs : List Bytes) : Machine :=
  ⟨deliveries D p bs, [], [], false, false⟩

inductive Step : Machine → Machine → Prop where
  | write (t : Text) (ts : List Text) (q : List Bytes) (out : Bytes)
      (returned : Bool) :
      Step ⟨t :: ts, q, out, false, false⟩
        ⟨ts, q ++ [encodeText t], out, false, false⟩
  | close (q : List Bytes) (out : Bytes) :
      Step ⟨[], q, out, false, false⟩ ⟨[], q, out, true, false⟩
  | flush (ts : List Text) (b : Bytes) (q : List Bytes) (out : Bytes) (closing : Bool) :
      Step ⟨ts, b :: q, out, closing, false⟩ ⟨ts, q, out ++ b, closing, false⟩
  | finish (out : Bytes) :
      Step ⟨[], [], out, true, false⟩ ⟨[], [], out, true, true⟩

/-- Bytes conserved by all queue and callback operations. -/
def remaining (m : Machine) : Bytes :=
  m.output ++ m.pending.flatten ++ encodeText m.events.flatten

/-- Time can stutter arbitrarily. Progress says that from every unfinished time
some subsequent I/O/callback step occurs, rather than assuming completion. -/
structure Execution (start : Machine) where
  state : Nat → Machine
  starts : state 0 = start
  transition : ∀ i, state (i+1) = state i ∨ Step (state i) (state (i+1))
  progress : ∀ i, (state i).done = false → ∃ j, i ≤ j ∧ Step (state j) (state (j+1))

def witnessBytes : Bytes := [0xC2, 0xA9]
def witnessBuffers : List Bytes := [[0xC2], [0xA9]]
def witnessOutput : Bytes := [0xEF, 0xBF, 0xBD, 0xEF, 0xBF, 0xBD]

end Copier
