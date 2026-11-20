/-
The reference streaming decoder `RefDecoder` (definitions only; the
proofs are in `Utf8Proofs.lean`).  These definitions are meant to stay
stable: downstream refinement proofs target them.

Design: the state is the list of pending bytes, which is always either
empty or a valid sequence prefix that is not yet a whole valid sequence
(so at most three bytes).  `step` consumes one byte; `decode_buffer` is
a left fold of `step` over the buffer.
-/
import Utf8Laws

namespace Utf8Pure

/-! ## The Unicode "well-formed UTF-8 byte sequences" table, as Bools -/

def isCont (b : UInt8) : Bool := 0x80 ≤ b && b ≤ 0xBF
def isLead1 (b : UInt8) : Bool := b ≤ 0x7F
def isLead2 (b : UInt8) : Bool := 0xC2 ≤ b && b ≤ 0xDF
def isLead3 (b : UInt8) : Bool := 0xE0 ≤ b && b ≤ 0xEF
def isLead4 (b : UInt8) : Bool := 0xF0 ≤ b && b ≤ 0xF4

/-- Allowed second byte after a multi-byte lead byte `b1`:
E0 → A0..BF, ED → 80..9F, F0 → 90..BF, F4 → 80..8F, otherwise 80..BF. -/
def secondOk (b1 b2 : UInt8) : Bool :=
  if b1 = 0xE0 then 0xA0 ≤ b2 && b2 ≤ 0xBF
  else if b1 = 0xED then 0x80 ≤ b2 && b2 ≤ 0x9F
  else if b1 = 0xF0 then 0x90 ≤ b2 && b2 ≤ 0xBF
  else if b1 = 0xF4 then 0x80 ≤ b2 && b2 ≤ 0x8F
  else 0x80 ≤ b2 && b2 ≤ 0xBF

/-- Whole valid sequence (equivalent to the spec's `is_valid_sequence`,
see `isVS_iff`). -/
def isVS : List UInt8 → Bool
  | [b1] => isLead1 b1
  | [b1, b2] => isLead2 b1 && secondOk b1 b2
  | [b1, b2, b3] => isLead3 b1 && secondOk b1 b2 && isCont b3
  | [b1, b2, b3, b4] => isLead4 b1 && secondOk b1 b2 && isCont b3 && isCont b4
  | _ => false

/-- Valid sequence prefix (equivalent to the spec's
`is_valid_sequence_prefix`, see `isVSP_iff`). -/
def isVSP : List UInt8 → Bool
  | [b1] => isLead1 b1 || isLead2 b1 || isLead3 b1 || isLead4 b1
  | [b1, b2] => (isLead2 b1 || isLead3 b1 || isLead4 b1) && secondOk b1 b2
  | [b1, b2, b3] => (isLead3 b1 || isLead4 b1) && secondOk b1 b2 && isCont b3
  | [b1, b2, b3, b4] => isLead4 b1 && secondOk b1 b2 && isCont b3 && isCont b4
  | _ => false

/-- The code point encoded by a valid sequence. -/
def cpOf : List UInt8 → UInt32
  | [b1] => b1.toUInt32
  | [b1, b2] => ((b1.toUInt32 &&& 0x1F) <<< 6) ||| (b2.toUInt32 &&& 0x3F)
  | [b1, b2, b3] =>
    ((b1.toUInt32 &&& 0x0F) <<< 12) ||| ((b2.toUInt32 &&& 0x3F) <<< 6) ||| (b3.toUInt32 &&& 0x3F)
  | [b1, b2, b3, b4] =>
    ((b1.toUInt32 &&& 0x07) <<< 18) ||| ((b2.toUInt32 &&& 0x3F) <<< 12) |||
      ((b3.toUInt32 &&& 0x3F) <<< 6) ||| (b4.toUInt32 &&& 0x3F)
  | _ => 0

/-! ## The streaming decoder -/

/-- Pending bytes: empty, or a valid sequence prefix that is not a
whole valid sequence. -/
abbrev State : Type := List UInt8

/-- Process one byte with no pending bytes. -/
def stepFresh (b : UInt8) : State × Text :=
  if isVS [b] then ([], [cpOf [b]])
  else if isVSP [b] then ([b], [])
  else ([], [replacement_char])

/-- Process one byte `b` with pending bytes `p`. -/
def step (p : State) (b : UInt8) : State × Text :=
  if isVS (p ++ [b]) then ([], [cpOf (p ++ [b])])
  else if isVSP (p ++ [b]) then (p ++ [b], [])
  else if p.isEmpty then ([], [replacement_char])
  else ((stepFresh b).1, replacement_char :: (stepFresh b).2)

/-- One loop iteration: state and accumulated output. -/
def stepAcc (acc : State × Text) (b : UInt8) : State × Text :=
  ((step acc.1 b).1, acc.2 ++ (step acc.1 b).2)

def decodeBuffer (s : State) (buf : List UInt8) : State × Text :=
  buf.foldl stepAcc (s, [])

def decodeDone (s : State) : Text :=
  if s.isEmpty then [] else [replacement_char]

def RefDecoder : Decoder where
  State := State
  start := []
  decode_buffer := decodeBuffer
  decode_done := decodeDone

end Utf8Pure
