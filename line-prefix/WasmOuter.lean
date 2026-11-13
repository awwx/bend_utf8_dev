import WasmCallback
import OuterModel

namespace PrefixWasm
open Wasm SmallStep

def outerAdjust : Program := [.localGet 3, .const 1, .sub, .localSet 3]
def outerLong : Program :=
  [.localGet 2, .const 4096, .add, .localSet 3,
   .localGet 0, .localGet 3, .const 1, .sub, .call 10, .localSet 4,
   .localGet 4, .const 55296, .geU, .localGet 4, .const 56320, .ltU, .and,
   .iff 0 0 outerAdjust []]
def outerShort : Program := [.localGet 1, .localSet 3]
def outerTail : Program := [.localGet 3, .localSet 2, .br 0]
def outerCallBody : Program :=
  [.localGet 0, .localGet 2, .localGet 3, .call 9,
   .localGet 3, .localGet 2, .sub, .call 12] ++ outerTail

def outerBody : Program :=
  [.localGet 2, .localGet 1, .eq, .br_if 1,
   .localGet 1, .localGet 2, .sub, .const 4096, .gtU,
   .iff 0 0 outerLong outerShort] ++ outerCallBody

def outerControls : List ControlFrame :=
  [{ kind := .loop, paramArity := 0, resultArity := 0, body := outerBody,
     continuation := [], belowStack := [] },
   { kind := .block, paramArity := 0, resultArity := 0, body := [.loop 0 0 outerBody],
     continuation := [], belowStack := [] }]

def outerMachine (s : Bool) (host : Host) (heap : List GcObject) : MachineStore Host :=
  { runtime := { instances := #[{module := prefixModule, host := env}], entry := ⟨0⟩ },
    wasm := store s host heap }

def outerConfig (s : Bool) (host : Host) (heap : List GcObject)
    (ref len pos stop : Nat) (unit : UInt32) (code : Program) : Config Host :=
  ⟨.running
    { locals := { params := [.externref (some ref)]
                  locals := [.i32 (UInt32.ofNat len), .i32 (UInt32.ofNat pos), .i32 (UInt32.ofNat stop), .i32 unit] },
      code := code, resultArity := 0, callerRemainder := [], control := outerControls },
    outerMachine s host heap⟩

def outerHead (s : Bool) (host : Host) (heap : List GcObject)
    (ref len pos stop : Nat) (unit : UInt32) : Config Host :=
  outerConfig s host heap ref len pos stop unit outerBody

theorem length_invoke (s : Bool) (host : Host) (heap : List GcObject)
    (ref : Nat) (units : List UInt32) (hr : host.strings[ref]? = some units) :
    stringLength.invoke (store s host heap) [.externref (some ref)] =
      .Return [.i32 (UInt32.ofNat units.length)] (store s host heap) := by
  simp [stringLength, store, hr]

theorem sub_invoke (s : Bool) (host : Host) (heap : List GcObject)
    (ref : Nat) (units : List UInt32) (a b : Nat) (hr : host.strings[ref]? = some units)
    (hab : a ≤ b) (hb : b ≤ units.length) (hlen : units.length < 2^32) :
    substring.invoke (store s host heap) [.externref (some ref), .i32 (UInt32.ofNat a), .i32 (UInt32.ofNat b)] =
      .Return [.externref (some host.strings.length)]
        (store s (prepareHost host ((units.drop a).take (b-a))) heap) := by
  have ha32 : a < 2^32 := by omega
  have hb32 : b < 2^32 := by omega
  simp only [substring, store, hr]
  rw [UInt32.toNat_ofNat_of_lt' ha32, UInt32.toNat_ofNat_of_lt' hb32]
  simp [prepareHost, show ¬ (b<a ∨ units.length<a) from by omega]

theorem char_invoke (s : Bool) (host : Host) (heap : List GcObject)
    (ref i : Nat) (units : List UInt32) (u : UInt32)
    (hr : host.strings[ref]? = some units) (hi : i < 2^32) (hu : units[i]? = some u) :
    charCodeAt.invoke (store s host heap) [.externref (some ref), .i32 (UInt32.ofNat i)] =
      .Return [.i32 u] (store s host heap) := by
  simp [charCodeAt, store, hr, UInt32.toNat_ofNat_of_lt' hi, hu]

theorem outer_short_steps (s : Bool) (host : Host) (heap : List GcObject)
    (ref len pos stop : Nat) (unit : UInt32)
    (hp : pos < len) (hshort : len-pos ≤ 4096) (hlen : len < 2^32) :
    ∃ trace, Steps (outerHead s host heap ref len pos stop unit) trace
      (outerConfig s host heap ref len pos len unit outerCallBody) := by
  have hnpos : (UInt32.ofNat pos).toNat = pos := UInt32.toNat_ofNat_of_lt' (by change _ < 2^32; omega)
  have hnlen : (UInt32.ofNat len).toNat = len := UInt32.toNat_ofNat_of_lt' hlen
  have hne : UInt32.ofNat pos ≠ UInt32.ofNat len := by
    intro h; have := congrArg UInt32.toNat h; omega
  have hs : UInt32.ofNat len - UInt32.ofNat pos = UInt32.ofNat (len-pos) :=
    (UInt32.ofNat_sub (by omega)).symm
  have hc : ¬ UInt32.ofNat (len-pos) > 4096 := by
    change ¬ (4096 : UInt32) < UInt32.ofNat (len-pos)
    rw [UInt32.lt_iff_toNat_lt, UInt32.toNat_ofNat_of_lt' (by change _ < 2^32; omega)]
    exact Nat.not_lt.mpr hshort
  refine ⟨([.localGet 2, .localGet 1, .eq, .br_if 1,
    .localGet 1, .localGet 2, .sub, .const 4096, .gtU,
    .iff 0 0 outerLong outerShort, .localGet 1, .localSet 3] : Program).map StepKind.instruction ++
    [.administrative .exitControl], ?_⟩
  wasm_steps [(.localGet rfl), (.localGet rfl), (.eq (result := 0) (by simp [hne])), .brIfZero,
    (.localGet rfl), (.localGet rfl), .sub]
  rw [hs]
  wasm_steps [.const, (.gtU (result := 0) (by simp [hc])), (.iff rfl),
    (.localGet rfl), (.localSet rfl), (.exitControl rfl)]
  exact Steps.refl _

def outerLongTrace (high : Bool) : List StepKind :=
  ([.localGet 2, .localGet 1, .eq, .br_if 1,
    .localGet 1, .localGet 2, .sub, .const 4096, .gtU,
    .iff 0 0 outerLong outerShort, .localGet 2, .const 4096, .add, .localSet 3,
    .localGet 0, .localGet 3, .const 1, .sub] : Program).map StepKind.instruction ++
  [.host 10] ++
  ([.localSet 4, .localGet 4, .const 55296, .geU,
    .localGet 4, .const 56320, .ltU, .and, .iff 0 0 outerAdjust []] : Program).map StepKind.instruction ++
  (if high then outerAdjust.map StepKind.instruction else []) ++
  [.administrative .exitControl, .administrative .exitControl]

theorem outer_long_steps (s : Bool) (host : Host) (heap : List GcObject)
    (ref pos stop : Nat) (unit u : UInt32) (units : List UInt32)
    (hr : host.strings[ref]? = some units)
    (hp : pos < units.length) (hlong : 4096 < units.length-pos)
    (hlen : units.length < 2^32) (hu : units[pos+4095]? = some u) :
    Steps (outerHead s host heap ref units.length pos stop unit)
      (outerLongTrace (decide (LinePrefix.Chunking.high u)))
      (outerConfig s host heap ref units.length pos
        (pos + if LinePrefix.Chunking.high u then 4095 else 4096) u outerCallBody) := by
  have hnpos : (UInt32.ofNat pos).toNat = pos := UInt32.toNat_ofNat_of_lt' (by change _ < 2^32; omega)
  have hnlen : (UInt32.ofNat units.length).toNat = units.length := UInt32.toNat_ofNat_of_lt' hlen
  have hne : UInt32.ofNat pos ≠ UInt32.ofNat units.length := by
    intro h; have := congrArg UInt32.toNat h; omega
  have hs : UInt32.ofNat units.length - UInt32.ofNat pos = UInt32.ofNat (units.length-pos) :=
    (UInt32.ofNat_sub (by omega)).symm
  have hc : UInt32.ofNat (units.length-pos) > 4096 := by
    change (4096 : UInt32) < UInt32.ofNat (units.length-pos)
    rw [UInt32.lt_iff_toNat_lt, UInt32.toNat_ofNat_of_lt' (by change _ < 2^32; omega)]
    exact hlong
  have hadd : 4096 + UInt32.ofNat pos = UInt32.ofNat (pos+4096) := by
    simp [UInt32.ofNat_add, UInt32.add_comm]
  have hsub : UInt32.ofNat (pos+4096) - 1 = UInt32.ofNat (pos+4095) := by
    change UInt32.ofNat (pos+4096) - UInt32.ofNat 1 = _
    rw [← UInt32.ofNat_sub (a := pos+4096) (b := 1) (by omega)]
    congr 1
  have hcall := char_invoke s host heap ref (pos+4095) units u hr (by omega) hu
  wasm_steps [(.localGet rfl), (.localGet rfl), (.eq (result := 0) (by simp [hne])), .brIfZero,
    (.localGet rfl), (.localGet rfl), .sub]
  rw [hs]
  wasm_steps [.const, (.gtU (result := 1) (by simp [hc])), (.iff (by rfl)),
    (.localGet rfl), .const, .add, (.localSet rfl)]
  rw [hadd]
  wasm_steps [(.localGet rfl), (.localGet rfl), .const, .sub]
  rw [hsub]
  wasm_steps [(.callHostReturn (by change 10 < 11; decide) rfl rfl hcall),
    (.localSet rfl), (.localGet rfl), .const, (.geU rfl),
    (.localGet rfl), .const, (.ltU rfl), .and]
  have hlow : (u ≥ 55296) ↔ 55296 ≤ u.toNat := by
    change (55296 : UInt32) ≤ u ↔ _
    rw [UInt32.le_iff_toNat_le]; rfl
  have hhigh : (u < 56320) ↔ u.toNat < 56320 := by
    rw [UInt32.lt_iff_toNat_lt]; rfl
  by_cases hl : 55296 ≤ u.toNat <;> by_cases hh : u.toNat < 56320
  all_goals simp only [hlow, hhigh, hl, hh, ↓reduceIte, LinePrefix.Chunking.high,
    and_self, false_and, and_false, decide_true, decide_false] at *
  · wasm_steps [(.iff (by rfl)), (.localGet rfl), .const, .sub, (.localSet rfl)]
    rw [hsub]
    wasm_steps [(.exitControl rfl), (.exitControl rfl)]
    exact Steps.refl _
  all_goals
    wasm_steps [(.iff (by rfl)), (.exitControl rfl), (.exitControl rfl)]
    exact Steps.refl _

theorem outer_select_steps (s : Bool) (host : Host) (heap : List GcObject)
    (ref pos stop : Nat) (unit : UInt32) (all rest : List UInt32)
    (hr : host.strings[ref]? = some all) (hrest : all.drop pos = rest)
    (hp : pos ≤ all.length) (hne : rest ≠ []) (hlen : all.length < 2^32) :
    ∃ unit' trace, Steps (outerHead s host heap ref all.length pos stop unit) trace
      (outerConfig s host heap ref all.length pos
        (pos + LinePrefix.Chunking.count rest) unit' outerCallBody) := by
  have hlength : rest.length = all.length-pos := by
    rw [← hrest, List.length_drop]
  have hpositive : 0 < rest.length := by cases rest <;> simp_all <;> omega
  by_cases hsmall : rest.length ≤ 4096
  · obtain ⟨trace, ht⟩ := outer_short_steps s host heap ref all.length pos stop unit
      (by omega) (by omega) hlen
    refine ⟨unit, trace, ?_⟩
    have hc := LinePrefix.Chunking.count_eq_of_short hsmall
    have he : pos + LinePrefix.Chunking.count rest = all.length := by omega
    simpa only [he] using ht
  · have hlong : 4096 < rest.length := by omega
    have hh : 4095 < rest.length := by omega
    let u := rest[4095]
    have hu : rest[4095]? = some u := List.getElem?_eq_getElem hh
    have hall : all[pos+4095]? = some u := by
      rw [← hrest, List.getElem?_drop] at hu
      exact hu
    have hc : LinePrefix.Chunking.count rest =
        if LinePrefix.Chunking.high u then 4095 else 4096 := by
      rw [LinePrefix.Chunking.count_eq_long hlong, hu]
      rfl
    refine ⟨u, outerLongTrace (decide (LinePrefix.Chunking.high u)), ?_⟩
    rw [hc]
    exact outer_long_steps s host heap ref pos stop unit u all hr
      (by omega) (by omega) hlen hall

theorem outer_done (s : Bool) (host : Host) (heap : List GcObject)
    (ref len stop : Nat) (unit : UInt32) :
    TerminatesWith (outerHead s host heap ref len len stop unit)
      (fun values st => values = [] ∧ st.wasm = store s host heap) := by
  refine ⟨[.instruction (.localGet 2), .instruction (.localGet 1),
    .instruction .eq, .instruction (.br_if 1), .administrative .finish],
    [], outerMachine s host heap, ?_, ⟨rfl,rfl⟩⟩
  wasm_steps [(.localGet rfl), (.localGet rfl), (.eq (result := 1) (by simp)),
    (.brIf (by decide) rfl)]
  exact Steps.single .finish

end PrefixWasm
