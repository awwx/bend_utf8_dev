import Utf16
set_option maxRecDepth 100000
namespace LinePrefix.Chunking
open Utf8Pure Utf16

def high (u : UInt32) : Prop := 0xD800 ≤ u.toNat ∧ u.toNat < 0xDC00
instance (u : UInt32) : Decidable (high u) := inferInstanceAs (Decidable (_ ∧ _))

def count (units : Text) : Nat :=
  let candidate := min 4096 units.length
  if candidate < units.length ∧ high (units[candidate - 1]?.getD 0) then
    candidate - 1 else candidate

theorem count_bounds {units : Text} (h : units ≠ []) :
    0 < count units ∧ count units ≤ 4096 ∧ count units ≤ units.length := by
  have hp : 0 < units.length := by cases units <;> simp_all
  unfold count
  dsimp only
  split
  · rename_i hh
    have hm : min 4096 units.length = 4096 := by omega
    omega
  · have := Nat.min_le_left 4096 units.length
    have := Nat.min_le_right 4096 units.length
    omega

/-- Exact indexing used by JavaScript's charCodeAt for an in-range offset. -/
def charCodeAt (units : Text) (index : Nat) : Option UInt32 := units[index]?

theorem charCodeAt_index {units : Text} {index : Nat} (h : index < units.length) :
    charCodeAt units index = some units[index] := by
  exact List.getElem?_eq_getElem h

private theorem scalar_shape {cp : UInt32} (h : is_unicode_scalar cp = true) :
    (∃ u, encodeScalar cp = [u] ∧ ¬ high u) ∨
    (∃ u v, encodeScalar cp = [u,v] ∧ high u ∧ ¬ high v) := by
  by_cases hs : cp.toNat < 65536
  · left; refine ⟨cp, by simp [encodeScalar, hs], ?_⟩
    have hb := (is_unicode_scalar_iff cp).mp h
    unfold high; omega
  · right
    have hb := supplementary_bounds h hs
    dsimp at hb
    refine ⟨UInt32.ofNat (0xD800 + (cp.toNat - 0x10000) / 1024), UInt32.ofNat (0xDC00 + (cp.toNat - 0x10000) % 1024), by simp only [encodeScalar, hs, ↓reduceIte], ?_, ?_⟩
    · unfold high; change 55296 ≤ _ % 4294967296 ∧ _ % 4294967296 < 56320; omega
    · unfold high; change ¬ (55296 ≤ _ % 4294967296 ∧ _ % 4294967296 < 56320); omega

def cut (units : Text) (k : Nat) : Nat :=
  if high (units[k-1]?.getD 0) then k-1 else k

private theorem split_encoding {text : Text} (ht : Scalars text) (k : Nat)
    (hk : k ≤ (encode text).length) :
    ∃ a b, Scalars a ∧ Scalars b ∧ text = a ++ b ∧
      (encode a).length = cut (encode text) k := by
  induction text generalizing k with
  | nil =>
    have : k = 0 := by simpa using hk
    subst k
    exact ⟨[], [], ht, ht, rfl, by simp [cut, high]⟩
  | cons cp rest ih =>
    have hc := ht cp (by simp)
    have hr : Scalars rest := fun c h => ht c (by simp [h])
    have zero : k = 0 → ∃ a b, Scalars a ∧ Scalars b ∧ cp :: rest = a ++ b ∧
        (encode a).length = cut (encode (cp :: rest)) k := by
      intro he; subst k
      refine ⟨[], cp :: rest, by simp [Scalars], ht, rfl, ?_⟩
      simp [cut]
    by_cases hz : k = 0
    · exact zero hz
    rcases scalar_shape hc with ⟨u, hu, hnu⟩ | ⟨u,v,hu,hhu,hnv⟩
    · have he : encode (cp :: rest) = u :: encode rest := by simp [hu]
      by_cases hk1 : k = 1
      · subst k
        refine ⟨[cp], rest, ?_, hr, by simp, ?_⟩
        · intro c h; simpa using (show c = cp from by simpa using h) ▸ hc
        · simp [he, cut, hu, hnu]
      · have hk' : k-1 ≤ (encode rest).length := by rw [he] at hk; simp at hk; omega
        obtain ⟨a,b,ha,hb,hab,hlen⟩ := ih hr (k-1) hk'
        refine ⟨cp :: a,b, ?_,hb, by simp [hab], ?_⟩
        · intro c h; simp only [List.mem_cons] at h; rcases h with rfl | h; exact hc; exact ha c h
        · simp only [encode_cons, hu, List.length_append, List.length_singleton]
          have hkm : k-1 = (k-2)+1 := by omega
          simp only [cut, hkm] at hlen
          simp only [cut, List.cons_append, List.nil_append, show k-1 = (k-2)+1 by omega, List.getElem?_cons_succ]
          split <;> rename_i hh
          · simp only [hh, ↓reduceIte, Nat.add_sub_cancel] at hlen; omega
          · simp only [hh, ↓reduceIte, Nat.add_sub_cancel] at hlen; omega
    · have he : encode (cp :: rest) = u :: v :: encode rest := by simp [hu]
      by_cases hk1 : k = 1
      · subst k
        refine ⟨[],cp :: rest,by simp [Scalars],ht,rfl,?_⟩
        simp [cut,he,hhu]
      by_cases hk2 : k = 2
      · subst k
        refine ⟨[cp],rest,?_,hr,by simp,?_⟩
        · intro c h; rcases List.mem_singleton.mp h with rfl; exact hc
        · simp [cut,he,hu,hnv]
      · have hk' : k-2 ≤ (encode rest).length := by rw [he] at hk; simp at hk; omega
        obtain ⟨a,b,ha,hb,hab,hlen⟩ := ih hr (k-2) hk'
        refine ⟨cp :: a,b,?_,hb,by simp [hab],?_⟩
        · intro c h; simp only [List.mem_cons] at h; rcases h with rfl | h; exact hc; exact ha c h
        · simp only [encode_cons, hu, List.length_append, List.length_cons, List.length_nil]
          have hkm : k-1 = (k-3)+1+1 := by omega
          simp only [cut, show k-2-1 = k-3 by omega] at hlen
          simp only [cut, List.cons_append, List.nil_append, hkm, List.getElem?_cons_succ]
          split <;> rename_i hh
          · simp only [hh, ↓reduceIte] at hlen; omega
          · simp only [hh, ↓reduceIte] at hlen; omega

theorem count_eq (units : Text) : count units =
    if units.length ≤ 4096 then units.length
    else if high (units[4095]?.getD 0) then 4095 else 4096 := by
  unfold count
  by_cases h : units.length ≤ 4096
  · simp [h, Nat.min_eq_right h]
  · have hm : min 4096 units.length = 4096 := Nat.min_eq_left (by omega)
    simp [h, hm, show 4096 < units.length by omega]

theorem wellFormed_take_drop {units : Text} (h : WellFormed units) :
    WellFormed (units.take (count units)) ∧ WellFormed (units.drop (count units)) := by
  by_cases hl : units.length ≤ 4096
  · rw [count_eq, ite_eq_left hl]
    simpa using And.intro h (show WellFormed [] from ⟨[], by simp [Scalars], rfl⟩)
  · obtain ⟨text,ht,rfl⟩ := h
    obtain ⟨a,b,ha,hb,hab,hlen⟩ := split_encoding ht 4096 (by omega)
    have hc : count (encode text) = cut (encode text) 4096 := by
      rw [count_eq, ite_eq_right hl]; rfl
    have he : encode text = encode a ++ encode b := by rw [hab, encode_append]
    rw [hc, ← hlen, he]
    constructor
    · exact ⟨a,ha,by simp⟩
    · exact ⟨b,hb,by simp⟩

def chunks (units : Text) : List Text :=
  if _h : units = [] then []
  else units.take (count units) :: chunks (units.drop (count units))
termination_by units.length
decreasing_by
  have hb := (count_bounds _h).1
  try simp_all only [List.length_drop]
  have hp : 0 < units.length := by cases units <;> simp_all
  omega

theorem flatten_chunks (units : Text) : (chunks units).flatten = units := by
  rw [chunks]
  split
  · rename_i h; subst units; rfl
  · simp only [List.flatten_cons]
    rw [flatten_chunks (units.drop (count units))]
    exact List.take_append_drop _ _
termination_by units.length
decreasing_by
  have hb := (count_bounds (units := units) (by assumption)).1
  try simp_all only [List.length_drop]
  have hp : 0 < units.length := by cases units <;> simp_all
  omega

theorem chunks_valid {units : Text} (h : WellFormed units) :
    ∀ part ∈ chunks units, WellFormed part ∧ 0 < part.length ∧ part.length ≤ 4096 := by
  rw [chunks]
  split
  · simp
  · rename_i hn
    obtain ⟨hp,hr⟩ := wellFormed_take_drop h
    intro part hm
    simp only [List.mem_cons] at hm
    rcases hm with rfl | hm
    · refine ⟨hp,?_,?_⟩
      all_goals simp only [List.length_take]; have hb := count_bounds hn; omega
    · exact chunks_valid hr part hm
termination_by units.length
decreasing_by
  have hb := (count_bounds (units := units) (by assumption)).1
  try simp_all only [List.length_drop]
  have hp : 0 < units.length := by cases units <;> simp_all
  omega

/-- Carry the line-start state across precisely the chunks used by the wrapper. -/
def runChunks (s : Bool) : List Text → Bool × Text
  | [] => (s, [])
  | part :: rest =>
    let first := run s part
    let tail := runChunks first.1 rest
    (tail.1, first.2 ++ tail.2)

theorem runChunks_flatten (parts : List Text) (s : Bool) :
    runChunks s parts = run s parts.flatten := by
  induction parts generalizing s with
  | nil => rfl
  | cons part rest ih => simp only [runChunks, List.flatten_cons, run_append, ih]

theorem run_chunks (units : Text) (s : Bool) : runChunks s (chunks units) = run s units := by
  rw [runChunks_flatten, flatten_chunks]

abbrev splitUnits := chunks

theorem count_eq_of_short {units : Text} (h : units.length ≤ 4096) :
    count units = units.length := by rw [count_eq, ite_eq_left h]

theorem count_eq_long {units : Text} (h : 4096 < units.length) :
    count units = if high (units[4095]?.getD 0) then 4095 else 4096 := by
  rw [count_eq, ite_eq_right (by omega)]

theorem chunks_length (units : Text) : (chunks units).length ≤ units.length := by
  rw [chunks]
  split
  · simp
  · rename_i hn
    simp only [List.length_cons]
    have ih := chunks_length (units.drop (count units))
    have hb := count_bounds hn
    simp only [List.length_drop] at ih
    omega
termination_by units.length
decreasing_by
  have hb := (count_bounds (units := units) (by assumption)).1
  simp only [List.length_drop]
  have hp : 0 < units.length := by cases units <;> simp_all
  omega

theorem decode_append_wellFormed {a b : Text} (ha : WellFormed a) (hb : WellFormed b) :
    decode (a ++ b) = decode a ++ decode b := by
  obtain ⟨x,hx,rfl⟩ := ha
  obtain ⟨y,hy,rfl⟩ := hb
  have hxy : Scalars (x ++ y) := by
    intro cp hc; rcases List.mem_append.mp hc with hc | hc
    exact hx cp hc
    exact hy cp hc
  rw [← encode_append, Utf16.decode_encode hxy, Utf16.decode_encode hx, Utf16.decode_encode hy]

theorem flatten_wellFormed {parts : List Text} (h : ∀ p ∈ parts, WellFormed p) :
    WellFormed parts.flatten := by
  induction parts with
  | nil => exact ⟨[],by simp [Scalars],rfl⟩
  | cons part rest ih =>
    obtain ⟨a,ha,hea⟩ := h part (by simp)
    obtain ⟨b,hb,heb⟩ := ih (fun p hp => h p (by simp [hp]))
    refine ⟨a ++ b,?_,?_⟩
    · intro cp hc; rcases List.mem_append.mp hc with hc | hc
      exact ha cp hc
      exact hb cp hc
    · simp [encode_append,hea,heb]

theorem decode_flatten {parts : List Text} (h : ∀ p ∈ parts, WellFormed p) :
    decode parts.flatten = (parts.map decode).flatten := by
  induction parts with
  | nil => rfl
  | cons part rest ih =>
    have hr : ∀ p ∈ rest, WellFormed p := fun p hp => h p (by simp [hp])
    simp only [List.flatten_cons, List.map_cons]
    rw [decode_append_wellFormed (h part (by simp)) (flatten_wellFormed hr), ih hr]

end LinePrefix.Chunking
