import CirclePacking.FifteenStageZero

/-! Kernel proofs connecting positional coarse labels with the exact Stage 0
assignment enumeration and the labels of its recorded negative cycles. -/

namespace CirclePacking

private def stage0LabelBit (digit : Nat) : Char :=
  if digit == 0 then '0' else '1'

private theorem fifteenStage0AssignmentsAux_complete (digits : List Nat)
    (hvalid : ∀ digit ∈ digits, 1 ≤ digit ∧ digit ≤ 3) :
    digits ∈ fifteenStage0AssignmentsAux digits.length := by
  induction digits with
  | nil => simp [fifteenStage0AssignmentsAux]
  | cons digit rest ih =>
    have hrest := ih (fun next hnext => hvalid next (by simp [hnext]))
    have hd := hvalid digit (by simp)
    have hchoices : digit ∈ [1, 2, 3] := by simp; omega
    apply List.mem_flatMap.mpr
    exact ⟨rest, hrest, List.mem_map.mpr ⟨digit, hchoices, rfl⟩⟩

private theorem fifteenStage0DigitsString_decodes (digits : List Nat)
    (hvalid : ∀ digit ∈ digits, 1 ≤ digit ∧ digit ≤ 3) :
    fifteenStage0Digits? (fifteenStage0DigitsString digits) = some digits := by
  induction digits with
  | nil => simp [fifteenStage0Digits?, fifteenStage0DigitsString]
  | cons digit rest ih =>
    have hrest := ih (fun next hnext => hvalid next (by simp [hnext]))
    have hd := hvalid digit (by simp)
    have hcases : digit = 1 ∨ digit = 2 ∨ digit = 3 := by omega
    simp only [fifteenStage0Digits?, fifteenStage0DigitsString, String.toList_ofList] at hrest ⊢
    have hfirst : (if '1' ≤ Char.ofNat (48 + digit) && Char.ofNat (48 + digit) ≤ '3'
        then some ((Char.ofNat (48 + digit)).toNat - 48) else none) = some digit := by
      rcases hcases with rfl | rfl | rfl <;> decide
    simp only [List.map_cons, List.mapM_cons, hfirst, hrest]
    rfl

private theorem fifteenStage0LabelList_reconstructs (labels : List Nat) :
    fifteenStage0LabelList (labels.map stage0LabelBit)
      (labels.filter (· != 0)) = labels := by
  induction labels with
  | nil => rfl
  | cons label rest ih =>
    by_cases hzero : label = 0
    · simp [stage0LabelBit, fifteenStage0LabelList, hzero, ih]
    · simp [stage0LabelBit, fifteenStage0LabelList, hzero, ih]

private theorem fifteenStage0InnerPositionsAux_length (bits : List Char) (start : Nat) :
    (fifteenStage0InnerPositionsAux start bits).length =
      (bits.filter (· == '1')).length := by
  induction bits generalizing start with
  | nil => rfl
  | cons bit rest ih =>
    by_cases hbit : bit = '1' <;>
      simp [fifteenStage0InnerPositionsAux, hbit, ih]

private theorem stage0ProfileWord_toList (profile : Fin 15 → Bool) :
    (fifteenStage0ProfileWord profile).toList =
      List.ofFn (fun i => if profile i then '1' else '0') := by
  change (String.ofList ((List.range 15).map fun i =>
    if Nat.testBit (fifteenStage0ProfileMask profile) (14 - i) then '1' else '0')).toList = _
  rw [String.toList_ofList]
  apply List.ext_getElem
  · simp
  · intro i hi _
    have hi' : i < 15 := by simpa using hi
    simp only [List.getElem_map, List.getElem_range, List.getElem_ofFn]
    rw [fifteenStage0ProfileMask_testBit profile ⟨i, hi'⟩]

/-- The actual finite assignment string of a coarse radius-label profile. -/
def fifteenStage0LabelProfileAssignment (labels : Fin 15 → Fin 4) : String :=
  fifteenStage0DigitsString ((List.ofFn fun i => (labels i).val).filter (· != 0))

def fifteenStage0LabelProfileWord (labels : Fin 15 → Fin 4) : String :=
  fifteenStage0ProfileWord (fun i => (labels i).val != 0)

private theorem stage0LabelProfileWord_toList (labels : Fin 15 → Fin 4) :
    (fifteenStage0LabelProfileWord labels).toList =
      (List.ofFn fun i => (labels i).val).map stage0LabelBit := by
  rw [fifteenStage0LabelProfileWord, stage0ProfileWord_toList, List.map_ofFn]
  congr 1
  funext i
  by_cases hzero : (labels i).val = 0 <;> simp [stage0LabelBit, hzero]

private theorem stage0LabelProfile_digits_valid (labels : Fin 15 → Fin 4) :
    ∀ digit ∈ (List.ofFn fun i => (labels i).val).filter (· != 0),
      1 ≤ digit ∧ digit ≤ 3 := by
  intro digit hdigit
  obtain ⟨hmem, hnonzero⟩ := List.mem_filter.mp hdigit
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hmem
  have hi := (labels i).isLt
  simp only [bne_iff_ne] at hnonzero
  omega

private theorem stage0LabelProfile_inner_count (labels : Fin 15 → Fin 4) :
    fifteenStage0InnerPositionCount (fifteenStage0LabelProfileWord labels) =
      ((List.ofFn fun i => (labels i).val).filter (· != 0)).length := by
  rw [fifteenStage0InnerPositionCount, fifteenStage0InnerPositions,
    fifteenStage0InnerPositionsAux_length, stage0LabelProfileWord_toList,
    List.filter_map, List.length_map]
  congr 1
  apply List.filter_congr
  intro digit _
  by_cases hzero : digit = 0 <;> simp [stage0LabelBit, hzero]

private theorem stage0LabelProfile_reconstructs (labels : Fin 15 → Fin 4) :
    fifteenStage0Labels (fifteenStage0LabelProfileWord labels)
      (fifteenStage0LabelProfileAssignment labels) =
      (List.ofFn fun i => (labels i).val).toArray := by
  rw [fifteenStage0Labels, stage0LabelProfileWord_toList,
    fifteenStage0LabelProfileAssignment,
    fifteenStage0DigitsString_decodes _ (stage0LabelProfile_digits_valid labels),
    Option.getD_some, fifteenStage0LabelList_reconstructs]

/-- Counts in a positional list agree with counts of the corresponding slots,
even when several slots carry the same label. -/
theorem fifteenStage0LabelProfile_count (labels : Fin 15 → Fin 4)
    (predicate : Nat → Bool) :
    ((List.ofFn fun i => (labels i).val).filter predicate).length =
      (Finset.univ.filter fun i : Fin 15 => predicate (labels i).val = true).card := by
  classical
  rw [List.ofFn_eq_map, List.filter_map, List.length_map]
  let positions := (List.finRange 15).filter (fun i => predicate (labels i).val)
  have hnodup : positions.Nodup := (List.nodup_finRange 15).filter _
  have hset : positions.toFinset =
      Finset.univ.filter (fun i => predicate (labels i).val = true) := by
    ext i
    simp [positions]
  exact (List.toFinset_card_of_nodup hnodup).symm.trans (congrArg Finset.card hset)

/-- All three-bin profiles satisfying the geometric population restrictions
occur in the existing finite table, with exactly their original per-slot labels. -/
theorem fifteenStage0LabelProfile_covered
    (labels : Fin 15 → Fin 4)
    (hpattern : fifteenStage0LabelProfileWord labels ∈ fifteenStage0OrbitWords)
    (hone : (Finset.univ.filter fun i : Fin 15 => (labels i).val = 1).card ≤ 1)
    (hthree : (Finset.univ.filter fun i : Fin 15 => (labels i).val = 3).card ≥
      (Finset.univ.filter fun i : Fin 15 => (labels i).val ≠ 0).card - 4) :
    fifteenStage0LabelProfileWord labels ∈ fifteenStage0SurvivorPatterns ∨
      ∃ witness ∈ fifteenStage0NegativeCycleWitnesses,
        witness.pattern = fifteenStage0LabelProfileWord labels ∧
        (∀ i, fifteenStage0CycleWitnessTypeIndex witness i = labels i) := by
  classical
  let digits := (List.ofFn fun i => (labels i).val).filter (· != 0)
  have hfilterOne : (digits.filter (· == 1)) =
      (List.ofFn fun i => (labels i).val).filter (· == 1) := by
    simp only [digits, List.filter_filter]
    apply List.filter_congr
    intro digit _
    by_cases h : digit = 1 <;> simp [h]
  have hfilterThree : (digits.filter (· == 3)) =
      (List.ofFn fun i => (labels i).val).filter (· == 3) := by
    simp only [digits, List.filter_filter]
    apply List.filter_congr
    intro digit _
    by_cases h : digit = 3 <;> simp [h]
  have hone' : (digits.filter (· == 1)).length ≤ 1 := by
    rw [hfilterOne, fifteenStage0LabelProfile_count]
    simpa using hone
  have hthree' : (digits.filter (· == 3)).length ≥ digits.length - 4 := by
    rw [hfilterThree, fifteenStage0LabelProfile_count]
    simpa only [digits, fifteenStage0LabelProfile_count, bne_iff_ne, beq_iff_eq] using hthree
  have hassignment : fifteenStage0LabelProfileAssignment labels ∈
      fifteenStage0ExpectedAssignments
        (fifteenStage0InnerPositionCount (fifteenStage0LabelProfileWord labels)) := by
    rw [stage0LabelProfile_inner_count]
    change fifteenStage0DigitsString digits ∈ List.map fifteenStage0DigitsString
      (List.filter (fun ds => (ds.filter (· == 1)).length ≤ 1 &&
        (ds.filter (· == 3)).length ≥ digits.length - 4)
        (fifteenStage0AssignmentsAux digits.length))
    apply List.mem_map.mpr
    refine ⟨digits, List.mem_filter.mpr ⟨?_, ?_⟩, rfl⟩
    · exact fifteenStage0AssignmentsAux_complete digits (stage0LabelProfile_digits_valid labels)
    · simp only [Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨hone', hthree'⟩
  rcases fifteenStage0Assignment_covered _ _ hpattern hassignment with
    hsurvivor | ⟨witness, hwitness, hword, hassignmentEq⟩
  · exact Or.inl hsurvivor
  · right
    refine ⟨witness, hwitness, hword, ?_⟩
    intro i
    have hlabel : fifteenStage0CycleWitnessLabel witness i = (labels i).val := by
      rw [fifteenStage0CycleWitnessLabel, hword, hassignmentEq,
        stage0LabelProfile_reconstructs]
      rw [getElem!_pos _ _ (by simp),
        List.getElem_toArray, List.getElem_ofFn]
    apply Fin.ext
    simp only [fifteenStage0CycleWitnessTypeIndex, hlabel]
    exact Nat.mod_eq_of_lt (labels i).isLt

end CirclePacking
