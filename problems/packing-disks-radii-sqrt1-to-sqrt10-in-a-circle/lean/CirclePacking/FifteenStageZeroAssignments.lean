import CirclePacking.FifteenStageZeroGeometry

/-! Assign the three inner radial bins directly from the radius of each
center.  The two cardinality conditions here are exactly the restrictions
used by the finite Stage 0 assignment enumerator. -/

namespace CirclePacking

noncomputable def fifteenStage0RadialType (r : ℝ) : Nat :=
  if r < 1 then 1 else if r < 5 / 3 then 2 else 3

theorem fifteenStage0RadialType_valid (r : ℝ) :
    1 ≤ fifteenStage0RadialType r ∧ fifteenStage0RadialType r ≤ 3 := by
  classical
  unfold fifteenStage0RadialType
  split_ifs <;> omega

theorem fifteenStage0RadialType_eq_one_iff (r : ℝ) :
    fifteenStage0RadialType r = 1 ↔ r < 1 := by
  classical
  constructor
  · intro htag
    by_contra hnot
    unfold fifteenStage0RadialType at htag
    by_cases h2 : r < 5 / 3
    · simp [hnot, h2] at htag
    · simp [hnot, h2] at htag
  · intro hsmall
    simp [fifteenStage0RadialType, hsmall]

theorem fifteenStage0RadialType_eq_three_iff (r : ℝ) :
    fifteenStage0RadialType r = 3 ↔ 5 / 3 ≤ r := by
  classical
  constructor
  · intro htag
    by_contra hnot
    have hlt : r < 5 / 3 := lt_of_not_ge hnot
    unfold fifteenStage0RadialType at htag
    by_cases h1 : r < 1
    · simp [h1] at htag
    · by_cases h2 : r < 5 / 3
      · simp [h1, h2] at htag
      · exact h2 hlt
  · intro houter
    unfold fifteenStage0RadialType
    have hnot1 : ¬ r < 1 := by linarith
    have hnot53 : ¬ r < 5 / 3 := not_lt.mpr houter
    simp [hnot1, hnot53]

theorem fifteenStage0_radial_type_assignment_counts
    {R : ℝ} (P : Packing 15 R)
    (hunit : ∀ i, (P.circles i).radius = 1)
    (S : Finset (Fin 15)) :
    (S.filter fun i =>
      fifteenStage0RadialType (fifteenPackingSortedRadius P i) = 1).card ≤ 1 ∧
    (S.filter fun i =>
      fifteenStage0RadialType (fifteenPackingSortedRadius P i) = 3).card ≥
        S.card - 4 := by
  classical
  let smallOne : Finset (Fin 15) := Finset.univ.filter fun i =>
    fifteenPackingSortedRadius P i < 1
  let smallFour : Finset (Fin 15) := Finset.univ.filter fun i =>
    fifteenPackingSortedRadius P i ≤ 5 / 3
  let oneSet : Finset (Fin 15) := S.filter fun i =>
    fifteenStage0RadialType (fifteenPackingSortedRadius P i) = 1
  let threeSet : Finset (Fin 15) := S.filter fun i =>
    fifteenStage0RadialType (fifteenPackingSortedRadius P i) = 3
  let notThree : Finset (Fin 15) := S.filter fun i =>
    fifteenStage0RadialType (fifteenPackingSortedRadius P i) ≠ 3
  have honeSubset : oneSet ⊆ smallOne := by
    intro i hi
    have htag := (Finset.mem_filter.mp hi).2
    have hsmall := (fifteenStage0RadialType_eq_one_iff _).mp htag
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsmall⟩
  have hthreeComplementSubset : notThree ⊆ smallFour := by
    intro i hi
    have hnot := (Finset.mem_filter.mp hi).2
    have hsmall : fifteenPackingSortedRadius P i ≤ 5 / 3 := by
      by_contra hbound
      have houter : 5 / 3 ≤ fifteenPackingSortedRadius P i := by
        linarith
      have htag := (fifteenStage0RadialType_eq_three_iff _).2 houter
      exact hnot htag
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsmall⟩
  have honeCount : oneSet.card ≤ 1 := by
    calc
      oneSet.card ≤ smallOne.card := Finset.card_le_card honeSubset
      _ ≤ 1 := fifteenStage0_subunitShell_population_bound P hunit
  have hnotThreeCount : notThree.card ≤ 4 := by
    calc
      notThree.card ≤ smallFour.card := Finset.card_le_card hthreeComplementSubset
      _ ≤ 4 := fifteenStage0_smallRadialShell_population_bound P hunit
  have hpartition : threeSet.card + notThree.card = S.card := by
    simpa [threeSet, notThree] using
      (Finset.card_filter_add_card_filter_not (s := S)
        (p := fun i =>
          fifteenStage0RadialType (fifteenPackingSortedRadius P i) = 3))
  constructor
  · simpa [oneSet] using honeCount
  · apply Nat.sub_le_iff_le_add.mpr
    calc
      S.card = threeSet.card + notThree.card := hpartition.symm
      _ ≤ threeSet.card + 4 := Nat.add_le_add_left hnotThreeCount _

end CirclePacking
