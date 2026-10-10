import CirclePacking.FifteenStageZeroAssignments
import CirclePacking.FifteenStageZeroInnerCount

/-! Packing-level interface to the finite Stage 0 assignment conditions. -/

namespace CirclePacking

/-- After wall replacement, the actual inner-center set has weight 5 through 8
and satisfies the three-bin assignment constraints used by the finite Stage 0
enumerator.  Both endpoints are derived from packing geometry. -/
theorem fifteen_unit_packing_wall_push_stage0_assignment
    {R : ℝ} (P : Packing 15 R)
    (hunit : ∀ i, (P.circles i).radius = 1)
    (hR : R ≤ fifteenCandidateOuterRadius + 1) :
    let Q := fifteen_unit_packing_wall_push P hunit hR
    let inner : Finset (Fin 15) := Finset.univ.filter fun k =>
      fifteenPackingSortedRadius Q k < fifteenCandidateInnerThreshold
    5 ≤ inner.card ∧ inner.card ≤ 8 ∧
      (∀ i ∈ inner,
        1 ≤ fifteenStage0RadialType (fifteenPackingSortedRadius Q i) ∧
          fifteenStage0RadialType (fifteenPackingSortedRadius Q i) ≤ 3) ∧
      (inner.filter fun i =>
        fifteenStage0RadialType (fifteenPackingSortedRadius Q i) = 1).card ≤ 1 ∧
      (inner.filter fun i =>
        fifteenStage0RadialType (fifteenPackingSortedRadius Q i) = 3).card ≥
          inner.card - 4 := by
  classical
  let Q := fifteen_unit_packing_wall_push P hunit hR
  let inner : Finset (Fin 15) := Finset.univ.filter fun k =>
    fifteenPackingSortedRadius Q k < fifteenCandidateInnerThreshold
  have hQunit : ∀ i, (Q.circles i).radius = 1 := by
    intro i
    exact fifteen_unit_packing_wall_push_preserves_unit_radii P hunit hR i
  have hassign := fifteenStage0_radial_type_assignment_counts Q hQunit inner
  refine ⟨?_, ?_, ?_, hassign.1, hassign.2⟩
  · simpa [Q, inner] using
      fifteen_unit_packing_wall_push_inner_count_ge_five P hunit hR
  · simpa [Q, inner] using
      fifteen_unit_packing_wall_push_inner_count_le_eight P hunit hR
  · intro i hi
    exact fifteenStage0RadialType_valid (fifteenPackingSortedRadius Q i)

/-- Convert a radius into the four coarse Stage 0 types.  Type zero denotes a
wall center; inner centers use the three radial bins from the assignment
enumerator. -/
noncomputable def fifteenStage0RadialTypeIndex (r : ℝ) : Fin 4 :=
  if hinner : r < fifteenCandidateInnerThreshold then
    ⟨fifteenStage0RadialType r, by
      have hvalid := fifteenStage0RadialType_valid r
      omega⟩
  else ⟨0, by omega⟩

/-- The geometric inner/outer classification assigns every wall-pushed
center to a Stage 0 radius box.  This is the packing-to-box half of the
finite reduction; the remaining step is matching the resulting cyclic word
to its recorded dihedral representative and assignment certificate. -/
theorem fifteenStage0RadialTypeIndex_box_of_classification
    (r : ℝ) (hr0 : 0 ≤ r)
    (hclass : r = fifteenCandidateOuterRadius ∨
      r < fifteenCandidateInnerThreshold) :
    ((fifteenStage0CoarseTypeBox
      (fifteenStage0RadialTypeIndex r)).1 : ℝ) ≤ r ∧
    r ≤ ((fifteenStage0CoarseTypeBox
      (fifteenStage0RadialTypeIndex r)).2 : ℝ) := by
  have hthreshold : fifteenCandidateInnerThreshold <
      (2385432 : ℝ) / 1000000 := by
    simpa [fifteenCandidateInnerThreshold] using
      fifteenCandidateInnerThreshold_lt_2385432_1e6
  by_cases hinner : r < fifteenCandidateInnerThreshold
  · have htype := fifteenStage0RadialType_valid r
    have htypeCases : fifteenStage0RadialType r = 1 ∨
        fifteenStage0RadialType r = 2 ∨
        fifteenStage0RadialType r = 3 := by omega
    rcases htypeCases with hone | htwo | hthree
    · have hrupper : r ≤ 1 := by
        have := (fifteenStage0RadialType_eq_one_iff r).mp hone
        linarith
      have hbox := fifteenStage0InnerTypeBox_real_bounds
      rw [show fifteenStage0RadialTypeIndex r = (1 : Fin 4) by
        simp [fifteenStage0RadialTypeIndex, hinner, hone]]
      exact ⟨by rw [hbox.1.1]; exact hr0,
        by rw [hbox.1.2]; exact hrupper⟩
    · have hnotSmall : ¬ r < 1 := by
        intro hs
        have htag := (fifteenStage0RadialType_eq_one_iff r).2 hs
        rw [htwo] at htag
        norm_num at htag
      have hbelow : r < 5 / 3 := by
        by_contra hnot
        have houter : 5 / 3 ≤ r := le_of_not_gt hnot
        have htag := (fifteenStage0RadialType_eq_three_iff r).2 houter
        rw [htwo] at htag
        norm_num at htag
      have hbox := fifteenStage0InnerTypeBox_real_bounds
      rw [show fifteenStage0RadialTypeIndex r = (2 : Fin 4) by
        simp [fifteenStage0RadialTypeIndex, hinner, htwo]]
      exact ⟨by rw [hbox.2.1.1]; exact le_of_not_gt hnotSmall,
        by rw [hbox.2.1.2]; exact hbelow.le⟩
    · have hrlower : 5 / 3 ≤ r :=
        (fifteenStage0RadialType_eq_three_iff r).mp hthree
      have hrupper : r ≤ (2385432 : ℝ) / 1000000 :=
        le_trans hinner.le hthreshold.le
      have hbox := fifteenStage0InnerTypeBox_real_bounds
      rw [show fifteenStage0RadialTypeIndex r = (3 : Fin 4) by
        simp [fifteenStage0RadialTypeIndex, hinner, hthree]]
      exact ⟨by rw [hbox.2.2.1]; exact hrlower,
        by rw [hbox.2.2.2]; exact hrupper⟩
  · have hwall : r = fifteenCandidateOuterRadius := hclass.resolve_right hinner
    have hbox := fifteenStage0OuterTypeBox_bounds
    rw [show fifteenStage0RadialTypeIndex r = (0 : Fin 4) by
      simp [fifteenStage0RadialTypeIndex, hinner]]
    rw [hwall]
    exact ⟨by rw [hbox.1]; exact (by
      have hb := fifteenCandidateOuterRadius_mem_Ioo_352_353
      linarith),
      by rw [hbox.2]; exact fifteenCandidateOuterRadius_lt_3522_1000.le⟩

theorem fifteen_unit_packing_wall_push_sorted_radial_type_box
    {R : ℝ} (P : Packing 15 R)
    (hunit : ∀ i, (P.circles i).radius = 1)
    (hR : R ≤ fifteenCandidateOuterRadius + 1) (i : Fin 15) :
    ((fifteenStage0CoarseTypeBox
      (fifteenStage0RadialTypeIndex
        (fifteenPackingSortedRadius
          (fifteen_unit_packing_wall_push P hunit hR) i))).1 : ℝ) ≤
        fifteenPackingSortedRadius
          (fifteen_unit_packing_wall_push P hunit hR) i ∧
    fifteenPackingSortedRadius
        (fifteen_unit_packing_wall_push P hunit hR) i ≤
      ((fifteenStage0CoarseTypeBox
        (fifteenStage0RadialTypeIndex
          (fifteenPackingSortedRadius
            (fifteen_unit_packing_wall_push P hunit hR) i))).2 : ℝ) := by
  let Q := fifteen_unit_packing_wall_push P hunit hR
  have hr0 : 0 ≤ fifteenPackingSortedRadius Q i := by
    simp [Q, fifteenPackingSortedRadius, fifteenCenterRadius]
    exact pointNorm_nonneg _
  have hclass := fifteen_unit_packing_wall_push_sorted_radial_classification
    P hunit hR i
  exact fifteenStage0RadialTypeIndex_box_of_classification
    (fifteenPackingSortedRadius Q i) hr0 (by simpa [Q] using hclass)

/-- The complete geometric input expected by the Stage 0 radial classifier:
five through eight inner centers, admissible populations of the three inner
types, and a certified coarse radius box at every angle-sorted position. -/
theorem fifteen_unit_packing_wall_push_stage0_profile
    {R : ℝ} (P : Packing 15 R)
    (hunit : ∀ i, (P.circles i).radius = 1)
    (hR : R ≤ fifteenCandidateOuterRadius + 1) :
    let Q := fifteen_unit_packing_wall_push P hunit hR
    let inner : Finset (Fin 15) := Finset.univ.filter fun i =>
      fifteenPackingSortedRadius Q i < fifteenCandidateInnerThreshold
    5 ≤ inner.card ∧ inner.card ≤ 8 ∧
      (∀ i ∈ inner,
        1 ≤ fifteenStage0RadialType (fifteenPackingSortedRadius Q i) ∧
          fifteenStage0RadialType (fifteenPackingSortedRadius Q i) ≤ 3) ∧
      (inner.filter fun i =>
        fifteenStage0RadialType (fifteenPackingSortedRadius Q i) = 1).card ≤ 1 ∧
      (inner.filter fun i =>
        fifteenStage0RadialType (fifteenPackingSortedRadius Q i) = 3).card ≥
          inner.card - 4 ∧
      (∀ i : Fin 15,
        ((fifteenStage0CoarseTypeBox
          (fifteenStage0RadialTypeIndex
            (fifteenPackingSortedRadius Q i))).1 : ℝ) ≤
            fifteenPackingSortedRadius Q i ∧
        fifteenPackingSortedRadius Q i ≤
          ((fifteenStage0CoarseTypeBox
            (fifteenStage0RadialTypeIndex
              (fifteenPackingSortedRadius Q i))).2 : ℝ)) := by
  classical
  let Q := fifteen_unit_packing_wall_push P hunit hR
  let inner : Finset (Fin 15) := Finset.univ.filter fun i =>
    fifteenPackingSortedRadius Q i < fifteenCandidateInnerThreshold
  have hassign := fifteen_unit_packing_wall_push_stage0_assignment P hunit hR
  have hbox := fifteen_unit_packing_wall_push_sorted_radial_type_box
    P hunit hR
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [Q, inner] using hassign.1
  · simpa [Q, inner] using hassign.2.1
  · simpa [Q, inner] using hassign.2.2.1
  · simpa [Q, inner] using hassign.2.2.2.1
  · simpa [Q, inner] using hassign.2.2.2.2
  · intro i
    simpa [Q] using hbox i

end CirclePacking
