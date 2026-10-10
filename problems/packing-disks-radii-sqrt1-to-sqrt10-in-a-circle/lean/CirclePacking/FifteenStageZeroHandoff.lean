import CirclePacking.FifteenStageZeroAssignments
import CirclePacking.FifteenWallPush

/-! Packing-level interface to the finite Stage 0 assignment conditions. -/

namespace CirclePacking

/-- After the wall replacement, the actual inner-center set has at least five
members and admits the same three-bin assignment constraints used by the
finite Stage 0 enumerator.  The only additional geometric input needed to
restrict the enumerated weights to `5` through `8` is stated separately by
the caller as `hinner_le_eight`. -/
theorem fifteen_unit_packing_wall_push_stage0_assignment
    {R : ℝ} (P : Packing 15 R)
    (hunit : ∀ i, (P.circles i).radius = 1)
    (hR : R ≤ fifteenCandidateOuterRadius + 1) :
    let Q := fifteen_unit_packing_wall_push P hunit hR
    let inner : Finset (Fin 15) := Finset.univ.filter fun k =>
      fifteenPackingSortedRadius Q k < fifteenCandidateInnerThreshold
    5 ≤ inner.card ∧
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
  refine ⟨?_, ?_, hassign.1, hassign.2⟩
  · simpa [Q, inner] using
      fifteen_unit_packing_wall_push_inner_count_ge_five P hunit hR
  · intro i hi
    exact fifteenStage0RadialType_valid (fifteenPackingSortedRadius Q i)

end CirclePacking
