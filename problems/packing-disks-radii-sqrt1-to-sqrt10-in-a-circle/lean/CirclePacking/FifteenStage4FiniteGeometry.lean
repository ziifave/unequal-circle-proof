import CirclePacking.FifteenStage3FiniteGeometry
import CirclePacking.FifteenStage4GeometricHandoff

/-! The verified Stage 4 streams remove the nineteen closed Stage 3 survivors
from actual packing profiles, leaving precisely the four profiles passed to
the exact radial subdivision certificate. -/

namespace CirclePacking

def fifteenStage4ResidualPartitionCheck : Bool :=
  fifteenStage3ResidualPatterns.all (fun pattern =>
    decide (pattern ∈ fifteenStage4CertifiedPatterns ∨
      pattern ∈ fifteenStage4ResidualPatterns))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem fifteenStage4ResidualPartition_replays :
    fifteenStage4ResidualPartitionCheck = true := by
  native_decide

theorem fifteenStage3Residual_mem_stage4_partition {pattern : String}
    (hmem : pattern ∈ fifteenStage3ResidualPatterns) :
    pattern ∈ fifteenStage4CertifiedPatterns ∨
      pattern ∈ fifteenStage4ResidualPatterns := by
  have hcheck := (List.all_eq_true.mp fifteenStage4ResidualPartition_replays)
    pattern hmem
  exact of_decide_eq_true hcheck

private theorem fifteenStage3OwnerSpec_nonneg {label : Nat} {r : ℝ}
    (howner : fifteenStage3OwnerSpec label r) : 0 ≤ r := by
  have hlabel : label = 0 ∨ label = 1 ∨ label = 2 ∨ label = 3 ∨
      label = 4 ∨ label = 5 ∨ label = 6 ∨ label = 7 ∨ label = 9 := by
    unfold fifteenStage3OwnerSpec at howner
    split at howner <;> simp_all
  rcases hlabel with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp_all [fifteenStage3OwnerSpec] <;>
    linarith [fifteenCandidateOuterRadius_pos]

private theorem fifteenStage3RadialOwner_classification {r : ℝ}
    (howner : fifteenStage3OwnerSpec (fifteenStage3RadialLabel r) r) :
    r = fifteenCandidateOuterRadius ∨
      r < fifteenCandidateInnerThreshold := by
  unfold fifteenStage3RadialLabel at howner
  split_ifs at howner with hinner
  · exact Or.inr hinner
  · exact Or.inl (by simpa [fifteenStage3OwnerSpec] using howner)

/-- Every candidate-radius packing that survived Stage 3 lies among the four
Stage 4 residual profile words. The nineteen other Stage 3 residual words are
excluded by their replayed certificates and the Stage 4 geometric handoff. -/
theorem fifteen_unit_packing_wall_push_stage4_residual_profile
    {R : ℝ} (P : Packing 15 R)
    (hunit : ∀ i, (P.circles i).radius = 1)
    (hR : R ≤ fifteenCandidateOuterRadius + 1) :
    ∃ reflected : Bool, ∃ shift : Fin 15,
      let Q := fifteen_unit_packing_wall_push P hunit hR
      let radii := fifteenStage0TransformProfile (fifteenPackingSortedRadius Q)
        reflected shift
      let theta := fifteenStage0DihedralAngles (fifteenPackingSortedAngle Q)
        reflected shift
      let labels := fun i => fifteenStage3RadialLabel (radii i)
      let profile := fun i => decide
        (radii i < fifteenCandidateInnerThreshold)
      fifteenStage0ProfileWord profile ∈ fifteenStage4ResidualPatterns ∧
      FifteenStage3GeometricConditions radii labels ∧
      (∀ i j : Fin 15, i.val < j.val → theta i ≤ theta j) ∧
      (∀ i, 0 ≤ theta i ∧ theta i ≤ 2 * Real.pi) ∧
      (∀ i j : Fin 15, i ≠ j →
        4 ≤ pointNorm
          ((polarPoint (radii i) (theta i)).1 - (polarPoint (radii j) (theta j)).1,
           (polarPoint (radii i) (theta i)).2 - (polarPoint (radii j) (theta j)).2) ^ 2) := by
  dsimp only
  obtain ⟨reflected, shift, hstage3Residual, hgeometry, hsorted, hrange, hsep⟩ :=
    fifteen_unit_packing_wall_push_stage3_residual_profile P hunit hR
  refine ⟨reflected, shift, ?_⟩
  let Q := fifteen_unit_packing_wall_push P hunit hR
  let radii := fifteenStage0TransformProfile (fifteenPackingSortedRadius Q)
    reflected shift
  let theta := fifteenStage0DihedralAngles (fifteenPackingSortedAngle Q)
    reflected shift
  let labels := fun i => fifteenStage3RadialLabel (radii i)
  let profile := fun i => decide
    (radii i < fifteenCandidateInnerThreshold)
  have hlabels : ∀ i, labels i = fifteenStage3RadialLabel (radii i) := by
    intro i
    rfl
  have hprofile : ∀ i, profile i = true ↔
      radii i < fifteenCandidateInnerThreshold := by
    intro i
    simp [profile]
  have hnonneg : ∀ i, 0 ≤ radii i := by
    intro i
    exact fifteenStage3OwnerSpec_nonneg (hgeometry.owners i)
  have hclassification : ∀ i,
      radii i = fifteenCandidateOuterRadius ∨
        radii i < fifteenCandidateInnerThreshold := by
    intro i
    exact fifteenStage3RadialOwner_classification (hgeometry.owners i)
  have hpartition := fifteenStage3Residual_mem_stage4_partition hstage3Residual
  rcases hpartition with hclosed | hresidual
  · exact False.elim (fifteenStage4ClosedPattern_excludes_geometric_profile
      radii labels hlabels hgeometry profile hprofile hnonneg hclassification
      theta hsorted (fun i => (hrange i).1) (fun i => (hrange i).2) hsep hclosed)
  · exact ⟨hresidual, hgeometry, hsorted, hrange, hsep⟩

end CirclePacking
