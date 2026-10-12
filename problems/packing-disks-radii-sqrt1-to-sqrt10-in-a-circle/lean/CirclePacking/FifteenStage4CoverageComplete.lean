import CirclePacking.FifteenStage4CoverageHandoff
import CirclePacking.FifteenStage4SpecialCoverageSoundness

/-! This module closes the exceptional Stage 4 profile in the arbitrary-packing
handoff.  The exact finite subdivision handles the normal profiles; the
origin-special certificate excludes the only residual exceptional profile. -/

namespace CirclePacking

open Real

private theorem s4Coverage_stage3Owner_nonneg {label : Nat} {r : ℝ}
    (howner : fifteenStage3OwnerSpec label r) : 0 ≤ r := by
  have hlabel : label = 0 ∨ label = 1 ∨ label = 2 ∨ label = 3 ∨
      label = 4 ∨ label = 5 ∨ label = 6 ∨ label = 7 ∨ label = 9 := by
    unfold fifteenStage3OwnerSpec at howner
    split at howner <;> simp_all
  rcases hlabel with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp_all [fifteenStage3OwnerSpec] <;>
    linarith [fifteenCandidateOuterRadius_pos]

private theorem s4Coverage_stage3Radial_classification {r : ℝ}
    (howner : fifteenStage3OwnerSpec (fifteenStage3RadialLabel r) r) :
    r = fifteenCandidateOuterRadius ∨
      r < fifteenCandidateInnerThreshold := by
  unfold fifteenStage3RadialLabel at howner
  split_ifs at howner with hinner
  · exact Or.inr hinner
  · exact Or.inl (by simpa [fifteenStage3OwnerSpec] using howner)

/-- Every unit-disk packing below the candidate radius, after the wall push
and cyclic relabeling, is forced into the unique certified local radius box.
This removes the exceptional six-inner profile left by
`fifteen_unit_packing_stage4_coverage_root_or_special`. -/
theorem fifteen_unit_packing_stage4_coverage_local
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
      let pattern := fifteenStage0ProfileWord profile
      ∃ box inner, fifteenRealBoxContains box radii ∧
        inner = fifteenInnerPositions "001001001001001" ∧
        ∀ p ∈ inner,
          fifteenLocalLo ≤ box[p]!.1 ∧ box[p]!.2 ≤ fifteenLocalHi := by
  obtain ⟨reflected, shift, hresidual, hgeometry, hsorted, hrange, hsep⟩ :=
    fifteen_unit_packing_wall_push_stage4_residual_profile P hunit hR
  refine ⟨reflected, shift, ?_⟩
  dsimp only
  let Q := fifteen_unit_packing_wall_push P hunit hR
  let radii := fifteenStage0TransformProfile (fifteenPackingSortedRadius Q)
    reflected shift
  let theta := fifteenStage0DihedralAngles (fifteenPackingSortedAngle Q)
    reflected shift
  let labels := fun i => fifteenStage3RadialLabel (radii i)
  let profile := fun i => decide
    (radii i < fifteenCandidateInnerThreshold)
  let pattern := fifteenStage0ProfileWord profile
  have hlabels : ∀ i, labels i = fifteenStage3RadialLabel (radii i) := by
    intro i
    rfl
  have hprofile : ∀ i, profile i = true ↔
      radii i < fifteenCandidateInnerThreshold := by
    intro i
    simp [profile]
  have hnonneg : ∀ i, 0 ≤ radii i := by
    intro i
    exact s4Coverage_stage3Owner_nonneg (hgeometry.owners i)
  have hclassification : ∀ i,
      radii i = fifteenCandidateOuterRadius ∨
        radii i < fifteenCandidateInnerThreshold := by
    intro i
    exact s4Coverage_stage3Radial_classification (hgeometry.owners i)
  have hprofileList : pattern ∈
      ["000100100010101", "000100100100101",
       "001001001001001", "001001001001011"] := by
    rw [← fifteenStage4ResidualPatterns_exact]
    exact hresidual
  simp only [List.mem_cons, List.mem_singleton] at hprofileList
  let G : FifteenStage4CoverageGeometry := {
    radii := radii
    labels := labels
    hlabels := hlabels
    hgeometry := hgeometry
    profile := profile
    hprofile := hprofile
    hnonneg := hnonneg
    hclassification := hclassification
    theta := theta
    hsorted := hsorted
    hthetaLo := fun i => (hrange i).1
    hthetaHi := fun i => (hrange i).2
    hsep := hsep
  }
  rcases hprofileList with h0 | h1 | h2 | hspecial
  · have hnormal : pattern ∈ s4CoverageNormalPatterns := by
      simp [s4CoverageNormalPatterns, h0]
    exact s4CoverageGeometricNormalTarget_forces_local pattern G rfl hnormal
  · have hnormal : pattern ∈ s4CoverageNormalPatterns := by
      simp [s4CoverageNormalPatterns, h1]
    exact s4CoverageGeometricNormalTarget_forces_local pattern G rfl hnormal
  · have hnormal : pattern ∈ s4CoverageNormalPatterns := by
      simp [s4CoverageNormalPatterns, h2]
    exact s4CoverageGeometricNormalTarget_forces_local pattern G rfl hnormal
  · rcases hspecial with hspecial | hnil
    · have hword : fifteenSpecialPattern = fifteenStage0ProfileWord G.profile := by
        change "001001001001011" = fifteenStage0ProfileWord profile
        simpa [fifteenSpecialPattern] using hspecial.symm
      exact False.elim (s4CoverageSpecialGeometry_impossible G hword)
    · simp at hnil

end CirclePacking
