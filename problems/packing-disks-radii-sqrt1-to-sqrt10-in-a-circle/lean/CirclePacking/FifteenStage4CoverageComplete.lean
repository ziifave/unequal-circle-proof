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

private theorem s4CoverageLocalBox_forces_profile_index_two
    (G : FifteenStage4CoverageGeometry) (pattern : String)
    (hword : pattern = fifteenStage0ProfileWord G.profile)
    (box : FifteenBox) (inner : List Nat)
    (hcontains : fifteenRealBoxContains box G.radii)
    (hinner : inner = fifteenInnerPositions "001001001001001")
    (hbounds : ∀ p ∈ inner,
      fifteenLocalLo ≤ box[p]!.1 ∧ box[p]!.2 ≤ fifteenLocalHi) :
    G.profile ⟨2, by decide⟩ = true := by
  have htwo : 2 ∈ inner := by
    rw [hinner]
    decide
  have hboxUpper : (box[2]!.2 : ℝ) ≤ (43 : ℝ) / 25 := by
    have h := (hbounds 2 htwo).2
    change box[2]!.2 ≤ fifteenRational 43 25 at h
    have hcast : (box[2]!.2 : ℝ) ≤ (fifteenLocalHi : ℝ) := by
      exact_mod_cast h
    calc
      (box[2]!.2 : ℝ) ≤ (fifteenLocalHi : ℝ) := hcast
      _ = (43 : ℝ) / 25 := by
        norm_num [fifteenLocalHi, fifteenRational, Rat.normalize_eq_mkRat,
          Rat.cast_mkRat_of_ne_zero]
  have hcontainsTwo := hcontains ⟨2, by decide⟩
  change (box[2]!.1 : ℝ) ≤ G.radii ⟨2, by decide⟩ ∧
    G.radii ⟨2, by decide⟩ ≤ (box[2]!.2 : ℝ) at hcontainsTwo
  have hupper : (43 : ℝ) / 25 < fifteenCandidateInnerThreshold := by
    have hsmall : (43 : ℝ) / 25 < 2 := by norm_num
    linarith [fifteenCandidateInnerThreshold_gt_two]
  have hradius : G.radii ⟨2, by decide⟩ <
      fifteenCandidateInnerThreshold :=
    lt_of_le_of_lt (le_trans hcontainsTwo.2 hboxUpper) hupper
  exact (G.hprofile ⟨2, by decide⟩).2 hradius

private theorem s4CoverageNormalPattern_eq_canonical
    (pattern : String) (G : FifteenStage4CoverageGeometry)
    (hword : pattern = fifteenStage0ProfileWord G.profile)
    (hpattern : pattern ∈ s4CoverageNormalPatterns) :
    pattern = "001001001001001" := by
  obtain ⟨box, inner, hcontains, hinner, hbounds⟩ :=
    s4CoverageGeometricNormalTarget_forces_local pattern G hword hpattern
  have htrue := s4CoverageLocalBox_forces_profile_index_two
    G pattern hword box inner hcontains hinner hbounds
  have hmem : 2 ∈ (s3InnerPositions pattern).toList := by
    have hmem' := (fifteenStage3ProfileWord_inner_iff G.profile ⟨2, by decide⟩).2 htrue
    simpa [hword] using hmem'
  have hchar := (s3InnerPositions_mem_iff_char pattern 2).mp hmem
  rcases List.mem_cons.mp hpattern with h0 | hrest
  · have hnot : ("000100100010101".toList[2]?) ≠ some '1' := by decide
    exact False.elim (hnot (by simpa [h0] using hchar.2))
  · rcases List.mem_cons.mp hrest with h1 | hrest
    · have hnot : ("000100100100101".toList[2]?) ≠ some '1' := by decide
      exact False.elim (hnot (by simpa [h1] using hchar.2))
    · exact List.mem_singleton.mp hrest

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
      ∃ geometry : FifteenStage4CoverageGeometry,
        geometry.radii = radii ∧ geometry.theta = theta ∧
        geometry.profile = profile ∧
      pattern = "001001001001001" ∧
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
    have hcanonical := s4CoverageNormalPattern_eq_canonical pattern G rfl hnormal
    simp [h0] at hcanonical
  · have hnormal : pattern ∈ s4CoverageNormalPatterns := by
      simp [s4CoverageNormalPatterns, h1]
    have hcanonical := s4CoverageNormalPattern_eq_canonical pattern G rfl hnormal
    simp [h1] at hcanonical
  · have hnormal : pattern ∈ s4CoverageNormalPatterns := by
      simp [s4CoverageNormalPatterns, h2]
    exact ⟨G, rfl, rfl, rfl, h2,
      s4CoverageGeometricNormalTarget_forces_local pattern G rfl hnormal⟩
  · rcases hspecial with hspecial | hnil
    · have hword : fifteenSpecialPattern = fifteenStage0ProfileWord G.profile := by
        change "001001001001011" = fifteenStage0ProfileWord profile
        simpa [fifteenSpecialPattern] using hspecial.symm
      exact False.elim (s4CoverageSpecialGeometry_impossible G hword)
    · simp at hnil

end CirclePacking
