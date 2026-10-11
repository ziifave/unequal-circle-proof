import CirclePacking.FifteenStages34
import CirclePacking.FifteenStage3StreamSoundness

/-! Retrieve the concrete, replayed stream for a closed Stage 3 pattern and
feed it to the geometric stream-soundness theorem. -/

namespace CirclePacking

theorem fifteenStage3ClosedPattern_excludes_geometric_profile
    (radii : Fin 15 → ℝ) (labels : Fin 15 → Nat)
    (profile : Fin 15 → Bool) (theta : Fin 15 → ℝ)
    (hgeometry : FifteenStage3GeometricConditions radii labels)
    (hprofile : ∀ i, profile i = true ↔
      radii i < fifteenCandidateInnerThreshold)
    (houterLabel : ∀ i, profile i = false → labels i = 7)
    (hsorted : ∀ i j : Fin 15, i.1 < j.1 → theta i ≤ theta j)
    (hthetaRange : ∀ i, 0 ≤ theta i ∧ theta i ≤ 2 * Real.pi)
    (hsep : ∀ i j : Fin 15, i ≠ j →
      4 ≤ pointNorm
        ((polarPoint (radii i) (theta i)).1 - (polarPoint (radii j) (theta j)).1,
         (polarPoint (radii i) (theta i)).2 - (polarPoint (radii j) (theta j)).2) ^ 2)
    (hclosed : fifteenStage0ProfileWord profile ∈ fifteenStage3CertifiedPatterns) :
    False := by
  let pattern := fifteenStage0ProfileWord profile
  obtain ⟨record, hrecordPattern, hrecordValid⟩ :=
    fifteenStage3CertifiedPattern_has_valid_record pattern (by simpa [pattern] using hclosed)
  have hstream : s3CheckStream (s3InnerPositions pattern).size
      (s3InnerPositions pattern) record.cycles (s3Initial pattern)
      record.stream.toList = some [] := by
    unfold s3RecordValid at hrecordValid
    rw [hrecordPattern] at hrecordValid
    cases hcheck : s3CheckStream (s3InnerPositions pattern).size
        (s3InnerPositions pattern) record.cycles (s3Initial pattern)
        record.stream.toList with
    | none => simp [hcheck] at hrecordValid
    | some suffix =>
        cases suffix with
        | nil => rfl
        | cons c rest => simp [hcheck] at hrecordValid
  exact fifteenStage3GeometricTargetPath_stream_no_success
    radii labels profile theta hgeometry hprofile houterLabel hsorted
    hthetaRange hsep record.cycles record.stream.toList hstream

/-- Every candidate-radius packing reaches one of the 23 Stage 3 residual
profiles. The 355 profiles with closed certificates are excluded using the
certificate-to-geometry bridge above. -/
theorem fifteen_unit_packing_wall_push_stage3_residual_profile
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
      fifteenStage0ProfileWord profile ∈ fifteenStage3ResidualPatterns ∧
      FifteenStage3GeometricConditions radii labels ∧
      (∀ i j : Fin 15, i.val < j.val → theta i ≤ theta j) ∧
      (∀ i, 0 ≤ theta i ∧ theta i ≤ 2 * Real.pi) ∧
      (∀ i j : Fin 15, i ≠ j →
        4 ≤ pointNorm
          ((polarPoint (radii i) (theta i)).1 - (polarPoint (radii j) (theta j)).1,
           (polarPoint (radii i) (theta i)).2 - (polarPoint (radii j) (theta j)).2) ^ 2) := by
  dsimp only
  obtain ⟨reflected, shift, hsurvivor, hgeometry, hsorted, hrange, hsep⟩ :=
    fifteen_unit_packing_wall_push_stage3_geometric_handoff P hunit hR
  refine ⟨reflected, shift, ?_⟩
  let Q := fifteen_unit_packing_wall_push P hunit hR
  let radii := fifteenStage0TransformProfile (fifteenPackingSortedRadius Q)
    reflected shift
  let theta := fifteenStage0DihedralAngles (fifteenPackingSortedAngle Q)
    reflected shift
  let labels := fun i => fifteenStage3RadialLabel (radii i)
  let profile := fun i => decide
    (radii i < fifteenCandidateInnerThreshold)
  have hprofile : ∀ i, profile i = true ↔
      radii i < fifteenCandidateInnerThreshold := by
    intro i
    simp [profile]
  have houterLabel : ∀ i, profile i = false → labels i = 7 := by
    intro i hfalse
    have hnot : ¬ radii i < fifteenCandidateInnerThreshold := by
      intro hlt
      have htrue := (hprofile i).2 hlt
      rw [hfalse] at htrue
      cases htrue
    simp [labels, fifteenStage3RadialLabel, hnot]
  have hclassification := fifteenStage0Survivor_stage3_closed_or_residual
    (fifteenStage0ProfileWord profile) hsurvivor
  rcases hclassification with hclosed | hresidual
  · exact False.elim (fifteenStage3ClosedPattern_excludes_geometric_profile
      radii labels profile theta hgeometry hprofile houterLabel hsorted hrange hsep hclosed)
  · exact ⟨hresidual, hgeometry, hsorted, hrange, hsep⟩

end CirclePacking
