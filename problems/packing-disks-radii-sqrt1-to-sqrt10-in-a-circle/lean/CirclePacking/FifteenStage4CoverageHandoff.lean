import CirclePacking.FifteenStage4Coverage000
import CirclePacking.FifteenStage4Coverage001
import CirclePacking.FifteenStage4Coverage002
import CirclePacking.FifteenStage4CoverageSoundness
import CirclePacking.FifteenStage4CoverageRoots
import CirclePacking.FifteenStage4FiniteGeometry

/-! The Stage 4 coverage trees are connected to geometric data and to the
normal roots of the exact radial-subdivision certificate. The exceptional
six-inner profile remains a separate origin-special case. -/

namespace CirclePacking

structure FifteenStage4CoverageGeometry where
  radii : Fin 15 → ℝ
  labels : Fin 15 → Nat
  hlabels : ∀ i, labels i = fifteenStage3RadialLabel (radii i)
  hgeometry : FifteenStage3GeometricConditions radii labels
  profile : Fin 15 → Bool
  hprofile : ∀ i, profile i = true ↔
    radii i < fifteenCandidateInnerThreshold
  hnonneg : ∀ i, 0 ≤ radii i
  hclassification : ∀ i, radii i = fifteenCandidateOuterRadius ∨
    radii i < fifteenCandidateInnerThreshold
  theta : Fin 15 → ℝ
  hsorted : ∀ i j : Fin 15, i.1 < j.1 → theta i ≤ theta j
  hthetaLo : ∀ i, 0 ≤ theta i
  hthetaHi : ∀ i, theta i ≤ 2 * Real.pi
  hsep : ∀ i j : Fin 15, i ≠ j →
    4 ≤ pointNorm
      ((polarPoint (radii i) (theta i)).1 - (polarPoint (radii j) (theta j)).1,
       (polarPoint (radii i) (theta i)).2 - (polarPoint (radii j) (theta j)).2) ^ 2

noncomputable def s4CoverageGeometryTarget
    (G : FifteenStage4CoverageGeometry) : Array Nat :=
  fifteenStage4OwnerLabelArray (fun i => fifteenStage4RadialLabel (G.radii i))

theorem s4CoverageNormalSource_replays (pattern : String)
    (hpattern : pattern ∈ s4CoverageNormalPatterns) :
    ∃ source, s4CoverageSourceValid source pattern = true := by
  simp [s4CoverageNormalPatterns] at hpattern
  rcases hpattern with h0 | h1 | h2
  · subst pattern
    exact ⟨fifteenStage4Coverage000Source, by
      change fifteenStage4Coverage000Valid = true
      exact fifteenStage4Coverage000_replays⟩
  · subst pattern
    exact ⟨fifteenStage4Coverage001Source, by
      change fifteenStage4Coverage001Valid = true
      exact fifteenStage4Coverage001_replays⟩
  · subst pattern
    exact ⟨fifteenStage4Coverage002Source, by
      change fifteenStage4Coverage002Valid = true
      exact fifteenStage4Coverage002_replays⟩

/-- A geometrically feasible normal Stage 4 profile follows the checked
coverage path to an accepted radial assignment, and that assignment is one
of the exact certificate's validated roots. -/
theorem s4CoverageGeometricNormalTarget_root
    (pattern : String) (G : FifteenStage4CoverageGeometry)
    (hword : pattern = fifteenStage0ProfileWord G.profile)
    (hpattern : pattern ∈ s4CoverageNormalPatterns) :
    ∃ roots, s4CoverageRootBoxes? = some roots ∧
      ∃ box, (pattern, s4CoverageTargetAssignment (s4InnerPositions pattern)
        (s4CoverageGeometryTarget G), box) ∈ roots := by
  obtain ⟨source, hsource⟩ := s4CoverageNormalSource_replays pattern hpattern
  obtain ⟨record, _hparse, hrecordPattern, hrecordValid⟩ :=
    s4CoverageSourceValid_record hsource
  obtain ⟨allowed, hallowed, hstream⟩ :=
    s4CoverageRecordValid_stream hrecordValid
  have hallowed' : s4ResidualAssignments? pattern = some allowed := by
    rw [hrecordPattern] at hallowed
    exact hallowed
  have hstream' : s4CoverageStream (s4InnerPositions pattern).size
      (s4InnerPositions pattern) record.cycles allowed
      (s4Initial pattern) record.stream.toList = some [] := by
    rw [hrecordPattern] at hstream
    exact hstream
  have hstream'' : s4CoverageStream
      (s4InnerPositions (fifteenStage0ProfileWord G.profile)).size
      (s4InnerPositions (fifteenStage0ProfileWord G.profile)) record.cycles allowed
      (s4Initial (fifteenStage0ProfileWord G.profile)) record.stream.toList =
        some [] := by
    simpa [hword] using hstream'
  have hmemWord := fifteenStage4CoverageGeometricTargetAssignment_mem
    G.radii G.labels G.hlabels G.hgeometry G.profile G.hprofile
    G.hnonneg G.hclassification G.theta G.hsorted G.hthetaLo G.hthetaHi G.hsep
    allowed record.cycles record.stream.toList hstream''
  have hmem : s4CoverageTargetAssignment (s4InnerPositions pattern)
      (s4CoverageGeometryTarget G) ∈ allowed := by
    simpa [hword, s4CoverageGeometryTarget] using hmemWord
  exact s4CoverageResidualAssignment_has_root_box hpattern
    ⟨allowed, hallowed', hmem⟩

theorem fifteenStage4ResidualPatterns_exact :
    fifteenStage4ResidualPatterns =
      ["000100100010101", "000100100100101",
       "001001001001001", "001001001001011"] := by
  native_decide

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

/-- Every packing below the candidate radius reaches one of the exact roots
for the three normal profiles, or the known six-inner special profile. -/
theorem fifteen_unit_packing_stage4_coverage_root_or_special
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
      pattern = "001001001001011" ∨
        ∃ roots, s4CoverageRootBoxes? = some roots ∧
          ∃ box, (pattern, s4CoverageTargetAssignment
            (s4InnerPositions pattern)
            (fifteenStage4OwnerLabelArray (fun i =>
              fifteenStage4RadialLabel (radii i))), box) ∈ roots := by
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
  · right
    have hnormal : pattern ∈ s4CoverageNormalPatterns := by
      simp [s4CoverageNormalPatterns, h0]
    exact s4CoverageGeometricNormalTarget_root pattern G rfl hnormal
  · right
    have hnormal : pattern ∈ s4CoverageNormalPatterns := by
      simp [s4CoverageNormalPatterns, h1]
    exact s4CoverageGeometricNormalTarget_root pattern G rfl hnormal
  · right
    have hnormal : pattern ∈ s4CoverageNormalPatterns := by
      simp [s4CoverageNormalPatterns, h2]
    exact s4CoverageGeometricNormalTarget_root pattern G rfl hnormal
  · left
    rcases hspecial with hspecial | hnil
    · exact hspecial
    · simp at hnil

end CirclePacking
