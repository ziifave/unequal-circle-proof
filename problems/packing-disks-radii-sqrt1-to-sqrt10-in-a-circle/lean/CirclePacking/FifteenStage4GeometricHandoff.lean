import CirclePacking.FifteenStage4PathGeometry
import CirclePacking.FifteenStage4

/-! The Stage 4 finite stream cannot accept a radial profile arising from a
geometrically feasible packing: the chosen target branch is legal, structural
leaves project to the already excluded Stage 3 leaves, and cycle leaves
contradict the contact-angle lower bounds. -/

namespace CirclePacking

private theorem fifteenStage4RadialOwner_mem_branchLabels (r : ℝ) :
    fifteenStage4RadialOwner r ∈ s4BranchLabels := by
  unfold fifteenStage4RadialOwner
  split_ifs <;> simp [s4BranchLabels]

/-- A successful Stage 4 stream contradicts any actual radial profile whose
Stage 3 owner conditions and pairwise geometry are valid. -/
theorem fifteenStage4GeometricTargetPath_stream_no_success
    (radii : Fin 15 → ℝ) (labels : Fin 15 → Nat)
    (hlabels : ∀ i, labels i = fifteenStage3RadialLabel (radii i))
    (hgeometry : FifteenStage3GeometricConditions radii labels)
    (profile : Fin 15 → Bool)
    (hprofile : ∀ i, profile i = true ↔
      radii i < fifteenCandidateInnerThreshold)
    (hnonneg : ∀ i, 0 ≤ radii i)
    (hclassification : ∀ i, radii i = fifteenCandidateOuterRadius ∨
      radii i < fifteenCandidateInnerThreshold)
    (theta : Fin 15 → ℝ)
    (hsorted : ∀ i j : Fin 15, i.1 < j.1 → theta i ≤ theta j)
    (hthetaLo : ∀ i, 0 ≤ theta i)
    (hthetaHi : ∀ i, theta i ≤ 2 * Real.pi)
    (hsep : ∀ i j : Fin 15, i ≠ j →
      4 ≤ pointNorm
        ((polarPoint (radii i) (theta i)).1 - (polarPoint (radii j) (theta j)).1,
         (polarPoint (radii i) (theta i)).2 - (polarPoint (radii j) (theta j)).2) ^ 2)
    (cycles : Array (List S4CertEdge)) (stream : List Char)
    (hstream : s4CheckStream
      (s4InnerPositions (fifteenStage0ProfileWord profile)).size
      (s4InnerPositions (fifteenStage0ProfileWord profile)) cycles
      (s4Initial (fifteenStage0ProfileWord profile)) stream = some []) :
    False := by
  let pattern := fifteenStage0ProfileWord profile
  let labels4 : Fin 15 → Nat := fun i => fifteenStage4RadialLabel (radii i)
  let target := fifteenStage4OwnerLabelArray labels4
  have howners4 : ∀ i, fifteenStage4OwnerSpec (labels4 i) (radii i) := by
    intro i
    exact fifteenStage4RadialLabel_spec_of_classification (radii i)
      (hnonneg i) (hclassification i)
  have houter4 : ∀ i, profile i = false → labels4 i = 11 := by
    intro i hfalse
    have hnot : ¬ radii i < fifteenCandidateInnerThreshold := by
      intro hlt
      have htrue := (hprofile i).2 hlt
      rw [hfalse] at htrue
      cases htrue
    simp [labels4, fifteenStage4RadialLabel, hnot]
  have hprojectedTarget : target.map s4ToS3Label =
      fifteenStage3OwnerLabelArray labels := by
    apply Array.ext
    · simp [target, labels4, fifteenStage4OwnerLabelArray,
        fifteenStage3OwnerLabelArray]
    · intro p hp₁ hp₂
      have hp : p < 15 := by
        simpa [target, labels4, fifteenStage4OwnerLabelArray] using hp₁
      simp [target, labels4, fifteenStage4OwnerLabelArray,
        fifteenStage3OwnerLabelArray, hlabels,
        s4ToS3RadialLabel_eq_stage3]
  have hallowed : ∀ {s : S4State},
      FifteenStage4TargetPath pattern target s →
      s.depth < (s4InnerPositions pattern).size →
      target[(s4InnerPositions pattern)[s.depth]!]! ∈ s4BranchLabels := by
    intro s _hpath hdepth
    let inner := s4InnerPositions pattern
    let p := inner[s.depth]!
    have hmemOrdinary : inner[s.depth] ∈ inner.toList :=
      Array.getElem_mem_toList hdepth
    have hmem : p ∈ inner.toList := by
      dsimp [p]
      rw [getElem!_pos inner s.depth hdepth]
      exact hmemOrdinary
    have hp : p < 15 := by
      dsimp [p]
      have hdepth' : s.depth < (s3InnerPositions pattern).size := by
        simpa [inner, s4InnerPositions_eq_s3] using hdepth
      exact fifteenStage3InnerPosition_get_bound pattern hdepth'
    have hprofileTrue : profile ⟨p, hp⟩ = true := by
      apply (fifteenStage3ProfileWord_inner_iff profile ⟨p, hp⟩).mp
      simpa [pattern, inner, p, s4InnerPositions_eq_s3] using hmem
    have hradiusInner : radii ⟨p, hp⟩ < fifteenCandidateInnerThreshold :=
      (hprofile ⟨p, hp⟩).mp hprofileTrue
    have htargetLabel : target[p]! = labels4 ⟨p, hp⟩ := by
      change (fifteenStage4OwnerLabelArray labels4)[p]! = labels4 ⟨p, hp⟩
      exact fifteenStage4OwnerLabelArray_get labels4 p hp
    change target[p]! ∈ s4BranchLabels
    rw [htargetLabel]
    have hradialLabel : labels4 ⟨p, hp⟩ =
        fifteenStage4RadialOwner (radii ⟨p, hp⟩) := by
      simp [labels4, fifteenStage4RadialLabel, hradiusInner]
    rw [hradialLabel]
    exact fifteenStage4RadialOwner_mem_branchLabels _
  have hstruct : ∀ {s : S4State},
      FifteenStage4TargetPath pattern target s →
      s4StructurallyPruned (s4InnerPositions pattern) s = false := by
    intro s hpath
    apply Bool.eq_false_of_not_eq_true
    intro hpruned
    exact fifteenStage4TargetPath_structuralPrune_excluded_of_geometry
      radii labels hgeometry profile hprofile target hpath
      (by simpa [pattern] using hprojectedTarget) hpruned
  have hcycle : ∀ {s : S4State},
      FifteenStage4TargetPath pattern target s →
      ∀ edges, s4CycleValid s.labels edges = true → False := by
    intro s hpath edges hvalid
    exact fifteenStage4TargetPath_cycleLeaf_excluded radii labels4 howners4
      hgeometry.pairSum theta hsorted hthetaLo hthetaHi hsep profile houter4
      hpath edges hvalid
  have hroot : FifteenStage4TargetPath pattern target (s4Initial pattern) := .initial
  have hremaining : (s4Initial pattern).depth +
      (s4InnerPositions pattern).size = (s4InnerPositions pattern).size := by
    simp [s4Initial]
  exact s4CheckStream_targetPath_no_success pattern target cycles
    hallowed hstruct hcycle (s4InnerPositions pattern).size hroot hremaining
    stream [] (by simpa [pattern] using hstream)

/-- Every certificate-closed Stage 4 profile is impossible for a feasible
geometric owner assignment. This is the finite-certificate-to-geometry
handoff for all nineteen eliminated Stage 4 profiles. -/
theorem fifteenStage4ClosedPattern_excludes_geometric_profile
    (radii : Fin 15 → ℝ) (labels : Fin 15 → Nat)
    (hlabels : ∀ i, labels i = fifteenStage3RadialLabel (radii i))
    (hgeometry : FifteenStage3GeometricConditions radii labels)
    (profile : Fin 15 → Bool)
    (hprofile : ∀ i, profile i = true ↔
      radii i < fifteenCandidateInnerThreshold)
    (hnonneg : ∀ i, 0 ≤ radii i)
    (hclassification : ∀ i, radii i = fifteenCandidateOuterRadius ∨
      radii i < fifteenCandidateInnerThreshold)
    (theta : Fin 15 → ℝ)
    (hsorted : ∀ i j : Fin 15, i.1 < j.1 → theta i ≤ theta j)
    (hthetaLo : ∀ i, 0 ≤ theta i)
    (hthetaHi : ∀ i, theta i ≤ 2 * Real.pi)
    (hsep : ∀ i j : Fin 15, i ≠ j →
      4 ≤ pointNorm
        ((polarPoint (radii i) (theta i)).1 - (polarPoint (radii j) (theta j)).1,
         (polarPoint (radii i) (theta i)).2 - (polarPoint (radii j) (theta j)).2) ^ 2)
    (hclosed : fifteenStage0ProfileWord profile ∈ fifteenStage4CertifiedPatterns) :
    False := by
  let pattern := fifteenStage0ProfileWord profile
  obtain ⟨record, hrecordPattern, hrecordValid⟩ :=
    fifteenStage4CertifiedPattern_has_valid_record pattern (by
      simpa [pattern] using hclosed)
  have hstream : s4CheckStream (s4InnerPositions pattern).size
      (s4InnerPositions pattern) record.cycles (s4Initial pattern)
      record.stream.toList = some [] := by
    unfold s4RecordValid at hrecordValid
    rw [hrecordPattern] at hrecordValid
    cases hcheck : s4CheckStream (s4InnerPositions pattern).size
        (s4InnerPositions pattern) record.cycles (s4Initial pattern)
        record.stream.toList with
    | none => simp [hcheck] at hrecordValid
    | some suffix =>
        cases suffix with
        | nil => rfl
        | cons c rest => simp [hcheck] at hrecordValid
  exact fifteenStage4GeometricTargetPath_stream_no_success radii labels hlabels
    hgeometry profile hprofile hnonneg hclassification theta hsorted
    hthetaLo hthetaHi hsep record.cycles record.stream.toList hstream

end CirclePacking
