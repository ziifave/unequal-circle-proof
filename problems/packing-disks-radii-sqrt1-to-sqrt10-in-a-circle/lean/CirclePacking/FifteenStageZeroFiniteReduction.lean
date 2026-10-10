import CirclePacking.FifteenStageZeroCanonicalGeometry
import CirclePacking.FifteenStageZeroLabelCoverage

/-! The complete geometric Stage 0 reduction from 760 canonical patterns
to the 378 recorded survivors. Enumeration coverage and per-assignment cycle
soundness are connected here; Stage 3/4 and the refined boxes remain separate. -/

namespace CirclePacking

theorem fifteenStage0RadialTypeIndex_nonzero_iff (r : ℝ) :
    (fifteenStage0RadialTypeIndex r).val ≠ 0 ↔
      r < fifteenCandidateInnerThreshold := by
  classical
  by_cases hinner : r < fifteenCandidateInnerThreshold
  · have hpositive := (fifteenStage0RadialType_valid r).1
    simp [fifteenStage0RadialTypeIndex, hinner]
    omega
  · simp [fifteenStage0RadialTypeIndex, hinner]

/-- The population restrictions are retained with their exact labels after
the same dihedral permutation used to canonicalize the binary pattern. -/
theorem fifteen_unit_packing_wall_push_stage0_dihedral_label_counts
    {R : ℝ} (P : Packing 15 R)
    (hunit : ∀ i, (P.circles i).radius = 1)
    (hR : R ≤ fifteenCandidateOuterRadius + 1)
    (reflected : Bool) (shift : Fin 15) :
    let Q := fifteen_unit_packing_wall_push P hunit hR
    let labels := fifteenStage0TransformProfile
      (fun i => fifteenStage0RadialTypeIndex (fifteenPackingSortedRadius Q i))
      reflected shift
    (Finset.univ.filter fun i : Fin 15 => (labels i).val = 1).card ≤ 1 ∧
    (Finset.univ.filter fun i : Fin 15 => (labels i).val = 3).card ≥
      (Finset.univ.filter fun i : Fin 15 => (labels i).val ≠ 0).card - 4 := by
  classical
  dsimp only
  let Q := fifteen_unit_packing_wall_push P hunit hR
  let inner : Finset (Fin 15) := Finset.univ.filter fun i =>
    fifteenPackingSortedRadius Q i < fifteenCandidateInnerThreshold
  let original := fun i => fifteenStage0RadialTypeIndex (fifteenPackingSortedRadius Q i)
  have hunitQ := fifteen_unit_packing_wall_push_preserves_unit_radii P hunit hR
  have hassign := fifteenStage0_radial_type_assignment_counts Q hunitQ inner
  have hones : (Finset.univ.filter fun i : Fin 15 => (original i).val = 1) =
      inner.filter (fun i => fifteenStage0RadialType (fifteenPackingSortedRadius Q i) = 1) := by
    ext i
    by_cases hinner : fifteenPackingSortedRadius Q i < fifteenCandidateInnerThreshold <;>
      simp [original, inner, fifteenStage0RadialTypeIndex, hinner]
  have hthrees : (Finset.univ.filter fun i : Fin 15 => (original i).val = 3) =
      inner.filter (fun i => fifteenStage0RadialType (fifteenPackingSortedRadius Q i) = 3) := by
    ext i
    by_cases hinner : fifteenPackingSortedRadius Q i < fifteenCandidateInnerThreshold <;>
      simp [original, inner, fifteenStage0RadialTypeIndex, hinner]
  have hnonzero : (Finset.univ.filter fun i : Fin 15 => (original i).val ≠ 0) = inner := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, original, inner]
    exact fifteenStage0RadialTypeIndex_nonzero_iff _
  have honeTransport := fifteenStage0TransformProfile_population original
    (fun label : Fin 4 => label.val = 1) reflected shift
  have hthreeTransport := fifteenStage0TransformProfile_population original
    (fun label : Fin 4 => label.val = 3) reflected shift
  have hinnerTransport := fifteenStage0TransformProfile_population original
    (fun label : Fin 4 => label.val ≠ 0) reflected shift
  change (Finset.univ.filter fun i : Fin 15 =>
      (fifteenStage0TransformProfile original reflected shift i).val = 1).card ≤ 1 ∧
    (Finset.univ.filter fun i : Fin 15 =>
      (fifteenStage0TransformProfile original reflected shift i).val = 3).card ≥
    (Finset.univ.filter fun i : Fin 15 =>
      (fifteenStage0TransformProfile original reflected shift i).val ≠ 0).card - 4
  rw [honeTransport, hthreeTransport, hinnerTransport, hones, hthrees, hnonzero]
  exact hassign

/-- A feasible ordered polar profile satisfying the assignment restrictions
cannot lie on any of the 382 excluded canonical patterns. -/
theorem fifteenStage0PolarProfile_survives
    (radii theta : Fin 15 → ℝ) (labels : Fin 15 → Fin 4)
    (hpattern : fifteenStage0LabelProfileWord labels ∈ fifteenStage0OrbitWords)
    (hone : (Finset.univ.filter fun i : Fin 15 => (labels i).val = 1).card ≤ 1)
    (hthree : (Finset.univ.filter fun i : Fin 15 => (labels i).val = 3).card ≥
      (Finset.univ.filter fun i : Fin 15 => (labels i).val ≠ 0).card - 4)
    (hboxes : ∀ i, ((fifteenStage0CoarseTypeBox (labels i)).1 : ℝ) ≤ radii i ∧
      radii i ≤ ((fifteenStage0CoarseTypeBox (labels i)).2 : ℝ))
    (hsorted : ∀ i j : Fin 15, i.val < j.val → theta i ≤ theta j)
    (hrange : ∀ i, 0 ≤ theta i ∧ theta i ≤ 2 * Real.pi)
    (hsep : ∀ i j : Fin 15, i ≠ j →
      4 ≤ pointNorm
        ((polarPoint (radii i) (theta i)).1 - (polarPoint (radii j) (theta j)).1,
         (polarPoint (radii i) (theta i)).2 - (polarPoint (radii j) (theta j)).2) ^ 2) :
    fifteenStage0LabelProfileWord labels ∈ fifteenStage0SurvivorPatterns := by
  rcases fifteenStage0LabelProfile_covered labels hpattern hone hthree with
    hsurvivor | ⟨witness, hwitness, _, hlabels⟩
  · exact hsurvivor
  · exfalso
    apply fifteenStage0PolarProfile_excludes_cycle_witness radii theta
      hsorted hrange hsep witness hwitness
    intro i
    rw [hlabels i]
    exact hboxes i

set_option maxHeartbeats 800000 in
/-- An arbitrary feasible candidate-radius packing belongs, after canonical
dihedral normalization, to one of the 378 checked Stage 0 survivor patterns.
The conclusion retains the actual ordered polar profile and its radius boxes. -/
theorem fifteen_unit_packing_wall_push_stage0_survivor_geometry
    {R : ℝ} (P : Packing 15 R)
    (hunit : ∀ i, (P.circles i).radius = 1)
    (hR : R ≤ fifteenCandidateOuterRadius + 1) :
    let Q := fifteen_unit_packing_wall_push P hunit hR
    let originalRadii := fifteenPackingSortedRadius Q
    let originalInner := fun i : Fin 15 =>
      decide (originalRadii i < fifteenCandidateInnerThreshold)
    ∃ reflected : Bool, ∃ shift : Fin 15,
      let radii := fifteenStage0TransformProfile originalRadii reflected shift
      let theta := fifteenStage0DihedralAngles (fifteenPackingSortedAngle Q) reflected shift
      let labels := fifteenStage0TransformProfile
        (fun i => fifteenStage0RadialTypeIndex (originalRadii i)) reflected shift
      let inner := fun i : Fin 15 => decide (radii i < fifteenCandidateInnerThreshold)
      fifteenStage0ProfileMask inner =
        fifteenStage0CanonicalMask (fifteenStage0ProfileMask originalInner) ∧
      fifteenStage0ProfileWord inner ∈ fifteenStage0SurvivorPatterns ∧
      (∀ i, ((fifteenStage0CoarseTypeBox (labels i)).1 : ℝ) ≤ radii i ∧
        radii i ≤ ((fifteenStage0CoarseTypeBox (labels i)).2 : ℝ)) ∧
      (∀ i j : Fin 15, i.val < j.val → theta i ≤ theta j) ∧
      (∀ i, 0 ≤ theta i ∧ theta i ≤ 2 * Real.pi) ∧
      (∀ i j : Fin 15, i ≠ j →
        4 ≤ pointNorm
          ((polarPoint (radii i) (theta i)).1 - (polarPoint (radii j) (theta j)).1,
           (polarPoint (radii i) (theta i)).2 - (polarPoint (radii j) (theta j)).2) ^ 2) := by
  classical
  dsimp only
  obtain ⟨reflected, shift, hmask, hpattern, _, _, hboxes, hsorted, hrange, hsep, _⟩ :=
    fifteen_unit_packing_wall_push_stage0_canonical_geometry P hunit hR
  let Q := fifteen_unit_packing_wall_push P hunit hR
  let radii := fifteenStage0TransformProfile (fifteenPackingSortedRadius Q) reflected shift
  let labels := fifteenStage0TransformProfile
    (fun i => fifteenStage0RadialTypeIndex (fifteenPackingSortedRadius Q i)) reflected shift
  let inner := fun i : Fin 15 => decide (radii i < fifteenCandidateInnerThreshold)
  have hprofile : (fun i : Fin 15 => (labels i).val != 0) = inner := by
    funext i
    apply Bool.eq_iff_iff.mpr
    simp only [bne_iff_ne, inner, decide_eq_true_eq]
    exact fifteenStage0RadialTypeIndex_nonzero_iff _
  have hword : fifteenStage0LabelProfileWord labels = fifteenStage0ProfileWord inner := by
    rw [fifteenStage0LabelProfileWord, hprofile]
  have hcounts := fifteen_unit_packing_wall_push_stage0_dihedral_label_counts
    P hunit hR reflected shift
  have hsurvives := fifteenStage0PolarProfile_survives radii
    (fifteenStage0DihedralAngles (fifteenPackingSortedAngle Q) reflected shift)
    labels (hword.symm ▸ hpattern) hcounts.1 hcounts.2 hboxes hsorted hrange hsep
  refine ⟨reflected, shift, hmask, ?_, hboxes, hsorted, hrange, hsep⟩
  exact hword ▸ hsurvives

end CirclePacking
