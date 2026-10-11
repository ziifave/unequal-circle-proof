import CirclePacking.FifteenStageZeroFiniteReduction
import CirclePacking.FifteenStage3StructuralSoundness

/-! The real profiles reaching Stage 3: the same dihedral normalization
which survived Stage 0 also supplies half-open Stage 3 owners and all
structural population restrictions.  Stage 3 stream soundness is still a
separate obligation, so this is not a 378-to-23 reduction theorem. -/

namespace CirclePacking

/-- Conditions extracted from an actual packing, independent of any
certificate stream.  Counts refer to the complete actual inner-center set. -/
structure FifteenStage3GeometricConditions
    (radii : Fin 15 → ℝ) (labels : Fin 15 → Nat) : Prop where
  owners : ∀ i, fifteenStage3OwnerSpec (labels i) (radii i)
  pairSum : ∀ i j, i ≠ j → 2 ≤ radii i + radii j
  smallCount : ((Finset.univ.filter fun i : Fin 15 =>
      radii i < fifteenCandidateInnerThreshold).filter fun i =>
        labels i ≤ 1 ∨ labels i = 9).card ≤ 1
  highCount : (Finset.univ.filter fun i : Fin 15 =>
      radii i < fifteenCandidateInnerThreshold).card - 4 ≤
    ((Finset.univ.filter fun i : Fin 15 =>
      radii i < fifteenCandidateInnerThreshold).filter fun i =>
        5 ≤ labels i ∧ labels i ≤ 6).card
  high2Count : (Finset.univ.filter fun i : Fin 15 =>
      radii i < fifteenCandidateInnerThreshold).card - 5 ≤
    ((Finset.univ.filter fun i : Fin 15 =>
      radii i < fifteenCandidateInnerThreshold).filter fun i => labels i = 6).card

theorem fifteen_unit_packing_wall_push_stage3_geometric_conditions
    {R : ℝ} (P : Packing 15 R)
    (hunit : ∀ i, (P.circles i).radius = 1)
    (hR : R ≤ fifteenCandidateOuterRadius + 1) (reflected : Bool) (shift : Fin 15) :
    let Q := fifteen_unit_packing_wall_push P hunit hR
    let radii := fifteenStage0TransformProfile (fifteenPackingSortedRadius Q) reflected shift
    FifteenStage3GeometricConditions radii (fun i => fifteenStage3RadialLabel (radii i)) := by
  rcases fifteen_unit_packing_wall_push_stage3_structural_profile P hunit hR reflected shift with
    ⟨howners, hsum, hsmall, hhigh, hhigh2⟩
  exact ⟨howners, hsum, hsmall, hhigh, hhigh2⟩

/-- Every arbitrary feasible candidate-radius packing reaches Stage 3 on
one of the 378 surviving words, with the actual ordered, separated polar
profile and all structural leaf hypotheses attached to that same profile. -/
theorem fifteen_unit_packing_wall_push_stage3_geometric_handoff
    {R : ℝ} (P : Packing 15 R)
    (hunit : ∀ i, (P.circles i).radius = 1)
    (hR : R ≤ fifteenCandidateOuterRadius + 1) :
    let Q := fifteen_unit_packing_wall_push P hunit hR
    ∃ reflected : Bool, ∃ shift : Fin 15,
      let radii := fifteenStage0TransformProfile (fifteenPackingSortedRadius Q) reflected shift
      let theta := fifteenStage0DihedralAngles (fifteenPackingSortedAngle Q) reflected shift
      let labels := fun i => fifteenStage3RadialLabel (radii i)
      let inner := fun i : Fin 15 => decide (radii i < fifteenCandidateInnerThreshold)
      fifteenStage0ProfileWord inner ∈ fifteenStage0SurvivorPatterns ∧
      FifteenStage3GeometricConditions radii labels ∧
      (∀ i j : Fin 15, i.val < j.val → theta i ≤ theta j) ∧
      (∀ i, 0 ≤ theta i ∧ theta i ≤ 2 * Real.pi) ∧
      (∀ i j : Fin 15, i ≠ j →
        4 ≤ pointNorm
          ((polarPoint (radii i) (theta i)).1 - (polarPoint (radii j) (theta j)).1,
           (polarPoint (radii i) (theta i)).2 - (polarPoint (radii j) (theta j)).2) ^ 2) := by
  dsimp only
  obtain ⟨reflected, shift, _, hsurvivor, _, hsorted, hrange, hsep⟩ :=
    fifteen_unit_packing_wall_push_stage0_survivor_geometry P hunit hR
  exact ⟨reflected, shift, hsurvivor,
    fifteen_unit_packing_wall_push_stage3_geometric_conditions P hunit hR reflected shift,
    hsorted, hrange, hsep⟩

end CirclePacking
