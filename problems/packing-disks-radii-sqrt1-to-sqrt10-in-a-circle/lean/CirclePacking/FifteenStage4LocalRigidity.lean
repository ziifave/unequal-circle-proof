import CirclePacking.FifteenStage4CoverageComplete
import CirclePacking.FifteenLocalAngleGeometry
import CirclePacking.FifteenCandidateBoxLocalBarrier
import CirclePacking.FifteenCandidateSmoothness
import CirclePacking.FifteenStageZeroAngleTransport

/-! The Stage 4 survivor's local box is placed into the five-sector angular
budget after one additional cyclic reindexing. This closes the arbitrary
dihedral phase gap for the local rigidity step. -/

namespace CirclePacking

private theorem s4CanonicalInnerPosition_iff (p : Nat) (hp : p < 15) :
    p ∈ fifteenInnerPositions "001001001001001" ↔ p % 3 = 2 := by
  interval_cases p <;> decide

theorem fifteenStage4CanonicalProfile_true_iff
    (G : FifteenStage4CoverageGeometry)
    (hword : fifteenStage0ProfileWord G.profile = "001001001001001")
    (i : Fin 15) : G.profile i = true ↔ i.val % 3 = 2 := by
  rw [← fifteenStage3ProfileWord_inner_iff G.profile i, hword]
  fin_cases i <;> decide

private theorem s4CoverageBox_radius_mem_local
    (G : FifteenStage4CoverageGeometry) (box : FifteenBox)
    (inner : List Nat) (hcontains : fifteenRealBoxContains box G.radii)
    (hinner : inner = fifteenInnerPositions "001001001001001")
    (hbounds : ∀ p ∈ inner,
      fifteenLocalLo ≤ box[p]!.1 ∧ box[p]!.2 ≤ fifteenLocalHi)
    (p : Nat) (hp : p ∈ inner) :
    G.radii ⟨p, by rw [hinner] at hp; exact fifteenInnerPositionsAux_lt 0 _ p hp⟩ ∈
      Set.Icc (42 / 25 : ℝ) (43 / 25) := by
  have hp15 : p < 15 := by
    rw [hinner] at hp
    exact fifteenInnerPositionsAux_lt 0 "001001001001001".toList p hp
  have hrad := hcontains ⟨p, hp15⟩
  change (box[p]!.1 : ℝ) ≤ G.radii ⟨p, hp15⟩ ∧
    G.radii ⟨p, hp15⟩ ≤ (box[p]!.2 : ℝ) at hrad
  have hboundsP := hbounds p hp
  have hlo : (42 : ℝ) / 25 ≤ (box[p]!.1 : ℝ) := by
    have hcast : (fifteenLocalLo : ℝ) ≤ (box[p]!.1 : ℝ) := by
      exact_mod_cast hboundsP.1
    calc
      (42 : ℝ) / 25 = (fifteenLocalLo : ℝ) := by
        norm_num [fifteenLocalLo, fifteenRational, Rat.normalize_eq_mkRat,
          Rat.cast_mkRat_of_ne_zero]
      _ ≤ (box[p]!.1 : ℝ) := hcast
  have hhi : (box[p]!.2 : ℝ) ≤ (43 : ℝ) / 25 := by
    have hcast : (box[p]!.2 : ℝ) ≤ (fifteenLocalHi : ℝ) := by
      exact_mod_cast hboundsP.2
    calc
      (box[p]!.2 : ℝ) ≤ (fifteenLocalHi : ℝ) := hcast
      _ = (43 : ℝ) / 25 := by
        norm_num [fifteenLocalHi, fifteenRational, Rat.normalize_eq_mkRat,
          Rat.cast_mkRat_of_ne_zero]
  exact ⟨le_trans hlo hrad.1, le_trans hrad.2 hhi⟩

/-- In the normalized Stage 4 geometry, the only certified local box forces
the five inner radii to the exact candidate value, even when its phase was
initially `2 mod 3`. The proof rotates the finite polar profile by two slots
and transports order and pairwise distances. -/
theorem fifteenStage4Coverage_local_rigidity
    (G : FifteenStage4CoverageGeometry) (box : FifteenBox) (inner : List Nat)
    (hword : fifteenStage0ProfileWord G.profile = "001001001001001")
    (hcontains : fifteenRealBoxContains box G.radii)
    (hinner : inner = fifteenInnerPositions "001001001001001")
    (hbounds : ∀ p ∈ inner,
      fifteenLocalLo ≤ box[p]!.1 ∧ box[p]!.2 ≤ fifteenLocalHi) :
    (G.radii ⟨2, by decide⟩ = fifteenCandidateInnerRadius ∧
     G.radii ⟨5, by decide⟩ = fifteenCandidateInnerRadius ∧
     G.radii ⟨8, by decide⟩ = fifteenCandidateInnerRadius ∧
     G.radii ⟨11, by decide⟩ = fifteenCandidateInnerRadius ∧
     G.radii ⟨14, by decide⟩ = fifteenCandidateInnerRadius) := by
  let shift : Fin 15 := 13
  let old : Fin 15 → Fin 15 := fun i => (finCycle shift).symm i
  let radii := fifteenStage0TransformProfile G.radii false shift
  let theta := fifteenStage0DihedralAngles G.theta false shift
  have hold : ∀ i : Fin 15,
      old i = ⟨(i.val + 2) % 15, by omega⟩ := by
    intro i
    fin_cases i <;> decide
  have hmod : ∀ i : Fin 15,
      ((old i).val % 3 = 2) ↔ i.val % 3 = 0 := by
    intro i
    rw [hold i]
    fin_cases i <;> norm_num
  have hprofile (i : Fin 15) : G.profile i = true ↔ i.val % 3 = 2 :=
    fifteenStage4CanonicalProfile_true_iff G hword i
  have hlocalAt (i : Fin 15) (hi : i.val % 3 = 0) :
      radii i ∈ Set.Icc (42 / 25 : ℝ) (43 / 25) := by
    have hsmall : G.profile (old i) = true := (hprofile (old i)).2
      ((hmod i).2 hi)
    have hmem : (old i).val ∈ inner := by
      rw [hinner]
      exact (s4CanonicalInnerPosition_iff (old i).val
        (by omega)).2 ((hmod i).2 hi)
    have hbox := s4CoverageBox_radius_mem_local G box inner hcontains
      hinner hbounds (old i).val hmem
    simpa [radii, fifteenStage0TransformProfile, old, shift,
      fifteenStage0DihedralPermutation] using hbox
  have houterAt (i : Fin 15) (hi : i.val % 3 ≠ 0) :
      radii i = fifteenCandidateOuterRadius := by
    have hfalse : G.profile (old i) ≠ true := by
      intro htrue
      have hmod' := (hprofile (old i)).mp htrue
      exact hi ((hmod i).mp hmod')
    change G.radii (old i) = fifteenCandidateOuterRadius
    rcases G.hclassification (old i) with hwall | hsmall
    · exact hwall
    · exact False.elim (hfalse ((G.hprofile (old i)).2 hsmall))
  let r₀ := radii 0
  let r₁ := radii 3
  let r₂ := radii 6
  let r₃ := radii 9
  let r₄ := radii 12
  have hR₀ : radii 0 = r₀ := rfl
  have hR₁ : radii 1 = fifteenCandidateOuterRadius := houterAt 1 (by decide)
  have hR₂ : radii 2 = fifteenCandidateOuterRadius := houterAt 2 (by decide)
  have hR₃ : radii 3 = r₁ := rfl
  have hR₄ : radii 4 = fifteenCandidateOuterRadius := houterAt 4 (by decide)
  have hR₅ : radii 5 = fifteenCandidateOuterRadius := houterAt 5 (by decide)
  have hR₆ : radii 6 = r₂ := rfl
  have hR₇ : radii 7 = fifteenCandidateOuterRadius := houterAt 7 (by decide)
  have hR₈ : radii 8 = fifteenCandidateOuterRadius := houterAt 8 (by decide)
  have hR₉ : radii 9 = r₃ := rfl
  have hR₁₀ : radii 10 = fifteenCandidateOuterRadius := houterAt 10 (by decide)
  have hR₁₁ : radii 11 = fifteenCandidateOuterRadius := houterAt 11 (by decide)
  have hR₁₂ : radii 12 = r₄ := rfl
  have hR₁₃ : radii 13 = fifteenCandidateOuterRadius := houterAt 13 (by decide)
  have hR₁₄ : radii 14 = fifteenCandidateOuterRadius := houterAt 14 (by decide)
  have hlocal₀ := hlocalAt 0 (by decide)
  have hlocal₁ := hlocalAt 3 (by decide)
  have hlocal₂ := hlocalAt 6 (by decide)
  have hlocal₃ := hlocalAt 9 (by decide)
  have hlocal₄ := hlocalAt 12 (by decide)
  have hangleInput : ∀ i, 0 ≤ G.theta i ∧ G.theta i ≤ 2 * Real.pi :=
    fun i => ⟨G.hthetaLo i, G.hthetaHi i⟩
  obtain ⟨horder, hrange⟩ := fifteenStage0DihedralAngles_ordered
    G.theta false shift G.hsorted hangleInput
  have hseparated : ∀ i j : Fin 15, i ≠ j →
      4 ≤ pointNorm
        ((polarPoint (radii i) (theta i)).1 -
          (polarPoint (radii j) (theta j)).1,
         (polarPoint (radii i) (theta i)).2 -
          (polarPoint (radii j) (theta j)).2) ^ 2 := by
    intro i j hij
    have hne : old i ≠ old j := by
      intro hEq
      apply hij
      exact (fifteenStage0DihedralPermutation false shift).symm.injective hEq
    have hdist := fifteenStage0DihedralAngles_distance_sq
      G.radii G.theta false shift i j
    change 4 ≤ pointNorm
      ((polarPoint (radii i) (theta i)).1 -
        (polarPoint (radii j) (theta j)).1,
       (polarPoint (radii i) (theta i)).2 -
        (polarPoint (radii j) (theta j)).2) ^ 2
    rw [hdist]
    exact G.hsep (old i) (old j) hne
  have hpositive : ∀ i : Fin 15, 0 < radii i := by
    intro i
    by_cases hi : i.val % 3 = 0
    · have h := (hlocalAt i hi).1
      have hpos : 0 < (42 : ℝ) / 25 := by norm_num
      linarith
    · rw [houterAt i hi]
      exact fifteenCandidateOuterRadius_pos
  have hbudget := fifteenOrderedPattern_packing_angle_budget
    radii theta r₀ r₁ r₂ r₃ r₄ fifteenCandidateOuterRadius
    hR₀ hR₁ hR₂ hR₃ hR₄ hR₅ hR₆ hR₇ hR₈ hR₉ hR₁₀ hR₁₁ hR₁₂ hR₁₃ hR₁₄
    horder (fun i => (hrange i).1) (fun i => (hrange i).2)
    hpositive hseparated
  have hDirectCont : ∀ dx dy : ℝ,
      |dx| ≤ (11 / 500 : ℝ) → |dy| ≤ (11 / 500 : ℝ) →
      ContDiffOn ℝ 2
        (fun t : ℝ => fifteenTouchAngle
          (fifteenCandidateInnerRadius + t * dx)
          (fifteenCandidateInnerRadius + t * dy))
        (Set.uIcc 0 1) := by
    intro dx dy hdx hdy
    exact fifteenCandidateDirectAngle_contDiffOn dx dy hdx hdy
  have hDetourCont : ∀ dx dy : ℝ,
      |dx| ≤ (11 / 500 : ℝ) → |dy| ≤ (11 / 500 : ℝ) →
      ContDiffOn ℝ 2
        (fun t : ℝ => fifteenDetourAngleAlongSegment
          fifteenCandidateOuterRadius fifteenCandidateInnerRadius
          fifteenCandidateInnerRadius dx dy t)
        (Set.uIcc 0 1) := by
    intro dx dy hdx hdy
    exact fifteenCandidateDetourAngle_contDiffOn dx dy hdx hdy
  have hrigid := fifteenCandidateLocalBarrier_rigidity_of_box
    r₀ r₁ r₂ r₃ r₄ hlocal₀ hlocal₁ hlocal₂ hlocal₃ hlocal₄
    hDirectCont hDetourCont hbudget
  exact ⟨hrigid.1, hrigid.2.1, hrigid.2.2.1,
    hrigid.2.2.2.1, hrigid.2.2.2.2⟩

/-- Apply the certificate-to-geometry coverage theorem and the local barrier
to an arbitrary unit-disk packing. The five exact candidate radii are now
available in the Stage 0 normalized slots, regardless of dihedral phase. -/
theorem fifteen_unit_packing_stage4_local_rigidity
    {R : ℝ} (P : Packing 15 R)
    (hunit : ∀ i, (P.circles i).radius = 1)
    (hR : R ≤ fifteenCandidateOuterRadius + 1) :
    ∃ reflected : Bool, ∃ shift : Fin 15,
      ∃ geometry : FifteenStage4CoverageGeometry,
        geometry.radii = fifteenStage0TransformProfile
          (fifteenPackingSortedRadius (fifteen_unit_packing_wall_push P hunit hR))
          reflected shift ∧
        geometry.theta = fifteenStage0DihedralAngles
          (fifteenPackingSortedAngle (fifteen_unit_packing_wall_push P hunit hR))
          reflected shift ∧
        fifteenStage0ProfileWord geometry.profile = "001001001001001" ∧
        geometry.radii ⟨2, by decide⟩ = fifteenCandidateInnerRadius ∧
        geometry.radii ⟨5, by decide⟩ = fifteenCandidateInnerRadius ∧
        geometry.radii ⟨8, by decide⟩ = fifteenCandidateInnerRadius ∧
        geometry.radii ⟨11, by decide⟩ = fifteenCandidateInnerRadius ∧
        geometry.radii ⟨14, by decide⟩ = fifteenCandidateInnerRadius := by
  obtain ⟨reflected, shift, geometry, hradii, htheta, hprofile,
      hcanonical, box, inner, hcontains, hinner, hbounds⟩ :=
    fifteen_unit_packing_stage4_coverage_local P hunit hR
  have hword : fifteenStage0ProfileWord geometry.profile =
      "001001001001001" := by
    simpa [hprofile] using hcanonical
  have hcontains' : fifteenRealBoxContains box geometry.radii := by
    simpa [hradii] using hcontains
  have hrigid := fifteenStage4Coverage_local_rigidity geometry box inner
    hword hcontains' hinner hbounds
  exact ⟨reflected, shift, geometry, hradii, htheta, hword, hrigid⟩

end CirclePacking
