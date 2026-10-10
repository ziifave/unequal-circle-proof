import CirclePacking.FifteenStageZeroHandoff
import CirclePacking.FifteenStageZeroMaskTransport
import CirclePacking.FifteenStageZeroAngleTransport

/-! Packing-to-certificate handoff after explicit dihedral normalization.
The normalized real angles and radius labels have exactly the canonical
binary mask, preserve separation, and satisfy the coarse graph constraints.
This supplies geometric data; matching all data to the finite exclusion or
survivor records remains a separate coverage obligation. -/

namespace CirclePacking

/-- A checked negative-cycle witness cannot be realized by any ordered real
angle potential satisfying its coarse pair constraints. This interface also
applies after a dihedral change of the first center. -/
theorem fifteenStage0Angles_exclude_cycle_witness
    (theta : Fin 15 → ℝ) (witness : FifteenStage0CycleWitness)
    (hwitness : witness ∈ fifteenStage0NegativeCycleWitnesses)
    (hsorted : ∀ i j : Fin 15, i.val < j.val → theta i ≤ theta j)
    (hpairs : ∀ i j : Fin 15, i.val < j.val →
      2800 * (theta i - theta j) ≤
        -(fifteenStage0CoarseQ (fifteenStage0CycleWitnessLabel witness i)
          (fifteenStage0CycleWitnessLabel witness j) : ℝ) ∧
      2800 * (theta j - theta i) ≤ 17600 -
        (fifteenStage0CoarseQ (fifteenStage0CycleWitnessLabel witness i)
          (fifteenStage0CycleWitnessLabel witness j) : ℝ)) :
    False := by
  have hshape := fifteenStage0NegativeCycleWitnesses_shape_certified
    witness hwitness
  let potential : Nat → ℝ := fun n =>
    2800 * theta
      ⟨n % 15, Nat.mod_lt n (by omega)⟩
  apply fifteenStage0NegativeCycleWitness_no_real_potential
    witness hwitness potential
  intro edge hedge
  have hmem : edge ∈ witness.steps.map
      (fifteenStage0CycleWitnessStepEdge witness) := by
    simpa [fifteenStage0CycleWitnessEdges] using hedge
  obtain ⟨step, hstep, hstepEdge⟩ := List.mem_map.mp hmem
  subst edge
  have hstepShape := hshape.1 step hstep
  rcases hstepShape with ⟨hsourceLt, htargetLt, hkind⟩
  let source : Fin 15 := ⟨step.1, hsourceLt⟩
  let target : Fin 15 := ⟨step.2.1, htargetLt⟩
  have hpotentialSource : potential step.1 =
      2800 * theta source := by
    simp [potential, source, Nat.mod_eq_of_lt hsourceLt]
  have hpotentialTarget : potential step.2.1 =
      2800 * theta target := by
    simp [potential, target, Nat.mod_eq_of_lt htargetLt]
  change potential step.2.1 ≤ potential step.1 +
    ((fifteenStage0CycleWitnessStepEdge witness step).weight : ℝ)
  rcases hkind with ⟨horder, hsuccessor, _⟩ |
      ⟨hlower, hdescending⟩ | ⟨hupper, hascending⟩
  · have hangle := hsorted target source (by
      dsimp [target, source]
      omega)
    have hweight :
        (fifteenStage0CycleWitnessStepEdge witness step).weight = 0 := by
      simp [fifteenStage0CycleWitnessStepEdge,
        fifteenStage0StepGraphEdge, fifteenStage0EdgeWeight, horder]
    rw [hpotentialTarget, hpotentialSource, hweight]
    have hscaled := mul_le_mul_of_nonneg_left hangle
      (by norm_num : (0 : ℝ) ≤ 2800)
    simpa using hscaled
  · have hpair := hpairs target source (by
        dsimp [target, source]
        omega)
    have hweight :
        (fifteenStage0CycleWitnessStepEdge witness step).weight =
          -(Int.ofNat (fifteenStage0CoarseQ
            (fifteenStage0CycleWitnessLabel witness target)
            (fifteenStage0CycleWitnessLabel witness source))) := by
      simp [fifteenStage0CycleWitnessStepEdge,
        fifteenStage0StepGraphEdge, fifteenStage0EdgeWeight,
        fifteenStage0CycleWitnessLabel, source, target, hlower]
    have hweightReal :
        ((fifteenStage0CycleWitnessStepEdge witness step).weight : ℝ) =
          -(fifteenStage0CoarseQ
            (fifteenStage0CycleWitnessLabel witness target)
            (fifteenStage0CycleWitnessLabel witness source) : ℝ) := by
      rw [hweight]
      simp
    rw [hpotentialTarget, hpotentialSource, hweightReal]
    nlinarith [hpair.1]
  · have hpair := hpairs source target (by
        dsimp [target, source]
        omega)
    let q := fifteenStage0CoarseQ
      (fifteenStage0CycleWitnessLabel witness source)
      (fifteenStage0CycleWitnessLabel witness target)
    have hqle : q ≤ 17600 := by
      dsimp [q, fifteenStage0CoarseQ]
      split_ifs <;> omega
    have hweight :
        (fifteenStage0CycleWitnessStepEdge witness step).weight =
          Int.ofNat (17600 - q) := by
      simp [fifteenStage0CycleWitnessStepEdge,
        fifteenStage0StepGraphEdge, fifteenStage0EdgeWeight,
        fifteenStage0CycleWitnessLabel, fifteenStage0TwoPiUpper,
        source, target, hupper, q]
    have hcastSub : ((17600 - q : ℕ) : ℝ) =
        (17600 : ℝ) - q := by
      exact Nat.cast_sub hqle
    have hweightReal :
        ((fifteenStage0CycleWitnessStepEdge witness step).weight : ℝ) =
          (17600 : ℝ) - q := by
      rw [hweight]
      exact hcastSub
    rw [hpotentialTarget, hpotentialSource, hweightReal]
    linarith [hpair.2]


/-- The coarse table applies to any ordered polar profile, including one
whose first center was changed by a cyclic rotation or reflection. -/
theorem fifteenStage0PolarProfile_pair_angle_gaps
    (radii theta : Fin 15 → ℝ)
    (hsorted : ∀ i j : Fin 15, i.val < j.val → theta i ≤ theta j)
    (hrange : ∀ i, 0 ≤ theta i ∧ theta i ≤ 2 * Real.pi)
    (hsep : ∀ i j : Fin 15, i ≠ j →
      4 ≤ pointNorm
        ((polarPoint (radii i) (theta i)).1 - (polarPoint (radii j) (theta j)).1,
         (polarPoint (radii i) (theta i)).2 - (polarPoint (radii j) (theta j)).2) ^ 2)
    (typeI typeJ : Fin 4) (i j : Fin 15) (hij : i.val < j.val)
    (hri : ((fifteenStage0CoarseTypeBox typeI).1 : ℝ) ≤ radii i ∧
      radii i ≤ ((fifteenStage0CoarseTypeBox typeI).2 : ℝ))
    (hrj : ((fifteenStage0CoarseTypeBox typeJ).1 : ℝ) ≤ radii j ∧
      radii j ≤ ((fifteenStage0CoarseTypeBox typeJ).2 : ℝ)) :
    (fifteenStage0CoarseAngleTick typeI typeJ : ℝ) / 2800 ≤ theta j - theta i ∧
      theta j - theta i ≤ (17600 : ℝ) / 2800 -
        (fifteenStage0CoarseAngleTick typeI typeJ : ℝ) / 2800 := by
  by_cases hzero : fifteenStage0CoarseAngleTick typeI typeJ = 0
  · have hspan : theta j - theta i ≤ 2 * Real.pi := by
      linarith [(hrange j).2, (hrange i).1]
    constructor
    · simpa [hzero] using sub_nonneg.mpr (hsorted i j hij)
    · simpa [hzero] using hspan.trans fifteen_two_pi_le_stage0_tau
  · have hpositive := Nat.pos_of_ne_zero hzero
    have hreversePositive : 0 < fifteenStage0CoarseAngleTick typeJ typeI := by
      rw [fifteenStage0CoarseAngleTick_symmetric]
      exact hpositive
    have hne : i ≠ j := by intro h; subst j; omega
    let forward : FifteenAngularEdge :=
      ⟨i, j, (fifteenStage0CoarseAngleTick typeI typeJ : ℝ) / 2800⟩
    let backward : FifteenAngularEdge :=
      ⟨j, i, (fifteenStage0CoarseAngleTick typeJ typeI : ℝ) / 2800⟩
    have hf := fifteenStage0CoarsePair_gives_polar_edge_bound
      typeI typeJ hpositive forward theta (radii i) (radii j)
      ((17600 : ℝ) / 2800) hri.1 hri.2 hrj.1 hrj.2 rfl hne
      hsorted (fun k => (hrange k).1) (fun k => (hrange k).2)
      (hsep i j hne) fifteen_two_pi_le_stage0_tau
    have hb := fifteenStage0CoarsePair_gives_polar_edge_bound
      typeJ typeI hreversePositive backward theta (radii j) (radii i)
      ((17600 : ℝ) / 2800) hrj.1 hrj.2 hri.1 hri.2 rfl hne.symm
      hsorted (fun k => (hrange k).1) (fun k => (hrange k).2)
      (hsep j i hne.symm) fifteen_two_pi_le_stage0_tau
    have hf' : theta j - theta i ≤ (17600 : ℝ) / 2800 -
        (fifteenStage0CoarseAngleTick typeI typeJ : ℝ) / 2800 := by
      simpa [forward, fifteenAngularEdgeUpper, hij] using hf
    have hb' : theta i - theta j ≤
        -((fifteenStage0CoarseAngleTick typeI typeJ : ℝ) / 2800) := by
      have hnot : ¬ j.val < i.val := by omega
      simpa [backward, fifteenAngularEdgeUpper, hnot,
        fifteenStage0CoarseAngleTick_symmetric] using hb
    exact ⟨by linarith, hf'⟩

/-- A separated normalized profile cannot occupy the labelled boxes of a
checked Stage 0 negative-cycle witness. The proof checks the recorded cycle;
it does not search for a new one. -/
theorem fifteenStage0PolarProfile_excludes_cycle_witness
    (radii theta : Fin 15 → ℝ)
    (hsorted : ∀ i j : Fin 15, i.val < j.val → theta i ≤ theta j)
    (hrange : ∀ i, 0 ≤ theta i ∧ theta i ≤ 2 * Real.pi)
    (hsep : ∀ i j : Fin 15, i ≠ j →
      4 ≤ pointNorm
        ((polarPoint (radii i) (theta i)).1 - (polarPoint (radii j) (theta j)).1,
         (polarPoint (radii i) (theta i)).2 - (polarPoint (radii j) (theta j)).2) ^ 2)
    (witness : FifteenStage0CycleWitness)
    (hwitness : witness ∈ fifteenStage0NegativeCycleWitnesses)
    (hboxes : ∀ i : Fin 15,
      ((fifteenStage0CoarseTypeBox (fifteenStage0CycleWitnessTypeIndex witness i)).1 : ℝ) ≤
          radii i ∧
      radii i ≤
        ((fifteenStage0CoarseTypeBox (fifteenStage0CycleWitnessTypeIndex witness i)).2 : ℝ)) :
    False := by
  have hshape := fifteenStage0NegativeCycleWitnesses_shape_certified witness hwitness
  apply fifteenStage0Angles_exclude_cycle_witness theta witness hwitness hsorted
  intro i j hij
  have hi : (fifteenStage0CycleWitnessTypeIndex witness i).val =
      fifteenStage0CycleWitnessLabel witness i := by
    simp [fifteenStage0CycleWitnessTypeIndex, Nat.mod_eq_of_lt (hshape.2 i)]
  have hj : (fifteenStage0CycleWitnessTypeIndex witness j).val =
      fifteenStage0CycleWitnessLabel witness j := by
    simp [fifteenStage0CycleWitnessTypeIndex, Nat.mod_eq_of_lt (hshape.2 j)]
  have hgap := fifteenStage0PolarProfile_pair_angle_gaps radii theta
    hsorted hrange hsep (fifteenStage0CycleWitnessTypeIndex witness i)
    (fifteenStage0CycleWitnessTypeIndex witness j) i j hij (hboxes i) (hboxes j)
  have hq : fifteenStage0CoarseAngleTick
      (fifteenStage0CycleWitnessTypeIndex witness i)
      (fifteenStage0CycleWitnessTypeIndex witness j) =
      fifteenStage0CoarseQ (fifteenStage0CycleWitnessLabel witness i)
        (fifteenStage0CycleWitnessLabel witness j) := by
    simp only [fifteenStage0CoarseAngleTick, hi, hj]
  rw [hq] at hgap
  constructor <;> nlinarith [hgap.1, hgap.2]

set_option maxHeartbeats 800000 in
/-- Every candidate-radius unit packing has a normalized real polar profile
with exactly the enumerator's canonical word, valid coarse radius boxes, and
the integer-scaled difference bounds needed by its cycle certificates. -/
theorem fifteen_unit_packing_wall_push_stage0_canonical_geometry
    {R : ℝ} (P : Packing 15 R)
    (hunit : ∀ i, (P.circles i).radius = 1)
    (hR : R ≤ fifteenCandidateOuterRadius + 1) :
    let Q := fifteen_unit_packing_wall_push P hunit hR
    let originalRadii := fifteenPackingSortedRadius Q
    let originalTheta := fifteenPackingSortedAngle Q
    let originalInner := fun i : Fin 15 =>
      decide (originalRadii i < fifteenCandidateInnerThreshold)
    ∃ reflected : Bool, ∃ shift : Fin 15,
      let radii := fifteenStage0TransformProfile originalRadii reflected shift
      let theta := fifteenStage0DihedralAngles originalTheta reflected shift
      let labels := fifteenStage0TransformProfile
        (fun i => fifteenStage0RadialTypeIndex (originalRadii i)) reflected shift
      let inner := fun i : Fin 15 => decide (radii i < fifteenCandidateInnerThreshold)
      fifteenStage0ProfileMask inner =
        fifteenStage0CanonicalMask (fifteenStage0ProfileMask originalInner) ∧
      fifteenStage0ProfileWord inner ∈ fifteenStage0OrbitWords ∧
      5 ≤ (Finset.univ.filter fun i => radii i < fifteenCandidateInnerThreshold).card ∧
      (Finset.univ.filter fun i => radii i < fifteenCandidateInnerThreshold).card ≤ 8 ∧
      (∀ i, ((fifteenStage0CoarseTypeBox (labels i)).1 : ℝ) ≤ radii i ∧
        radii i ≤ ((fifteenStage0CoarseTypeBox (labels i)).2 : ℝ)) ∧
      (∀ i j : Fin 15, i.val < j.val → theta i ≤ theta j) ∧
      (∀ i, 0 ≤ theta i ∧ theta i ≤ 2 * Real.pi) ∧
      (∀ i j : Fin 15, i ≠ j →
        4 ≤ pointNorm
          ((polarPoint (radii i) (theta i)).1 - (polarPoint (radii j) (theta j)).1,
           (polarPoint (radii i) (theta i)).2 - (polarPoint (radii j) (theta j)).2) ^ 2) ∧
      (∀ i j : Fin 15, i.val < j.val →
        2800 * (theta i - theta j) ≤
            -(fifteenStage0CoarseAngleTick (labels i) (labels j) : ℝ) ∧
          2800 * (theta j - theta i) ≤ 17600 -
            (fifteenStage0CoarseAngleTick (labels i) (labels j) : ℝ)) := by
  classical
  dsimp only
  let Q := fifteen_unit_packing_wall_push P hunit hR
  let originalInner := fun i : Fin 15 =>
    decide (fifteenPackingSortedRadius Q i < fifteenCandidateInnerThreshold)
  obtain ⟨reflected, shift, hmask⟩ := fifteenStage0Profile_canonical_dihedral originalInner
  let radii := fifteenStage0TransformProfile (fifteenPackingSortedRadius Q) reflected shift
  let theta := fifteenStage0DihedralAngles (fifteenPackingSortedAngle Q) reflected shift
  let labels := fifteenStage0TransformProfile
    (fun i => fifteenStage0RadialTypeIndex (fifteenPackingSortedRadius Q i)) reflected shift
  let inner := fun i : Fin 15 => decide (radii i < fifteenCandidateInnerThreshold)
  have hmask' : fifteenStage0ProfileMask inner =
      fifteenStage0CanonicalMask (fifteenStage0ProfileMask originalInner) := by
    have hinner : inner = fifteenStage0TransformProfile originalInner reflected shift := by
      funext i
      rfl
    rw [hinner]
    exact hmask
  have hword : fifteenStage0ProfileWord inner ∈ fifteenStage0OrbitWords := by
    have hcanonical : fifteenStage0CanonicalProfileWord originalInner ∈
        fifteenStage0OrbitWords :=
      fifteen_unit_packing_wall_push_stage0_canonical_pattern P hunit hR
    have hwordEq := fifteenStage0ProfileWord_eq_canonical_of_mask originalInner inner hmask'
    exact hwordEq.symm ▸ hcanonical
  have hprofile := fifteen_unit_packing_wall_push_stage0_dihedral_profile
    P hunit hR reflected shift
  dsimp only at hprofile
  have horder := fifteenStage0DihedralAngles_ordered (fifteenPackingSortedAngle Q)
    reflected shift (fun i j hij => fifteenPackingSortedAngle_monotone Q hij)
    (fifteenPackingSortedAngle_range Q)
  have hQunit : ∀ i, (Q.circles i).radius = 1 :=
    fifteen_unit_packing_wall_push_preserves_unit_radii P hunit hR
  have hsep : ∀ i j : Fin 15, i ≠ j →
      4 ≤ pointNorm
        ((polarPoint (radii i) (theta i)).1 - (polarPoint (radii j) (theta j)).1,
         (polarPoint (radii i) (theta i)).2 - (polarPoint (radii j) (theta j)).2) ^ 2 := by
    intro i j hij
    rw [fifteenStage0DihedralAngles_distance_sq]
    apply fifteen_unit_packing_sorted_pair_separated Q hQunit
    exact (fifteenStage0DihedralPermutation reflected shift).symm.injective.ne hij
  refine ⟨reflected, shift, hmask', hword, hprofile.1, hprofile.2.1,
    hprofile.2.2, horder.1, horder.2, hsep, ?_⟩
  intro i j hij
  have hgap := fifteenStage0PolarProfile_pair_angle_gaps radii theta
    horder.1 horder.2 hsep (labels i) (labels j) i j hij
    (hprofile.2.2 i) (hprofile.2.2 j)
  constructor <;> linarith only [hgap.1, hgap.2]

end CirclePacking
