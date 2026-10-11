import CirclePacking.FifteenStage3CycleSoundness

/-! Geometry-facing interpretation of Stage 3 cycle ticks. -/

namespace CirclePacking

def s3ArrayOwnerLabels (labels : Array Nat) : Fin 15 → Nat :=
  fun i => labels[i.1]!

private theorem s3PairTick_matches_ownerPairTick
    (labels : Array Nat) (i j : Nat) (hi : i < 15) (hj : j < 15) :
    s3PairTick labels i j =
      fifteenStage3OwnerPairTick (s3ArrayOwnerLabels labels)
        (fifteenCycleFin i) (fifteenCycleFin j) := by
  simp [s3PairTick, fifteenStage3OwnerPairTick, s3ArrayOwnerLabels,
    Id.run, fifteenCycleFin, Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj]
  <;> rfl

private theorem s3RegularEdgeTick_matches_ownerPairTick
    (labels : Array Nat) (edge : S3CertEdge)
    (hsource : edge.source < 15) (htarget : edge.target < 15)
    (hkind : edge.kind = 'L' ∨ edge.kind = 'U') :
    s3EdgeTick labels edge =
      fifteenStage3OwnerPairTick (s3ArrayOwnerLabels labels)
        (fifteenCycleFin edge.source) (fifteenCycleFin edge.target) := by
  rcases hkind with hL | hU
  · have hreverse := s3PairTick_matches_ownerPairTick labels
      edge.target edge.source htarget hsource
    rw [show s3EdgeTick labels edge = s3PairTick labels edge.target edge.source by
      simp [s3EdgeTick, hL]]
    rw [hreverse]
    exact (fifteenStage3OwnerPairTick_comm (s3ArrayOwnerLabels labels)
      (fifteenCycleFin edge.target) (fifteenCycleFin edge.source))
  · have hdirect := s3PairTick_matches_ownerPairTick labels
      edge.source edge.target hsource htarget
    simpa [s3EdgeTick, hU] using hdirect

theorem s3CertEdge_angular_bound
    (labels : Array Nat) (radii : Fin 15 → ℝ)
    (howners : ∀ i, s3ArrayOwnerLabels labels i < 8 →
      fifteenStage3OwnerSpec (s3ArrayOwnerLabels labels i) (radii i))
    (hsum : ∀ i j, i ≠ j → 2 ≤ radii i + radii j)
    (theta : Fin 15 → ℝ)
    (hsorted : ∀ i j : Fin 15, i.1 < j.1 → theta i ≤ theta j)
    (hthetaLo : ∀ i, 0 ≤ theta i)
    (hthetaHi : ∀ i, theta i ≤ 2 * Real.pi)
    (hsep : ∀ i j : Fin 15, i ≠ j →
      4 ≤ pointNorm
        ((polarPoint (radii i) (theta i)).1 - (polarPoint (radii j) (theta j)).1,
         (polarPoint (radii i) (theta i)).2 - (polarPoint (radii j) (theta j)).2) ^ 2)
    (edge : S3CertEdge)
    (hshape : s3EdgeShape (s3MaterializeEdge labels edge) = true) :
    theta (fifteenCycleFin edge.target) - theta (fifteenCycleFin edge.source) ≤
      (fifteenCycleEdgeWeight
        (s3WeightedCycleEdge (s3MaterializeEdge labels edge)) : ℝ) /
        fifteenAngleScale := by
  have hweightedShape : s3EdgeShape (s3MaterializeEdge labels edge) = true := hshape
  have hconvertedShape := s3WeightedCycleEdge_shape
    (s3MaterializeEdge labels edge) hweightedShape
  let converted := s3WeightedCycleEdge (s3MaterializeEdge labels edge)
  obtain ⟨hsource, htarget, hticks, hsemantic⟩ :=
    fifteenCycleEdgeShape_spec converted hconvertedShape
  have hsource' : edge.source < 15 := by
    simpa [converted, s3WeightedCycleEdge, s3MaterializeEdge] using hsource
  have htarget' : edge.target < 15 := by
    simpa [converted, s3WeightedCycleEdge, s3MaterializeEdge] using htarget
  have hneq_of_order {i j : Fin 15} (hij : i.1 < j.1) : i ≠ j := by
    intro heq
    have := congrArg Fin.val heq
    omega
  rcases hsemantic with houter | hlower | hupper
  · rcases houter with ⟨hkind, hstep, htickZero⟩
    have hstep' : edge.source = edge.target + 1 := by
      simpa [converted, s3WeightedCycleEdge, s3MaterializeEdge] using hstep
    have horder : (fifteenCycleFin edge.target).1 <
        (fifteenCycleFin edge.source).1 := by
      change edge.target % 15 < edge.source % 15
      rw [Nat.mod_eq_of_lt htarget', Nat.mod_eq_of_lt hsource']
      omega
    have hangle := hsorted _ _ horder
    have hweight : fifteenCycleEdgeWeight converted = 0 := by
      simp [fifteenCycleEdgeWeight, hkind, htickZero]
    rw [hweight]
    norm_num [fifteenAngleScale]
    exact hangle
  · rcases hlower with ⟨hkind, horder⟩
    have hback : edge.target < edge.source := by
      simpa [converted, s3WeightedCycleEdge, s3MaterializeEdge] using horder
    have hencoded : s3CycleKindString edge.kind = "L" := by
      simpa [converted, s3WeightedCycleEdge, s3MaterializeEdge] using hkind
    have hchar : edge.kind = 'L' := by
      by_cases hO : edge.kind == 'O'
      · simp [s3CycleKindString, hO] at hencoded
      · by_cases hL : edge.kind == 'L'
        · exact beq_iff_eq.mp hL
        · simp [s3CycleKindString, hO, hL] at hencoded
    have hregularTick := s3RegularEdgeTick_matches_ownerPairTick
      labels edge hsource' htarget' (Or.inl hchar)
    have hangular := fifteenStage3OwnerPair_angular_bound
      radii (s3ArrayOwnerLabels labels) howners hsum theta
      ((fifteenPiUpperTicks : ℝ) / fifteenAngleScale)
      hsorted hthetaLo hthetaHi hsep fifteen_two_pi_le_cycle_tau
      (fifteenCycleFin edge.source) (fifteenCycleFin edge.target)
      (by
        intro heq
        have hval := congrArg Fin.val heq
        have hsourceVal : (fifteenCycleFin edge.source).val = edge.source :=
          Nat.mod_eq_of_lt hsource'
        have htargetVal : (fifteenCycleFin edge.target).val = edge.target :=
          Nat.mod_eq_of_lt htarget'
        have : edge.source = edge.target := by
          calc
            edge.source = (fifteenCycleFin edge.source).val := hsourceVal.symm
            _ = (fifteenCycleFin edge.target).val := hval
            _ = edge.target := htargetVal
        omega)
    have hangular' : theta (fifteenCycleFin edge.target) -
        theta (fifteenCycleFin edge.source) ≤
        fifteenAngularEdgeUpper
          ((fifteenPiUpperTicks : ℝ) / fifteenAngleScale)
          (fifteenCycleAngularEdge converted) := by
      simpa [converted, fifteenCycleAngularEdge, s3WeightedCycleEdge,
        s3MaterializeEdge, fifteenAngleScale, hregularTick] using hangular
    rw [fifteenCycleAngularEdge_upper_eq_weight converted hsource htarget
      (Or.inr (Or.inl ⟨hkind, horder⟩)) hticks] at hangular'
    simpa [converted] using hangular'
  · rcases hupper with ⟨hkind, horder⟩
    have hforward : edge.source < edge.target := by
      simpa [converted, s3WeightedCycleEdge, s3MaterializeEdge] using horder
    have hencoded : s3CycleKindString edge.kind = "U" := by
      simpa [converted, s3WeightedCycleEdge, s3MaterializeEdge] using hkind
    have hchar : edge.kind = 'U' := by
      by_cases hO : edge.kind == 'O'
      · simp [s3CycleKindString, hO] at hencoded
      · by_cases hL : edge.kind == 'L'
        · simp [s3CycleKindString, hO, hL] at hencoded
        · by_cases hU : edge.kind == 'U'
          · exact beq_iff_eq.mp hU
          · simp [s3EdgeShape, s3N, s3MaterializeEdge, s3EdgeTick,
              hO, hL, hU] at hshape
    have hregularTick := s3RegularEdgeTick_matches_ownerPairTick
      labels edge hsource' htarget' (Or.inr hchar)
    have hangular := fifteenStage3OwnerPair_angular_bound
      radii (s3ArrayOwnerLabels labels) howners hsum theta
      ((fifteenPiUpperTicks : ℝ) / fifteenAngleScale)
      hsorted hthetaLo hthetaHi hsep fifteen_two_pi_le_cycle_tau
      (fifteenCycleFin edge.source) (fifteenCycleFin edge.target)
      (hneq_of_order (by
        change edge.source % 15 < edge.target % 15
        rw [Nat.mod_eq_of_lt hsource', Nat.mod_eq_of_lt htarget']
        exact hforward))
    have hangular' : theta (fifteenCycleFin edge.target) -
        theta (fifteenCycleFin edge.source) ≤
        fifteenAngularEdgeUpper
          ((fifteenPiUpperTicks : ℝ) / fifteenAngleScale)
          (fifteenCycleAngularEdge converted) := by
      simpa [converted, fifteenCycleAngularEdge, s3WeightedCycleEdge,
        s3MaterializeEdge, fifteenAngleScale, hregularTick] using hangular
    rw [fifteenCycleAngularEdge_upper_eq_weight converted hsource htarget
      (Or.inr (Or.inr ⟨hkind, horder⟩)) hticks] at hangular'
    simpa [converted] using hangular'

/-- A Stage 3 cycle accepted by the exact checker cannot occur among the
polar-angle differences of a geometrically separated owner assignment. -/
theorem s3CycleValid_excludes_ownerAngles
    (labels : Array Nat) (radii : Fin 15 → ℝ)
    (howners : ∀ i, s3ArrayOwnerLabels labels i < 8 →
      fifteenStage3OwnerSpec (s3ArrayOwnerLabels labels i) (radii i))
    (hsum : ∀ i j, i ≠ j → 2 ≤ radii i + radii j)
    (theta : Fin 15 → ℝ)
    (hsorted : ∀ i j : Fin 15, i.1 < j.1 → theta i ≤ theta j)
    (hthetaLo : ∀ i, 0 ≤ theta i)
    (hthetaHi : ∀ i, theta i ≤ 2 * Real.pi)
    (hsep : ∀ i j : Fin 15, i ≠ j →
      4 ≤ pointNorm
        ((polarPoint (radii i) (theta i)).1 - (polarPoint (radii j) (theta j)).1,
         (polarPoint (radii i) (theta i)).2 - (polarPoint (radii j) (theta j)).2) ^ 2)
    (edges : List S3CertEdge)
    (hvalid : s3CycleValid labels edges = true) : False := by
  obtain ⟨_, _, hshape, _, _, _⟩ := s3CycleValid_specs labels edges hvalid
  have hshapeAll : ∀ weighted ∈ edges.map (s3MaterializeEdge labels),
      s3EdgeShape weighted = true := fifteenListAllTrue_spec _ _ hshape
  apply s3CycleValid_excludes_angularPotential labels edges theta hvalid
  intro converted hconverted
  change converted ∈
    ((edges.map (s3MaterializeEdge labels)).map s3WeightedCycleEdge) at hconverted
  obtain ⟨weighted, hweighted, rfl⟩ := List.mem_map.mp hconverted
  obtain ⟨certEdge, hcertEdge, rfl⟩ := List.mem_map.mp hweighted
  have hmaterialized : s3MaterializeEdge labels certEdge ∈
      edges.map (s3MaterializeEdge labels) :=
    List.mem_map.mpr ⟨certEdge, hcertEdge, rfl⟩
  exact s3CertEdge_angular_bound labels radii howners hsum theta hsorted
    hthetaLo hthetaHi hsep certEdge (hshapeAll _ hmaterialized)

end CirclePacking
