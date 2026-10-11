import CirclePacking.FifteenStage4CycleSoundness

/-! Geometry-facing interpretation of Stage 4 cycle ticks. -/

namespace CirclePacking

def s4ArrayOwnerLabels (labels : Array Nat) : Fin 15 → Nat :=
  fun i => labels[i.1]!

private theorem s4PairTick_matches_ownerPairTick
    (labels : Array Nat) (i j : Nat) (hi : i < 15) (hj : j < 15) :
    s4PairTick labels i j =
      fifteenStage4OwnerPairTick (s4ArrayOwnerLabels labels)
        (fifteenCycleFin i) (fifteenCycleFin j) := by
  simp [s4PairTick, fifteenStage4OwnerPairTick, s4ArrayOwnerLabels,
    Id.run, fifteenCycleFin, Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj]
  <;> rfl

private theorem s4RegularEdgeTick_matches_ownerPairTick
    (labels : Array Nat) (edge : S4CertEdge)
    (hsource : edge.source < 15) (htarget : edge.target < 15)
    (hkind : edge.kind = 'L' ∨ edge.kind = 'U') :
    s4EdgeTick labels edge =
      fifteenStage4OwnerPairTick (s4ArrayOwnerLabels labels)
        (fifteenCycleFin edge.source) (fifteenCycleFin edge.target) := by
  rcases hkind with hL | hU
  · have hreverse := s4PairTick_matches_ownerPairTick labels
      edge.target edge.source htarget hsource
    rw [show s4EdgeTick labels edge = s4PairTick labels edge.target edge.source by
      simp [s4EdgeTick, hL]]
    rw [hreverse]
    exact (fifteenStage4OwnerPairTick_comm (s4ArrayOwnerLabels labels)
      (fifteenCycleFin edge.target) (fifteenCycleFin edge.source))
  · have hdirect := s4PairTick_matches_ownerPairTick labels
      edge.source edge.target hsource htarget
    simpa [s4EdgeTick, hU] using hdirect

theorem s4CertEdge_angular_bound
    (labels : Array Nat) (radii : Fin 15 → ℝ)
    (howners : ∀ i, s4ArrayOwnerLabels labels i < 12 →
      fifteenStage4OwnerSpec (s4ArrayOwnerLabels labels i) (radii i))
    (hsum : ∀ i j, i ≠ j → 2 ≤ radii i + radii j)
    (theta : Fin 15 → ℝ)
    (hsorted : ∀ i j : Fin 15, i.1 < j.1 → theta i ≤ theta j)
    (hthetaLo : ∀ i, 0 ≤ theta i)
    (hthetaHi : ∀ i, theta i ≤ 2 * Real.pi)
    (hsep : ∀ i j : Fin 15, i ≠ j →
      4 ≤ pointNorm
        ((polarPoint (radii i) (theta i)).1 - (polarPoint (radii j) (theta j)).1,
         (polarPoint (radii i) (theta i)).2 - (polarPoint (radii j) (theta j)).2) ^ 2)
    (edge : S4CertEdge)
    (hshape : s4EdgeShape (s4MaterializeEdge labels edge) = true) :
    theta (fifteenCycleFin edge.target) - theta (fifteenCycleFin edge.source) ≤
      (fifteenCycleEdgeWeight
        (s4WeightedCycleEdge (s4MaterializeEdge labels edge)) : ℝ) /
        fifteenAngleScale := by
  have hweightedShape : s4EdgeShape (s4MaterializeEdge labels edge) = true := hshape
  have hconvertedShape := s4WeightedCycleEdge_shape
    (s4MaterializeEdge labels edge) hweightedShape
  let converted := s4WeightedCycleEdge (s4MaterializeEdge labels edge)
  obtain ⟨hsource, htarget, hticks, hsemantic⟩ :=
    fifteenCycleEdgeShape_spec converted hconvertedShape
  have hsource' : edge.source < 15 := by
    simpa [converted, s4WeightedCycleEdge, s4MaterializeEdge] using hsource
  have htarget' : edge.target < 15 := by
    simpa [converted, s4WeightedCycleEdge, s4MaterializeEdge] using htarget
  have hneq_of_order {i j : Fin 15} (hij : i.1 < j.1) : i ≠ j := by
    intro heq
    have := congrArg Fin.val heq
    omega
  rcases hsemantic with houter | hlower | hupper
  · rcases houter with ⟨hkind, hstep, htickZero⟩
    have hstep' : edge.source = edge.target + 1 := by
      simpa [converted, s4WeightedCycleEdge, s4MaterializeEdge] using hstep
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
      simpa [converted, s4WeightedCycleEdge, s4MaterializeEdge] using horder
    have hencoded : s4CycleKindString edge.kind = "L" := by
      simpa [converted, s4WeightedCycleEdge, s4MaterializeEdge] using hkind
    have hchar : edge.kind = 'L' := by
      by_cases hO : edge.kind == 'O'
      · simp [s4CycleKindString, hO] at hencoded
      · by_cases hL : edge.kind == 'L'
        · exact beq_iff_eq.mp hL
        · simp [s4CycleKindString, hO, hL] at hencoded
    have hregularTick := s4RegularEdgeTick_matches_ownerPairTick
      labels edge hsource' htarget' (Or.inl hchar)
    have hangular := fifteenStage4OwnerPair_angular_bound
      radii (s4ArrayOwnerLabels labels) howners hsum theta
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
      simpa [converted, fifteenCycleAngularEdge, s4WeightedCycleEdge,
        s4MaterializeEdge, fifteenAngleScale, hregularTick] using hangular
    rw [fifteenCycleAngularEdge_upper_eq_weight converted hsource htarget
      (Or.inr (Or.inl ⟨hkind, horder⟩)) hticks] at hangular'
    simpa [converted] using hangular'
  · rcases hupper with ⟨hkind, horder⟩
    have hforward : edge.source < edge.target := by
      simpa [converted, s4WeightedCycleEdge, s4MaterializeEdge] using horder
    have hencoded : s4CycleKindString edge.kind = "U" := by
      simpa [converted, s4WeightedCycleEdge, s4MaterializeEdge] using hkind
    have hchar : edge.kind = 'U' := by
      by_cases hO : edge.kind == 'O'
      · simp [s4CycleKindString, hO] at hencoded
      · by_cases hL : edge.kind == 'L'
        · simp [s4CycleKindString, hO, hL] at hencoded
        · by_cases hU : edge.kind == 'U'
          · exact beq_iff_eq.mp hU
          · simp [s4EdgeShape, s4N, s4MaterializeEdge, s4EdgeTick,
              hO, hL, hU] at hshape
    have hregularTick := s4RegularEdgeTick_matches_ownerPairTick
      labels edge hsource' htarget' (Or.inr hchar)
    have hangular := fifteenStage4OwnerPair_angular_bound
      radii (s4ArrayOwnerLabels labels) howners hsum theta
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
      simpa [converted, fifteenCycleAngularEdge, s4WeightedCycleEdge,
        s4MaterializeEdge, fifteenAngleScale, hregularTick] using hangular
    rw [fifteenCycleAngularEdge_upper_eq_weight converted hsource htarget
      (Or.inr (Or.inr ⟨hkind, horder⟩)) hticks] at hangular'
    simpa [converted] using hangular'

/-- A Stage 4 cycle accepted by the exact checker cannot occur among the
polar-angle differences of a geometrically separated owner assignment. -/
theorem s4CycleValid_excludes_ownerAngles
    (labels : Array Nat) (radii : Fin 15 → ℝ)
    (howners : ∀ i, s4ArrayOwnerLabels labels i < 12 →
      fifteenStage4OwnerSpec (s4ArrayOwnerLabels labels i) (radii i))
    (hsum : ∀ i j, i ≠ j → 2 ≤ radii i + radii j)
    (theta : Fin 15 → ℝ)
    (hsorted : ∀ i j : Fin 15, i.1 < j.1 → theta i ≤ theta j)
    (hthetaLo : ∀ i, 0 ≤ theta i)
    (hthetaHi : ∀ i, theta i ≤ 2 * Real.pi)
    (hsep : ∀ i j : Fin 15, i ≠ j →
      4 ≤ pointNorm
        ((polarPoint (radii i) (theta i)).1 - (polarPoint (radii j) (theta j)).1,
         (polarPoint (radii i) (theta i)).2 - (polarPoint (radii j) (theta j)).2) ^ 2)
    (edges : List S4CertEdge)
    (hvalid : s4CycleValid labels edges = true) : False := by
  obtain ⟨_, _, hshape, _, _, _⟩ := s4CycleValid_specs labels edges hvalid
  have hshapeAll : ∀ weighted ∈ edges.map (s4MaterializeEdge labels),
      s4EdgeShape weighted = true := fifteenListAllTrue_spec _ _ hshape
  apply s4CycleValid_excludes_angularPotential labels edges theta hvalid
  intro converted hconverted
  change converted ∈
    ((edges.map (s4MaterializeEdge labels)).map s4WeightedCycleEdge) at hconverted
  obtain ⟨weighted, hweighted, rfl⟩ := List.mem_map.mp hconverted
  obtain ⟨certEdge, hcertEdge, rfl⟩ := List.mem_map.mp hweighted
  have hmaterialized : s4MaterializeEdge labels certEdge ∈
      edges.map (s4MaterializeEdge labels) :=
    List.mem_map.mpr ⟨certEdge, hcertEdge, rfl⟩
  exact s4CertEdge_angular_bound labels radii howners hsum theta hsorted
    hthetaLo hthetaHi hsep certEdge (hshapeAll _ hmaterialized)

end CirclePacking
