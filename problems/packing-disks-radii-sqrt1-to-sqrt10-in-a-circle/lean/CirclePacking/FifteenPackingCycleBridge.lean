import CirclePacking.FifteenPackingCycleEdgeGeometry

/-! The regular-edge angular estimate specialized to an actual unit-disk
packing.  The caller supplies the finite radial-box assignment; the polar
angle order and pairwise distance hypotheses are obtained directly from the
packing. -/

namespace CirclePacking

theorem fifteen_two_pi_le_cycle_tau :
    2 * Real.pi ≤ (fifteenPiUpperTicks : ℝ) / fifteenAngleScale := by
  apply le_of_lt ?_
  calc
    2 * Real.pi < 2 * (3.1416 : ℝ) := by nlinarith [Real.pi_lt_d4]
    _ ≤ (fifteenPiUpperTicks : ℝ) / fifteenAngleScale := by
      norm_num [fifteenPiUpperTicks, fifteenAngleScale]

theorem fifteen_unit_packing_regular_cycle_edge_bound
    {R : ℝ} (P : Packing 15 R)
    (hunit : ∀ i, (P.circles i).radius = 1)
    (edge : FifteenCycleEdge) (x y : FifteenInterval)
    (hshape : fifteenCycleEdgeShape edge = true)
    (hregular : (edge.kind = "L" ∧ edge.source > edge.target) ∨
      (edge.kind = "U" ∧ edge.source < edge.target))
    (hsum : 2 ≤ x.2 + y.2)
    (hvalid : fifteenTickCertificateValid x y false false edge.ticks = true)
    (hxOrder : x.1 ≤ x.2) (hyOrder : y.1 ≤ y.2)
    (hx0 : 0 < (x.1 : ℝ)) (hy0 : 0 < (y.1 : ℝ))
    (hsourceL : (x.1 : ℝ) ≤
      fifteenPackingSortedRadius P (fifteenCycleFin edge.source))
    (hsourceU : fifteenPackingSortedRadius P (fifteenCycleFin edge.source) ≤
      (x.2 : ℝ))
    (htargetL : (y.1 : ℝ) ≤
      fifteenPackingSortedRadius P (fifteenCycleFin edge.target))
    (htargetU : fifteenPackingSortedRadius P (fifteenCycleFin edge.target) ≤
      (y.2 : ℝ)) :
    fifteenPackingSortedAngle P (fifteenCycleFin edge.target) -
        fifteenPackingSortedAngle P (fifteenCycleFin edge.source) ≤
      (fifteenCycleEdgeWeight edge : ℝ) / fifteenAngleScale := by
  have hspec := fifteenCycleEdgeShape_spec edge hshape
  have hsourceNeTarget : edge.source ≠ edge.target := by
    rcases hregular with hlower | hupper
    · exact Nat.ne_of_gt hlower.2
    · exact Nat.ne_of_lt hupper.2
  let sourceIndex := fifteenCycleFin edge.source
  let targetIndex := fifteenCycleFin edge.target
  have hsourceVal : sourceIndex.val = edge.source :=
    Nat.mod_eq_of_lt hspec.1
  have htargetVal : targetIndex.val = edge.target :=
    Nat.mod_eq_of_lt hspec.2.1
  have hindices : sourceIndex ≠ targetIndex := by
    intro heq
    apply hsourceNeTarget
    calc
      edge.source = sourceIndex.val := hsourceVal.symm
      _ = targetIndex.val := congrArg Fin.val heq
      _ = edge.target := htargetVal
  have hsep := fifteen_unit_packing_sorted_pair_separated P hunit
    (i := sourceIndex) (j := targetIndex) hindices
  have hsep' : 4 ≤ pointNorm
      ((polarPoint (fifteenPackingSortedRadius P sourceIndex)
          (fifteenPackingSortedAngle P sourceIndex)).1 -
          (polarPoint (fifteenPackingSortedRadius P targetIndex)
          (fifteenPackingSortedAngle P targetIndex)).1,
       (polarPoint (fifteenPackingSortedRadius P sourceIndex)
          (fifteenPackingSortedAngle P sourceIndex)).2 -
      (polarPoint (fifteenPackingSortedRadius P targetIndex)
          (fifteenPackingSortedAngle P targetIndex)).2) ^ 2 := by
    simpa [sourceIndex, targetIndex] using hsep
  exact fifteenRegularTick_cycleEdge_weight_bound edge x y
    (fifteenPackingSortedAngle P)
    (fifteenPackingSortedRadius P sourceIndex)
    (fifteenPackingSortedRadius P targetIndex)
    ((fifteenPiUpperTicks : ℝ) / fifteenAngleScale)
    hshape hregular hsum hvalid hxOrder hyOrder hx0 hy0
    hsourceL hsourceU htargetL htargetU
    (fun i j hij => fifteenPackingSortedAngle_monotone P hij)
    (fun i => (fifteenPackingSortedAngle_range P i).1)
    (fun i => (fifteenPackingSortedAngle_range P i).2)
    hsep' fifteen_two_pi_le_cycle_tau rfl

theorem fifteen_unit_packing_outer_cycle_edge_bound
    {R : ℝ} (P : Packing 15 R)
    (edge : FifteenCycleEdge)
    (hshape : fifteenCycleEdgeShape edge = true)
    (houter : edge.kind = "O" ∧ edge.source = edge.target + 1 ∧
      edge.target < 14 ∧ edge.ticks = 0) :
    fifteenPackingSortedAngle P (fifteenCycleFin edge.target) -
        fifteenPackingSortedAngle P (fifteenCycleFin edge.source) ≤
      (fifteenCycleEdgeWeight edge : ℝ) / fifteenAngleScale := by
  have hspec := fifteenCycleEdgeShape_spec edge hshape
  have hsourceVal := Nat.mod_eq_of_lt hspec.1
  have htargetVal := Nat.mod_eq_of_lt hspec.2.1
  have hindexOrder : (fifteenCycleFin edge.target).val <
      (fifteenCycleFin edge.source).val := by
    change edge.target % 15 < edge.source % 15
    rw [Nat.mod_eq_of_lt hspec.2.1, Nat.mod_eq_of_lt hspec.1]
    omega
  have hangle := fifteenPackingSortedAngle_monotone P hindexOrder
  have hweight : fifteenCycleEdgeWeight edge = 0 := by
    simp [fifteenCycleEdgeWeight, houter.1]
  rw [hweight]
  norm_num [fifteenAngleScale]
  linarith

end CirclePacking
