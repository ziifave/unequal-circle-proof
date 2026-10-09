import CirclePacking.FifteenPackingGeometry
import CirclePacking.NineCirclePackingSoundness
import CirclePacking.PolarAngle

/-! Polar coordinates and pairwise separation for arbitrary 15-circle packings.
These lemmas do not assume a cyclic order on the original labels. -/

namespace CirclePacking

noncomputable def fifteenPackingPolarAngle {R : ℝ}
    (P : Packing 15 R) (i : Fin 15) : ℝ :=
  pointPolarAngle (P.circles i).center

theorem fifteenPackingPolarAngle_spec {R : ℝ}
    (P : Packing 15 R) (i : Fin 15) :
    0 ≤ fifteenPackingPolarAngle P i ∧
    fifteenPackingPolarAngle P i ≤ 2 * Real.pi ∧
    polarPoint (fifteenCenterRadius P i) (fifteenPackingPolarAngle P i) =
      (P.circles i).center := by
  simpa [fifteenPackingPolarAngle, fifteenCenterRadius] using
    pointPolarAngle_representation (P.circles i).center

theorem fifteenPolarPair_distance_sq (a b α β : ℝ) :
    pointNorm
        ((polarPoint a α).1 - (polarPoint b β).1,
         (polarPoint a α).2 - (polarPoint b β).2) ^ 2 =
      a ^ 2 + b ^ 2 - 2 * a * b * Real.cos (α - β) := by
  rw [pointNorm_sq]
  simp [polarPoint]
  calc
    _ = a ^ 2 * (Real.cos α ^ 2 + Real.sin α ^ 2) +
          b ^ 2 * (Real.cos β ^ 2 + Real.sin β ^ 2) -
          2 * a * b * (Real.cos α * Real.cos β + Real.sin α * Real.sin β) := by ring
    _ = a ^ 2 + b ^ 2 -
          2 * a * b * (Real.cos α * Real.cos β + Real.sin α * Real.sin β) := by
      rw [Real.cos_sq_add_sin_sq α, Real.cos_sq_add_sin_sq β]
      ring
    _ = a ^ 2 + b ^ 2 - 2 * a * b * Real.cos (α - β) := by
      rw [← Real.cos_sub]

theorem fifteenPolarPairRadiusSwap (a b α β : ℝ) :
    pointNorm
        ((polarPoint a α).1 - (polarPoint b β).1,
         (polarPoint a α).2 - (polarPoint b β).2) ^ 2 =
      pointNorm
        ((polarPoint b α).1 - (polarPoint a β).1,
         (polarPoint b α).2 - (polarPoint a β).2) ^ 2 := by
  rw [fifteenPolarPair_distance_sq, fifteenPolarPair_distance_sq]
  ring

theorem fifteen_unit_packing_polar_pair_separated
    {R : ℝ} (P : Packing 15 R)
    (hunit : ∀ i, (P.circles i).radius = 1)
    (i j : Fin 15) (hij : i ≠ j) :
    4 ≤ pointNorm
      ((polarPoint (fifteenCenterRadius P i) (fifteenPackingPolarAngle P i)).1 -
          (polarPoint (fifteenCenterRadius P j) (fifteenPackingPolarAngle P j)).1,
       (polarPoint (fifteenCenterRadius P i) (fifteenPackingPolarAngle P i)).2 -
          (polarPoint (fifteenCenterRadius P j) (fifteenPackingPolarAngle P j)).2) ^ 2 := by
  have hseparated := P.separated hij
  have hdist : 4 ≤ distSq (P.circles i).center (P.circles j).center := by
    have h := hseparated
    change ((P.circles i).radius + (P.circles j).radius) ^ 2 ≤
      distSq (P.circles i).center (P.circles j).center at h
    rw [hunit i, hunit j] at h
    norm_num at h
    exact h
  have hpolarI := (fifteenPackingPolarAngle_spec P i).2.2
  have hpolarJ := (fifteenPackingPolarAngle_spec P j).2.2
  rw [← hpolarI, ← hpolarJ] at hdist
  simpa [distSq, pointNorm_sq] using hdist

theorem fifteen_unit_packing_polar_pair_separated_swapped
    {R : ℝ} (P : Packing 15 R)
    (hunit : ∀ i, (P.circles i).radius = 1)
    (i j : Fin 15) (hij : i ≠ j) :
    4 ≤ pointNorm
      ((polarPoint (fifteenCenterRadius P j) (fifteenPackingPolarAngle P i)).1 -
          (polarPoint (fifteenCenterRadius P i) (fifteenPackingPolarAngle P j)).1,
       (polarPoint (fifteenCenterRadius P j) (fifteenPackingPolarAngle P i)).2 -
          (polarPoint (fifteenCenterRadius P i) (fifteenPackingPolarAngle P j)).2) ^ 2 := by
  have hsep := fifteen_unit_packing_polar_pair_separated P hunit i j hij
  rw [fifteenPolarPairRadiusSwap] at hsep
  exact hsep

end CirclePacking
