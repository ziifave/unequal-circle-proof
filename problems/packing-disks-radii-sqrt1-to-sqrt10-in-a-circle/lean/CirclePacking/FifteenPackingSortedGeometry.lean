import CirclePacking.FifteenPackingPolarCoordinates
import CirclePacking.FifteenPackingAngleOrder

/-! Reindex the actual polar data of a packing in nondecreasing angular order.
This is the interface needed to apply a finite cyclic certificate to an
arbitrarily labelled packing. -/

namespace CirclePacking

noncomputable def fifteenPackingSortedIndex {R : ℝ}
    (P : Packing 15 R) (k : Fin 15) : Fin 15 :=
  fifteenPackingAngleOrder (fifteenPackingPolarAngle P) k

noncomputable def fifteenPackingSortedAngle {R : ℝ}
    (P : Packing 15 R) (k : Fin 15) : ℝ :=
  fifteenPackingPolarAngle P (fifteenPackingSortedIndex P k)

noncomputable def fifteenPackingSortedRadius {R : ℝ}
    (P : Packing 15 R) (k : Fin 15) : ℝ :=
  fifteenCenterRadius P (fifteenPackingSortedIndex P k)

theorem fifteenPackingSortedIndex_bijective {R : ℝ} (P : Packing 15 R) :
    Function.Bijective (fifteenPackingSortedIndex P) := by
  exact fifteenPackingAngleOrder_bijective (fifteenPackingPolarAngle P)

theorem fifteenPackingSortedAngle_monotone {R : ℝ} (P : Packing 15 R)
    {i j : Fin 15} (hij : i.1 < j.1) :
    fifteenPackingSortedAngle P i ≤ fifteenPackingSortedAngle P j := by
  exact fifteenPackingAngleOrder_monotone (fifteenPackingPolarAngle P) hij

theorem fifteenPackingSortedAngle_range {R : ℝ}
    (P : Packing 15 R) (k : Fin 15) :
    0 ≤ fifteenPackingSortedAngle P k ∧
      fifteenPackingSortedAngle P k ≤ 2 * Real.pi := by
  rcases fifteenPackingPolarAngle_spec P (fifteenPackingSortedIndex P k) with
    ⟨hlo, hhi, _⟩
  exact ⟨hlo, hhi⟩

theorem fifteenPackingSortedRadius_preserves_bounds {R : ℝ}
    (P : Packing 15 R) (lower upper : Fin 15 → ℝ)
    (hbound : ∀ i, lower i ≤ fifteenCenterRadius P i ∧
      fifteenCenterRadius P i ≤ upper i) (k : Fin 15) :
    lower (fifteenPackingSortedIndex P k) ≤ fifteenPackingSortedRadius P k ∧
      fifteenPackingSortedRadius P k ≤ upper (fifteenPackingSortedIndex P k) :=
  hbound (fifteenPackingSortedIndex P k)

theorem fifteen_unit_packing_sorted_pair_separated {R : ℝ}
    (P : Packing 15 R) (hunit : ∀ i, (P.circles i).radius = 1)
    {i j : Fin 15} (hij : i ≠ j) :
    4 ≤ pointNorm
      ((polarPoint (fifteenPackingSortedRadius P i)
          (fifteenPackingSortedAngle P i)).1 -
          (polarPoint (fifteenPackingSortedRadius P j)
          (fifteenPackingSortedAngle P j)).1,
       (polarPoint (fifteenPackingSortedRadius P i)
          (fifteenPackingSortedAngle P i)).2 -
          (polarPoint (fifteenPackingSortedRadius P j)
          (fifteenPackingSortedAngle P j)).2) ^ 2 := by
  have hinj := fifteenPackingAngleOrder_injective (fifteenPackingPolarAngle P)
  have hindices : fifteenPackingSortedIndex P i ≠ fifteenPackingSortedIndex P j := by
    intro heq
    apply hij
    exact hinj heq
  simpa [fifteenPackingSortedIndex, fifteenPackingSortedAngle,
    fifteenPackingSortedRadius] using
      (fifteen_unit_packing_polar_pair_separated P hunit
        (fifteenPackingSortedIndex P i) (fifteenPackingSortedIndex P j) hindices)

theorem fifteen_unit_packing_sorted_pair_separated_swapped {R : ℝ}
    (P : Packing 15 R) (hunit : ∀ i, (P.circles i).radius = 1)
    {i j : Fin 15} (hij : i ≠ j) :
    4 ≤ pointNorm
      ((polarPoint (fifteenPackingSortedRadius P j)
          (fifteenPackingSortedAngle P i)).1 -
          (polarPoint (fifteenPackingSortedRadius P i)
          (fifteenPackingSortedAngle P j)).1,
       (polarPoint (fifteenPackingSortedRadius P j)
          (fifteenPackingSortedAngle P i)).2 -
          (polarPoint (fifteenPackingSortedRadius P i)
          (fifteenPackingSortedAngle P j)).2) ^ 2 := by
  have hinj := fifteenPackingAngleOrder_injective (fifteenPackingPolarAngle P)
  have hindices : fifteenPackingSortedIndex P i ≠ fifteenPackingSortedIndex P j := by
    intro heq
    apply hij
    exact hinj heq
  simpa [fifteenPackingSortedIndex, fifteenPackingSortedAngle,
    fifteenPackingSortedRadius] using
      (fifteen_unit_packing_polar_pair_separated_swapped P hunit
        (fifteenPackingSortedIndex P i) (fifteenPackingSortedIndex P j) hindices)

end CirclePacking
