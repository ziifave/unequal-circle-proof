import CirclePacking.SevenNineCoverage
import CirclePacking.FifteenCertificate

/-! Basic geometric consequences of the `Packing` model used by the 15-disk
certificate. These lemmas connect arbitrary unit-disk packings to the radial
quantities consumed by the finite checker, independently of how the radial
boxes were generated. -/

namespace CirclePacking

noncomputable def fifteenCenterRadius {R : ℝ} (P : Packing 15 R) (i : Fin 15) : ℝ :=
  pointNorm (P.circles i).center

theorem fifteen_packing_center_radius_le_container_gap
    {R : ℝ} (P : Packing 15 R) (i : Fin 15) :
    fifteenCenterRadius P i ≤ R - (P.circles i).radius := by
  have hcontained := P.contained i
  rcases hcontained with ⟨hradius, hcenter⟩
  have hgap : 0 ≤ R - (P.circles i).radius := sub_nonneg.mpr hradius
  have hsquare :
      fifteenCenterRadius P i ^ 2 ≤
        (R - (P.circles i).radius) ^ 2 := by
    rw [fifteenCenterRadius, pointNorm_sq]
    simpa [distSq] using hcenter
  exact (sq_le_sq₀ (pointNorm_nonneg _) hgap).mp hsquare

theorem fifteen_unit_packing_center_radius_le_container
    {R : ℝ} (P : Packing 15 R)
    (hunit : ∀ i, (P.circles i).radius = 1) (i : Fin 15) :
    fifteenCenterRadius P i ≤ R - 1 := by
  simpa [hunit i] using fifteen_packing_center_radius_le_container_gap P i

theorem fifteen_packing_radius_sum_le_center_radius_sum
    {R : ℝ} (P : Packing 15 R) {i j : Fin 15} (hij : i ≠ j) :
    (P.circles i).radius + (P.circles j).radius ≤
      fifteenCenterRadius P i + fifteenCenterRadius P j := by
  have hseparated := P.separated hij
  have hdistanceSquare :
      ((P.circles i).radius + (P.circles j).radius) ^ 2 ≤
        pointNorm ((P.circles i).center.1 - (P.circles j).center.1,
          (P.circles i).center.2 - (P.circles j).center.2) ^ 2 := by
    rw [pointNorm_sq]
    simpa [Separated, distSq] using hseparated
  have hdistance :=
    (sq_le_sq₀
      (add_nonneg (P.circles i).radius_nonneg (P.circles j).radius_nonneg)
      (pointNorm_nonneg _)).mp hdistanceSquare
  have htriangle := pointNorm_triangle (P.circles i).center (P.circles j).center
  exact hdistance.trans (by simpa [fifteenCenterRadius] using htriangle)

theorem fifteen_unit_packing_pair_radial_sum_ge_two
    {R : ℝ} (P : Packing 15 R)
    (hunit : ∀ i, (P.circles i).radius = 1)
    {i j : Fin 15} (hij : i ≠ j) :
    2 ≤ fifteenCenterRadius P i + fifteenCenterRadius P j := by
  have hsum := fifteen_packing_radius_sum_le_center_radius_sum P hij
  rw [hunit i, hunit j] at hsum
  norm_num at hsum ⊢
  exact hsum

theorem fifteen_unit_packing_subunit_centers_unique
    {R : ℝ} (P : Packing 15 R)
    (hunit : ∀ i, (P.circles i).radius = 1)
    {i j : Fin 15}
    (hi : fifteenCenterRadius P i < 1)
    (hj : fifteenCenterRadius P j < 1) : i = j := by
  by_contra hne
  have hsum := fifteen_unit_packing_pair_radial_sum_ge_two P hunit hne
  linarith

theorem fifteen_unit_packing_origin_forces_other_centers_radius_two
    {R : ℝ} (P : Packing 15 R)
    (hunit : ∀ i, (P.circles i).radius = 1)
    {i j : Fin 15} (hij : i ≠ j)
    (horigin : fifteenCenterRadius P i = 0) :
    2 ≤ fifteenCenterRadius P j := by
  have hsum := fifteen_unit_packing_pair_radial_sum_ge_two P hunit hij
  rw [horigin] at hsum
  simpa using hsum

theorem fifteen_unit_packing_excludes_two_subunit_box_upper_bounds
    {R : ℝ} (P : Packing 15 R)
    (hunit : ∀ i, (P.circles i).radius = 1)
    {i j : Fin 15} (hij : i ≠ j)
    (x y : FifteenInterval)
    (hix : fifteenCenterRadius P i ≤ (x.2 : ℝ))
    (hjy : fifteenCenterRadius P j ≤ (y.2 : ℝ))
    (hx : (x.2 : ℝ) < 1) (hy : (y.2 : ℝ) < 1) : False := by
  have hsum := fifteen_unit_packing_pair_radial_sum_ge_two P hunit hij
  have hupper :
      (fifteenCenterRadius P i + fifteenCenterRadius P j : ℝ) < 2 := by
    linarith
  exact (not_lt_of_ge hsum) hupper

theorem fifteen_unit_packing_pair_box_upper_sum_ge_two
    {R : ℝ} (P : Packing 15 R)
    (hunit : ∀ i, (P.circles i).radius = 1)
    {i j : Fin 15} (hij : i ≠ j)
    (x y : FifteenInterval)
    (hix : fifteenCenterRadius P i ≤ (x.2 : ℝ))
    (hjy : fifteenCenterRadius P j ≤ (y.2 : ℝ)) :
    2 ≤ x.2 + y.2 := by
  have hradial := fifteen_unit_packing_pair_radial_sum_ge_two P hunit hij
  have hupper :
      (fifteenCenterRadius P i + fifteenCenterRadius P j : ℝ) ≤
        (x.2 : ℝ) + (y.2 : ℝ) := add_le_add hix hjy
  have hreal : (2 : ℝ) ≤ (x.2 : ℝ) + (y.2 : ℝ) := hradial.trans hupper
  exact_mod_cast hreal

theorem fifteen_unit_packing_excludes_pair_sum_leaf
    {R : ℝ} (P : Packing 15 R)
    (hunit : ∀ i, (P.circles i).radius = 1)
    {i j : Fin 15} (hij : i ≠ j)
    (x y : FifteenInterval)
    (hix : fifteenCenterRadius P i ≤ (x.2 : ℝ))
    (hjy : fifteenCenterRadius P j ≤ (y.2 : ℝ))
    (hleaf : x.2 + y.2 < 2) : False := by
  have hsum := fifteen_unit_packing_pair_box_upper_sum_ge_two
    P hunit hij x y hix hjy
  exact (not_lt_of_ge hsum) hleaf

theorem fifteen_unit_packing_excludes_sum_leaf
    {R : ℝ} (P : Packing 15 R)
    (hunit : ∀ i, (P.circles i).radius = 1)
    (box : FifteenBox) (i j : Nat)
    (hi : i < 15) (hj : j < 15) (hij : i ≠ j)
    (hradial : ∀ k : Fin 15,
      fifteenCenterRadius P k ≤ (box[k.1]!.2 : ℝ))
    (hleaf : decide (box[i]!.2 + box[j]!.2 < 2) = true) : False := by
  let fi : Fin 15 := ⟨i, hi⟩
  let fj : Fin 15 := ⟨j, hj⟩
  have hfij : fi ≠ fj := by
    intro h
    apply hij
    exact congrArg Fin.val h
  have hix : fifteenCenterRadius P fi ≤ (box[i]!.2 : ℝ) := by
    simpa [fi] using hradial fi
  have hjy : fifteenCenterRadius P fj ≤ (box[j]!.2 : ℝ) := by
    simpa [fj] using hradial fj
  have hsum := fifteen_unit_packing_pair_box_upper_sum_ge_two
    P hunit hfij box[i]! box[j]! hix hjy
  have hleaf' : box[i]!.2 + box[j]!.2 < 2 := of_decide_eq_true hleaf
  exact (not_lt_of_ge hsum) hleaf'

end CirclePacking
