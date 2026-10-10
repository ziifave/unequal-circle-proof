import CirclePacking.FifteenPackingPolarCoordinates
import CirclePacking.FifteenCandidateDetourCurvature

/-! The wall-replacement step for outer centers.  The main inequality is
proved after normalizing the two radii by the candidate wall radius; the
threshold `b - 4/b` makes the mixed outer corner agree with the wall corner. -/

namespace CirclePacking

noncomputable def fifteenCandidateInnerThreshold : ℝ :=
  fifteenCandidateOuterRadius - 4 / fifteenCandidateOuterRadius

theorem fifteenCandidateInnerThreshold_gt_two :
    2 < fifteenCandidateInnerThreshold := by
  have hb := fifteenCandidateOuterRadius_mem_Ioo_352_353
  have hbpos := fifteenCandidateOuterRadius_pos
  have hbc : 0 < fifteenCandidateOuterRadius - (352 : ℝ) / 100 := by
    linarith [hb.1]
  have hbc2 : 0 < fifteenCandidateOuterRadius + (352 : ℝ) / 100 - 2 := by
    have := fifteenCandidateOuterRadius_pos
    linarith [hb.1]
  have hprod := mul_pos hbc hbc2
  have hc : 4 < ((352 : ℝ) / 100 - 2) * ((352 : ℝ) / 100) := by
    norm_num
  have hdiv : 4 < (fifteenCandidateOuterRadius - 2) * fifteenCandidateOuterRadius := by
    nlinarith [hprod, hc]
  have hquotient : 4 / fifteenCandidateOuterRadius <
      fifteenCandidateOuterRadius - 2 :=
    (div_lt_iff₀ hbpos).2 (by nlinarith [hdiv])
  dsimp [fifteenCandidateInnerThreshold]
  linarith

private theorem fifteen_normalized_wall_inequality
    (ε u v : ℝ)
    (hε : 0 ≤ ε) (hεone : ε ≤ 1)
    (huLo : 1 - ε ≤ u) (huHi : u ≤ 1)
    (hvLo : 1 - ε ≤ v) (hvHi : v ≤ 1) :
    (u - v) ^ 2 ≤ ε * (1 - u * v) := by
  have hu0 : 0 ≤ u := by linarith
  have hv0 : 0 ≤ v := by linarith
  have hremU0 : 0 ≤ 1 - u := by linarith
  have hremV0 : 0 ≤ 1 - v := by linarith
  have hremU : 1 - u ≤ ε := by linarith
  have hremV : 1 - v ≤ ε := by linarith
  by_cases huv : u ≤ v
  · have hdiff0 : 0 ≤ v - u := sub_nonneg.mpr huv
    have hdiffle : v - u ≤ 1 - u := by linarith
    have hprod : u * v ≤ u := by
      calc
        u * v ≤ u * 1 := mul_le_mul_of_nonneg_left hvHi hu0
        _ = u := by ring
    have hrem : 1 - u ≤ 1 - u * v := by linarith
    have hsq : (v - u) ^ 2 ≤ (1 - u) ^ 2 := by nlinarith
    have hsqε : (1 - u) ^ 2 ≤ ε * (1 - u) := by
      nlinarith [mul_le_mul_of_nonneg_right hremU hremU0]
    have hmul : ε * (1 - u) ≤ ε * (1 - u * v) :=
      mul_le_mul_of_nonneg_left hrem hε
    nlinarith [hsq, hsqε, hmul]
  · have hvu : v ≤ u := le_of_not_ge huv
    have hdiff0 : 0 ≤ u - v := sub_nonneg.mpr hvu
    have hdiffle : u - v ≤ 1 - v := by linarith
    have hprod : u * v ≤ v := by
      calc
        u * v = v * u := mul_comm _ _
        _ ≤ v * 1 := mul_le_mul_of_nonneg_left huHi hv0
        _ = v := by ring
    have hrem : 1 - v ≤ 1 - u * v := by linarith
    have hsq : (u - v) ^ 2 ≤ (1 - v) ^ 2 := by nlinarith
    have hsqε : (1 - v) ^ 2 ≤ ε * (1 - v) := by
      nlinarith [mul_le_mul_of_nonneg_right hremV hremV0]
    have hmul : ε * (1 - v) ≤ ε * (1 - u * v) :=
      mul_le_mul_of_nonneg_left hrem hε
    nlinarith [hsq, hsqε, hmul]

theorem fifteen_wall_cosine_cap_le
    {L b x y : ℝ}
    (hb : 0 < b) (hL : 2 ≤ L)
    (hthreshold : L = b - 4 / b)
    (hx : L ≤ x ∧ x ≤ b) (hy : L ≤ y ∧ y ≤ b) :
    (x ^ 2 + y ^ 2 - 4) / (2 * x * y) ≤ 1 - 2 / b ^ 2 := by
  let u : ℝ := x / b
  let v : ℝ := y / b
  let ε : ℝ := 4 / b ^ 2
  have hb2 : 0 < b ^ 2 := sq_pos_of_pos hb
  have hε0 : 0 ≤ ε := by positivity
  have hεone : ε ≤ 1 := by
    apply (div_le_iff₀ hb2).2
    have hbL : 2 ≤ b := le_trans hL (le_trans hx.1 hx.2)
    nlinarith [sq_nonneg (b - 2)]
  have hratio : (b - 4 / b) / b = 1 - ε := by
    dsimp [ε]
    field_simp [hb.ne']
    <;> ring
  have huLo : 1 - ε ≤ u := by
    dsimp [u]
    calc
      1 - ε = (b - 4 / b) / b := hratio.symm
      _ ≤ x / b := div_le_div_of_nonneg_right (by simpa [hthreshold] using hx.1) hb.le
  have huHi : u ≤ 1 := by
    dsimp [u]
    calc
      x / b ≤ b / b := div_le_div_of_nonneg_right hx.2 hb.le
      _ = 1 := by rw [div_self hb.ne']
  have hvLo : 1 - ε ≤ v := by
    dsimp [v]
    calc
      1 - ε = (b - 4 / b) / b := hratio.symm
      _ ≤ y / b := div_le_div_of_nonneg_right (by simpa [hthreshold] using hy.1) hb.le
  have hvHi : v ≤ 1 := by
    dsimp [v]
    calc
      y / b ≤ b / b := div_le_div_of_nonneg_right hy.2 hb.le
      _ = 1 := by rw [div_self hb.ne']
  have hnormalized := fifteen_normalized_wall_inequality ε u v
    hε0 hεone huLo huHi hvLo hvHi
  have huEq : x = b * u := by
    dsimp [u]
    field_simp [hb.ne']
  have hvEq : y = b * v := by
    dsimp [v]
    field_simp [hb.ne']
  have hnormalizedMul : b ^ 2 * (u - v) ^ 2 ≤ 4 * (1 - u * v) := by
    calc
      b ^ 2 * (u - v) ^ 2 ≤ b ^ 2 * (ε * (1 - u * v)) :=
        mul_le_mul_of_nonneg_left hnormalized (sq_nonneg b)
      _ = 4 * (1 - u * v) := by
        dsimp [ε]
        field_simp [hb.ne']
  have hnormalizedMul' :=
    mul_le_mul_of_nonneg_left hnormalizedMul (sq_nonneg b)
  have hwallDistancePolynomial :
      0 ≤ 4 * b ^ 2 - 4 * x * y - b ^ 2 * (x - y) ^ 2 := by
    rw [huEq, hvEq]
    nlinarith [hnormalizedMul']
  have hcross :
      b ^ 2 * (x ^ 2 + y ^ 2 - 4) ≤ 2 * x * y * (b ^ 2 - 2) := by
    nlinarith [hwallDistancePolynomial]
  have hscaled : x ^ 2 + y ^ 2 - 4 ≤ 2 * x * y * (1 - 2 / b ^ 2) := by
    calc
      x ^ 2 + y ^ 2 - 4 ≤
          (2 * x * y * (b ^ 2 - 2)) / b ^ 2 :=
        (le_div_iff₀ hb2).2 (by nlinarith [hcross])
      _ = 2 * x * y * (1 - 2 / b ^ 2) := by
        field_simp [hb.ne']
        <;> ring
  have hxpos : 0 < x := lt_of_lt_of_le (by norm_num) (le_trans hL hx.1)
  have hypos : 0 < y := lt_of_lt_of_le (by norm_num) (le_trans hL hy.1)
  apply (div_le_iff₀ (by positivity : 0 < 2 * x * y)).2
  simpa [mul_comm, mul_left_comm, mul_assoc] using hscaled

/-- Replacing both members of an outer--outer pair by wall centers at their
original polar angles preserves their separation. -/
theorem fifteen_wall_push_preserves_outer_pair
    {L b x y α β : ℝ}
    (hb : 0 < b) (hL : 2 ≤ L)
    (hthreshold : L = b - 4 / b)
    (hx : L ≤ x ∧ x ≤ b) (hy : L ≤ y ∧ y ≤ b)
    (hsep : 4 ≤ pointNorm
      ((polarPoint x α).1 - (polarPoint y β).1,
       (polarPoint x α).2 - (polarPoint y β).2) ^ 2) :
    4 ≤ pointNorm
      ((polarPoint b α).1 - (polarPoint b β).1,
       (polarPoint b α).2 - (polarPoint b β).2) ^ 2 := by
  have hxpos : 0 < x := lt_of_lt_of_le (by norm_num) (le_trans hL hx.1)
  have hypos : 0 < y := lt_of_lt_of_le (by norm_num) (le_trans hL hy.1)
  rw [fifteenPolarPair_distance_sq] at hsep ⊢
  have hcosNum :
      2 * x * y * Real.cos (α - β) ≤ x ^ 2 + y ^ 2 - 4 := by
    nlinarith [hsep]
  have hcosNum' : Real.cos (α - β) * (2 * x * y) ≤ x ^ 2 + y ^ 2 - 4 := by
    nlinarith [hcosNum]
  have hcos : Real.cos (α - β) ≤
      (x ^ 2 + y ^ 2 - 4) / (2 * x * y) :=
    (le_div_iff₀ (by positivity : 0 < 2 * x * y)).2 hcosNum'
  have hcap := fifteen_wall_cosine_cap_le hb hL hthreshold hx hy
  have hcosWall : Real.cos (α - β) ≤ 1 - 2 / b ^ 2 := hcos.trans hcap
  have hscaled := mul_le_mul_of_nonneg_left hcosWall
    (by positivity : 0 ≤ 2 * b ^ 2)
  have hreduce : 2 * b ^ 2 * (1 - 2 / b ^ 2) = 2 * b ^ 2 - 4 := by
    field_simp [hb.ne']
    <;> ring
  nlinarith [hscaled, hreduce]

/-- Pushing an outer center radially outward also preserves separation from an
inner center.  The inner radius is no larger than the old outer radius. -/
theorem fifteen_wall_push_preserves_outer_inner_pair
    {x y b α β : ℝ}
    (hxb : x ≤ b) (hyx : y ≤ x) (hy0 : 0 ≤ y)
    (hsep : 4 ≤ pointNorm
      ((polarPoint x α).1 - (polarPoint y β).1,
       (polarPoint x α).2 - (polarPoint y β).2) ^ 2) :
    4 ≤ pointNorm
      ((polarPoint b α).1 - (polarPoint y β).1,
       (polarPoint b α).2 - (polarPoint y β).2) ^ 2 := by
  rw [fifteenPolarPair_distance_sq] at hsep ⊢
  have hfactor : 0 ≤ b + x - 2 * y * Real.cos (α - β) := by
    nlinarith [Real.cos_le_one (α - β)]
  have hgap : 0 ≤ (b - x) * (b + x - 2 * y * Real.cos (α - β)) :=
    mul_nonneg (sub_nonneg.mpr hxb) hfactor
  nlinarith [hsep, hgap]

theorem fifteen_unit_packing_wall_push_outer_pair
    {R : ℝ} (P : Packing 15 R)
    (hunit : ∀ i, (P.circles i).radius = 1)
    (i j : Fin 15) (hij : i ≠ j)
    (hri : fifteenCandidateInnerThreshold ≤ fifteenCenterRadius P i)
    (hrj : fifteenCandidateInnerThreshold ≤ fifteenCenterRadius P j)
    (hRi : fifteenCenterRadius P i ≤ fifteenCandidateOuterRadius)
    (hRj : fifteenCenterRadius P j ≤ fifteenCandidateOuterRadius) :
    4 ≤ pointNorm
      ((polarPoint fifteenCandidateOuterRadius (fifteenPackingPolarAngle P i)).1 -
          (polarPoint fifteenCandidateOuterRadius (fifteenPackingPolarAngle P j)).1,
       (polarPoint fifteenCandidateOuterRadius (fifteenPackingPolarAngle P i)).2 -
          (polarPoint fifteenCandidateOuterRadius (fifteenPackingPolarAngle P j)).2) ^ 2 := by
  apply fifteen_wall_push_preserves_outer_pair
    fifteenCandidateOuterRadius_pos (le_of_lt fifteenCandidateInnerThreshold_gt_two)
    rfl ⟨hri, hRi⟩ ⟨hrj, hRj⟩
  exact fifteen_unit_packing_polar_pair_separated P hunit i j hij

noncomputable def fifteenWallPushedCenter {R : ℝ}
    (P : Packing 15 R) (i : Fin 15) : Point :=
  if fifteenCandidateInnerThreshold ≤ fifteenCenterRadius P i then
    polarPoint fifteenCandidateOuterRadius (fifteenPackingPolarAngle P i)
  else (P.circles i).center

/-- After the wall replacement, each center is either exactly on the wall or
strictly inside the radial threshold used for the inner class. -/
theorem fifteen_wall_pushed_center_radial_classification
    {R : ℝ} (P : Packing 15 R) (i : Fin 15) :
    pointNorm (fifteenWallPushedCenter P i) = fifteenCandidateOuterRadius ∨
      pointNorm (fifteenWallPushedCenter P i) < fifteenCandidateInnerThreshold := by
  by_cases h : fifteenCandidateInnerThreshold ≤ fifteenCenterRadius P i
  · left
    simp [fifteenWallPushedCenter, h, pointNorm_polarPoint
      (θ := fifteenPackingPolarAngle P i)
      (le_of_lt fifteenCandidateOuterRadius_pos)]
  · right
    have hlt : fifteenCenterRadius P i < fifteenCandidateInnerThreshold := lt_of_not_ge h
    rw [fifteenWallPushedCenter, if_neg h]
    simpa [fifteenCenterRadius] using hlt

/-- A single formula covers outer--outer, outer--inner, inner--outer, and
inner--inner pairs.  Thus the wall replacement preserves the complete
pairwise-separation relation. -/
theorem fifteen_unit_packing_wall_push_pair_separated
    {R : ℝ} (P : Packing 15 R)
    (hunit : ∀ i, (P.circles i).radius = 1)
    (i j : Fin 15) (hij : i ≠ j)
    (hRi : fifteenCenterRadius P i ≤ fifteenCandidateOuterRadius)
    (hRj : fifteenCenterRadius P j ≤ fifteenCandidateOuterRadius) :
    4 ≤ distSq (fifteenWallPushedCenter P i) (fifteenWallPushedCenter P j) := by
  have hpolarI := (fifteenPackingPolarAngle_spec P i).2.2
  have hpolarJ := (fifteenPackingPolarAngle_spec P j).2.2
  have hsep := fifteen_unit_packing_polar_pair_separated P hunit i j hij
  change 4 ≤ distSq (fifteenWallPushedCenter P i)
      (fifteenWallPushedCenter P j)
  by_cases hi : fifteenCandidateInnerThreshold ≤ fifteenCenterRadius P i
  · by_cases hj : fifteenCandidateInnerThreshold ≤ fifteenCenterRadius P j
    · have houter := fifteen_unit_packing_wall_push_outer_pair
        P hunit i j hij hi hj hRi hRj
      simpa [fifteenWallPushedCenter, hi, hj, distSq, pointNorm_sq] using houter
    · have hjlt : fifteenCenterRadius P j < fifteenCandidateInnerThreshold := lt_of_not_ge hj
      have hji : fifteenCenterRadius P j ≤ fifteenCenterRadius P i := le_of_lt (lt_of_lt_of_le hjlt hi)
      have hmix := fifteen_wall_push_preserves_outer_inner_pair
        hRi hji (pointNorm_nonneg (P.circles j).center) hsep
      simpa [fifteenWallPushedCenter, hi, hj, distSq, pointNorm_sq, hpolarJ] using hmix
  · by_cases hj : fifteenCandidateInnerThreshold ≤ fifteenCenterRadius P j
    · have hilt : fifteenCenterRadius P i < fifteenCandidateInnerThreshold := lt_of_not_ge hi
      have hijr : fifteenCenterRadius P i ≤ fifteenCenterRadius P j := le_of_lt (lt_of_lt_of_le hilt hj)
      have hsepRev : 4 ≤ pointNorm
          ((polarPoint (fifteenCenterRadius P j) (fifteenPackingPolarAngle P j)).1 -
              (polarPoint (fifteenCenterRadius P i) (fifteenPackingPolarAngle P i)).1,
           (polarPoint (fifteenCenterRadius P j) (fifteenPackingPolarAngle P j)).2 -
              (polarPoint (fifteenCenterRadius P i) (fifteenPackingPolarAngle P i)).2) ^ 2 := by
        rw [fifteenPolarPair_distance_sq] at hsep ⊢
        have hcos : Real.cos (fifteenPackingPolarAngle P j - fifteenPackingPolarAngle P i) =
            Real.cos (fifteenPackingPolarAngle P i - fifteenPackingPolarAngle P j) := by
          rw [show fifteenPackingPolarAngle P j - fifteenPackingPolarAngle P i =
            -(fifteenPackingPolarAngle P i - fifteenPackingPolarAngle P j) by ring,
            Real.cos_neg]
        rw [hcos]
        nlinarith [hsep]
      have hmix := fifteen_wall_push_preserves_outer_inner_pair
        hRj hijr (pointNorm_nonneg (P.circles i).center) hsepRev
      have hmixRev : 4 ≤ pointNorm
          ((polarPoint (fifteenCenterRadius P i) (fifteenPackingPolarAngle P i)).1 -
              (polarPoint fifteenCandidateOuterRadius (fifteenPackingPolarAngle P j)).1,
           (polarPoint (fifteenCenterRadius P i) (fifteenPackingPolarAngle P i)).2 -
              (polarPoint fifteenCandidateOuterRadius (fifteenPackingPolarAngle P j)).2) ^ 2 := by
        rw [fifteenPolarPair_distance_sq] at hmix ⊢
        have hcos : Real.cos (fifteenPackingPolarAngle P i - fifteenPackingPolarAngle P j) =
            Real.cos (fifteenPackingPolarAngle P j - fifteenPackingPolarAngle P i) := by
          rw [show fifteenPackingPolarAngle P i - fifteenPackingPolarAngle P j =
            -(fifteenPackingPolarAngle P j - fifteenPackingPolarAngle P i) by ring,
            Real.cos_neg]
        rw [hcos]
        nlinarith [hmix]
      simpa [fifteenWallPushedCenter, hi, hj, distSq, pointNorm_sq, hpolarI] using hmixRev
    · have hinnerI := (fifteenPackingPolarAngle_spec P i).2.2
      have hinnerJ := (fifteenPackingPolarAngle_spec P j).2.2
      rw [hinnerI, hinnerJ] at hsep
      simpa [fifteenWallPushedCenter, hi, hj, distSq, pointNorm_sq] using hsep

/-- Replacing every center of radius at least `L` by its same-angle wall
center yields a feasible unit-disk packing in the candidate container. -/
noncomputable def fifteen_unit_packing_wall_push
    {R : ℝ} (P : Packing 15 R)
    (hunit : ∀ i, (P.circles i).radius = 1)
    (hR : R ≤ fifteenCandidateOuterRadius + 1) :
    Packing 15 (fifteenCandidateOuterRadius + 1) where
  circles i := {
    center := fifteenWallPushedCenter P i
    radius := (P.circles i).radius
    radius_nonneg := (P.circles i).radius_nonneg
  }
  container_nonneg := add_nonneg
    (le_of_lt fifteenCandidateOuterRadius_pos) (by norm_num)
  contained i := by
    change (P.circles i).radius ≤ fifteenCandidateOuterRadius + 1 ∧
      distSq (fifteenWallPushedCenter P i) (0, 0) ≤
        (fifteenCandidateOuterRadius + 1 - (P.circles i).radius) ^ 2
    constructor
    · have hcontained := (P.enlarge hR).contained i
      exact hcontained.1
    · by_cases hi : fifteenCandidateInnerThreshold ≤ fifteenCenterRadius P i
      · simp [fifteenWallPushedCenter, hi]
        rw [hunit i]
        have hnorm : distSq
            (polarPoint fifteenCandidateOuterRadius (fifteenPackingPolarAngle P i)) (0, 0) =
            fifteenCandidateOuterRadius ^ 2 := by
          have hp := pointNorm_polarPoint
            (θ := fifteenPackingPolarAngle P i)
            (le_of_lt fifteenCandidateOuterRadius_pos)
          have hs := pointNorm_sq
            (polarPoint fifteenCandidateOuterRadius (fifteenPackingPolarAngle P i))
          rw [hp] at hs
          simpa [distSq] using hs.symm
        nlinarith [hnorm]
      · have hcontained := (P.enlarge hR).contained i
        simpa [fifteenWallPushedCenter, hi, Packing.enlarge] using hcontained.2
  separated := by
    intro i j hij
    change ((P.circles i).radius + (P.circles j).radius) ^ 2 ≤
      distSq (fifteenWallPushedCenter P i) (fifteenWallPushedCenter P j)
    rw [hunit i, hunit j]
    norm_num
    have hRi := (fifteen_unit_packing_center_radius_le_container P hunit i).trans
      (by linarith : R - 1 ≤ fifteenCandidateOuterRadius)
    have hRj := (fifteen_unit_packing_center_radius_le_container P hunit j).trans
      (by linarith : R - 1 ≤ fifteenCandidateOuterRadius)
    exact fifteen_unit_packing_wall_push_pair_separated P hunit i j hij hRi hRj

theorem fifteen_unit_packing_wall_push_preserves_unit_radii
    {R : ℝ} (P : Packing 15 R)
    (hunit : ∀ i, (P.circles i).radius = 1)
    (hR : R ≤ fifteenCandidateOuterRadius + 1) (i : Fin 15) :
    ((fifteen_unit_packing_wall_push P hunit hR).circles i).radius = 1 := by
  simp [fifteen_unit_packing_wall_push, hunit i]

end CirclePacking
