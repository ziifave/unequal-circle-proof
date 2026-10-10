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

end CirclePacking
