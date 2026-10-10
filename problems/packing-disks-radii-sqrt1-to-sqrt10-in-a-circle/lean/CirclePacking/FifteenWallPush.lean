import CirclePacking.FifteenPackingPolarCoordinates
import CirclePacking.FifteenPackingSortedGeometry
import CirclePacking.FifteenCandidateDetourCurvature
import CirclePacking.FifteenStageZeroGeometry
import Mathlib.Data.Finset.Sort

/-! The wall-replacement step for outer centers.  The main inequality is
proved after normalizing the two radii by the candidate wall radius; the
threshold `b - 4/b` makes the mixed outer corner agree with the wall corner. -/

namespace CirclePacking

noncomputable def fifteenCandidateInnerThreshold : ℝ :=
  fifteenCandidateOuterRadius - 4 / fifteenCandidateOuterRadius

/-- The chosen polar angle is always strictly below one full turn.  This
strict endpoint fact lets same-angle radial replacement preserve the exact
angle used by the sorted-order interface. -/
theorem pointPolarAngle_lt_two_pi (p : Point) :
    pointPolarAngle p < 2 * Real.pi := by
  let z : ℂ := (p.1 : ℂ) + (p.2 : ℂ) * Complex.I
  change (if 0 ≤ Complex.arg z then Complex.arg z
    else Complex.arg z + 2 * Real.pi) < 2 * Real.pi
  by_cases h : 0 ≤ Complex.arg z
  · rw [if_pos h]
    have harg := Complex.arg_le_pi z
    nlinarith [Real.pi_pos]
  · have harg : Complex.arg z < 0 := lt_of_not_ge h
    rw [if_neg h]
    simpa using add_lt_add_right harg (2 * Real.pi)

/-- A positive radial replacement preserves the canonical polar angle as
long as the input angle lies in `[0,2π)`. -/
theorem pointPolarAngle_polarPoint_eq
    {r θ : ℝ} (hr : 0 < r) (hθ0 : 0 ≤ θ)
    (hθ2 : θ < 2 * Real.pi) :
    pointPolarAngle (polarPoint r θ) = θ := by
  let z : ℂ := (polarPoint r θ).1 + (polarPoint r θ).2 * Complex.I
  have hz : z = (r : ℂ) *
      ((Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I) := by
    dsimp [z, polarPoint]
    push_cast
    ring
  have harg : Complex.arg z =
      toIocMod Real.two_pi_pos (-Real.pi) θ := by
    rw [hz]
    simpa only [Complex.ofReal_cos, Complex.ofReal_sin] using
      Complex.arg_mul_cos_add_sin_mul_I_eq_toIocMod hr θ
  change (if 0 ≤ Complex.arg z then Complex.arg z
    else Complex.arg z + 2 * Real.pi) = θ
  by_cases hθpi : θ ≤ Real.pi
  · have hargEq : Complex.arg z = θ := by
      rw [harg]
      apply (toIocMod_eq_self Real.two_pi_pos).2
      constructor <;> nlinarith [Real.pi_pos, hθ0, hθpi]
    rw [hargEq]
    simp [hθ0]
  · have hθpi' : Real.pi < θ := lt_of_not_ge hθpi
    have hmem : θ - 2 * Real.pi ∈ Set.Ioc (-Real.pi) Real.pi := by
      constructor <;> nlinarith [Real.pi_pos, hθpi', hθ2]
    have hmod : toIocMod Real.two_pi_pos (-Real.pi) θ =
        θ - 2 * Real.pi := by
      apply (toIocMod_eq_iff Real.two_pi_pos).2
      refine ⟨?_, 1, ?_⟩
      · simpa [two_mul] using hmem
      · simp only [one_smul]
        ring
    have hargEq : Complex.arg z = θ - 2 * Real.pi := by
      rw [harg, hmod]
    rw [hargEq]
    have hneg : ¬ 0 ≤ θ - 2 * Real.pi := by linarith
    simp [hneg]

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

theorem fifteenCandidateInnerThreshold_lt_outerRadius :
    fifteenCandidateInnerThreshold < fifteenCandidateOuterRadius := by
  dsimp [fifteenCandidateInnerThreshold]
  have hb := fifteenCandidateOuterRadius_pos
  have hpositive : 0 < (4 : ℝ) / fifteenCandidateOuterRadius := by
    positivity
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

/-- The outer-pair cosine cap is strict when both original radii are strictly
inside the candidate wall. This is the angular slack needed to rule out a
container smaller than the candidate. -/
theorem fifteen_wall_cosine_cap_lt
    {L b x y : ℝ}
    (hb : 0 < b) (hL : 2 ≤ L)
    (hthreshold : L = b - 4 / b)
    (hx : L ≤ x ∧ x < b) (hy : L ≤ y ∧ y < b) :
    (x ^ 2 + y ^ 2 - 4) / (2 * x * y) < 1 - 2 / b ^ 2 := by
  let u : ℝ := x / b
  let v : ℝ := y / b
  let ε : ℝ := 4 / b ^ 2
  have hb2 : 0 < b ^ 2 := sq_pos_of_pos hb
  have hbge : 2 ≤ b := le_trans hL (le_trans hx.1 hx.2.le)
  have hεone : ε ≤ 1 := by
    apply (div_le_iff₀ hb2).2
    nlinarith [sq_nonneg (b - 2)]
  have hratio : (b - 4 / b) / b = 1 - ε := by
    dsimp [ε]
    field_simp [hb.ne']
    <;> ring
  have huLo : 1 - ε ≤ u := by
    dsimp [u]
    calc
      1 - ε = (b - 4 / b) / b := hratio.symm
      _ ≤ x / b :=
        div_le_div_of_nonneg_right (by simpa [hthreshold] using hx.1) hb.le
  have hvLo : 1 - ε ≤ v := by
    dsimp [v]
    calc
      1 - ε = (b - 4 / b) / b := hratio.symm
      _ ≤ y / b :=
        div_le_div_of_nonneg_right (by simpa [hthreshold] using hy.1) hb.le
  have huHi : u < 1 := by
    dsimp [u]
    calc
      x / b < b / b := div_lt_div_of_pos_right hx.2 hb
      _ = 1 := div_self hb.ne'
  have hvHi : v < 1 := by
    dsimp [v]
    calc
      y / b < b / b := div_lt_div_of_pos_right hy.2 hb
      _ = 1 := div_self hb.ne'
  have huPos : 0 < u := by
    dsimp [u]
    apply div_pos _ hb
    linarith [hL, hx.1]
  have hvPos : 0 < v := by
    dsimp [v]
    apply div_pos _ hb
    linarith [hL, hy.1]
  have hremU : 1 - u ≤ ε := by linarith [huLo]
  have hremV : 1 - v ≤ ε := by linarith [hvLo]
  have hremU0 : 0 ≤ 1 - u := le_of_lt (sub_pos.mpr huHi)
  have hremV0 : 0 ≤ 1 - v := le_of_lt (sub_pos.mpr hvHi)
  have hstrict : b ^ 2 * (u - v) ^ 2 < 4 * (1 - u * v) := by
    by_cases huv : u ≤ v
    · have hdiff : 0 ≤ v - u := sub_nonneg.mpr huv
      have hdiffle : v - u ≤ 1 - u := by linarith [huHi]
      have hsq : (v - u) ^ 2 ≤ (1 - u) ^ 2 := by nlinarith
      have hsqε : (1 - u) ^ 2 ≤ ε * (1 - u) := by
        nlinarith [mul_le_mul_of_nonneg_right hremU hremU0]
      have hsqBound : b ^ 2 * (u - v) ^ 2 ≤ 4 * (1 - u) := by
        calc
          b ^ 2 * (u - v) ^ 2 = b ^ 2 * (v - u) ^ 2 := by ring
          _ ≤ b ^ 2 * (1 - u) ^ 2 :=
            mul_le_mul_of_nonneg_left hsq (sq_nonneg b)
          _ ≤ b ^ 2 * (ε * (1 - u)) :=
            mul_le_mul_of_nonneg_left hsqε (sq_nonneg b)
          _ = 4 * (1 - u) := by
            dsimp [ε]
            field_simp [hb.ne']
      have hpositive := mul_pos huPos (sub_pos.mpr hvHi)
      nlinarith [hsqBound, hpositive]
    · have hvu : v ≤ u := le_of_not_ge huv
      have hdiff : 0 ≤ u - v := sub_nonneg.mpr hvu
      have hdiffle : u - v ≤ 1 - v := by linarith [huHi]
      have hsq : (u - v) ^ 2 ≤ (1 - v) ^ 2 := by nlinarith
      have hsqε : (1 - v) ^ 2 ≤ ε * (1 - v) := by
        nlinarith [mul_le_mul_of_nonneg_right hremV hremV0]
      have hsqBound : b ^ 2 * (u - v) ^ 2 ≤ 4 * (1 - v) := by
        calc
          b ^ 2 * (u - v) ^ 2 ≤ b ^ 2 * (1 - v) ^ 2 :=
            mul_le_mul_of_nonneg_left hsq (sq_nonneg b)
          _ ≤ b ^ 2 * (ε * (1 - v)) :=
            mul_le_mul_of_nonneg_left hsqε (sq_nonneg b)
          _ = 4 * (1 - v) := by
            dsimp [ε]
            field_simp [hb.ne']
      have hpositive := mul_pos hvPos (sub_pos.mpr huHi)
      nlinarith [hsqBound, hpositive]
  have huEq : x = b * u := by
    dsimp [u]
    field_simp [hb.ne']
  have hvEq : y = b * v := by
    dsimp [v]
    field_simp [hb.ne']
  have hscaled : b ^ 2 * (x ^ 2 + y ^ 2 - 4) <
      2 * x * y * (b ^ 2 - 2) := by
    rw [huEq, hvEq]
    nlinarith [hstrict]
  have hquotient : x ^ 2 + y ^ 2 - 4 <
      2 * x * y * (1 - 2 / b ^ 2) := by
    calc
      x ^ 2 + y ^ 2 - 4 <
          (2 * x * y * (b ^ 2 - 2)) / b ^ 2 :=
        (lt_div_iff₀ hb2).2 (by nlinarith [hscaled])
      _ = 2 * x * y * (1 - 2 / b ^ 2) := by
        field_simp [hb.ne']
        <;> ring
  have hxpos : 0 < x := by linarith [hL, hx.1]
  have hypos : 0 < y := by linarith [hL, hy.1]
  have hquotient' : x ^ 2 + y ^ 2 - 4 <
      (1 - 2 / b ^ 2) * (2 * x * y) := by
    calc
      x ^ 2 + y ^ 2 - 4 < 2 * x * y * (1 - 2 / b ^ 2) := hquotient
      _ = (1 - 2 / b ^ 2) * (2 * x * y) := by ring
  exact (div_lt_iff₀ (by positivity : 0 < 2 * x * y)).2 hquotient'

/-- In contact-angle form, two outer centers strictly inside the candidate
wall require strictly more angular separation than two centers on the wall. -/
theorem fifteen_wall_touch_angle_strict
    {L b x y : ℝ}
    (hb : 0 < b) (hL : 2 ≤ L)
    (hthreshold : L = b - 4 / b)
    (hx : L ≤ x ∧ x < b) (hy : L ≤ y ∧ y < b) :
    fifteenTouchAngle b b < fifteenTouchAngle x y := by
  have hcap := fifteen_wall_cosine_cap_lt hb hL hthreshold hx hy
  have hxpos : 0 < x := by linarith [hL, hx.1]
  have hypos : 0 < y := by linarith [hL, hy.1]
  have hnum : 0 ≤ x ^ 2 + y ^ 2 - 4 := by nlinarith
  have hcapLow : -1 ≤ (x ^ 2 + y ^ 2 - 4) / (2 * x * y) := by
    have hcapNonneg : 0 ≤ (x ^ 2 + y ^ 2 - 4) / (2 * x * y) :=
      div_nonneg hnum (by positivity)
    linarith
  have hwallHigh : 1 - 2 / b ^ 2 ≤ 1 := by
    have hfrac : 0 ≤ (2 : ℝ) / b ^ 2 := by positivity
    linarith
  have hwallCos : fifteenAngleCosineArgument b b = 1 - 2 / b ^ 2 := by
    unfold fifteenAngleCosineArgument
    field_simp [hb.ne']
    <;> ring
  have hangle := Real.arccos_lt_arccos hcapLow hcap hwallHigh
  rw [← hwallCos] at hangle
  simpa [fifteenTouchAngle, fifteenAngleCosineArgument] using hangle

/-- In a container strictly smaller than the candidate, every center has
radius strictly below the candidate wall. Therefore any two centers in the
outer radial class pay a strictly larger contact angle than the wall pair. -/
theorem fifteen_unit_packing_outer_pair_touch_angle_strict
    {R : ℝ} (P : Packing 15 R)
    (hunit : ∀ i, (P.circles i).radius = 1)
    (hR : R < fifteenCandidateOuterRadius + 1)
    (i j : Fin 15)
    (hi : fifteenCandidateInnerThreshold ≤ fifteenCenterRadius P i)
    (hj : fifteenCandidateInnerThreshold ≤ fifteenCenterRadius P j) :
    fifteenTouchAngle fifteenCandidateOuterRadius fifteenCandidateOuterRadius <
      fifteenTouchAngle (fifteenCenterRadius P i) (fifteenCenterRadius P j) := by
  have hri := fifteen_unit_packing_center_radius_le_container P hunit i
  have hrj := fifteen_unit_packing_center_radius_le_container P hunit j
  have hriLt : fifteenCenterRadius P i < fifteenCandidateOuterRadius := by
    linarith
  have hrjLt : fifteenCenterRadius P j < fifteenCandidateOuterRadius := by
    linarith
  exact fifteen_wall_touch_angle_strict
    fifteenCandidateOuterRadius_pos
    (le_of_lt fifteenCandidateInnerThreshold_gt_two)
    rfl ⟨hi, hriLt⟩ ⟨hj, hrjLt⟩

/-- For a fixed inner radius, increasing the other radius decreases the
cosine-rule contact angle whenever the side-length margin is nonnegative. -/
theorem fifteen_touch_angle_antitone_outer_radius
    {a x y : ℝ}
    (ha : 0 < a) (hx : 0 < x) (hy : 0 < y)
    (hxy : x ≤ y) (hmargin : a ^ 2 ≤ x * y + 4) :
    fifteenTouchAngle a y ≤ fifteenTouchAngle a x := by
  unfold fifteenTouchAngle
  apply Real.antitone_arccos
  unfold fifteenAngleCosineArgument
  apply (div_le_div_iff₀ (by positivity : 0 < 2 * a * x)
    (by positivity : 0 < 2 * a * y)).2
  have hcross :
      (a ^ 2 + y ^ 2 - 4) * (2 * a * x) -
        (a ^ 2 + x ^ 2 - 4) * (2 * a * y) =
          2 * a * (y - x) * (x * y + 4 - a ^ 2) := by ring
  have hnonneg : 0 ≤ 2 * a * (y - x) * (x * y + 4 - a ^ 2) :=
    mul_nonneg (mul_nonneg (by positivity) (sub_nonneg.mpr hxy))
      (sub_nonneg.mpr hmargin)
  nlinarith [hcross, hnonneg]

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

/-- The wall-pushed center of each label has the same canonical polar angle
as the original center. -/
theorem fifteen_unit_packing_wall_push_polar_angle_preserved
    {R : ℝ} (P : Packing 15 R)
    (hunit : ∀ i, (P.circles i).radius = 1)
    (hR : R ≤ fifteenCandidateOuterRadius + 1) (i : Fin 15) :
    fifteenPackingPolarAngle
        (fifteen_unit_packing_wall_push P hunit hR) i =
      fifteenPackingPolarAngle P i := by
  by_cases hi : fifteenCandidateInnerThreshold ≤ fifteenCenterRadius P i
  · have hpolar := fifteenPackingPolarAngle_spec P i
    have hthetaLt := pointPolarAngle_lt_two_pi (P.circles i).center
    change pointPolarAngle (fifteenWallPushedCenter P i) =
      pointPolarAngle (P.circles i).center
    rw [fifteenWallPushedCenter, if_pos hi]
    exact pointPolarAngle_polarPoint_eq fifteenCandidateOuterRadius_pos
      hpolar.1 hthetaLt
  · change pointPolarAngle (fifteenWallPushedCenter P i) =
      pointPolarAngle (P.circles i).center
    rw [fifteenWallPushedCenter, if_neg hi]

/-- The angle-sort permutation is unchanged by the wall replacement. -/
theorem fifteen_unit_packing_wall_push_sorted_index_preserved
    {R : ℝ} (P : Packing 15 R)
    (hunit : ∀ i, (P.circles i).radius = 1)
    (hR : R ≤ fifteenCandidateOuterRadius + 1) (k : Fin 15) :
    fifteenPackingSortedIndex
        (fifteen_unit_packing_wall_push P hunit hR) k =
      fifteenPackingSortedIndex P k := by
  have hangles :
      fifteenPackingPolarAngle
          (fifteen_unit_packing_wall_push P hunit hR) =
        fifteenPackingPolarAngle P := by
    funext i
    exact fifteen_unit_packing_wall_push_polar_angle_preserved P hunit hR i
  simp [fifteenPackingSortedIndex, hangles]

/-- Sorting after wall replacement therefore preserves the original angular
coordinates term by term. -/
theorem fifteen_unit_packing_wall_push_sorted_angle_preserved
    {R : ℝ} (P : Packing 15 R)
    (hunit : ∀ i, (P.circles i).radius = 1)
    (hR : R ≤ fifteenCandidateOuterRadius + 1) (k : Fin 15) :
    fifteenPackingSortedAngle
        (fifteen_unit_packing_wall_push P hunit hR) k =
      fifteenPackingSortedAngle P k := by
  unfold fifteenPackingSortedAngle
  rw [fifteen_unit_packing_wall_push_sorted_index_preserved P hunit hR k]
  exact fifteen_unit_packing_wall_push_polar_angle_preserved P hunit hR
    (fifteenPackingSortedIndex P k)

/-- Wall replacement preserves the threshold classification in sorted order.
An outer center is moved to radius `b`, which is strictly beyond the inner
threshold; an inner center is left exactly where it was. -/
theorem fifteen_unit_packing_wall_push_sorted_radius_inner_iff
    {R : ℝ} (P : Packing 15 R)
    (hunit : ∀ i, (P.circles i).radius = 1)
    (hR : R ≤ fifteenCandidateOuterRadius + 1) (k : Fin 15) :
    fifteenPackingSortedRadius
        (fifteen_unit_packing_wall_push P hunit hR) k <
          fifteenCandidateInnerThreshold ↔
      fifteenPackingSortedRadius P k < fifteenCandidateInnerThreshold := by
  rw [fifteenPackingSortedRadius,
    fifteen_unit_packing_wall_push_sorted_index_preserved P hunit hR k]
  change pointNorm (fifteenWallPushedCenter P
      (fifteenPackingSortedIndex P k)) < fifteenCandidateInnerThreshold ↔
    pointNorm ((P.circles (fifteenPackingSortedIndex P k)).center) <
      fifteenCandidateInnerThreshold
  by_cases houter : fifteenCandidateInnerThreshold ≤
      fifteenCenterRadius P (fifteenPackingSortedIndex P k)
  · have hthreshold := fifteenCandidateInnerThreshold_gt_two
    have hwallNorm : pointNorm (fifteenWallPushedCenter P
        (fifteenPackingSortedIndex P k)) = fifteenCandidateOuterRadius := by
      rw [fifteenWallPushedCenter, if_pos houter]
      exact pointNorm_polarPoint (le_of_lt fifteenCandidateOuterRadius_pos)
    have horiginal : fifteenCandidateInnerThreshold ≤
        pointNorm ((P.circles (fifteenPackingSortedIndex P k)).center) := by
      simpa [fifteenCenterRadius] using houter
    rw [hwallNorm]
    exact iff_of_false
      (not_lt_of_ge (by
        have hb := fifteenCandidateInnerThreshold_lt_outerRadius
        exact le_of_lt hb))
      (not_lt_of_ge horiginal)
  · rw [fifteenWallPushedCenter, if_neg houter]

/-- In angular order, the wall-pushed packing supplies the two radial classes
used by the finite reduction: wall radius `b`, or strictly below `L`. -/
theorem fifteen_unit_packing_wall_push_sorted_radial_classification
    {R : ℝ} (P : Packing 15 R)
    (hunit : ∀ i, (P.circles i).radius = 1)
    (hR : R ≤ fifteenCandidateOuterRadius + 1) (k : Fin 15) :
    fifteenPackingSortedRadius (fifteen_unit_packing_wall_push P hunit hR) k =
        fifteenCandidateOuterRadius ∨
      fifteenPackingSortedRadius (fifteen_unit_packing_wall_push P hunit hR) k <
        fifteenCandidateInnerThreshold := by
  have hclass := fifteen_wall_pushed_center_radial_classification P
    (fifteenPackingSortedIndex (fifteen_unit_packing_wall_push P hunit hR) k)
  simpa [fifteenPackingSortedRadius, fifteenCenterRadius,
    fifteen_unit_packing_wall_push] using hclass

/-- The same ordered packing retains the pairwise separation hypothesis
required by the certificate soundness lemmas. -/
theorem fifteen_unit_packing_wall_push_sorted_pair_separated
    {R : ℝ} (P : Packing 15 R)
    (hunit : ∀ i, (P.circles i).radius = 1)
    (hR : R ≤ fifteenCandidateOuterRadius + 1)
    {i j : Fin 15} (hij : i ≠ j) :
    4 ≤ pointNorm
      ((polarPoint
          (fifteenPackingSortedRadius (fifteen_unit_packing_wall_push P hunit hR) i)
          (fifteenPackingSortedAngle (fifteen_unit_packing_wall_push P hunit hR) i)).1 -
          (polarPoint
          (fifteenPackingSortedRadius (fifteen_unit_packing_wall_push P hunit hR) j)
          (fifteenPackingSortedAngle (fifteen_unit_packing_wall_push P hunit hR) j)).1,
       (polarPoint
          (fifteenPackingSortedRadius (fifteen_unit_packing_wall_push P hunit hR) i)
          (fifteenPackingSortedAngle (fifteen_unit_packing_wall_push P hunit hR) i)).2 -
          (polarPoint
          (fifteenPackingSortedRadius (fifteen_unit_packing_wall_push P hunit hR) j)
          (fifteenPackingSortedAngle (fifteen_unit_packing_wall_push P hunit hR) j)).2) ^ 2 := by
  exact fifteen_unit_packing_sorted_pair_separated
    (fifteen_unit_packing_wall_push P hunit hR)
    (fifteen_unit_packing_wall_push_preserves_unit_radii P hunit hR)
    hij

/-- Two wall centers in angular order must have at least the stage-zero
outer/outer contact angle in either direction around the circle.  This turns
the finite table entry into a geometric constraint on an arbitrary packing. -/
theorem fifteen_unit_packing_wall_push_outer_pair_ordered_gap
    {R : ℝ} (P : Packing 15 R)
    (hunit : ∀ i, (P.circles i).radius = 1)
    (hR : R ≤ fifteenCandidateOuterRadius + 1)
    {i j : Fin 15} (hij : i.1 < j.1)
    (hi : fifteenPackingSortedRadius
      (fifteen_unit_packing_wall_push P hunit hR) i =
        fifteenCandidateOuterRadius)
    (hj : fifteenPackingSortedRadius
      (fifteen_unit_packing_wall_push P hunit hR) j =
        fifteenCandidateOuterRadius) :
    (1610 : ℝ) / 2800 ≤
        fifteenPackingSortedAngle
          (fifteen_unit_packing_wall_push P hunit hR) j -
          fifteenPackingSortedAngle
            (fifteen_unit_packing_wall_push P hunit hR) i ∧
      fifteenPackingSortedAngle
          (fifteen_unit_packing_wall_push P hunit hR) j -
          fifteenPackingSortedAngle
            (fifteen_unit_packing_wall_push P hunit hR) i ≤
        2 * Real.pi - (1610 : ℝ) / 2800 := by
  let Q := fifteen_unit_packing_wall_push P hunit hR
  have hpositive : 0 < fifteenStage0CoarseAngleTick (0 : Fin 4) (0 : Fin 4) := by
    norm_num [fifteenStage0CoarseAngleTick, fifteenStage0CoarseQ]
  have hbox := fifteenStage0OuterTypeBox_bounds
  have hbLower : (2385 : ℝ) / 1000 ≤ fifteenCandidateOuterRadius := by
    have hb := fifteenCandidateOuterRadius_mem_Ioo_352_353
    linarith
  have hbUpper : fifteenCandidateOuterRadius ≤ (3522 : ℝ) / 1000 :=
    le_of_lt fifteenCandidateOuterRadius_lt_3522_1000
  have hell : (1610 : ℝ) / 2800 ≤
      touchAngle fifteenCandidateOuterRadius fifteenCandidateOuterRadius 2 := by
    exact fifteenStage0CoarsePair_lower_bounds_touch_angle
      (0 : Fin 4) (0 : Fin 4) hpositive
      fifteenCandidateOuterRadius fifteenCandidateOuterRadius
      (by rw [hbox.1]; exact hbLower)
      (by rw [hbox.2]; exact hbUpper)
      (by rw [hbox.1]; exact hbLower)
      (by rw [hbox.2]; exact hbUpper)
  have hsep := fifteen_unit_packing_wall_push_sorted_pair_separated
    P hunit hR (i := i) (j := j) (ne_of_lt hij)
  have hsep' : 4 ≤ pointNorm
      ((polarPoint fifteenCandidateOuterRadius
          (fifteenPackingSortedAngle Q i)).1 -
          (polarPoint fifteenCandidateOuterRadius
          (fifteenPackingSortedAngle Q j)).1,
       (polarPoint fifteenCandidateOuterRadius
          (fifteenPackingSortedAngle Q i)).2 -
          (polarPoint fifteenCandidateOuterRadius
          (fifteenPackingSortedAngle Q j)).2) ^ 2 := by
    simpa [Q, hi, hj] using hsep
  have hsep2 : 2 ^ 2 ≤ pointNorm
      ((polarPoint fifteenCandidateOuterRadius
          (fifteenPackingSortedAngle Q i)).1 -
          (polarPoint fifteenCandidateOuterRadius
          (fifteenPackingSortedAngle Q j)).1,
       (polarPoint fifteenCandidateOuterRadius
          (fifteenPackingSortedAngle Q i)).2 -
          (polarPoint fifteenCandidateOuterRadius
          (fifteenPackingSortedAngle Q j)).2) ^ 2 := by
    rw [show (2 : ℝ) ^ 2 = 4 by norm_num]
    exact hsep'
  have hdelta0 : 0 ≤ fifteenPackingSortedAngle Q j -
      fifteenPackingSortedAngle Q i := by
    exact sub_nonneg.mpr (fifteenPackingSortedAngle_monotone Q hij)
  have hdelta2 : fifteenPackingSortedAngle Q j -
      fifteenPackingSortedAngle Q i ≤ 2 * Real.pi := by
    have hj' := (fifteenPackingSortedAngle_range Q j).2
    have hi' := (fifteenPackingSortedAngle_range Q i).1
    linarith
  have hellpi : (1610 : ℝ) / 2800 ≤ Real.pi := by
    have hp := Real.pi_gt_three
    norm_num at hp ⊢
    linarith
  exact fifteen_polar_touch_angle_ordered_gap
    (a := fifteenCandidateOuterRadius)
    (b := fifteenCandidateOuterRadius) (d := 2) (ell := 1610 / 2800)
    (alpha := fifteenPackingSortedAngle Q i)
    (beta := fifteenPackingSortedAngle Q j)
    fifteenCandidateOuterRadius_pos fifteenCandidateOuterRadius_pos
    hellpi hdelta0 hdelta2 hsep2 hell

/-- There can be at most ten centers on the pushed wall.  Eleven such centers
would contribute ten ordered gaps and a final wraparound gap, each at least
the stage-zero outer/outer tick, exceeding a full turn. -/
theorem fifteen_unit_packing_wall_push_outer_count_le_ten
    {R : ℝ} (P : Packing 15 R)
    (hunit : ∀ i, (P.circles i).radius = 1)
    (hR : R ≤ fifteenCandidateOuterRadius + 1) :
    (Finset.univ.filter fun i : Fin 15 =>
      fifteenPackingSortedRadius
        (fifteen_unit_packing_wall_push P hunit hR) i =
          fifteenCandidateOuterRadius).card ≤ 10 := by
  classical
  let Q := fifteen_unit_packing_wall_push P hunit hR
  let S : Finset (Fin 15) := Finset.univ.filter fun i =>
    fifteenPackingSortedRadius Q i = fifteenCandidateOuterRadius
  change S.card ≤ 10
  by_contra hnot
  have hcard : 11 ≤ S.card := by omega
  obtain ⟨T, hTsub, hTcard⟩ := Finset.exists_subset_card_eq hcard
  let order : Fin 11 ↪o Fin 15 := T.orderEmbOfFin hTcard
  let theta : Fin 11 → ℝ := fun k => fifteenPackingSortedAngle Q (order k)
  have houter (k : Fin 11) :
      fifteenPackingSortedRadius Q (order k) = fifteenCandidateOuterRadius := by
    have hmemT : order k ∈ T := by
      simpa [order] using T.orderEmbOfFin_mem hTcard k
    have hmemS : order k ∈ S := hTsub hmemT
    exact (Finset.mem_filter.mp hmemS).2
  have hgap (k : Fin 10) :
      (1610 : ℝ) / 2800 ≤ theta k.succ - theta k.castSucc := by
    have hkn : k.castSucc < k.succ := by
      exact Fin.castSucc_lt_succ_iff.mpr le_rfl
    have hlt : (order k.castSucc).1 < (order k.succ).1 := by
      exact order.strictMono hkn
    have hbound := fifteen_unit_packing_wall_push_outer_pair_ordered_gap
      P hunit hR hlt (houter k.castSucc) (houter k.succ)
    simpa [theta] using hbound.1
  have hspan_nat : ∀ (n : Nat) (hn : n ≤ 10),
      (n : ℝ) * ((1610 : ℝ) / 2800) ≤
        theta ⟨n, by omega⟩ - theta (0 : Fin 11) := by
    intro n
    induction n with
    | zero =>
        intro _
        simp [theta]
    | succ n ih =>
        intro hn
        have hn10 : n ≤ 10 := by omega
        have hprev := ih hn10
        let k : Fin 10 := ⟨n, by omega⟩
        have hstep : (1610 : ℝ) / 2800 ≤
            theta ⟨n + 1, by omega⟩ - theta ⟨n, by omega⟩ := by
          simpa [k] using hgap k
        calc
          ((n + 1 : Nat) : ℝ) * ((1610 : ℝ) / 2800) =
              (n : ℝ) * ((1610 : ℝ) / 2800) + (1610 : ℝ) / 2800 := by
                push_cast
                ring
          _ ≤ (theta ⟨n, by omega⟩ - theta (0 : Fin 11)) +
                (theta ⟨n + 1, by omega⟩ - theta ⟨n, by omega⟩) :=
              add_le_add hprev hstep
          _ = theta ⟨n + 1, by omega⟩ - theta (0 : Fin 11) := by ring
  have hspan : (10 : ℝ) * ((1610 : ℝ) / 2800) ≤
      theta (10 : Fin 11) - theta (0 : Fin 11) := by
    simpa using hspan_nat 10 (by omega)
  have hfirstlast : (order (0 : Fin 11)).1 < (order (10 : Fin 11)).1 := by
    have hlt : (0 : Fin 11) < (10 : Fin 11) := by decide
    exact order.strictMono hlt
  have hwrap := fifteen_unit_packing_wall_push_outer_pair_ordered_gap
    P hunit hR hfirstlast (houter 0) (houter 10)
  have hwrap' : theta (10 : Fin 11) - theta (0 : Fin 11) ≤
      2 * Real.pi - (1610 : ℝ) / 2800 := by
    simpa [theta] using hwrap.2
  have hsum : (11 : ℝ) * ((1610 : ℝ) / 2800) ≤ 2 * Real.pi := by
    calc
      (11 : ℝ) * ((1610 : ℝ) / 2800) =
          (10 : ℝ) * ((1610 : ℝ) / 2800) + (1610 : ℝ) / 2800 := by
            norm_num
      _ ≤ theta (10 : Fin 11) - theta (0 : Fin 11) +
            (1610 : ℝ) / 2800 := add_le_add_left hspan _
      _ ≤ 2 * Real.pi := by linarith
  have hstrict : 2 * Real.pi <
      (11 : ℝ) * ((1610 : ℝ) / 2800) := by
    have hpi := Real.pi_lt_d4
    have hrat : (44 : ℝ) / 7 <
        (11 : ℝ) * ((1610 : ℝ) / 2800) := by norm_num
    nlinarith
  linarith

/-- Encode the angularly sorted inner/outer classification in the same
`0`/`1` convention consumed by the finite pattern checker (`1` means inner). -/
noncomputable def fifteen_unit_packing_wall_push_sorted_pattern
    {R : ℝ} (P : Packing 15 R)
    (hunit : ∀ i, (P.circles i).radius = 1)
    (hR : R ≤ fifteenCandidateOuterRadius + 1) : String :=
  String.ofList (List.ofFn fun k : Fin 15 =>
    if fifteenPackingSortedRadius (fifteen_unit_packing_wall_push P hunit hR) k <
        fifteenCandidateInnerThreshold then '1' else '0')

theorem fifteen_unit_packing_wall_push_sorted_pattern_length
    {R : ℝ} (P : Packing 15 R)
    (hunit : ∀ i, (P.circles i).radius = 1)
    (hR : R ≤ fifteenCandidateOuterRadius + 1) :
    (fifteen_unit_packing_wall_push_sorted_pattern P hunit hR).length = 15 := by
  simp [fifteen_unit_packing_wall_push_sorted_pattern]

theorem fifteen_unit_packing_wall_push_sorted_pattern_bit
    {R : ℝ} (P : Packing 15 R)
    (hunit : ∀ i, (P.circles i).radius = 1)
    (hR : R ≤ fifteenCandidateOuterRadius + 1) (k : Fin 15) :
    (fifteen_unit_packing_wall_push_sorted_pattern P hunit hR).toList[k.1]? =
      some (if fifteenPackingSortedRadius
          (fifteen_unit_packing_wall_push P hunit hR) k <
          fifteenCandidateInnerThreshold then '1' else '0') := by
  rw [fifteen_unit_packing_wall_push_sorted_pattern, String.toList_ofList]
  rw [List.getElem?_ofFn]
  simp

/-- The finite classifier's bit at an ordered position is the original
packing's threshold bit; wall-pushing does not alter the bit string. -/
theorem fifteen_unit_packing_wall_push_sorted_pattern_original_bit
    {R : ℝ} (P : Packing 15 R)
    (hunit : ∀ i, (P.circles i).radius = 1)
    (hR : R ≤ fifteenCandidateOuterRadius + 1) (k : Fin 15) :
    (fifteen_unit_packing_wall_push_sorted_pattern P hunit hR).toList[k.1]? =
      some (if fifteenPackingSortedRadius P k <
          fifteenCandidateInnerThreshold then '1' else '0') := by
  rw [fifteen_unit_packing_wall_push_sorted_pattern_bit P hunit hR k]
  by_cases h : fifteenPackingSortedRadius P k < fifteenCandidateInnerThreshold
  · have hpush := (fifteen_unit_packing_wall_push_sorted_radius_inner_iff
      P hunit hR k).2 h
    simp [h, hpush]
  · have hpush : ¬ fifteenPackingSortedRadius
      (fifteen_unit_packing_wall_push P hunit hR) k <
        fifteenCandidateInnerThreshold := by
      intro hp
      exact h ((fifteen_unit_packing_wall_push_sorted_radius_inner_iff
        P hunit hR k).1 hp)
    simp [h, hpush]

theorem fifteen_unit_packing_wall_push_sorted_pattern_is_binary
    {R : ℝ} (P : Packing 15 R)
    (hunit : ∀ i, (P.circles i).radius = 1)
    (hR : R ≤ fifteenCandidateOuterRadius + 1) :
    (fifteen_unit_packing_wall_push_sorted_pattern P hunit hR).toList.all
      (fun c => c == '0' || c == '1') = true := by
  unfold fifteen_unit_packing_wall_push_sorted_pattern
  rw [String.toList_ofList, List.all_eq_true, List.forall_mem_ofFn_iff]
  intro k
  by_cases h : fifteenPackingSortedRadius
      (fifteen_unit_packing_wall_push P hunit hR) k < fifteenCandidateInnerThreshold
  · simp [h]
  · simp [h]

/-! The finite Stage 0 list starts at five inner centers.  The wall-push
argument already proves this lower endpoint geometrically: the complementary
wall class has at most ten members.  Keeping this as a packing-level lemma
means later code need not trust a separately supplied bit count. -/
theorem fifteen_unit_packing_wall_push_inner_count_ge_five
    {R : ℝ} (P : Packing 15 R)
    (hunit : ∀ i, (P.circles i).radius = 1)
    (hR : R ≤ fifteenCandidateOuterRadius + 1) :
    5 ≤ (Finset.univ.filter fun k : Fin 15 =>
      fifteenPackingSortedRadius
        (fifteen_unit_packing_wall_push P hunit hR) k <
          fifteenCandidateInnerThreshold).card := by
  classical
  let Q := fifteen_unit_packing_wall_push P hunit hR
  let isInner := fun k : Fin 15 =>
    fifteenPackingSortedRadius Q k < fifteenCandidateInnerThreshold
  let inner : Finset (Fin 15) := Finset.univ.filter isInner
  let outer : Finset (Fin 15) := Finset.univ.filter fun k =>
    fifteenPackingSortedRadius Q k = fifteenCandidateOuterRadius
  have hthreshold : fifteenCandidateInnerThreshold < fifteenCandidateOuterRadius := by
    dsimp [fifteenCandidateInnerThreshold]
    have hb := fifteenCandidateOuterRadius_pos
    have hfrac : 0 < (4 : ℝ) / fifteenCandidateOuterRadius := by positivity
    linarith
  have hnotInner (k : Fin 15) :
      ¬ isInner k ↔
        fifteenPackingSortedRadius Q k = fifteenCandidateOuterRadius := by
    constructor
    · intro hnot
      rcases fifteen_unit_packing_wall_push_sorted_radial_classification
          P hunit hR k with hwall | hsmall
      · exact hwall
      · exact (hnot hsmall).elim
    · intro hwall hsmall
      dsimp [isInner] at hsmall
      rw [hwall] at hsmall
      exact (not_lt_of_ge hthreshold.le) hsmall
  have hnotInnerSet :
      Finset.univ.filter (fun k : Fin 15 => ¬ isInner k) = outer := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    simpa [outer] using hnotInner k
  have hpartition : inner.card + outer.card = 15 := by
    have hcard := Finset.card_filter_add_card_filter_not
      (s := Finset.univ) (p := isInner)
    rw [hnotInnerSet] at hcard
    simpa [inner] using hcard
  have houter : outer.card ≤ 10 := by
    simpa [Q, outer] using
      fifteen_unit_packing_wall_push_outer_count_le_ten P hunit hR
  have hinner : 5 ≤ inner.card := by omega
  simpa [Q, inner, isInner] using hinner

/-- The bit-vector handed to the finite classifier marks exactly the sorted
indices whose pushed centers lie in the inner radial class.  This is the
index-level interface needed to connect geometric occupancy to Stage 0. -/
theorem fifteen_unit_packing_wall_push_pattern_one_positions_eq_inner
    {R : ℝ} (P : Packing 15 R)
    (hunit : ∀ i, (P.circles i).radius = 1)
    (hR : R ≤ fifteenCandidateOuterRadius + 1) :
    (Finset.univ.filter fun k : Fin 15 =>
      (fifteen_unit_packing_wall_push_sorted_pattern P hunit hR).toList[k.1]? =
        some '1') =
    (Finset.univ.filter fun k : Fin 15 =>
      fifteenPackingSortedRadius
        (fifteen_unit_packing_wall_push P hunit hR) k <
          fifteenCandidateInnerThreshold) := by
  classical
  ext k
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [fifteen_unit_packing_wall_push_sorted_pattern_bit P hunit hR k]
  by_cases h : fifteenPackingSortedRadius
      (fifteen_unit_packing_wall_push P hunit hR) k <
        fifteenCandidateInnerThreshold
  · simp [h]
  · simp [h]

/-- At least five `1`-positions occur in the actual wall-pushed pattern.
This states the Stage 0 lower weight bound using the pattern itself, rather
than an independently supplied radial count. -/
theorem fifteen_unit_packing_wall_push_pattern_one_count_ge_five
    {R : ℝ} (P : Packing 15 R)
    (hunit : ∀ i, (P.circles i).radius = 1)
    (hR : R ≤ fifteenCandidateOuterRadius + 1) :
    5 ≤ (Finset.univ.filter fun k : Fin 15 =>
      (fifteen_unit_packing_wall_push_sorted_pattern P hunit hR).toList[k.1]? =
        some '1').card := by
  rw [fifteen_unit_packing_wall_push_pattern_one_positions_eq_inner P hunit hR]
  exact fifteen_unit_packing_wall_push_inner_count_ge_five P hunit hR

/-- The `1`-positions in the exported finite-classifier word are exactly the
original centers below the threshold, in the original angular order. -/
theorem fifteen_unit_packing_wall_push_pattern_original_one_positions_eq_inner
    {R : ℝ} (P : Packing 15 R)
    (hunit : ∀ i, (P.circles i).radius = 1)
    (hR : R ≤ fifteenCandidateOuterRadius + 1) :
    (Finset.univ.filter fun k : Fin 15 =>
      (fifteen_unit_packing_wall_push_sorted_pattern P hunit hR).toList[k.1]? =
        some '1') =
    (Finset.univ.filter fun k : Fin 15 =>
      fifteenPackingSortedRadius P k < fifteenCandidateInnerThreshold) := by
  classical
  ext k
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [fifteen_unit_packing_wall_push_sorted_pattern_original_bit P hunit hR k]
  by_cases h : fifteenPackingSortedRadius P k < fifteenCandidateInnerThreshold
  · simp [h]
  · simp [h]

/-- Consequently the actual packing has at least five centers below the
threshold; this is the Stage 0 lower-weight condition without referring to
the modified packing. -/
theorem fifteen_unit_packing_wall_push_original_inner_count_ge_five
    {R : ℝ} (P : Packing 15 R)
    (hunit : ∀ i, (P.circles i).radius = 1)
    (hR : R ≤ fifteenCandidateOuterRadius + 1) :
    5 ≤ (Finset.univ.filter fun k : Fin 15 =>
      fifteenPackingSortedRadius P k < fifteenCandidateInnerThreshold).card := by
  rw [← fifteen_unit_packing_wall_push_pattern_original_one_positions_eq_inner
    P hunit hR]
  exact fifteen_unit_packing_wall_push_pattern_one_count_ge_five P hunit hR

end CirclePacking
