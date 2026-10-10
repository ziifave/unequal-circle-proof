import CirclePacking.FifteenCandidateAngles

/-! Exact identities for the candidate route that passes through the two
wall centers.  The outer radius is the one in the construction in the paper. -/

namespace CirclePacking

noncomputable def fifteenCandidateOuterRadius : ℝ :=
  Real.sqrt (1 +
    (2 + Real.cos fifteenLocalPhi / Real.sin fifteenLocalPhi) ^ 2)

noncomputable def fifteenCandidateWallHalfAngle : ℝ :=
  Real.arcsin (1 / fifteenCandidateOuterRadius)

theorem fifteenCandidateOuterRadius_pos :
    0 < fifteenCandidateOuterRadius := by
  unfold fifteenCandidateOuterRadius
  apply Real.sqrt_pos.2
  positivity

theorem fifteenCandidateOuterRadius_sq :
    fifteenCandidateOuterRadius ^ 2 =
      1 + (2 + Real.cos fifteenLocalPhi / Real.sin fifteenLocalPhi) ^ 2 := by
  unfold fifteenCandidateOuterRadius
  rw [Real.sq_sqrt]
  positivity

/-- The candidate center radius in the conventional cotangent notation. -/
theorem fifteenCandidateOuterRadius_eq_cot_formula :
    fifteenCandidateOuterRadius =
      Real.sqrt (1 + (2 + Real.cot (Real.pi / 5)) ^ 2) := by
  rw [fifteenCandidateOuterRadius, fifteenLocalPhi, Real.cot_eq_cos_div_sin]

theorem fifteenCandidateOuterRadius_gt_one :
    1 < fifteenCandidateOuterRadius := by
  have ht : 0 < 2 + Real.cos fifteenLocalPhi / Real.sin fifteenLocalPhi := by
    have hratio : 0 < Real.cos fifteenLocalPhi / Real.sin fifteenLocalPhi :=
      div_pos fifteenLocalCos_pos fifteenLocalSin_pos
    linarith
  have hrad :
      1 < 1 + (2 + Real.cos fifteenLocalPhi / Real.sin fifteenLocalPhi) ^ 2 := by
    nlinarith [sq_pos_of_pos ht]
  unfold fifteenCandidateOuterRadius
  calc
    (1 : ℝ) = Real.sqrt 1 := by simp
    _ < Real.sqrt
        (1 + (2 + Real.cos fifteenLocalPhi / Real.sin fifteenLocalPhi) ^ 2) :=
      Real.sqrt_lt_sqrt (by norm_num) hrad

theorem fifteenCandidateWallHalfAngle_pos :
    0 < fifteenCandidateWallHalfAngle := by
  unfold fifteenCandidateWallHalfAngle
  apply Real.arcsin_pos.2
  exact one_div_pos.mpr fifteenCandidateOuterRadius_pos

theorem fifteenCandidateWallHalfAngle_lt_localPhi :
    fifteenCandidateWallHalfAngle < fifteenLocalPhi := by
  apply (Real.arcsin_lt_iff_lt_sin
    (by
      constructor
      · have hb := one_div_pos.mpr fifteenCandidateOuterRadius_pos
        linarith
      · rw [div_le_one fifteenCandidateOuterRadius_pos]
        exact fifteenCandidateOuterRadius_gt_one.le)
    (by
      constructor
      · unfold fifteenLocalPhi
        nlinarith [Real.pi_pos]
      · exact fifteenLocalPhi_lt_pi_div_two.le)).2
  have hs : Real.sin fifteenLocalPhi ≠ 0 := fifteenLocalSin_pos.ne'
  have hb := fifteenCandidateOuterRadius_sq
  have hbsq :
      (fifteenCandidateOuterRadius * Real.sin fifteenLocalPhi) ^ 2 =
        1 + 4 * Real.sin fifteenLocalPhi ^ 2 +
          4 * Real.sin fifteenLocalPhi * Real.cos fifteenLocalPhi := by
    have htrig := Real.sin_sq_add_cos_sq fifteenLocalPhi
    calc
      (fifteenCandidateOuterRadius * Real.sin fifteenLocalPhi) ^ 2 =
          fifteenCandidateOuterRadius ^ 2 * Real.sin fifteenLocalPhi ^ 2 := by ring
      _ = (1 + (2 + Real.cos fifteenLocalPhi / Real.sin fifteenLocalPhi) ^ 2) *
          Real.sin fifteenLocalPhi ^ 2 := by rw [fifteenCandidateOuterRadius_sq]
      _ = 1 + 4 * Real.sin fifteenLocalPhi ^ 2 +
          4 * Real.sin fifteenLocalPhi * Real.cos fifteenLocalPhi := by
        have hs' : Real.sin fifteenLocalPhi ≠ 0 := hs
        field_simp [hs']
        nlinarith [htrig]
  have hprod :
      1 < fifteenCandidateOuterRadius * Real.sin fifteenLocalPhi := by
    have hsq :
        1 < (fifteenCandidateOuterRadius * Real.sin fifteenLocalPhi) ^ 2 := by
      rw [hbsq]
      nlinarith [sq_pos_of_pos fifteenLocalSin_pos,
        mul_pos fifteenLocalSin_pos fifteenLocalCos_pos]
    have hpos := mul_pos fifteenCandidateOuterRadius_pos fifteenLocalSin_pos
    nlinarith
  rw [div_lt_iff₀ fifteenCandidateOuterRadius_pos]
  nlinarith [hprod]

theorem fifteenCandidateWallHalfAngle_sin :
    Real.sin fifteenCandidateWallHalfAngle =
      1 / fifteenCandidateOuterRadius := by
  unfold fifteenCandidateWallHalfAngle
  apply Real.sin_arcsin
  · have hb := one_div_pos.mpr fifteenCandidateOuterRadius_pos
    linarith
  · rw [div_le_one fifteenCandidateOuterRadius_pos]
    exact fifteenCandidateOuterRadius_gt_one.le

theorem fifteenCandidateWallHalfAngle_cos :
    Real.cos fifteenCandidateWallHalfAngle =
      (2 + Real.cos fifteenLocalPhi / Real.sin fifteenLocalPhi) /
        fifteenCandidateOuterRadius := by
  rw [fifteenCandidateWallHalfAngle, Real.cos_arcsin]
  have hb := fifteenCandidateOuterRadius_sq
  have hrad :
      1 - (1 / fifteenCandidateOuterRadius) ^ 2 =
        ((2 + Real.cos fifteenLocalPhi / Real.sin fifteenLocalPhi) /
          fifteenCandidateOuterRadius) ^ 2 := by
    have hne := fifteenCandidateOuterRadius_pos.ne'
    field_simp [hne]
    rw [fifteenCandidateOuterRadius_sq]
    ring
  rw [hrad, Real.sqrt_sq_eq_abs]
  rw [abs_of_pos]
  exact div_pos (by
    have hratio := div_pos fifteenLocalCos_pos fifteenLocalSin_pos
    linarith) fifteenCandidateOuterRadius_pos

theorem fifteenCandidateMixedAngleCosineArgument_eq :
    fifteenAngleCosineArgument fifteenCandidateInnerRadius
        fifteenCandidateOuterRadius =
      Real.cos (fifteenLocalPhi - fifteenCandidateWallHalfAngle) := by
  rw [Real.cos_sub, fifteenCandidateWallHalfAngle_cos,
    fifteenCandidateWallHalfAngle_sin]
  unfold fifteenAngleCosineArgument fifteenCandidateInnerRadius
  have hs : Real.sin fifteenLocalPhi ≠ 0 := fifteenLocalSin_pos.ne'
  have hb := fifteenCandidateOuterRadius_sq
  field_simp [hs, fifteenCandidateOuterRadius_pos.ne']
  rw [fifteenCandidateOuterRadius_sq]
  field_simp [hs]
  nlinarith [Real.sin_sq_add_cos_sq fifteenLocalPhi]

theorem fifteenCandidateWallCosineArgument_eq :
    fifteenAngleCosineArgument fifteenCandidateOuterRadius
        fifteenCandidateOuterRadius =
      Real.cos (2 * fifteenCandidateWallHalfAngle) := by
  rw [Real.cos_two_mul, fifteenCandidateWallHalfAngle_cos]
  unfold fifteenAngleCosineArgument
  have hb := fifteenCandidateOuterRadius_pos.ne'
  field_simp [hb]
  rw [fifteenCandidateOuterRadius_sq]
  ring

theorem fifteenCandidateMixedTouchAngle_eq :
    fifteenTouchAngle fifteenCandidateInnerRadius
        fifteenCandidateOuterRadius =
      fifteenLocalPhi - fifteenCandidateWallHalfAngle := by
  unfold fifteenTouchAngle
  rw [fifteenCandidateMixedAngleCosineArgument_eq]
  apply Real.arccos_cos
  · linarith [fifteenCandidateWallHalfAngle_lt_localPhi]
  · have hu : 0 ≤ fifteenCandidateWallHalfAngle :=
      le_of_lt fifteenCandidateWallHalfAngle_pos
    linarith [fifteenLocalPhi_lt_pi]

theorem fifteenCandidateWallTouchAngle_eq :
    fifteenTouchAngle fifteenCandidateOuterRadius
        fifteenCandidateOuterRadius =
      2 * fifteenCandidateWallHalfAngle := by
  unfold fifteenTouchAngle
  rw [fifteenCandidateWallCosineArgument_eq]
  apply Real.arccos_cos
  · linarith [fifteenCandidateWallHalfAngle_pos]
  · have hu := Real.arcsin_le_pi_div_two
      (1 / fifteenCandidateOuterRadius)
    unfold fifteenCandidateWallHalfAngle
    linarith [Real.pi_pos]

theorem fifteenCandidateDetourBase_eq :
    fifteenDetourAngle fifteenCandidateOuterRadius
      fifteenCandidateInnerRadius fifteenCandidateInnerRadius =
        2 * fifteenLocalPhi := by
  unfold fifteenDetourAngle
  rw [fifteenCandidateMixedTouchAngle_eq,
    fifteenCandidateWallTouchAngle_eq]
  ring

theorem fifteenCandidateMixedAngleSqrt_eq :
    Real.sqrt (1 -
      fifteenAngleCosineArgument fifteenCandidateInnerRadius
        fifteenCandidateOuterRadius ^ 2) =
      Real.sin (fifteenLocalPhi - fifteenCandidateWallHalfAngle) := by
  rw [fifteenCandidateMixedAngleCosineArgument_eq]
  have hangle :
      0 < fifteenLocalPhi - fifteenCandidateWallHalfAngle ∧
      fifteenLocalPhi - fifteenCandidateWallHalfAngle < Real.pi := by
    constructor
    · linarith [fifteenCandidateWallHalfAngle_lt_localPhi]
    · have hu : 0 ≤ fifteenCandidateWallHalfAngle :=
        le_of_lt fifteenCandidateWallHalfAngle_pos
      linarith [fifteenLocalPhi_lt_pi]
  have hsin :
      0 < Real.sin (fifteenLocalPhi - fifteenCandidateWallHalfAngle) :=
    Real.sin_pos_of_pos_of_lt_pi hangle.1 hangle.2
  have htrig := Real.sin_sq_add_cos_sq
    (fifteenLocalPhi - fifteenCandidateWallHalfAngle)
  have hroot :
      1 - Real.cos (fifteenLocalPhi - fifteenCandidateWallHalfAngle) ^ 2 =
        Real.sin (fifteenLocalPhi - fifteenCandidateWallHalfAngle) ^ 2 := by
    nlinarith
  rw [hroot, Real.sqrt_sq_eq_abs, abs_of_pos hsin]

theorem fifteenCandidateMixedAngleSin_eq :
    Real.sin (fifteenLocalPhi - fifteenCandidateWallHalfAngle) =
      2 * Real.sin fifteenLocalPhi / fifteenCandidateOuterRadius := by
  rw [Real.sin_sub, fifteenCandidateWallHalfAngle_cos,
    fifteenCandidateWallHalfAngle_sin]
  have hs : Real.sin fifteenLocalPhi ≠ 0 := fifteenLocalSin_pos.ne'
  field_simp [hs, fifteenCandidateOuterRadius_pos.ne']
  ring

theorem fifteenCandidateDetourNumerator_eq :
    (fifteenCandidateInnerRadius ^ 2 - fifteenCandidateOuterRadius ^ 2 + 4) /
        (2 * fifteenCandidateInnerRadius ^ 2 * fifteenCandidateOuterRadius) =
      -2 * Real.sin fifteenLocalPhi * Real.cos fifteenLocalPhi /
        fifteenCandidateOuterRadius := by
  unfold fifteenCandidateInnerRadius
  have hs : Real.sin fifteenLocalPhi ≠ 0 := fifteenLocalSin_pos.ne'
  field_simp [hs, fifteenCandidateOuterRadius_pos.ne']
  rw [fifteenCandidateOuterRadius_sq]
  field_simp [hs]
  nlinarith [Real.sin_sq_add_cos_sq fifteenLocalPhi]

theorem fifteenCandidateDetourSlope_eq :
    fifteenDetourSlope fifteenCandidateInnerRadius
        fifteenCandidateOuterRadius =
      fifteenCandidateDetourCoefficient := by
  unfold fifteenDetourSlope fifteenCandidateDetourCoefficient
  rw [fifteenCandidateMixedAngleSqrt_eq,
    fifteenCandidateDetourNumerator_eq,
    fifteenCandidateMixedAngleSin_eq]
  have hs : Real.sin fifteenLocalPhi ≠ 0 := fifteenLocalSin_pos.ne'
  have hb : fifteenCandidateOuterRadius ≠ 0 :=
    fifteenCandidateOuterRadius_pos.ne'
  field_simp [hs, hb]

end CirclePacking
