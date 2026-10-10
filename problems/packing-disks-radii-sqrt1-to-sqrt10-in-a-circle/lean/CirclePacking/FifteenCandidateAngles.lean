import CirclePacking.FifteenLocalBarrierAnalytic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

/-! Exact trigonometric identities at the conjectured five-fold symmetric
inner radius.  These identify the direct contact angle and its first-order
coefficient with the constants used by the local barrier. -/

namespace CirclePacking

noncomputable def fifteenLocalPhi : ℝ := Real.pi / 5

noncomputable def fifteenCandidateInnerRadius : ℝ :=
  1 / Real.sin fifteenLocalPhi

noncomputable def fifteenCandidateDirectCoefficient : ℝ :=
  Real.sin fifteenLocalPhi ^ 2 / Real.cos fifteenLocalPhi

noncomputable def fifteenCandidateDetourCoefficient : ℝ :=
  Real.cos fifteenLocalPhi

theorem fifteenLocalPhi_pos : 0 < fifteenLocalPhi := by
  unfold fifteenLocalPhi
  positivity

theorem fifteenLocalPhi_lt_pi : fifteenLocalPhi < Real.pi := by
  unfold fifteenLocalPhi
  nlinarith [Real.pi_pos]

theorem fifteenLocalPhi_lt_pi_div_two :
    fifteenLocalPhi < Real.pi / 2 := by
  unfold fifteenLocalPhi
  nlinarith [Real.pi_pos]

theorem fifteenLocalSin_pos : 0 < Real.sin fifteenLocalPhi :=
  Real.sin_pos_of_pos_of_lt_pi fifteenLocalPhi_pos fifteenLocalPhi_lt_pi

theorem fifteenLocalCos_pos : 0 < Real.cos fifteenLocalPhi := by
  apply Real.cos_pos_of_mem_Ioo
  constructor
  · unfold fifteenLocalPhi
    nlinarith [Real.pi_pos]
  · exact fifteenLocalPhi_lt_pi_div_two

theorem fifteenCandidateInnerRadius_pos : 0 < fifteenCandidateInnerRadius := by
  unfold fifteenCandidateInnerRadius
  exact div_pos one_pos fifteenLocalSin_pos

theorem fifteenCandidateAngleCosineArgument_eq :
    fifteenAngleCosineArgument fifteenCandidateInnerRadius
        fifteenCandidateInnerRadius = Real.cos (2 * fifteenLocalPhi) := by
  unfold fifteenAngleCosineArgument fifteenCandidateInnerRadius
  have hs : Real.sin fifteenLocalPhi ≠ 0 := fifteenLocalSin_pos.ne'
  field_simp [hs]
  rw [Real.cos_two_mul]
  nlinarith [Real.sin_sq_add_cos_sq fifteenLocalPhi]

theorem fifteenCandidateDirectAngle_eq :
    fifteenTouchAngle fifteenCandidateInnerRadius
        fifteenCandidateInnerRadius = 2 * fifteenLocalPhi := by
  unfold fifteenTouchAngle
  rw [fifteenCandidateAngleCosineArgument_eq]
  apply Real.arccos_cos
  · unfold fifteenLocalPhi
    nlinarith [Real.pi_pos]
  · unfold fifteenLocalPhi
    nlinarith [Real.pi_pos]

theorem fifteenCandidateDoubleAngleSin_pos :
    0 < Real.sin (2 * fifteenLocalPhi) := by
  apply Real.sin_pos_of_pos_of_lt_pi
  · unfold fifteenLocalPhi
    nlinarith [Real.pi_pos]
  · unfold fifteenLocalPhi
    nlinarith [Real.pi_pos]

theorem fifteenCandidateAngleCosineArgument_ne_neg_one :
    fifteenAngleCosineArgument fifteenCandidateInnerRadius
        fifteenCandidateInnerRadius ≠ -1 := by
  intro h
  rw [fifteenCandidateAngleCosineArgument_eq] at h
  have hsquare := Real.sin_sq_add_cos_sq (2 * fifteenLocalPhi)
  have hsin : 0 < Real.sin (2 * fifteenLocalPhi) :=
    fifteenCandidateDoubleAngleSin_pos
  nlinarith

theorem fifteenCandidateAngleCosineArgument_ne_one :
    fifteenAngleCosineArgument fifteenCandidateInnerRadius
        fifteenCandidateInnerRadius ≠ 1 := by
  intro h
  rw [fifteenCandidateAngleCosineArgument_eq] at h
  have hsquare := Real.sin_sq_add_cos_sq (2 * fifteenLocalPhi)
  have hsin : 0 < Real.sin (2 * fifteenLocalPhi) :=
    fifteenCandidateDoubleAngleSin_pos
  nlinarith

theorem fifteenCandidateAngleCosineSqrt_eq :
    Real.sqrt (1 -
      fifteenAngleCosineArgument fifteenCandidateInnerRadius
        fifteenCandidateInnerRadius ^ 2) =
      Real.sin (2 * fifteenLocalPhi) := by
  rw [fifteenCandidateAngleCosineArgument_eq]
  have htrig := Real.sin_sq_add_cos_sq (2 * fifteenLocalPhi)
  have hroot :
      1 - Real.cos (2 * fifteenLocalPhi) ^ 2 =
        Real.sin (2 * fifteenLocalPhi) ^ 2 := by
    nlinarith
  rw [hroot, Real.sqrt_sq_eq_abs, abs_of_pos fifteenCandidateDoubleAngleSin_pos]

theorem fifteenCandidateDirectNumerator_eq :
    (fifteenCandidateInnerRadius ^ 2 - fifteenCandidateInnerRadius ^ 2 + 4) /
        (2 * fifteenCandidateInnerRadius ^ 2 * fifteenCandidateInnerRadius) =
      2 * Real.sin fifteenLocalPhi ^ 3 := by
  unfold fifteenCandidateInnerRadius
  have hs : Real.sin fifteenLocalPhi ≠ 0 := fifteenLocalSin_pos.ne'
  field_simp [hs]
  ring

theorem fifteenCandidateDirectSlopeLeft_eq :
    fifteenDirectSlopeLeft fifteenCandidateInnerRadius =
      -fifteenCandidateDirectCoefficient := by
  unfold fifteenDirectSlopeLeft fifteenCandidateDirectCoefficient
  rw [fifteenCandidateAngleCosineSqrt_eq, fifteenCandidateDirectNumerator_eq]
  rw [Real.sin_two_mul]
  have hs : Real.sin fifteenLocalPhi ≠ 0 := fifteenLocalSin_pos.ne'
  have hc : Real.cos fifteenLocalPhi ≠ 0 := fifteenLocalCos_pos.ne'
  field_simp [hs, hc]

theorem fifteenCandidateDirectSlopeRight_eq :
    fifteenDirectSlopeRight fifteenCandidateInnerRadius =
      -fifteenCandidateDirectCoefficient := by
  unfold fifteenDirectSlopeRight fifteenCandidateDirectCoefficient
  rw [fifteenCandidateAngleCosineSqrt_eq]
  have hnum :
      (fifteenCandidateInnerRadius ^ 2 - fifteenCandidateInnerRadius ^ 2 + 4) /
          (2 * fifteenCandidateInnerRadius * fifteenCandidateInnerRadius ^ 2) =
        2 * Real.sin fifteenLocalPhi ^ 3 := by
    unfold fifteenCandidateInnerRadius
    have hs : Real.sin fifteenLocalPhi ≠ 0 := fifteenLocalSin_pos.ne'
    field_simp [hs]
    ring
  rw [hnum, Real.sin_two_mul]
  have hs : Real.sin fifteenLocalPhi ≠ 0 := fifteenLocalSin_pos.ne'
  have hc : Real.cos fifteenLocalPhi ≠ 0 := fifteenLocalCos_pos.ne'
  field_simp [hs, hc]

theorem fifteenCandidateDirectCoefficient_eq_radical :
    fifteenCandidateDirectCoefficient = (3 * Real.sqrt 5 - 5) / 4 := by
  unfold fifteenCandidateDirectCoefficient fifteenLocalPhi
  rw [Real.cos_pi_div_five]
  have htrig := Real.sin_sq_add_cos_sq (Real.pi / 5)
  rw [Real.cos_pi_div_five] at htrig
  have hc : (1 + Real.sqrt 5) / 4 ≠ 0 := by positivity
  field_simp [hc]
  have hsqrt := Real.sq_sqrt (show 0 ≤ (5 : ℝ) by norm_num)
  nlinarith [htrig, hsqrt]

theorem fifteenCandidateDirectCoefficient_gt_21_50 :
    (21 : ℝ) / 50 < fifteenCandidateDirectCoefficient := by
  rw [fifteenCandidateDirectCoefficient_eq_radical]
  have hroot := Real.sq_sqrt (show 0 ≤ (5 : ℝ) by norm_num)
  have hlower : (67 : ℝ) / 30 < Real.sqrt 5 := by
    have hsq : ((67 : ℝ) / 30) ^ 2 < (Real.sqrt 5) ^ 2 := by
      rw [hroot]
      norm_num
    have hsqrtpos : 0 < Real.sqrt 5 := Real.sqrt_pos.2 (by norm_num)
    nlinarith
  nlinarith

theorem fifteenCandidateDetourCoefficient_gt_direct :
    fifteenCandidateDirectCoefficient < fifteenCandidateDetourCoefficient := by
  rw [fifteenCandidateDirectCoefficient_eq_radical]
  unfold fifteenCandidateDetourCoefficient fifteenLocalPhi
  rw [Real.cos_pi_div_five]
  have hroot := Real.sq_sqrt (show 0 ≤ (5 : ℝ) by norm_num)
  have hsqrt_lt : Real.sqrt 5 < 3 := by
    have hsqrt_nonneg : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
    nlinarith
  nlinarith

end CirclePacking
