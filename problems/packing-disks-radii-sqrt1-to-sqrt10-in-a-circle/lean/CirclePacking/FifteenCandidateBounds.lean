import CirclePacking.FifteenCandidateDetour
import Mathlib.Analysis.Real.Sqrt

/-! Rational enclosures for the candidate inner radius, connecting the exact
five-fold-symmetric construction with the surviving local box. -/

namespace CirclePacking

theorem fifteenLocalSinSq_eq_radical :
    Real.sin fifteenLocalPhi ^ 2 = (5 - Real.sqrt 5) / 8 := by
  have htrig := Real.sin_sq_add_cos_sq fifteenLocalPhi
  have hcos : Real.cos fifteenLocalPhi = (1 + Real.sqrt 5) / 4 := by
    unfold fifteenLocalPhi
    exact Real.cos_pi_div_five
  rw [hcos] at htrig
  have hsqrt := Real.sq_sqrt (show 0 ≤ (5 : ℝ) by norm_num)
  nlinarith [htrig, hsqrt]

theorem fifteenCandidateInnerRadius_sq_eq_radical :
    fifteenCandidateInnerRadius ^ 2 = 2 + (2 / 5 : ℝ) * Real.sqrt 5 := by
  have hs : Real.sin fifteenLocalPhi ≠ 0 := fifteenLocalSin_pos.ne'
  have hsin := fifteenLocalSinSq_eq_radical
  have hsqrt := Real.sq_sqrt (show 0 ≤ (5 : ℝ) by norm_num)
  have hden : (5 : ℝ) - Real.sqrt 5 ≠ 0 := by
    intro h
    rw [sub_eq_zero] at h
    nlinarith
  unfold fifteenCandidateInnerRadius
  rw [div_pow, hsin]
  field_simp [hden]
  nlinarith [hsqrt]

theorem fifteenSqrtFive_gt_eleven_fifths :
    (11 : ℝ) / 5 < Real.sqrt 5 := by
  apply Real.lt_sqrt_of_sq_lt
  norm_num

theorem fifteenSqrtFive_lt_nine_fourths :
    Real.sqrt 5 < (9 : ℝ) / 4 := by
  have h := Real.sqrt_lt_sqrt (show 0 ≤ (5 : ℝ) by norm_num)
    (show (5 : ℝ) < ((9 : ℝ) / 4) ^ 2 by norm_num)
  rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (by positivity)] at h
  exact h

theorem fifteenCandidateInnerRadius_sq_gt_42_25_sq :
    ((42 : ℝ) / 25) ^ 2 < fifteenCandidateInnerRadius ^ 2 := by
  rw [fifteenCandidateInnerRadius_sq_eq_radical]
  nlinarith [fifteenSqrtFive_gt_eleven_fifths]

theorem fifteenCandidateInnerRadius_sq_lt_43_25_sq :
    fifteenCandidateInnerRadius ^ 2 < ((43 : ℝ) / 25) ^ 2 := by
  rw [fifteenCandidateInnerRadius_sq_eq_radical]
  nlinarith [fifteenSqrtFive_lt_nine_fourths]

theorem fifteenCandidateInnerRadius_gt_42_25 :
    (42 : ℝ) / 25 < fifteenCandidateInnerRadius := by
  rw [← sq_lt_sq₀ (by positivity)
    (le_of_lt fifteenCandidateInnerRadius_pos)]
  exact fifteenCandidateInnerRadius_sq_gt_42_25_sq

theorem fifteenCandidateInnerRadius_lt_43_25 :
    fifteenCandidateInnerRadius < (43 : ℝ) / 25 := by
  rw [← sq_lt_sq₀ (le_of_lt fifteenCandidateInnerRadius_pos)
    (by positivity)]
  exact fifteenCandidateInnerRadius_sq_lt_43_25_sq

theorem fifteenCandidateInnerRadius_mem_local_interval :
    fifteenCandidateInnerRadius ∈ Set.Icc (42 / 25 : ℝ) (43 / 25) :=
  ⟨le_of_lt fifteenCandidateInnerRadius_gt_42_25,
    le_of_lt fifteenCandidateInnerRadius_lt_43_25⟩

end CirclePacking
