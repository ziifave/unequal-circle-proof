import CirclePacking.FifteenCandidateDetourCurvature

/-! Kernel-checked rational enclosure of the exact wall radius used by all
refined certificate tables.  No decimal approximation is an assumption. -/

namespace CirclePacking

theorem fifteenCandidateCot_sq_eq_radical :
    (Real.cos fifteenLocalPhi / Real.sin fifteenLocalPhi) ^ 2 =
      1 + (2 / 5 : ℝ) * Real.sqrt 5 := by
  have hc : Real.cos fifteenLocalPhi = (1 + Real.sqrt 5) / 4 := by
    unfold fifteenLocalPhi
    exact Real.cos_pi_div_five
  have hc2 := congrArg (fun z : ℝ => z ^ 2) hc
  have hs2 := fifteenLocalSinSq_eq_radical
  have hden : (5 : ℝ) - Real.sqrt 5 ≠ 0 := by
    intro h
    rw [sub_eq_zero] at h
    nlinarith [fifteenSqrtFive_lt_nine_fourths]
  rw [div_pow, hc2, hs2]
  field_simp [hden]
  nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)]

private theorem fifteenSqrtFive_certificate_enclosure :
    (2236067977499 : ℝ) / 1000000000000 < Real.sqrt 5 ∧
      Real.sqrt 5 < (2236067977500 : ℝ) / 1000000000000 := by
  constructor
  · apply Real.lt_sqrt_of_sq_lt
    norm_num
  · apply (sq_lt_sq₀ (Real.sqrt_nonneg _) (by norm_num)).mp
    rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)]
    norm_num

private theorem fifteenCandidateCot_certificate_enclosure :
    (1376381920471 : ℝ) / 1000000000000 <
        Real.cos fifteenLocalPhi / Real.sin fifteenLocalPhi ∧
      Real.cos fifteenLocalPhi / Real.sin fifteenLocalPhi <
        (1376381920472 : ℝ) / 1000000000000 := by
  have hcpos := div_pos fifteenLocalCos_pos fifteenLocalSin_pos
  have hsqrt := fifteenSqrtFive_certificate_enclosure
  constructor
  · apply (sq_lt_sq₀ (by norm_num) hcpos.le).mp
    rw [fifteenCandidateCot_sq_eq_radical]
    nlinarith [hsqrt.1]
  · apply (sq_lt_sq₀ hcpos.le (by norm_num)).mp
    rw [fifteenCandidateCot_sq_eq_radical]
    nlinarith [hsqrt.2]

/-- The exact candidate wall radius lies strictly between the two rational
endpoints stored in the Stage 3/4 and final subdivision certificates. -/
theorem fifteenCandidateOuterRadius_mem_certificate_interval :
    (35213569647 : ℝ) / 10000000000 < fifteenCandidateOuterRadius ∧
      fifteenCandidateOuterRadius < (35213569648 : ℝ) / 10000000000 := by
  let c := Real.cos fifteenLocalPhi / Real.sin fifteenLocalPhi
  have hc := fifteenCandidateCot_certificate_enclosure
  have hcpos : 0 < c := div_pos fifteenLocalCos_pos fifteenLocalSin_pos
  have hbpos := fifteenCandidateOuterRadius_pos
  constructor
  · apply (sq_lt_sq₀ (by norm_num) hbpos.le).mp
    rw [fifteenCandidateOuterRadius_sq]
    have hsum : 2 + (1376381920471 : ℝ) / 1000000000000 < 2 + c := by
      linarith [hc.1]
    have hsq := (sq_lt_sq₀ (by norm_num) (by linarith : 0 ≤ 2 + c)).2 hsum
    have hrat : ((35213569647 : ℝ) / 10000000000) ^ 2 <
        1 + (2 + (1376381920471 : ℝ) / 1000000000000) ^ 2 := by norm_num
    nlinarith
  · apply (sq_lt_sq₀ hbpos.le (by norm_num)).mp
    rw [fifteenCandidateOuterRadius_sq]
    have hsum : 2 + c < 2 + (1376381920472 : ℝ) / 1000000000000 := by
      linarith [hc.2]
    have hsq := (sq_lt_sq₀ (by linarith : 0 ≤ 2 + c) (by norm_num)).2 hsum
    have hrat : 1 + (2 + (1376381920472 : ℝ) / 1000000000000) ^ 2 <
        ((35213569648 : ℝ) / 10000000000) ^ 2 := by norm_num
    nlinarith

end CirclePacking
