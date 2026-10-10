import CirclePacking.FifteenCandidateCurvature

/-! A rational second-derivative certificate for the two mixed contacts in the
wall detour.  Together with the direct-contact estimate, this closes the
quantitative curvature inputs to the local five-cycle lemma. -/

namespace CirclePacking

private theorem fifteenSqrtFive_gt_2236_1000 :
    (2236 : ℝ) / 1000 < Real.sqrt 5 := by
  apply Real.lt_sqrt_of_sq_lt
  norm_num

private theorem fifteenSqrtFive_lt_2237_1000 :
    Real.sqrt 5 < (2237 : ℝ) / 1000 := by
  have hs := Real.sqrt_lt_sqrt (show (0 : ℝ) ≤ 5 by norm_num)
    (show (5 : ℝ) < ((2237 : ℝ) / 1000) ^ 2 by norm_num)
  rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (by norm_num)] at hs
  exact hs

private theorem fifteenCandidateCot_sq_eq :
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

private theorem fifteenCandidateCot_mem_Ioo :
    (1376 : ℝ) / 1000 <
        Real.cos fifteenLocalPhi / Real.sin fifteenLocalPhi ∧
      Real.cos fifteenLocalPhi / Real.sin fifteenLocalPhi <
        (1377 : ℝ) / 1000 := by
  have hcot2 := fifteenCandidateCot_sq_eq
  have hcotPos : 0 < Real.cos fifteenLocalPhi / Real.sin fifteenLocalPhi :=
    div_pos fifteenLocalCos_pos fifteenLocalSin_pos
  have hcotLoSq : ((1376 : ℝ) / 1000) ^ 2 <
      (Real.cos fifteenLocalPhi / Real.sin fifteenLocalPhi) ^ 2 := by
    rw [hcot2]
    nlinarith [fifteenSqrtFive_gt_2236_1000]
  have hcotHiSq :
      (Real.cos fifteenLocalPhi / Real.sin fifteenLocalPhi) ^ 2 <
        ((1377 : ℝ) / 1000) ^ 2 := by
    rw [hcot2]
    nlinarith [fifteenSqrtFive_lt_2237_1000]
  exact ⟨(sq_lt_sq₀ (by norm_num) (le_of_lt hcotPos)).mp hcotLoSq,
    (sq_lt_sq₀ (le_of_lt hcotPos) (by norm_num)).mp hcotHiSq⟩

theorem fifteenCandidateOuterRadius_mem_Ioo_352_353 :
    (352 : ℝ) / 100 < fifteenCandidateOuterRadius ∧
      fifteenCandidateOuterRadius < (353 : ℝ) / 100 := by
  have hcot := fifteenCandidateCot_mem_Ioo
  have hqPos : 0 < 2 + Real.cos fifteenLocalPhi / Real.sin fifteenLocalPhi := by
    have hcp := div_pos fifteenLocalCos_pos fifteenLocalSin_pos
    linarith
  have hqLo : (3376 : ℝ) / 1000 <
      2 + Real.cos fifteenLocalPhi / Real.sin fifteenLocalPhi := by
    linarith [hcot.1]
  have hqHi : 2 + Real.cos fifteenLocalPhi / Real.sin fifteenLocalPhi <
      (3377 : ℝ) / 1000 := by
    linarith [hcot.2]
  have hqSqLo : ((3376 : ℝ) / 1000) ^ 2 <
      (2 + Real.cos fifteenLocalPhi / Real.sin fifteenLocalPhi) ^ 2 :=
    (sq_lt_sq₀ (by norm_num) (le_of_lt hqPos)).2 hqLo
  have hqSqHi :
      (2 + Real.cos fifteenLocalPhi / Real.sin fifteenLocalPhi) ^ 2 <
        ((3377 : ℝ) / 1000) ^ 2 :=
    (sq_lt_sq₀ (le_of_lt hqPos) (by norm_num)).2 hqHi
  have hbSq := fifteenCandidateOuterRadius_sq
  have hbPos := fifteenCandidateOuterRadius_pos
  constructor
  · apply (sq_lt_sq₀ (by norm_num) (le_of_lt hbPos)).mp
    rw [hbSq]
    nlinarith [hqSqLo]
  · have hbSqHi : fifteenCandidateOuterRadius ^ 2 <
        ((353 : ℝ) / 100) ^ 2 := by
      rw [hbSq]
      nlinarith [hqSqHi]
    exact (sq_lt_sq₀ (le_of_lt hbPos) (by norm_num)).mp hbSqHi

/-- A tighter rational upper bound places the candidate wall radius inside
the outer radial interval used by the stage-zero angular table. -/
theorem fifteenCandidateOuterRadius_lt_3522_1000 :
    fifteenCandidateOuterRadius < (3522 : ℝ) / 1000 := by
  have hcot2 := fifteenCandidateCot_sq_eq
  have hcotPos : 0 < Real.cos fifteenLocalPhi / Real.sin fifteenLocalPhi :=
    div_pos fifteenLocalCos_pos fifteenLocalSin_pos
  have hcotSqHi :
      (Real.cos fifteenLocalPhi / Real.sin fifteenLocalPhi) ^ 2 <
        ((1377 : ℝ) / 1000) ^ 2 := by
    rw [hcot2]
    nlinarith [fifteenSqrtFive_lt_2237_1000]
  have hcotHi : Real.cos fifteenLocalPhi / Real.sin fifteenLocalPhi <
      (1377 : ℝ) / 1000 :=
    (sq_lt_sq₀ (le_of_lt hcotPos) (by norm_num)).mp hcotSqHi
  have hqPos : 0 < 2 + Real.cos fifteenLocalPhi / Real.sin fifteenLocalPhi := by
    linarith
  have hqHi : 2 + Real.cos fifteenLocalPhi / Real.sin fifteenLocalPhi <
      (3377 : ℝ) / 1000 := by linarith
  have hqSqHi :
      (2 + Real.cos fifteenLocalPhi / Real.sin fifteenLocalPhi) ^ 2 <
        ((3377 : ℝ) / 1000) ^ 2 :=
    (sq_lt_sq₀ (le_of_lt hqPos) (by norm_num)).2 hqHi
  have hbPos := fifteenCandidateOuterRadius_pos
  have hbSq := fifteenCandidateOuterRadius_sq
  have hbSqHi : fifteenCandidateOuterRadius ^ 2 < ((3522 : ℝ) / 1000) ^ 2 := by
    rw [hbSq]
    nlinarith [hqSqHi]
  exact (sq_lt_sq₀ (le_of_lt hbPos) (by norm_num)).mp hbSqHi

private theorem fifteenSqrtFive_lt_2236067978_1e9 :
    Real.sqrt 5 < (2236067978 : ℝ) / 1000000000 := by
  have hs := Real.sqrt_lt_sqrt (show (0 : ℝ) ≤ 5 by norm_num)
    (show (5 : ℝ) < ((2236067978 : ℝ) / 1000000000) ^ 2 by norm_num)
  rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (by norm_num)] at hs
  exact hs

/-- A tighter rational enclosure of the candidate wall radius.  The Stage 0
inner radial box ends at `2385432/1000000`, so the coarse `3.522` bound is not
strong enough for the packing-to-box classification. -/
theorem fifteenCandidateOuterRadius_lt_3521357_1e6 :
    fifteenCandidateOuterRadius < (3521357 : ℝ) / 1000000 := by
  let c := Real.cos fifteenLocalPhi / Real.sin fifteenLocalPhi
  have hcpos : 0 < c := by
    dsimp [c]
    exact div_pos fifteenLocalCos_pos fifteenLocalSin_pos
  have hcSq := fifteenCandidateCot_sq_eq
  have hcUpperSq : c ^ 2 < ((1376381921 : ℝ) / 1000000000) ^ 2 := by
    dsimp [c]
    rw [fifteenCandidateCot_sq_eq]
    nlinarith [fifteenSqrtFive_lt_2236067978_1e9]
  have hcUpper : c < (1376381921 : ℝ) / 1000000000 :=
    (sq_lt_sq₀ (le_of_lt hcpos) (by norm_num)).mp hcUpperSq
  have hsum : 0 < 2 + c := by linarith
  have hsumUpper : 2 + c < 2 + (1376381921 : ℝ) / 1000000000 := by
    linarith
  have hsumSq := (sq_lt_sq₀ (le_of_lt hsum) (by norm_num)).2 hsumUpper
  have hBpos := fifteenCandidateOuterRadius_pos
  have hBsq : fifteenCandidateOuterRadius ^ 2 <
      ((3521357 : ℝ) / 1000000) ^ 2 := by
    rw [fifteenCandidateOuterRadius_sq]
    have htarget :
        1 + (2 + (1376381921 : ℝ) / 1000000000) ^ 2 <
          ((3521357 : ℝ) / 1000000) ^ 2 := by norm_num
    nlinarith [hsumSq, htarget]
  exact (sq_lt_sq₀ (le_of_lt hBpos) (by norm_num)).mp hBsq

/-- The wall-push threshold lies inside the certified Stage 0 outer edge of
the type-3 radial box. -/
theorem fifteenCandidateInnerThreshold_lt_2385432_1e6 :
    fifteenCandidateOuterRadius - 4 / fifteenCandidateOuterRadius <
      (2385432 : ℝ) / 1000000 := by
  have hbpos := fifteenCandidateOuterRadius_pos
  have hupper := fifteenCandidateOuterRadius_lt_3521357_1e6
  have huPos : 0 < (3521357 : ℝ) / 1000000 := by norm_num
  have hrecip : 4 / ((3521357 : ℝ) / 1000000) <
      4 / fifteenCandidateOuterRadius := by
    apply (div_lt_div_iff₀ huPos hbpos).2
    nlinarith
  calc
    fifteenCandidateOuterRadius - 4 / fifteenCandidateOuterRadius <
        (3521357 : ℝ) / 1000000 - 4 / fifteenCandidateOuterRadius :=
      sub_lt_sub_right hupper _
    _ < (3521357 : ℝ) / 1000000 -
        4 / ((3521357 : ℝ) / 1000000) := by linarith
    _ < (2385432 : ℝ) / 1000000 := by norm_num

private theorem fifteenCandidateMixedCap_mem_Ioo
    {x : ℝ} (hxlo : (839 : ℝ) / 500 < x)
    (hxhi : x < (862 : ℝ) / 500) :
    0 < fifteenAngleCosineArgument x fifteenCandidateOuterRadius ∧
      fifteenAngleCosineArgument x fifteenCandidateOuterRadius <
        (191 : ℝ) / 200 := by
  have hb := fifteenCandidateOuterRadius_mem_Ioo_352_353
  have hxlo' : (839 : ℝ) / 500 ≤ x := le_of_lt hxlo
  have hxhi' : x ≤ (862 : ℝ) / 500 := le_of_lt hxhi
  have hblo' : (352 : ℝ) / 100 ≤ fifteenCandidateOuterRadius :=
    le_of_lt hb.1
  have hbhi' : fifteenCandidateOuterRadius ≤ (353 : ℝ) / 100 :=
    le_of_lt hb.2
  have hxSqLo : ((839 : ℝ) / 500) ^ 2 < x ^ 2 :=
    (sq_lt_sq₀ (by norm_num) (by positivity)).2 hxlo
  have hbSqLo : ((352 : ℝ) / 100) ^ 2 < fifteenCandidateOuterRadius ^ 2 :=
    (sq_lt_sq₀ (by norm_num) (by positivity)).2 hb.1
  have hden : 0 < 2 * x * fifteenCandidateOuterRadius := by positivity
  have hnumPos : 0 < x ^ 2 + fifteenCandidateOuterRadius ^ 2 - 4 := by
    nlinarith
  have hFmaxX :
      x + (839 : ℝ) / 500 - (191 / 100 : ℝ) * fifteenCandidateOuterRadius < 0 := by
    nlinarith [hxhi', hblo']
  have hFmaxB :
      0 < fifteenCandidateOuterRadius + (353 : ℝ) / 100 -
        (191 / 100 : ℝ) * ((839 : ℝ) / 500) := by
    nlinarith [hblo']
  have hFidentity :
      x ^ 2 + fifteenCandidateOuterRadius ^ 2 - 4 -
          (191 / 100 : ℝ) * x * fifteenCandidateOuterRadius =
        (((839 : ℝ) / 500) ^ 2 + ((353 : ℝ) / 100) ^ 2 - 4 -
            (191 / 100 : ℝ) * ((839 : ℝ) / 500) * ((353 : ℝ) / 100)) +
          (x - (839 : ℝ) / 500) *
            (x + (839 : ℝ) / 500 - (191 / 100 : ℝ) * fifteenCandidateOuterRadius) +
          (fifteenCandidateOuterRadius - (353 : ℝ) / 100) *
            (fifteenCandidateOuterRadius + (353 : ℝ) / 100 -
              (191 / 100 : ℝ) * ((839 : ℝ) / 500)) := by
    ring
  have htermX :
      (x - (839 : ℝ) / 500) *
          (x + (839 : ℝ) / 500 - (191 / 100 : ℝ) * fifteenCandidateOuterRadius) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by linarith) (le_of_lt hFmaxX)
  have htermB :
      (fifteenCandidateOuterRadius - (353 : ℝ) / 100) *
          (fifteenCandidateOuterRadius + (353 : ℝ) / 100 -
            (191 / 100 : ℝ) * ((839 : ℝ) / 500)) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by linarith [hbhi']) (le_of_lt hFmaxB)
  have hFneg :
      x ^ 2 + fifteenCandidateOuterRadius ^ 2 - 4 -
          (191 / 100 : ℝ) * x * fifteenCandidateOuterRadius < 0 := by
    rw [hFidentity]
    norm_num at htermX htermB ⊢
    nlinarith
  constructor
  · exact div_pos hnumPos hden
  · rw [fifteenAngleCosineArgument, div_lt_iff₀ hden]
    nlinarith [hFneg]

private theorem fifteenCandidateMixedCapGradient_abs_le
    {x : ℝ} (hxlo : (839 : ℝ) / 500 < x)
    (hxhi : x < (862 : ℝ) / 500) :
    |(x ^ 2 - fifteenCandidateOuterRadius ^ 2 + 4) /
        (2 * x ^ 2 * fifteenCandidateOuterRadius)| ≤ (29 : ℝ) / 100 := by
  have hb := fifteenCandidateOuterRadius_mem_Ioo_352_353
  have hxlo' : (839 : ℝ) / 500 ≤ x := le_of_lt hxlo
  have hxhi' : x ≤ (862 : ℝ) / 500 := le_of_lt hxhi
  have hblo' : (352 : ℝ) / 100 ≤ fifteenCandidateOuterRadius :=
    le_of_lt hb.1
  have hbhi' : fifteenCandidateOuterRadius ≤ (353 : ℝ) / 100 :=
    le_of_lt hb.2
  have hx2Lo : ((839 : ℝ) / 500) ^ 2 < x ^ 2 :=
    (sq_lt_sq₀ (by norm_num) (by positivity)).2 hxlo
  have hb2Lo : ((352 : ℝ) / 100) ^ 2 <
      fifteenCandidateOuterRadius ^ 2 :=
    (sq_lt_sq₀ (by norm_num) (by positivity)).2 hb.1
  have hx2Hi : x ^ 2 < ((862 : ℝ) / 500) ^ 2 :=
    (sq_lt_sq₀ (by positivity) (by norm_num)).2 hxhi
  have hb2Lo : ((352 : ℝ) / 100) ^ 2 <
      fifteenCandidateOuterRadius ^ 2 :=
    (sq_lt_sq₀ (by norm_num) (by positivity)).2 hb.1
  have hb2Hi : fifteenCandidateOuterRadius ^ 2 < ((353 : ℝ) / 100) ^ 2 :=
    (sq_lt_sq₀ (by positivity) (by norm_num)).2 hb.2
  have hdenPos : 0 < 2 * x ^ 2 * fifteenCandidateOuterRadius := by positivity
  have hdenLo :
      2 * ((839 : ℝ) / 500) ^ 2 * ((352 : ℝ) / 100) <
        2 * x ^ 2 * fifteenCandidateOuterRadius := by
    have hstep₁ := mul_lt_mul_of_pos_right hx2Lo
      (by norm_num : (0 : ℝ) < (352 : ℝ) / 100)
    have hstep₂ := mul_lt_mul_of_pos_left hb.1 (by positivity :
      (0 : ℝ) < x ^ 2)
    nlinarith
  have hnumNeg :
      x ^ 2 - fifteenCandidateOuterRadius ^ 2 + 4 < 0 := by
    nlinarith
  rw [abs_div, abs_of_neg hnumNeg, abs_of_pos hdenPos]
  rw [div_le_iff₀ hdenPos]
  have hnumUp :
      fifteenCandidateOuterRadius ^ 2 - x ^ 2 - 4 ≤
        ((353 : ℝ) / 100) ^ 2 - ((839 : ℝ) / 500) ^ 2 - 4 := by
    nlinarith
  have hconst :
      ((353 : ℝ) / 100) ^ 2 - ((839 : ℝ) / 500) ^ 2 - 4 <
        (29 : ℝ) / 100 *
          (2 * ((839 : ℝ) / 500) ^ 2 * ((352 : ℝ) / 100)) := by
    norm_num
  have hdenScaled := mul_le_mul_of_nonneg_left (le_of_lt hdenLo)
    (by norm_num : (0 : ℝ) ≤ (29 : ℝ) / 100)
  nlinarith

private theorem fifteenCandidateMixedCapSecond_abs_le
    {x : ℝ} (hxlo : (839 : ℝ) / 500 < x)
    (hxhi : x < (862 : ℝ) / 500) :
    |(fifteenCandidateOuterRadius ^ 2 - 4) /
        (x ^ 3 * fifteenCandidateOuterRadius)| ≤ (51 : ℝ) / 100 := by
  have hb := fifteenCandidateOuterRadius_mem_Ioo_352_353
  have hxlo' : (839 : ℝ) / 500 ≤ x := le_of_lt hxlo
  have hxhi' : x ≤ (862 : ℝ) / 500 := le_of_lt hxhi
  have hblo' : (352 : ℝ) / 100 ≤ fifteenCandidateOuterRadius :=
    le_of_lt hb.1
  have hbhi' : fifteenCandidateOuterRadius ≤ (353 : ℝ) / 100 :=
    le_of_lt hb.2
  have hx2Lo : ((839 : ℝ) / 500) ^ 2 < x ^ 2 :=
    (sq_lt_sq₀ (by norm_num) (by positivity)).2 hxlo
  have hx3Lo : ((839 : ℝ) / 500) ^ 3 < x ^ 3 := by
    calc
      ((839 : ℝ) / 500) ^ 3 =
          ((839 : ℝ) / 500) ^ 2 * ((839 : ℝ) / 500) := by ring
      _ < x ^ 2 * ((839 : ℝ) / 500) :=
        mul_lt_mul_of_pos_right hx2Lo (by norm_num)
      _ < x ^ 2 * x := mul_lt_mul_of_pos_left hxlo (by positivity)
      _ = x ^ 3 := by ring
  have hdenPos : 0 < x ^ 3 * fifteenCandidateOuterRadius := by positivity
  have hdenLo :
      ((839 : ℝ) / 500) ^ 3 * ((352 : ℝ) / 100) <
        x ^ 3 * fifteenCandidateOuterRadius := by
    calc
      _ < x ^ 3 * ((352 : ℝ) / 100) :=
        mul_lt_mul_of_pos_right hx3Lo (by norm_num)
      _ < x ^ 3 * fifteenCandidateOuterRadius :=
        mul_lt_mul_of_pos_left hb.1 (by positivity)
  have hb2Lo : ((352 : ℝ) / 100) ^ 2 <
      fifteenCandidateOuterRadius ^ 2 :=
    (sq_lt_sq₀ (by norm_num) (by positivity)).2 hb.1
  have hnumPos : 0 < fifteenCandidateOuterRadius ^ 2 - 4 := by
    nlinarith [hb2Lo]
  rw [abs_div, abs_of_pos hnumPos, abs_of_pos hdenPos]
  rw [div_le_iff₀ hdenPos]
  have hnumUp : fifteenCandidateOuterRadius ^ 2 - 4 ≤
      ((353 : ℝ) / 100) ^ 2 - 4 := by nlinarith
  have hconst : ((353 : ℝ) / 100) ^ 2 - 4 <
      (51 : ℝ) / 100 *
        (((839 : ℝ) / 500) ^ 3 * ((352 : ℝ) / 100)) := by norm_num
  have hdenScaled := mul_le_mul_of_nonneg_left (le_of_lt hdenLo)
    (by norm_num : (0 : ℝ) ≤ (51 : ℝ) / 100)
  nlinarith

private theorem fifteenMixedAngle_second_derivative_bound_of_cap_bounds
    (q q' q'' s d : ℝ)
    (hqlo : 0 ≤ q) (hqhi : q ≤ (191 : ℝ) / 200)
    (hs : (59 : ℝ) / 200 ≤ s)
    (hq' : |q'| ≤ (29 : ℝ) / 100 * |d|)
    (hq'' : |q''| ≤ (51 : ℝ) / 100 * d ^ 2) :
    |q' ^ 2 * (-(q / s ^ 3)) + q'' * (-(1 / s))| ≤ 5 * d ^ 2 := by
  have hspos : 0 < s := by linarith
  have hSpos : 0 < (59 : ℝ) / 200 := by norm_num
  have hS2 : ((59 : ℝ) / 200) ^ 2 ≤ s ^ 2 := by
    have h := mul_nonneg (by linarith : 0 ≤ s - (59 : ℝ) / 200)
      (by positivity : 0 ≤ s + (59 : ℝ) / 200)
    nlinarith
  have hS3 : ((59 : ℝ) / 200) ^ 3 ≤ s ^ 3 := by
    calc
      ((59 : ℝ) / 200) ^ 3 =
          ((59 : ℝ) / 200) ^ 2 * ((59 : ℝ) / 200) := by ring
      _ ≤ s ^ 2 * ((59 : ℝ) / 200) :=
        mul_le_mul_of_nonneg_right hS2 (by norm_num)
      _ ≤ s ^ 2 * s := mul_le_mul_of_nonneg_left hs (sq_nonneg s)
      _ = s ^ 3 := by ring
  have hinv : 1 / s ≤ 200 / 59 := by
    rw [div_le_iff₀ hspos]
    norm_num
    nlinarith
  have hinvS : 1 / s ≤ 200 / 59 := hinv
  have hinvS3 : 1 / s ^ 3 ≤ (200 / 59 : ℝ) ^ 3 := by
    rw [div_le_iff₀ (pow_pos hspos 3)]
    norm_num
    nlinarith [hS3]
  have hqSq : q' ^ 2 ≤ ((29 : ℝ) / 100) ^ 2 * d ^ 2 := by
    have h := (sq_le_sq₀ (abs_nonneg q')
      (by positivity : 0 ≤ (29 : ℝ) / 100 * |d|)).2 hq'
    simpa [abs_mul, sq_abs, mul_pow] using h
  have hqcoef : q / s ^ 3 ≤ (191 : ℝ) / 200 * (200 / 59 : ℝ) ^ 3 := by
    have h := mul_le_mul hqhi hinvS3 (by positivity) (by positivity)
    calc
      q / s ^ 3 = q * (1 / s ^ 3) := by ring
      _ ≤ (191 : ℝ) / 200 * (200 / 59 : ℝ) ^ 3 := by
        simpa [one_div] using h
  have hcoefNonneg : 0 ≤ q / s ^ 3 := div_nonneg hqlo (by positivity)
  have hterm1 :
      |q' ^ 2 * (-(q / s ^ 3))| ≤
        ((191 : ℝ) / 200 * (200 / 59 : ℝ) ^ 3) *
          (((29 : ℝ) / 100) ^ 2 * d ^ 2) := by
    calc
      |q' ^ 2 * (-(q / s ^ 3))| = q' ^ 2 * (q / s ^ 3) := by
        rw [abs_mul, abs_of_nonneg (sq_nonneg q'), abs_neg,
          abs_of_nonneg hcoefNonneg]
      _ ≤ q' ^ 2 * ((191 : ℝ) / 200 * (200 / 59 : ℝ) ^ 3) :=
        mul_le_mul_of_nonneg_left hqcoef (sq_nonneg q')
      _ ≤ (((29 : ℝ) / 100) ^ 2 * d ^ 2) *
          ((191 : ℝ) / 200 * (200 / 59 : ℝ) ^ 3) :=
        mul_le_mul_of_nonneg_right hqSq (by positivity)
      _ = ((191 : ℝ) / 200 * (200 / 59 : ℝ) ^ 3) *
          (((29 : ℝ) / 100) ^ 2 * d ^ 2) := by ring
  have hterm2 :
      |q'' * (-(1 / s))| ≤
        ((51 : ℝ) / 100 * d ^ 2) * (200 / 59 : ℝ) := by
    have hInvPos : 0 < 1 / s := one_div_pos.mpr hspos
    calc
      |q'' * (-(1 / s))| = |q''| * (1 / s) := by
        rw [abs_mul, abs_neg, abs_of_pos hInvPos]
      _ ≤ ((51 : ℝ) / 100 * d ^ 2) * (1 / s) :=
        mul_le_mul_of_nonneg_right hq'' (by positivity)
      _ ≤ ((51 : ℝ) / 100 * d ^ 2) * (200 / 59 : ℝ) :=
        mul_le_mul_of_nonneg_left hinvS (by positivity)
  have htotal :
      ((191 : ℝ) / 200 * (200 / 59 : ℝ) ^ 3) * ((29 : ℝ) / 100) ^ 2 +
          (51 : ℝ) / 100 * (200 / 59 : ℝ) < 5 := by
    norm_num
  calc
    |q' ^ 2 * (-(q / s ^ 3)) + q'' * (-(1 / s))| ≤
        |q' ^ 2 * (-(q / s ^ 3))| + |q'' * (-(1 / s))| := abs_add_le _ _
    _ ≤ ((191 : ℝ) / 200 * (200 / 59 : ℝ) ^ 3) *
          (((29 : ℝ) / 100) ^ 2 * d ^ 2) +
        ((51 : ℝ) / 100 * d ^ 2) * (200 / 59 : ℝ) := by
      exact add_le_add hterm1 hterm2
    _ ≤ 5 * d ^ 2 := by
      have hd2 : 0 ≤ d ^ 2 := sq_nonneg d
      nlinarith [htotal]

private theorem fifteenTouchAngle_path_add_zero
    (a d b : ℝ) :
    (fun u : ℝ => fifteenTouchAngle (a + u * d) b) =
      (fun u : ℝ => fifteenTouchAngle (a + u * d) (b + u * 0)) := by
  funext u
  simp

private theorem fifteenAngleCosineArgument_path_add_zero
    (a d b : ℝ) :
    (fun u : ℝ => fifteenAngleCosineArgument (a + u * d) (b + u * 0)) =
      (fun u : ℝ => fifteenAngleCosineArgument (a + u * d) b) := by
  funext u
  simp

private theorem fifteenCandidateMixedTouchAngle_second_deriv_bound
    (d : ℝ) (hd : |d| ≤ (11 : ℝ) / 500)
    {t : ℝ} (ht : t ∈ Set.uIcc 0 1) :
    |iteratedDeriv 2
      (fun u : ℝ => fifteenTouchAngle
        (fifteenCandidateInnerRadius + u * d)
        fifteenCandidateOuterRadius) t| ≤ 5 * d ^ 2 := by
  let x := fifteenCandidateInnerRadius + t * d
  have htlo : 0 ≤ t := by
    rcases Set.mem_uIcc.mp ht with h | h
    · exact h.1
    · linarith
  have hthi : t ≤ 1 := by
    rcases Set.mem_uIcc.mp ht with h | h
    · exact h.2
    · linarith
  have htabs : |t| ≤ 1 := by
    rw [abs_le]
    exact ⟨by linarith, by linarith⟩
  have hpert : |t * d| ≤ (11 : ℝ) / 500 := by
    rw [abs_mul]
    calc
      |t| * |d| ≤ 1 * ((11 : ℝ) / 500) :=
        mul_le_mul htabs hd (abs_nonneg d) (by norm_num)
      _ = (11 : ℝ) / 500 := by norm_num
  have hxlo : (839 : ℝ) / 500 < x := by
    have ha := fifteenCandidateInnerRadius_gt_17_10
    dsimp [x]
    rw [abs_le] at hpert
    linarith
  have hxhi : x < (862 : ℝ) / 500 := by
    have ha := fifteenCandidateInnerRadius_lt_851_500
    dsimp [x]
    rw [abs_le] at hpert
    linarith
  have hcap := fifteenCandidateMixedCap_mem_Ioo hxlo hxhi
  have hcapX := fifteenCandidateMixedCapGradient_abs_le hxlo hxhi
  have hcapXX := fifteenCandidateMixedCapSecond_abs_le hxlo hxhi
  have hXne : x ≠ 0 := ne_of_gt (by linarith [hxlo])
  have hbne : fifteenCandidateOuterRadius ≠ 0 :=
    fifteenCandidateOuterRadius_pos.ne'
  have hcapFirst := fifteenAngleCosineArgument_segment_hasDerivAt
    fifteenCandidateInnerRadius fifteenCandidateOuterRadius d 0 t hXne
    (by simpa using hbne)
  have hcapFirst' := hcapFirst.deriv
  have hvalid : ∀ᶠ u in nhds t,
      fifteenCandidateInnerRadius + u * d ≠ 0 ∧
        fifteenCandidateOuterRadius + u * 0 ≠ 0 := by
    have hcx : ContinuousAt
        (fun u : ℝ => fifteenCandidateInnerRadius + u * d) t := by fun_prop
    exact (hcx.eventually_ne hXne).and (Filter.Eventually.of_forall fun _ => by
      simpa using hbne)
  have hcapSecond := fifteenAngleCosineArgument_segment_iteratedDeriv_two
    fifteenCandidateInnerRadius fifteenCandidateOuterRadius d 0 t hvalid
  have hqFirst :
      deriv (fun u : ℝ => fifteenAngleCosineArgument
        (fifteenCandidateInnerRadius + u * d) fifteenCandidateOuterRadius) t =
        ((x ^ 2 - fifteenCandidateOuterRadius ^ 2 + 4) /
          (2 * x ^ 2 * fifteenCandidateOuterRadius)) * d := by
    simpa [x] using hcapFirst'
  have hqSecond :
      iteratedDeriv 2 (fun u : ℝ => fifteenAngleCosineArgument
        (fifteenCandidateInnerRadius + u * d) fifteenCandidateOuterRadius) t =
        ((fifteenCandidateOuterRadius ^ 2 - 4) /
          (x ^ 3 * fifteenCandidateOuterRadius)) * d ^ 2 := by
    simpa [x] using hcapSecond
  have hangle := fifteenTouchAngle_segment_iteratedDeriv_two
    fifteenCandidateInnerRadius fifteenCandidateOuterRadius d 0 t hXne
    (by simpa using hbne)
    (by
      have h := lt_trans (by norm_num : (-1 : ℝ) < 0) hcap.1
      simpa [x] using h)
    (by
      have h := lt_trans hcap.2 (by norm_num : (191 : ℝ) / 200 < 1)
      simpa [x] using h)
  simpa only [fifteenTouchAngle_path_add_zero, hangle,
    fifteenAngleCosineArgument_path_add_zero, zero_mul, mul_zero, add_zero,
    hqFirst, hqSecond] using
    (fifteenMixedAngle_second_derivative_bound_of_cap_bounds
      (fifteenAngleCosineArgument x fifteenCandidateOuterRadius)
      (((x ^ 2 - fifteenCandidateOuterRadius ^ 2 + 4) /
        (2 * x ^ 2 * fifteenCandidateOuterRadius)) * d)
      (((fifteenCandidateOuterRadius ^ 2 - 4) /
        (x ^ 3 * fifteenCandidateOuterRadius)) * d ^ 2)
      (Real.sqrt (1 - fifteenAngleCosineArgument x
        fifteenCandidateOuterRadius ^ 2)) d
      (le_of_lt hcap.1) (le_of_lt hcap.2)
      (by
        have hqSq : fifteenAngleCosineArgument x fifteenCandidateOuterRadius ^ 2 <
            ((191 : ℝ) / 200) ^ 2 :=
          (sq_lt_sq₀ (le_of_lt hcap.1) (by norm_num)).2 hcap.2
        have hrad : ((59 : ℝ) / 200) ^ 2 <
            1 - fifteenAngleCosineArgument x fifteenCandidateOuterRadius ^ 2 := by
          nlinarith [hqSq]
        have hsqrtpos : 0 < Real.sqrt
            (1 - fifteenAngleCosineArgument x fifteenCandidateOuterRadius ^ 2) :=
          Real.sqrt_pos.2 (by nlinarith [hcap.1, hcap.2])
        have hsquare := Real.sq_sqrt (show 0 ≤
          1 - fifteenAngleCosineArgument x fifteenCandidateOuterRadius ^ 2 by
            nlinarith [hcap.1, hcap.2])
        have hsq : ((59 : ℝ) / 200) ^ 2 <
            Real.sqrt (1 - fifteenAngleCosineArgument x
              fifteenCandidateOuterRadius ^ 2) ^ 2 := by
          rw [hsquare]
          linarith [hrad]
        have hsqrt_lower : (59 : ℝ) / 200 <
            Real.sqrt (1 - fifteenAngleCosineArgument x
              fifteenCandidateOuterRadius ^ 2) :=
          (sq_lt_sq₀ (by norm_num) hsqrtpos.le).mp hsq
        exact le_of_lt hsqrt_lower)
      (by
        rw [abs_mul]
        calc
          |(x ^ 2 - fifteenCandidateOuterRadius ^ 2 + 4) /
              (2 * x ^ 2 * fifteenCandidateOuterRadius)| * |d| ≤
            (29 : ℝ) / 100 * |d| :=
              mul_le_mul_of_nonneg_right hcapX (abs_nonneg d))
      (by
        rw [abs_mul, abs_of_nonneg (sq_nonneg d)]
        exact mul_le_mul_of_nonneg_right hcapXX (sq_nonneg d)))

private theorem fifteenCandidateMixedTouchAngle_contDiffAt
    (d : ℝ) (hd : |d| ≤ (11 : ℝ) / 500)
    {t : ℝ} (ht : t ∈ Set.uIcc 0 1) :
    ContDiffAt ℝ 2
      (fun u : ℝ => fifteenTouchAngle
        (fifteenCandidateInnerRadius + u * d)
        fifteenCandidateOuterRadius) t := by
  let x := fifteenCandidateInnerRadius + t * d
  have htlo : 0 ≤ t := by
    rcases Set.mem_uIcc.mp ht with h | h
    · exact h.1
    · linarith
  have hthi : t ≤ 1 := by
    rcases Set.mem_uIcc.mp ht with h | h
    · exact h.2
    · linarith
  have htabs : |t| ≤ 1 := by
    rw [abs_le]
    exact ⟨by linarith, by linarith⟩
  have hpert : |t * d| ≤ (11 : ℝ) / 500 := by
    rw [abs_mul]
    calc
      |t| * |d| ≤ 1 * ((11 : ℝ) / 500) :=
        mul_le_mul htabs hd (abs_nonneg d) (by norm_num)
      _ = (11 : ℝ) / 500 := by norm_num
  have hxlo : (839 : ℝ) / 500 < x := by
    have ha := fifteenCandidateInnerRadius_gt_17_10
    dsimp [x]
    rw [abs_le] at hpert
    linarith
  have hxhi : x < (862 : ℝ) / 500 := by
    have ha := fifteenCandidateInnerRadius_lt_851_500
    dsimp [x]
    rw [abs_le] at hpert
    linarith
  have hcap := fifteenCandidateMixedCap_mem_Ioo hxlo hxhi
  have hXne : x ≠ 0 := ne_of_gt (by linarith [hxlo])
  have hbne : fifteenCandidateOuterRadius ≠ 0 :=
    fifteenCandidateOuterRadius_pos.ne'
  have hnum : ContDiffAt ℝ 2
      (fun u : ℝ => (fifteenCandidateInnerRadius + u * d) ^ 2 +
        fifteenCandidateOuterRadius ^ 2 - 4) t := by
    fun_prop
  have hden : ContDiffAt ℝ 2
      (fun u : ℝ => 2 * (fifteenCandidateInnerRadius + u * d) *
        fifteenCandidateOuterRadius) t := by
    fun_prop
  have hden0 :
      2 * (fifteenCandidateInnerRadius + t * d) *
        fifteenCandidateOuterRadius ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num) hXne) hbne
  have hcapAt : ContDiffAt ℝ 2
      (fun u : ℝ => fifteenAngleCosineArgument
        (fifteenCandidateInnerRadius + u * d)
        fifteenCandidateOuterRadius) t := by
    change ContDiffAt ℝ 2
      (fun u : ℝ => ((fifteenCandidateInnerRadius + u * d) ^ 2 +
        fifteenCandidateOuterRadius ^ 2 - 4) /
          (2 * (fifteenCandidateInnerRadius + u * d) *
            fifteenCandidateOuterRadius)) t
    exact hnum.div hden hden0
  have hargLo : -1 < fifteenAngleCosineArgument x fifteenCandidateOuterRadius := by
    linarith [hcap.1]
  have hargHi : fifteenAngleCosineArgument x fifteenCandidateOuterRadius < 1 := by
    have hQ : (191 : ℝ) / 200 < 1 := by norm_num
    linarith [hcap.2]
  have harc : ContDiffAt ℝ 2 Real.arccos
      (fifteenAngleCosineArgument x fifteenCandidateOuterRadius) := by
    exact Real.contDiffAt_arccos (ne_of_gt hargLo) (ne_of_lt hargHi)
  have hcomp := harc.comp t hcapAt
  simpa [Function.comp_def, fifteenTouchAngle, x] using hcomp

theorem fifteenCandidateDetourAngle_second_deriv_bound
    (dx dy : ℝ)
    (hdx : |dx| ≤ (11 : ℝ) / 500)
    (hdy : |dy| ≤ (11 : ℝ) / 500)
    {t : ℝ} (ht : t ∈ Set.uIcc 0 1) :
    |iteratedDeriv 2
      (fun s : ℝ => fifteenDetourAngleAlongSegment
        fifteenCandidateOuterRadius fifteenCandidateInnerRadius
        fifteenCandidateInnerRadius dx dy s) t| ≤
      5 * (dx ^ 2 + dy ^ 2) := by
  let f : ℝ → ℝ := fun s => fifteenTouchAngle
    (fifteenCandidateInnerRadius + s * dx) fifteenCandidateOuterRadius
  let g : ℝ → ℝ := fun s => fifteenTouchAngle
    (fifteenCandidateInnerRadius + s * dy) fifteenCandidateOuterRadius
  let c := fifteenTouchAngle fifteenCandidateOuterRadius fifteenCandidateOuterRadius
  have hf : ContDiffAt ℝ 2 f t := by
    exact fifteenCandidateMixedTouchAngle_contDiffAt dx hdx ht
  have hg : ContDiffAt ℝ 2 g t := by
    exact fifteenCandidateMixedTouchAngle_contDiffAt dy hdy ht
  have hsum :
      iteratedDeriv 2
        (fun s : ℝ => fifteenDetourAngleAlongSegment
          fifteenCandidateOuterRadius fifteenCandidateInnerRadius
          fifteenCandidateInnerRadius dx dy s) t =
        iteratedDeriv 2 f t + iteratedDeriv 2 g t := by
    have hf' : ContDiffAt ℝ 2 (fun s : ℝ => f s + c) t :=
      hf.add contDiffAt_const
    have h1 := iteratedDeriv_add (n := 2) hf' hg
    have hc : ContDiffAt ℝ 2 (fun _ : ℝ => c) t := contDiffAt_const
    have hconst : iteratedDeriv 2 (fun s : ℝ => f s + c) t =
        iteratedDeriv 2 f t := by
      have hfun : (fun s : ℝ => f s + c) =
          (fun s : ℝ => c + f s) := by
        funext s
        ring
      rw [hfun, iteratedDeriv_const_add (by norm_num : 0 < (2 : ℕ)) c]
    have hdecomp :
        (fun s : ℝ => fifteenDetourAngleAlongSegment
          fifteenCandidateOuterRadius fifteenCandidateInnerRadius
          fifteenCandidateInnerRadius dx dy s) =
        (fun s : ℝ => (f s + c) + g s) := by
      funext s
      simp [f, g, c, fifteenDetourAngleAlongSegment,
        fifteenDetourAngle, add_assoc]
    rw [hdecomp]
    change iteratedDeriv 2 ((fun s : ℝ => f s + c) + g) t = _
    rw [h1]
    rw [hconst]
  have hfd := fifteenCandidateMixedTouchAngle_second_deriv_bound dx hdx ht
  have hgd := fifteenCandidateMixedTouchAngle_second_deriv_bound dy hdy ht
  rw [hsum]
  calc
    |iteratedDeriv 2 f t + iteratedDeriv 2 g t| ≤
        |iteratedDeriv 2 f t| + |iteratedDeriv 2 g t| := abs_add_le _ _
    _ ≤ 5 * dx ^ 2 + 5 * dy ^ 2 := add_le_add hfd hgd
    _ = 5 * (dx ^ 2 + dy ^ 2) := by ring

end CirclePacking
