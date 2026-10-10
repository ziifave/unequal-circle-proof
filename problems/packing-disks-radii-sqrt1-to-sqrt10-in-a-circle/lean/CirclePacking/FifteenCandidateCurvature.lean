import CirclePacking.FifteenCandidateSmoothness

/-! Explicit rational enclosures for the direct contact-angle curvature on the
certified five-inner-radius box.  These estimates discharge one of the
quantitative hypotheses in the local rigidity theorem. -/

namespace CirclePacking

private theorem fifteenBoxX2_lower {x : ℝ} (hx : 8 / 5 < x) :
    (8 / 5 : ℝ) ^ 2 < x ^ 2 := by
  exact (sq_lt_sq₀ (by norm_num) (le_of_lt (by linarith : 0 < x))).2 hx

private theorem fifteenBoxX2_upper {x : ℝ} (hxlo : 0 < x) (hx : x < 7 / 4) :
    x ^ 2 < (7 / 4 : ℝ) ^ 2 := by
  exact (sq_lt_sq₀ (le_of_lt hxlo) (by norm_num)).2 hx

private theorem fifteenBoxX3Y_gt_six
    {x y : ℝ} (hx : 8 / 5 < x) (hy : 8 / 5 < y) :
    6 < x ^ 3 * y := by
  have hx2 := fifteenBoxX2_lower hx
  have hx3 : (8 / 5 : ℝ) ^ 3 < x ^ 3 := by
    calc
      (8 / 5 : ℝ) ^ 3 = (8 / 5) ^ 2 * (8 / 5) := by ring
      _ < x ^ 2 * (8 / 5) :=
        mul_lt_mul_of_pos_right hx2 (by norm_num)
      _ < x ^ 2 * x := mul_lt_mul_of_pos_left hx (sq_pos_of_pos (by linarith))
      _ = x ^ 3 := by ring
  have hprod : (8 / 5 : ℝ) ^ 4 < x ^ 3 * y := by
    calc
      (8 / 5 : ℝ) ^ 4 = (8 / 5) ^ 3 * (8 / 5) := by ring
      _ < x ^ 3 * (8 / 5) :=
        mul_lt_mul_of_pos_right hx3 (by norm_num)
      _ < x ^ 3 * y := mul_lt_mul_of_pos_left hy (by positivity)
  have hconst : (6 : ℝ) < (8 / 5) ^ 4 := by norm_num
  linarith

private theorem fifteenBoxX2Y_gt_four
    {x y : ℝ} (hx : 8 / 5 < x) (hy : 8 / 5 < y) :
    4 < x ^ 2 * y := by
  have hx2 := fifteenBoxX2_lower hx
  have hprod : (8 / 5 : ℝ) ^ 3 < x ^ 2 * y := by
    calc
      (8 / 5 : ℝ) ^ 3 = (8 / 5) ^ 2 * (8 / 5) := by ring
      _ < x ^ 2 * (8 / 5) :=
        mul_lt_mul_of_pos_right hx2 (by norm_num)
      _ < x ^ 2 * y := mul_lt_mul_of_pos_left hy (sq_pos_of_pos (by linarith))
  have hconst : (4 : ℝ) < (8 / 5) ^ 3 := by norm_num
  linarith

private theorem fifteenBoxX2Y2_gt_thirteen_halves
    {x y : ℝ} (hx : 8 / 5 < x) (hy : 8 / 5 < y) :
    13 / 2 < x ^ 2 * y ^ 2 := by
  have hxy : (8 / 5 : ℝ) ^ 2 < x * y := by
    calc
      (8 / 5 : ℝ) ^ 2 = (8 / 5) * (8 / 5) := by ring
      _ < x * (8 / 5) := mul_lt_mul_of_pos_right hx (by norm_num)
      _ < x * y := mul_lt_mul_of_pos_left hy (by positivity)
  have hsq : ((8 / 5 : ℝ) ^ 2) ^ 2 < (x * y) ^ 2 :=
    (sq_lt_sq₀ (by positivity) (by positivity)).2 hxy
  have hconst : (13 : ℝ) / 2 < (8 / 5) ^ 4 := by norm_num
  have hsq' : (8 / 5 : ℝ) ^ 4 < x ^ 2 * y ^ 2 := by
    calc
      (8 / 5 : ℝ) ^ 4 = ((8 / 5) ^ 2) ^ 2 := by ring
      _ < (x * y) ^ 2 := hsq
      _ = x ^ 2 * y ^ 2 := by ring
  linarith

private theorem fifteenBoxCap_mem
    {x y : ℝ} (hxlo : 8 / 5 < x) (hxhi : x < 7 / 4)
    (hylo : 8 / 5 < y) (hyhi : y < 7 / 4) :
    0 < fifteenAngleCosineArgument x y ∧
      fifteenAngleCosineArgument x y < 1 / 2 := by
  have hden : 0 < 2 * x * y := by positivity
  have hx2lo := fifteenBoxX2_lower hxlo
  have hy2lo := fifteenBoxX2_lower hylo
  have hx2hi := fifteenBoxX2_upper (by linarith) hxhi
  have hy2hi := fifteenBoxX2_upper (by linarith) hyhi
  have hxylo : (8 / 5 : ℝ) ^ 2 < x * y := by
    calc
      (8 / 5 : ℝ) ^ 2 = (8 / 5) * (8 / 5) := by ring
      _ < x * (8 / 5) := mul_lt_mul_of_pos_right hxlo (by norm_num)
      _ < x * y := mul_lt_mul_of_pos_left hylo (by positivity)
  constructor
  · unfold fifteenAngleCosineArgument
    apply div_pos
    · nlinarith
    · positivity
  · unfold fifteenAngleCosineArgument
    rw [div_lt_iff₀ hden]
    nlinarith

private theorem fifteenBoxCapGradientX_abs_le
    {x y : ℝ} (hxlo : 8 / 5 < x) (hxhi : x < 7 / 4)
    (hylo : 8 / 5 < y) (hyhi : y < 7 / 4) :
    |(x ^ 2 - y ^ 2 + 4) / (2 * x ^ 2 * y)| ≤ 2 / 3 := by
  have hx2lo := fifteenBoxX2_lower hxlo
  have hy2lo := fifteenBoxX2_lower hylo
  have hx2hi := fifteenBoxX2_upper (by linarith) hxhi
  have hy2hi := fifteenBoxX2_upper (by linarith) hyhi
  have hnumpos : 0 < x ^ 2 - y ^ 2 + 4 := by nlinarith
  have hnumhi : x ^ 2 - y ^ 2 + 4 < 5 := by nlinarith
  have hdenlo : 8 < 2 * x ^ 2 * y := by
    have hprod : (8 / 5 : ℝ) ^ 3 < x ^ 2 * y := by
      calc
        (8 / 5 : ℝ) ^ 3 = (8 / 5) ^ 2 * (8 / 5) := by ring
        _ < x ^ 2 * (8 / 5) :=
          mul_lt_mul_of_pos_right hx2lo (by norm_num)
        _ < x ^ 2 * y := mul_lt_mul_of_pos_left hylo (sq_pos_of_pos (by linarith))
    have hconst : (8 : ℝ) < 2 * (8 / 5) ^ 3 := by norm_num
    nlinarith
  have hdenpos : 0 < 2 * x ^ 2 * y := by positivity
  have hratio_nonneg :
      0 ≤ (x ^ 2 - y ^ 2 + 4) / (2 * x ^ 2 * y) :=
    div_nonneg (le_of_lt hnumpos) (le_of_lt hdenpos)
  rw [abs_of_nonneg hratio_nonneg]
  rw [div_le_iff₀ hdenpos]
  nlinarith

private theorem fifteenBoxCapXX_abs_le
    {x y : ℝ} (hxlo : 8 / 5 < x) (hxhi : x < 7 / 4)
    (hylo : 8 / 5 < y) (_hyhi : y < 7 / 4) :
    |(y ^ 2 - 4) / (x ^ 3 * y)| ≤ 1 / 4 := by
  have hy2lo := fifteenBoxX2_lower hylo
  have hy2hi := fifteenBoxX2_upper (by linarith) _hyhi
  have hdenlo := fifteenBoxX3Y_gt_six hxlo hylo
  have hdenpos : 0 < x ^ 3 * y := by positivity
  have hnumneg : y ^ 2 - 4 < 0 := by nlinarith
  rw [abs_div, abs_of_neg hnumneg, abs_of_pos hdenpos]
  rw [div_le_iff₀ hdenpos]
  nlinarith

private theorem fifteenBoxCapYY_abs_le
    {x y : ℝ} (hxlo : 8 / 5 < x) (_hxhi : x < 7 / 4)
    (hylo : 8 / 5 < y) (_hyhi : y < 7 / 4) :
    |(x ^ 2 - 4) / (x * y ^ 3)| ≤ 1 / 4 := by
  have hx2lo := fifteenBoxX2_lower hxlo
  have hx2hi := fifteenBoxX2_upper (by linarith) _hxhi
  have hdenlo := fifteenBoxX3Y_gt_six hylo hxlo
  have hdenpos : 0 < x * y ^ 3 := by positivity
  have hnumneg : x ^ 2 - 4 < 0 := by nlinarith
  have hdenlo' : 6 < x * y ^ 3 := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using hdenlo
  rw [abs_div, abs_of_neg hnumneg, abs_of_pos hdenpos]
  rw [div_le_iff₀ hdenpos]
  nlinarith

private theorem fifteenBoxCapMixed_abs_le
    {x y : ℝ} (hxlo : 8 / 5 < x) (hxhi : x < 7 / 4)
    (hylo : 8 / 5 < y) (hyhi : y < 7 / 4) :
    |(x ^ 2 + y ^ 2 + 4) / (x ^ 2 * y ^ 2)| ≤ 8 / 5 := by
  have hx2hi := fifteenBoxX2_upper (by linarith) hxhi
  have hy2hi := fifteenBoxX2_upper (by linarith) hyhi
  have hdenlo := fifteenBoxX2Y2_gt_thirteen_halves hxlo hylo
  have hdenpos : 0 < x ^ 2 * y ^ 2 := by positivity
  have hnumpos : 0 < x ^ 2 + y ^ 2 + 4 := by positivity
  have hnumhi : x ^ 2 + y ^ 2 + 4 < 81 / 8 := by nlinarith
  rw [abs_div, abs_of_pos hnumpos, abs_of_pos hdenpos]
  rw [div_le_iff₀ hdenpos]
  nlinarith

private theorem fifteenDirectionalCapFirstDerivative_bound
    (a b dx dy : ℝ)
    (ha : |a| ≤ 2 / 3) (hb : |b| ≤ 2 / 3) :
    |a * dx + b * dy| ≤ 2 / 3 * (|dx| + |dy|) := by
  calc
    |a * dx + b * dy| ≤ |a * dx| + |b * dy| := abs_add_le _ _
    _ = |a| * |dx| + |b| * |dy| := by rw [abs_mul, abs_mul]
    _ ≤ 2 / 3 * (|dx| + |dy|) := by
      have h₁ := mul_le_mul_of_nonneg_right ha (abs_nonneg dx)
      have h₂ := mul_le_mul_of_nonneg_right hb (abs_nonneg dy)
      nlinarith

private theorem fifteenDirectionalCapSecondDerivative_bound
    (a c b dx dy : ℝ)
    (ha : |a| ≤ 1 / 4) (hc : |c| ≤ 8 / 5)
    (hb : |b| ≤ 1 / 4) :
    |a * dx ^ 2 - c * (dx * dy) + b * dy ^ 2| ≤
      2 * (dx ^ 2 + dy ^ 2) := by
  have hab : 2 * |dx * dy| ≤ dx ^ 2 + dy ^ 2 := by
    have h := sq_nonneg (|dx| - |dy|)
    nlinarith [sq_abs dx, sq_abs dy, abs_mul dx dy]
  have hfirst : |a * dx ^ 2| ≤ 1 / 4 * dx ^ 2 := by
    rw [abs_mul, abs_of_nonneg (sq_nonneg dx)]
    exact mul_le_mul_of_nonneg_right ha (sq_nonneg dx)
  have hmiddle : |c * (dx * dy)| ≤ 8 / 5 * |dx * dy| := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right hc (abs_nonneg (dx * dy))
  have hlast : |b * dy ^ 2| ≤ 1 / 4 * dy ^ 2 := by
    rw [abs_mul, abs_of_nonneg (sq_nonneg dy)]
    exact mul_le_mul_of_nonneg_right hb (sq_nonneg dy)
  calc
    |a * dx ^ 2 - c * (dx * dy) + b * dy ^ 2|
        ≤ |a * dx ^ 2| + |c * (dx * dy)| + |b * dy ^ 2| := by
          have htriangle :
              |a * dx ^ 2 - c * (dx * dy)| ≤
                |a| * dx ^ 2 + |c| * (|dx| * |dy|) := by
            have htriangle0 :
                |a * dx ^ 2 - c * (dx * dy)| ≤
                  |a * dx ^ 2| + |c * (dx * dy)| := by
              simpa only [sub_zero, zero_sub, abs_neg] using
                (abs_sub_le (a * dx ^ 2) (0 : ℝ) (c * (dx * dy)))
            calc
              |a * dx ^ 2 - c * (dx * dy)| ≤
                  |a * dx ^ 2| + |c * (dx * dy)| := htriangle0
              _ = |a| * dx ^ 2 + |c| * (|dx| * |dy|) := by
                simp [abs_mul, abs_of_nonneg (sq_nonneg dx)]
          calc
            _ ≤ |a * dx ^ 2 - c * (dx * dy)| + |b * dy ^ 2| := abs_add_le _ _
            _ ≤ |a * dx ^ 2| + |c * (dx * dy)| + |b * dy ^ 2| := by
              have h := add_le_add_right htriangle |b * dy ^ 2|
              simpa [abs_mul, abs_of_nonneg (sq_nonneg dx)] using h
    _ ≤ 2 * (dx ^ 2 + dy ^ 2) := by nlinarith [hfirst, hmiddle, hlast, hab]

private theorem fifteenTouchAngle_second_derivative_bound_of_cap_bounds
    (q dq ddq s dx dy : ℝ)
    (hqlo : 0 ≤ q) (hqhi : q ≤ 1 / 2)
    (hs : 4 / 5 ≤ s)
    (hdq : |dq| ≤ 2 / 3 * (|dx| + |dy|))
    (hddq : |ddq| ≤ 2 * (dx ^ 2 + dy ^ 2)) :
    |dq ^ 2 * (-(q / s ^ 3)) + ddq * (-(1 / s))| ≤
      5 * (dx ^ 2 + dy ^ 2) := by
  have hspos : 0 < s := by linarith
  have hsquare : (4 / 5 : ℝ) ^ 2 ≤ s ^ 2 := by
    have hprod := mul_nonneg (by linarith : 0 ≤ s - 4 / 5)
      (by positivity : 0 ≤ s + 4 / 5)
    nlinarith
  have hscube : (4 / 5 : ℝ) ^ 3 ≤ s ^ 3 := by
    calc
      (4 / 5 : ℝ) ^ 3 = (4 / 5) ^ 2 * (4 / 5) := by ring
      _ ≤ s ^ 2 * (4 / 5) := mul_le_mul_of_nonneg_right hsquare (by norm_num)
      _ ≤ s ^ 2 * s := mul_le_mul_of_nonneg_left hs (sq_nonneg s)
      _ = s ^ 3 := by ring
  have hinv : 1 / s ≤ 5 / 4 := by
    rw [div_le_iff₀ hspos]
    nlinarith
  have hinvCube : 1 / s ^ 3 ≤ 2 := by
    rw [div_le_iff₀ (pow_pos hspos 3)]
    nlinarith
  have hcoeff : q / s ^ 3 ≤ 1 := by
    have hInvCube : (s ^ 3)⁻¹ ≤ 2 := by
      simpa [one_div] using hinvCube
    rw [div_eq_mul_inv]
    calc
      q * (s ^ 3)⁻¹ ≤ (1 / 2) * 2 :=
        mul_le_mul hqhi hInvCube (by positivity) (by norm_num)
      _ = 1 := by norm_num
  have hsumSq : (|dx| + |dy|) ^ 2 ≤ 2 * (dx ^ 2 + dy ^ 2) := by
    have h := sq_nonneg (|dx| - |dy|)
    nlinarith [sq_abs dx, sq_abs dy]
  have hdqSq : dq ^ 2 ≤ 8 / 9 * (dx ^ 2 + dy ^ 2) := by
    have hsquare' : |dq| ^ 2 ≤ (2 / 3 * (|dx| + |dy|)) ^ 2 :=
      (sq_le_sq₀ (abs_nonneg dq) (by positivity)).2 hdq
    rw [sq_abs] at hsquare'
    nlinarith [hsumSq]
  have hterm1 : |dq ^ 2 * (-(q / s ^ 3))| ≤ dq ^ 2 := by
    rw [abs_mul, abs_of_nonneg (sq_nonneg dq), abs_neg,
      abs_div, abs_of_nonneg hqlo, abs_of_pos (pow_pos hspos 3)]
    have hfactor : 0 ≤ 1 - q / s ^ 3 := by linarith [hcoeff]
    nlinarith [mul_nonneg (sq_nonneg dq) hfactor]
  have hterm2 : |ddq * (-(1 / s))| ≤ 5 / 4 * |ddq| := by
    rw [abs_mul, abs_neg, abs_div, abs_of_nonneg (by norm_num : 0 ≤ (1 : ℝ)),
      abs_of_pos hspos]
    have hfactor : 0 ≤ 5 / 4 - 1 / s := by linarith [hinv]
    nlinarith [mul_nonneg (abs_nonneg ddq) hfactor]
  calc
    |dq ^ 2 * (-(q / s ^ 3)) + ddq * (-(1 / s))|
        ≤ |dq ^ 2 * (-(q / s ^ 3))| + |ddq * (-(1 / s))| := abs_add_le _ _
    _ ≤ dq ^ 2 + 5 / 4 * |ddq| := add_le_add hterm1 hterm2
    _ ≤ 8 / 9 * (dx ^ 2 + dy ^ 2) + 5 / 4 * (2 * (dx ^ 2 + dy ^ 2)) := by
      gcongr
    _ ≤ 5 * (dx ^ 2 + dy ^ 2) := by nlinarith [sq_nonneg dx, sq_nonneg dy]

private theorem fifteenCandidateSegmentCoarseBounds
    (d : ℝ) (hd : |d| ≤ 11 / 500)
    {t : ℝ} (ht : t ∈ Set.uIcc 0 1) :
    8 / 5 < fifteenCandidateInnerRadius + t * d ∧
      fifteenCandidateInnerRadius + t * d < 7 / 4 := by
  rcases Set.mem_uIcc.mp ht with ht | ht
  · have htlo : 0 ≤ t := ht.1
    have hthi : t ≤ 1 := ht.2
    have htabs : |t| ≤ 1 := by
      rw [abs_le]
      constructor <;> linarith
    have hpert : |t * d| ≤ 11 / 500 := by
      rw [abs_mul]
      calc
        |t| * |d| ≤ 1 * (11 / 500 : ℝ) :=
          mul_le_mul htabs hd (abs_nonneg d) (by norm_num)
        _ = 11 / 500 := by norm_num
    rcases abs_le.mp hpert with ⟨hlo, hhi⟩
    constructor
    · have hbase := fifteenCandidateInnerRadius_gt_17_10
      norm_num at hbase ⊢
      linarith
    · have hbase := fifteenCandidateInnerRadius_lt_851_500
      norm_num at hbase ⊢
      linarith
  · have htlo : 0 ≤ t := by linarith [ht.2]
    have hthi : t ≤ 1 := by linarith [ht.1]
    have htabs : |t| ≤ 1 := by
      rw [abs_le]
      constructor <;> linarith
    have hpert : |t * d| ≤ 11 / 500 := by
      rw [abs_mul]
      calc
        |t| * |d| ≤ 1 * (11 / 500 : ℝ) :=
          mul_le_mul htabs hd (abs_nonneg d) (by norm_num)
        _ = 11 / 500 := by norm_num
    rcases abs_le.mp hpert with ⟨hlo, hhi⟩
    constructor
    · have hbase := fifteenCandidateInnerRadius_gt_17_10
      norm_num at hbase ⊢
      linarith
    · have hbase := fifteenCandidateInnerRadius_lt_851_500
      norm_num at hbase ⊢
      linarith

/-- Uniform second-derivative estimate for the direct contact angle along any
segment contained in the certified inner-radius box. -/
theorem fifteenCandidateDirectAngle_second_deriv_bound
    (dx dy : ℝ)
    (hdx : |dx| ≤ 11 / 500) (hdy : |dy| ≤ 11 / 500)
    {t : ℝ} (ht : t ∈ Set.uIcc 0 1) :
    |iteratedDeriv 2
      (fun u : ℝ => fifteenTouchAngle
        (fifteenCandidateInnerRadius + u * dx)
        (fifteenCandidateInnerRadius + u * dy)) t| ≤
      5 * (dx ^ 2 + dy ^ 2) := by
  let X := fifteenCandidateInnerRadius + t * dx
  let Y := fifteenCandidateInnerRadius + t * dy
  have hX := fifteenCandidateSegmentCoarseBounds dx hdx ht
  have hY := fifteenCandidateSegmentCoarseBounds dy hdy ht
  have hcap := fifteenBoxCap_mem hX.1 hX.2 hY.1 hY.2
  have hqX := fifteenBoxCapGradientX_abs_le hX.1 hX.2 hY.1 hY.2
  have hqY := fifteenBoxCapGradientX_abs_le hY.1 hY.2 hX.1 hX.2
  have hqXX := fifteenBoxCapXX_abs_le hX.1 hX.2 hY.1 hY.2
  have hqYY := fifteenBoxCapYY_abs_le hX.1 hX.2 hY.1 hY.2
  have hqXY := fifteenBoxCapMixed_abs_le hX.1 hX.2 hY.1 hY.2
  have hX0 : X ≠ 0 := ne_of_gt (by linarith [hX.1])
  have hY0 : Y ≠ 0 := ne_of_gt (by linarith [hY.1])
  have hcapFirst := fifteenAngleCosineArgument_segment_hasDerivAt
    fifteenCandidateInnerRadius fifteenCandidateInnerRadius dx dy t hX0 hY0
  have hcapFirst' := hcapFirst.deriv
  have hvalid : ∀ᶠ u in nhds t,
      fifteenCandidateInnerRadius + u * dx ≠ 0 ∧
        fifteenCandidateInnerRadius + u * dy ≠ 0 := by
    have hcx : ContinuousAt
        (fun u : ℝ => fifteenCandidateInnerRadius + u * dx) t := by fun_prop
    have hcy : ContinuousAt
        (fun u : ℝ => fifteenCandidateInnerRadius + u * dy) t := by fun_prop
    exact (hcx.eventually_ne hX0).and (hcy.eventually_ne hY0)
  have hcapSecond := fifteenAngleCosineArgument_segment_iteratedDeriv_two
    fifteenCandidateInnerRadius fifteenCandidateInnerRadius dx dy t hvalid
  have hqX' :
      deriv (fun u : ℝ => fifteenAngleCosineArgument
        (fifteenCandidateInnerRadius + u * dx)
        (fifteenCandidateInnerRadius + u * dy)) t =
        ((X ^ 2 - Y ^ 2 + 4) / (2 * X ^ 2 * Y)) * dx +
          ((Y ^ 2 - X ^ 2 + 4) / (2 * X * Y ^ 2)) * dy := by
    simpa [X, Y] using hcapFirst'
  have hqXX' :
      ((Y ^ 2 - 4) / (X ^ 3 * Y)) * dx ^ 2 -
        ((X ^ 2 + Y ^ 2 + 4) / (X ^ 2 * Y ^ 2)) * (dx * dy) +
        ((X ^ 2 - 4) / (X * Y ^ 3)) * dy ^ 2 =
      iteratedDeriv 2
        (fun u : ℝ => fifteenAngleCosineArgument
          (fifteenCandidateInnerRadius + u * dx)
          (fifteenCandidateInnerRadius + u * dy)) t := by
    simpa [X, Y] using hcapSecond.symm
  have hqFirstBound :
      |((X ^ 2 - Y ^ 2 + 4) / (2 * X ^ 2 * Y)) * dx +
        ((Y ^ 2 - X ^ 2 + 4) / (2 * X * Y ^ 2)) * dy|
        ≤ 2 / 3 * (|dx| + |dy|) := by
    have hqx' := fifteenDirectionalCapFirstDerivative_bound
      _ _ dx dy hqX hqY
    simpa [X, Y, mul_comm, mul_left_comm, mul_assoc] using hqx'
  have hqSecondBound :
      |((Y ^ 2 - 4) / (X ^ 3 * Y)) * dx ^ 2 -
        ((X ^ 2 + Y ^ 2 + 4) / (X ^ 2 * Y ^ 2)) * (dx * dy) +
        ((X ^ 2 - 4) / (X * Y ^ 3)) * dy ^ 2|
        ≤ 2 * (dx ^ 2 + dy ^ 2) := by
    exact fifteenDirectionalCapSecondDerivative_bound _ _ _ dx dy
      hqXX hqXY hqYY
  have hsqrt : 4 / 5 ≤ Real.sqrt (1 - (fifteenAngleCosineArgument X Y) ^ 2) := by
    have harg := hcap
    have hrad : (4 / 5 : ℝ) ^ 2 <
        1 - (fifteenAngleCosineArgument X Y) ^ 2 := by
      nlinarith [harg.2]
    have hsqrtpos : 0 < Real.sqrt
        (1 - (fifteenAngleCosineArgument X Y) ^ 2) :=
      Real.sqrt_pos.2 (by positivity)
    have hsqrteq := Real.sq_sqrt (show 0 ≤
        1 - (fifteenAngleCosineArgument X Y) ^ 2 by nlinarith [hcap.1, hcap.2])
    have hsq : (4 / 5 : ℝ) ^ 2 <
        Real.sqrt (1 - (fifteenAngleCosineArgument X Y) ^ 2) ^ 2 := by
      rw [hsqrteq]
      exact hrad
    exact (sq_lt_sq₀ (by norm_num) hsqrtpos.le).mp hsq |>.le
  have hangle := fifteenTouchAngle_segment_iteratedDeriv_two
    fifteenCandidateInnerRadius fifteenCandidateInnerRadius dx dy t hX0 hY0
    (by linarith [hcap.1]) (by linarith [hcap.2])
  rw [hangle, hqX', ← hqXX']
  exact fifteenTouchAngle_second_derivative_bound_of_cap_bounds
    (fifteenAngleCosineArgument X Y)
    (((X ^ 2 - Y ^ 2 + 4) / (2 * X ^ 2 * Y)) * dx +
      ((Y ^ 2 - X ^ 2 + 4) / (2 * X * Y ^ 2)) * dy)
    (((Y ^ 2 - 4) / (X ^ 3 * Y)) * dx ^ 2 -
      ((X ^ 2 + Y ^ 2 + 4) / (X ^ 2 * Y ^ 2)) * (dx * dy) +
      ((X ^ 2 - 4) / (X * Y ^ 3)) * dy ^ 2)
    (Real.sqrt (1 - (fifteenAngleCosineArgument X Y) ^ 2)) dx dy
    (le_of_lt hcap.1) (le_of_lt hcap.2) hsqrt hqFirstBound hqSecondBound

end CirclePacking
