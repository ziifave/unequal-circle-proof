import CirclePacking.FifteenAngleSmoothness
import CirclePacking.FifteenCandidateBounds

/-! Domain bounds on the certified local box imply that the direct and
wall-detour angle functions are twice continuously differentiable along every
allowed radius segment.  Thus the local rigidity interface only needs the
quantitative curvature estimates; smoothness itself is discharged here. -/

namespace CirclePacking

private theorem fifteenAngleCosineArgument_ne_endpoints_of_geometry
    {x y : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hsum : 2 < x + y) (hdiff : |x - y| < 2) :
    fifteenAngleCosineArgument x y ≠ -1 ∧
      fifteenAngleCosineArgument x y ≠ 1 := by
  have hden : 2 * x * y ≠ 0 := ne_of_gt (by positivity)
  constructor
  · intro h
    have hm : x ^ 2 + y ^ 2 - 4 = (-1) * (2 * x * y) :=
      (div_eq_iff hden).mp (by simpa [fifteenAngleCosineArgument] using h)
    nlinarith [sq_pos_of_pos (show 0 < x + y - 2 by linarith)]
  · intro h
    have hm : x ^ 2 + y ^ 2 - 4 = 1 * (2 * x * y) :=
      (div_eq_iff hden).mp (by simpa [fifteenAngleCosineArgument] using h)
    have hdiff' := abs_lt.mp hdiff
    nlinarith [sq_nonneg (x - y)]

private theorem fifteenCandidateSegmentRadius_mem
    (d : ℝ) (hd : |d| ≤ (11 / 500 : ℝ))
    {t : ℝ} (ht : t ∈ Set.uIcc 0 1) :
    839 / 500 < fifteenCandidateInnerRadius + t * d ∧
      fifteenCandidateInnerRadius + t * d < 862 / 500 := by
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
  have hperturb : |t * d| ≤ (11 / 500 : ℝ) := by
    rw [abs_mul]
    calc
      |t| * |d| ≤ 1 * (11 / 500 : ℝ) :=
        mul_le_mul htabs hd (abs_nonneg d) (by norm_num)
      _ = 11 / 500 := by norm_num
  rcases abs_le.mp hperturb with ⟨hperturbLo, hperturbHi⟩
  constructor
  · have hbase := fifteenCandidateInnerRadius_gt_17_10
    linarith
  · have hbase := fifteenCandidateInnerRadius_lt_851_500
    linarith

private theorem fifteenCandidateOuterRadius_gt_three :
    3 < fifteenCandidateOuterRadius := by
  have hs2 := fifteenLocalSinSq_eq_radical
  have hc : Real.cos fifteenLocalPhi = (1 + Real.sqrt 5) / 4 := by
    unfold fifteenLocalPhi
    exact Real.cos_pi_div_five
  have hspos := fifteenLocalSin_pos
  have hcpos := fifteenLocalCos_pos
  have hrootLo := fifteenSqrtFive_gt_eleven_fifths
  have hrootHi := fifteenSqrtFive_lt_nine_fourths
  have hcosSq : Real.cos fifteenLocalPhi ^ 2 =
      ((1 + Real.sqrt 5) / 4) ^ 2 := by rw [hc]
  have hsinLtCos : Real.sin fifteenLocalPhi < Real.cos fifteenLocalPhi := by
    have hsqrtpos := Real.sqrt_nonneg (5 : ℝ)
    nlinarith [hs2, hcosSq, hrootLo, hsqrtpos,
      sq_nonneg (Real.sin fifteenLocalPhi - Real.cos fifteenLocalPhi)]
  have hcotLo : 1 < Real.cos fifteenLocalPhi / Real.sin fifteenLocalPhi := by
    rw [lt_div_iff₀ hspos]
    simpa using hsinLtCos
  have hsineq : 4 * Real.cos fifteenLocalPhi ^ 2 <
      9 * Real.sin fifteenLocalPhi ^ 2 := by
    rw [hcosSq, hs2]
    nlinarith
  have htwocosLtThreesin : 2 * Real.cos fifteenLocalPhi <
      3 * Real.sin fifteenLocalPhi := by
    have hcpos := fifteenLocalCos_pos
    have hleft : 0 ≤ 2 * Real.cos fifteenLocalPhi := by positivity
    have hright : 0 ≤ 3 * Real.sin fifteenLocalPhi := by positivity
    have hsq : (2 * Real.cos fifteenLocalPhi) ^ 2 <
        (3 * Real.sin fifteenLocalPhi) ^ 2 := by nlinarith [hsineq]
    exact (sq_lt_sq₀ hleft hright).mp hsq
  have hcotHi : Real.cos fifteenLocalPhi / Real.sin fifteenLocalPhi <
      3 / 2 := by
    rw [div_lt_iff₀ hspos]
    nlinarith [htwocosLtThreesin]
  have hbase : 3 < 2 + Real.cos fifteenLocalPhi / Real.sin fifteenLocalPhi :=
    by linarith
  have hbSq := fifteenCandidateOuterRadius_sq
  have hbpos := fifteenCandidateOuterRadius_pos
  have hqpos : 0 < 2 + Real.cos fifteenLocalPhi / Real.sin fifteenLocalPhi := by
    linarith
  have hqSq : (3 : ℝ) ^ 2 <
      (2 + Real.cos fifteenLocalPhi / Real.sin fifteenLocalPhi) ^ 2 :=
    (sq_lt_sq₀ (by norm_num) hqpos.le).2 hbase
  have hbSqLower : (3 : ℝ) ^ 2 < fifteenCandidateOuterRadius ^ 2 := by
    rw [hbSq]
    nlinarith [hqSq]
  exact (sq_lt_sq₀ (by norm_num) hbpos.le).mp hbSqLower

private theorem fifteenCandidateOuterRadius_lt_73_20 :
    fifteenCandidateOuterRadius < (73 : ℝ) / 20 := by
  have hs2 := fifteenLocalSinSq_eq_radical
  have hc : Real.cos fifteenLocalPhi = (1 + Real.sqrt 5) / 4 := by
    unfold fifteenLocalPhi
    exact Real.cos_pi_div_five
  have hspos := fifteenLocalSin_pos
  have hrootHi := fifteenSqrtFive_lt_nine_fourths
  have hcosSq : Real.cos fifteenLocalPhi ^ 2 =
      ((1 + Real.sqrt 5) / 4) ^ 2 := by rw [hc]
  have hsineq : 4 * Real.cos fifteenLocalPhi ^ 2 <
      9 * Real.sin fifteenLocalPhi ^ 2 := by
    rw [hcosSq, hs2]
    nlinarith [hrootHi, Real.sqrt_nonneg (5 : ℝ)]
  have htwocosLtThreesin : 2 * Real.cos fifteenLocalPhi <
      3 * Real.sin fifteenLocalPhi := by
    have hcpos := fifteenLocalCos_pos
    have hleft : 0 ≤ 2 * Real.cos fifteenLocalPhi := by positivity
    have hright : 0 ≤ 3 * Real.sin fifteenLocalPhi := by positivity
    have hsq : (2 * Real.cos fifteenLocalPhi) ^ 2 <
        (3 * Real.sin fifteenLocalPhi) ^ 2 := by nlinarith [hsineq]
    exact (sq_lt_sq₀ hleft hright).mp hsq
  have hcotHi : Real.cos fifteenLocalPhi / Real.sin fifteenLocalPhi <
      3 / 2 := by
    rw [div_lt_iff₀ hspos]
    nlinarith
  have hbSq := fifteenCandidateOuterRadius_sq
  have hbpos := fifteenCandidateOuterRadius_pos
  rw [← sq_lt_sq₀ hbpos.le (by positivity)]
  rw [hbSq]
  have hq : 0 < 2 + Real.cos fifteenLocalPhi / Real.sin fifteenLocalPhi := by
    have hcotpos : 0 < Real.cos fifteenLocalPhi / Real.sin fifteenLocalPhi :=
      div_pos fifteenLocalCos_pos fifteenLocalSin_pos
    linarith
  have hqUpper : 2 + Real.cos fifteenLocalPhi / Real.sin fifteenLocalPhi ≤
      7 / 2 := by linarith
  have hqSq : (2 + Real.cos fifteenLocalPhi / Real.sin fifteenLocalPhi) ^ 2 ≤
      (7 / 2 : ℝ) ^ 2 := by
    have hfactor₁ : 0 ≤ 7 / 2 -
        (2 + Real.cos fifteenLocalPhi / Real.sin fifteenLocalPhi) := by linarith
    have hfactor₂ : 0 ≤ 7 / 2 +
        (2 + Real.cos fifteenLocalPhi / Real.sin fifteenLocalPhi) := by linarith
    nlinarith [mul_nonneg hfactor₁ hfactor₂]
  nlinarith [hqSq]

theorem fifteenCandidateDirectCosineArgument_mem_Ioo
    (dx dy : ℝ)
    (hdx : |dx| ≤ (11 / 500 : ℝ))
    (hdy : |dy| ≤ (11 / 500 : ℝ))
    {t : ℝ} (ht : t ∈ Set.uIcc 0 1) :
    fifteenAngleCosineArgument
        (fifteenCandidateInnerRadius + t * dx)
        (fifteenCandidateInnerRadius + t * dy) ∈ Set.Ioo (-1) 1 := by
  have hx := fifteenCandidateSegmentRadius_mem dx hdx ht
  have hy := fifteenCandidateSegmentRadius_mem dy hdy ht
  apply fifteenAngleCosineArgument_mem_Ioo
  · linarith [hx.1]
  · linarith [hy.1]
  · linarith [hx.1, hy.1]
  · rw [abs_lt]
    constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]

theorem fifteenCandidateMixedCosineArgument_mem_Ioo
    {x : ℝ} (hx : 839 / 500 < x) (hx' : x < 862 / 500) :
    fifteenAngleCosineArgument x fifteenCandidateOuterRadius ∈ Set.Ioo (-1) 1 := by
  have hblo := fifteenCandidateOuterRadius_gt_three
  have hbhi := fifteenCandidateOuterRadius_lt_73_20
  apply fifteenAngleCosineArgument_mem_Ioo
  · exact lt_trans (by norm_num) hx
  · exact fifteenCandidateOuterRadius_pos
  · linarith
  · rw [abs_lt]
    constructor <;> linarith

private theorem fifteenCandidateMixedCosineArgument_ne_endpoints
    {x : ℝ} (hx : 839 / 500 < x) (hx' : x < 862 / 500) :
    fifteenAngleCosineArgument x fifteenCandidateOuterRadius ≠ -1 ∧
      fifteenAngleCosineArgument x fifteenCandidateOuterRadius ≠ 1 := by
  have hcap := fifteenCandidateMixedCosineArgument_mem_Ioo hx hx'
  exact ⟨ne_of_gt hcap.1, ne_of_lt hcap.2⟩

theorem fifteenCandidateDirectAngle_contDiffOn
    (dx dy : ℝ)
    (hdx : |dx| ≤ (11 / 500 : ℝ))
    (hdy : |dy| ≤ (11 / 500 : ℝ)) :
    ContDiffOn ℝ 2
      (fun t : ℝ => fifteenTouchAngle
        (fifteenCandidateInnerRadius + t * dx)
        (fifteenCandidateInnerRadius + t * dy))
      (Set.uIcc 0 1) := by
  apply fifteenTouchAngle_segment_contDiffOn
  · intro t ht
    have hx := fifteenCandidateSegmentRadius_mem dx hdx ht
    linarith
  · intro t ht
    have hy := fifteenCandidateSegmentRadius_mem dy hdy ht
    linarith
  · intro t ht
    have hx := fifteenCandidateSegmentRadius_mem dx hdx ht
    have hy := fifteenCandidateSegmentRadius_mem dy hdy ht
    have hdiff : |(fifteenCandidateInnerRadius + t * dx) -
        (fifteenCandidateInnerRadius + t * dy)| < 2 := by
      rw [abs_lt]
      constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]
    have hgeom := fifteenAngleCosineArgument_ne_endpoints_of_geometry
      (by linarith [hx.1]) (by linarith [hy.1]) (by linarith [hx.1, hy.1]) hdiff
    exact hgeom.1
  · intro t ht
    have hx := fifteenCandidateSegmentRadius_mem dx hdx ht
    have hy := fifteenCandidateSegmentRadius_mem dy hdy ht
    have hdiff : |(fifteenCandidateInnerRadius + t * dx) -
        (fifteenCandidateInnerRadius + t * dy)| < 2 := by
      rw [abs_lt]
      constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]
    have hgeom := fifteenAngleCosineArgument_ne_endpoints_of_geometry
      (by linarith [hx.1]) (by linarith [hy.1]) (by linarith [hx.1, hy.1]) hdiff
    exact hgeom.2

theorem fifteenCandidateDetourAngle_contDiffOn
    (dx dy : ℝ)
    (hdx : |dx| ≤ (11 / 500 : ℝ))
    (hdy : |dy| ≤ (11 / 500 : ℝ)) :
    ContDiffOn ℝ 2
      (fun t : ℝ => fifteenDetourAngleAlongSegment
        fifteenCandidateOuterRadius fifteenCandidateInnerRadius
        fifteenCandidateInnerRadius dx dy t)
      (Set.uIcc 0 1) := by
  apply fifteenDetourAngle_segment_contDiffOn
    (b := fifteenCandidateOuterRadius)
  · exact fifteenCandidateOuterRadius_pos.ne'
  · intro t ht
    exact ne_of_gt (by linarith
      [(fifteenCandidateSegmentRadius_mem dx hdx ht).1])
  · intro t ht
    exact ne_of_gt (by linarith
      [(fifteenCandidateSegmentRadius_mem dy hdy ht).1])
  · intro t ht
    exact (fifteenCandidateMixedCosineArgument_ne_endpoints
      (fifteenCandidateSegmentRadius_mem dx hdx ht).1
      (fifteenCandidateSegmentRadius_mem dx hdx ht).2).1
  · intro t ht
    exact (fifteenCandidateMixedCosineArgument_ne_endpoints
      (fifteenCandidateSegmentRadius_mem dx hdx ht).1
      (fifteenCandidateSegmentRadius_mem dx hdx ht).2).2
  · intro t ht
    exact (fifteenCandidateMixedCosineArgument_ne_endpoints
      (fifteenCandidateSegmentRadius_mem dy hdy ht).1
      (fifteenCandidateSegmentRadius_mem dy hdy ht).2).1
  · intro t ht
    exact (fifteenCandidateMixedCosineArgument_ne_endpoints
      (fifteenCandidateSegmentRadius_mem dy hdy ht).1
      (fifteenCandidateSegmentRadius_mem dy hdy ht).2).2

end CirclePacking
