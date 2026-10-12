import CirclePacking.FifteenPackingPolarCoordinates
import CirclePacking.FifteenCandidateDetour
import CirclePacking.FifteenCandidateBounds

/-! Reusable geometry for formalizing the explicit fivefold-symmetric
15-disk construction.  The candidate contact-angle identities are already
available; this file turns a lower bound on a polar gap into the corresponding
Euclidean separation inequality. -/

namespace CirclePacking

/-- If the smaller polar gap is at least the cosine-rule touch angle, the
centers are separated by at least the prescribed distance.  The range premise
ensures `arccos` is an actual inverse of cosine at the contact argument. -/
theorem fifteenPolarPair_separated_of_touchAngle_le_gap
    (a b alpha beta : ℝ)
    (ha : 0 < a) (hb : 0 < b)
    (hgapPi : beta - alpha ≤ Real.pi)
    (hangle : fifteenTouchAngle a b ≤ beta - alpha)
    (hargLo : -1 ≤ fifteenAngleCosineArgument a b)
    (hargHi : fifteenAngleCosineArgument a b ≤ 1) :
    4 ≤ pointNorm
      ((polarPoint a alpha).1 - (polarPoint b beta).1,
       (polarPoint a alpha).2 - (polarPoint b beta).2) ^ 2 := by
  have hcosGap : Real.cos (beta - alpha) ≤
      Real.cos (fifteenTouchAngle a b) :=
    Real.cos_le_cos_of_nonneg_of_le_pi (Real.arccos_nonneg _)
      hgapPi hangle
  rw [fifteenPolarPair_distance_sq]
  unfold fifteenTouchAngle at hcosGap
  rw [Real.cos_arccos hargLo hargHi] at hcosGap
  unfold fifteenAngleCosineArgument at hcosGap
  have hab : 0 < 2 * a * b := by positivity
  have hscaled := mul_le_mul_of_nonneg_left hcosGap (le_of_lt hab)
  have hcancel : 2 * a * b *
      ((a ^ 2 + b ^ 2 - 4) / (2 * a * b)) =
        a ^ 2 + b ^ 2 - 4 := by
    field_simp [ne_of_gt hab]
  rw [hcancel] at hscaled
  have hcosEq : Real.cos (alpha - beta) = Real.cos (beta - alpha) := by
    rw [show alpha - beta = -(beta - alpha) by ring, Real.cos_neg]
  rw [hcosEq]
  nlinarith [hscaled]

/-- Pair separation can be checked on either arc between the two polar
angles.  The complementary branch shifts one point by a full turn and swaps
which endpoint is listed first. -/
theorem fifteenPolarPair_separated_of_touchAngle_le_cyclic_arcs
    (a b alpha beta : ℝ)
    (ha : 0 < a) (hb : 0 < b)
    (hargLo : -1 ≤ fifteenAngleCosineArgument a b)
    (hargHi : fifteenAngleCosineArgument a b ≤ 1)
    (hangleForward : fifteenTouchAngle a b ≤ beta - alpha)
    (hangleBackward : fifteenTouchAngle a b ≤
      2 * Real.pi - (beta - alpha)) :
    4 ≤ pointNorm
      ((polarPoint a alpha).1 - (polarPoint b beta).1,
       (polarPoint a alpha).2 - (polarPoint b beta).2) ^ 2 := by
  by_cases hshort : beta - alpha ≤ Real.pi
  · exact fifteenPolarPair_separated_of_touchAngle_le_gap a b alpha beta
      ha hb hshort hangleForward hargLo hargHi
  · have hgapSwap : (alpha + 2 * Real.pi) - beta ≤ Real.pi := by
      linarith
    have hangleSymm : fifteenTouchAngle b a = fifteenTouchAngle a b := by
      unfold fifteenTouchAngle
      rw [fifteenAngleCosineArgument_symm]
    have hangleSwap : fifteenTouchAngle b a ≤
        (alpha + 2 * Real.pi) - beta := by
      rw [hangleSymm]
      linarith
    have hargLoSwap : -1 ≤ fifteenAngleCosineArgument b a := by
      rw [fifteenAngleCosineArgument_symm]
      exact hargLo
    have hargHiSwap : fifteenAngleCosineArgument b a ≤ 1 := by
      rw [fifteenAngleCosineArgument_symm]
      exact hargHi
    have hsepSwap := fifteenPolarPair_separated_of_touchAngle_le_gap
      b a beta (alpha + 2 * Real.pi) hb ha hgapSwap hangleSwap
      hargLoSwap hargHiSwap
    rw [fifteenPolarPair_distance_sq] at hsepSwap ⊢
    have hcos : Real.cos (beta - (alpha + 2 * Real.pi)) =
        Real.cos (alpha - beta) := by
      calc
        Real.cos (beta - (alpha + 2 * Real.pi)) =
            Real.cos ((beta - alpha) - 2 * Real.pi) := by congr 1 <;> ring
        _ = Real.cos (beta - alpha) := Real.cos_sub_two_pi _
        _ = Real.cos (alpha - beta) := by
          rw [show beta - alpha = -(alpha - beta) by ring, Real.cos_neg]
    rw [hcos] at hsepSwap
    nlinarith [hsepSwap]

/-- Candidate inner centers separated by their regular-pentagon angular gap. -/
theorem fifteenCandidateInnerPair_separated_of_gap
    (alpha beta : ℝ)
    (hgap : 2 * fifteenLocalPhi ≤ beta - alpha)
    (hgapPi : beta - alpha ≤ Real.pi) :
    4 ≤ pointNorm
      ((polarPoint fifteenCandidateInnerRadius alpha).1 -
          (polarPoint fifteenCandidateInnerRadius beta).1,
       (polarPoint fifteenCandidateInnerRadius alpha).2 -
          (polarPoint fifteenCandidateInnerRadius beta).2) ^ 2 := by
  have hangle : fifteenTouchAngle fifteenCandidateInnerRadius
      fifteenCandidateInnerRadius ≤ beta - alpha := by
    rw [fifteenCandidateDirectAngle_eq]
    exact hgap
  have hrange := Real.cos_mem_Icc (2 * fifteenLocalPhi)
  exact fifteenPolarPair_separated_of_touchAngle_le_gap
    fifteenCandidateInnerRadius fifteenCandidateInnerRadius alpha beta
    fifteenCandidateInnerRadius_pos fifteenCandidateInnerRadius_pos
    hgapPi hangle
    (by rw [fifteenCandidateAngleCosineArgument_eq]; exact hrange.1)
    (by rw [fifteenCandidateAngleCosineArgument_eq]; exact hrange.2)

/-- Candidate inner/outer centers separated by their construction angle. -/
theorem fifteenCandidateMixedPair_separated_of_gap
    (alpha beta : ℝ)
    (hgap : fifteenLocalPhi - fifteenCandidateWallHalfAngle ≤ beta - alpha)
    (hgapPi : beta - alpha ≤ Real.pi) :
    4 ≤ pointNorm
      ((polarPoint fifteenCandidateInnerRadius alpha).1 -
          (polarPoint fifteenCandidateOuterRadius beta).1,
       (polarPoint fifteenCandidateInnerRadius alpha).2 -
          (polarPoint fifteenCandidateOuterRadius beta).2) ^ 2 := by
  have hangle : fifteenTouchAngle fifteenCandidateInnerRadius
      fifteenCandidateOuterRadius ≤ beta - alpha := by
    rw [fifteenCandidateMixedTouchAngle_eq]
    exact hgap
  have hrange := Real.cos_mem_Icc
    (fifteenLocalPhi - fifteenCandidateWallHalfAngle)
  exact fifteenPolarPair_separated_of_touchAngle_le_gap
    fifteenCandidateInnerRadius fifteenCandidateOuterRadius alpha beta
    fifteenCandidateInnerRadius_pos fifteenCandidateOuterRadius_pos
    hgapPi hangle
    (by rw [fifteenCandidateMixedAngleCosineArgument_eq]; exact hrange.1)
    (by rw [fifteenCandidateMixedAngleCosineArgument_eq]; exact hrange.2)

/-- Candidate outer centers separated by the smaller outer-ring gap. -/
theorem fifteenCandidateOuterPair_separated_of_gap
    (alpha beta : ℝ)
    (hgap : 2 * fifteenCandidateWallHalfAngle ≤ beta - alpha)
    (hgapPi : beta - alpha ≤ Real.pi) :
    4 ≤ pointNorm
      ((polarPoint fifteenCandidateOuterRadius alpha).1 -
          (polarPoint fifteenCandidateOuterRadius beta).1,
       (polarPoint fifteenCandidateOuterRadius alpha).2 -
          (polarPoint fifteenCandidateOuterRadius beta).2) ^ 2 := by
  have hangle : fifteenTouchAngle fifteenCandidateOuterRadius
      fifteenCandidateOuterRadius ≤ beta - alpha := by
    rw [fifteenCandidateWallTouchAngle_eq]
    exact hgap
  have hrange := Real.cos_mem_Icc
    (2 * fifteenCandidateWallHalfAngle)
  exact fifteenPolarPair_separated_of_touchAngle_le_gap
    fifteenCandidateOuterRadius fifteenCandidateOuterRadius alpha beta
    fifteenCandidateOuterRadius_pos fifteenCandidateOuterRadius_pos
    hgapPi hangle
    (by rw [fifteenCandidateWallCosineArgument_eq]; exact hrange.1)
    (by rw [fifteenCandidateWallCosineArgument_eq]; exact hrange.2)

/-- The angular offset from an inner center to the following outer center in
the fivefold-symmetric candidate. -/
noncomputable def fifteenCandidateMixedGap : ℝ :=
  fifteenLocalPhi - fifteenCandidateWallHalfAngle

/-- Polar angle of the cyclic candidate sequence.  Each sector lists an inner
center, the clockwise outer center from the next sector, then its counterpart;
the index 15 is the periodic copy of index 0 at angle `2*pi`. -/
noncomputable def fifteenCandidateAngleNat (n : ℕ) : ℝ :=
  let k : ℝ := ((n / 3 : ℕ) : ℝ)
  if n % 3 = 0 then
    2 * k * fifteenLocalPhi
  else if n % 3 = 1 then
    2 * k * fifteenLocalPhi + fifteenCandidateMixedGap
  else
    2 * (k + 1) * fifteenLocalPhi - fifteenCandidateMixedGap

/-- Inner centers occupy every third point in the cyclic candidate order. -/
noncomputable def fifteenCandidateRadiusNat (n : ℕ) : ℝ :=
  if n % 3 = 0 then fifteenCandidateInnerRadius
  else fifteenCandidateOuterRadius

/-- The three consecutive angular gaps repeat as mixed, outer, mixed. -/
theorem fifteenCandidateAngleNat_step (n : ℕ) :
    (if n % 3 = 0 then
      fifteenCandidateAngleNat (n + 1) - fifteenCandidateAngleNat n =
        fifteenCandidateMixedGap
    else if n % 3 = 1 then
      fifteenCandidateAngleNat (n + 1) - fifteenCandidateAngleNat n =
        2 * fifteenCandidateWallHalfAngle
    else
      fifteenCandidateAngleNat (n + 1) - fifteenCandidateAngleNat n =
        fifteenCandidateMixedGap) := by
  by_cases h0 : n % 3 = 0
  · have hq : (n + 1) / 3 = n / 3 := by omega
    have hr : (n + 1) % 3 = 1 := by omega
    simp [fifteenCandidateAngleNat, h0, hq, hr]
  · by_cases h1 : n % 3 = 1
    · have hq : (n + 1) / 3 = n / 3 := by omega
      have hr : (n + 1) % 3 = 2 := by omega
      simp [fifteenCandidateAngleNat, h1, hq, hr,
        fifteenCandidateMixedGap]
      ring
    · have h2 : n % 3 = 2 := by omega
      have hq : (n + 1) / 3 = n / 3 + 1 := by omega
      have hr : (n + 1) % 3 = 0 := by omega
      simp [fifteenCandidateAngleNat, h2, hq, hr,
        fifteenCandidateMixedGap]

theorem fifteenCandidateAngleNat_inner_sector (k : ℕ) :
    fifteenCandidateAngleNat (3 * k) =
      2 * (k : ℝ) * fifteenLocalPhi := by
  have hq : (3 * k) / 3 = k := by omega
  have hr : (3 * k) % 3 = 0 := by omega
  simp [fifteenCandidateAngleNat, hq, hr]

theorem fifteenCandidateAngleNat_outer_left_sector (k : ℕ) :
    fifteenCandidateAngleNat (3 * k + 1) =
      2 * (k : ℝ) * fifteenLocalPhi + fifteenCandidateMixedGap := by
  have hq : (3 * k + 1) / 3 = k := by omega
  have hr : (3 * k + 1) % 3 = 1 := by omega
  simp [fifteenCandidateAngleNat, hq, hr]

theorem fifteenCandidateAngleNat_outer_right_sector (k : ℕ) :
    fifteenCandidateAngleNat (3 * k + 2) =
      2 * ((k + 1 : ℕ) : ℝ) * fifteenLocalPhi -
        fifteenCandidateMixedGap := by
  have hq : (3 * k + 2) / 3 = k := by omega
  have hr : (3 * k + 2) % 3 = 2 := by omega
  simp [fifteenCandidateAngleNat, hq, hr]

theorem fifteenCandidateAngleNat_strict_step (n : ℕ) :
    fifteenCandidateAngleNat n < fifteenCandidateAngleNat (n + 1) := by
  have hmix : 0 < fifteenCandidateMixedGap :=
    sub_pos.mpr fifteenCandidateWallHalfAngle_lt_localPhi
  have hstep := fifteenCandidateAngleNat_step n
  by_cases h0 : n % 3 = 0
  · have hgap : fifteenCandidateAngleNat (n + 1) -
        fifteenCandidateAngleNat n = fifteenCandidateMixedGap := by
      simpa [h0] using hstep
    linarith [hmix]
  · by_cases h1 : n % 3 = 1
    · have hgap : fifteenCandidateAngleNat (n + 1) -
          fifteenCandidateAngleNat n =
            2 * fifteenCandidateWallHalfAngle := by
        simpa [h0, h1] using hstep
      linarith [fifteenCandidateWallHalfAngle_pos]
    · have hgap : fifteenCandidateAngleNat (n + 1) -
          fifteenCandidateAngleNat n = fifteenCandidateMixedGap := by
        have h2 : n % 3 = 2 := by omega
        simpa [h0, h1, h2] using hstep
      linarith [hmix]

/-- The cyclic list closes at the same point after one full turn. -/
theorem fifteenCandidateAngleNat_fifteen :
    fifteenCandidateAngleNat 15 = 2 * Real.pi := by
  norm_num [fifteenCandidateAngleNat, fifteenCandidateMixedGap,
    fifteenLocalPhi] <;> ring

private theorem fifteenCandidateMixedGap_pos :
    0 < fifteenCandidateMixedGap := by
  exact sub_pos.mpr fifteenCandidateWallHalfAngle_lt_localPhi

private theorem fifteenCandidateMixedGap_lt_pi :
    fifteenCandidateMixedGap < Real.pi := by
  unfold fifteenCandidateMixedGap
  linarith [fifteenCandidateWallHalfAngle_pos, fifteenLocalPhi_lt_pi]

private theorem fifteenCandidateOuterGap_le_pi :
    2 * fifteenCandidateWallHalfAngle ≤ Real.pi := by
  have h := Real.arcsin_le_pi_div_two
    (1 / fifteenCandidateOuterRadius)
  unfold fifteenCandidateWallHalfAngle at h ⊢
  linarith

private theorem fifteenCandidateWallHalfAngle_lt_halfPhi :
    fifteenCandidateWallHalfAngle < fifteenLocalPhi / 2 := by
  have hsqrtPos : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg _
  have hsqrtSq : (Real.sqrt 5) ^ 2 = 5 := by
    rw [Real.sq_sqrt]
    norm_num
  have hcos : (4 / 5 : ℝ) < Real.cos fifteenLocalPhi := by
    rw [fifteenLocalPhi, Real.cos_pi_div_five]
    nlinarith [hsqrtPos, hsqrtSq]
  have hsin : Real.sin fifteenLocalPhi < 3 / 5 := by
    have htrig := Real.sin_sq_add_cos_sq fifteenLocalPhi
    nlinarith [fifteenLocalSin_pos, hcos, htrig]
  have hcot : 4 / 3 <
      Real.cos fifteenLocalPhi / Real.sin fifteenLocalPhi := by
    rw [lt_div_iff₀ fifteenLocalSin_pos]
    nlinarith [hcos, hsin]
  have hbase : (10 / 3 : ℝ) <
      2 + Real.cos fifteenLocalPhi / Real.sin fifteenLocalPhi := by
    linarith
  have hbasePos : 0 <
      2 + Real.cos fifteenLocalPhi / Real.sin fifteenLocalPhi := by
    linarith
  have hbaseSq : (10 / 3 : ℝ) ^ 2 <
      (2 + Real.cos fifteenLocalPhi / Real.sin fifteenLocalPhi) ^ 2 :=
    (sq_lt_sq₀ (by norm_num) hbasePos.le).2 hbase
  have houterSq : (109 / 9 : ℝ) < fifteenCandidateOuterRadius ^ 2 := by
    rw [fifteenCandidateOuterRadius_sq]
    nlinarith [hbaseSq]
  have houterWide : (1000 / 289 : ℝ) < fifteenCandidateOuterRadius := by
    apply (sq_lt_sq₀ (by norm_num) (le_of_lt fifteenCandidateOuterRadius_pos)).mp
    have hrat : (1000 / 289 : ℝ) ^ 2 < 109 / 9 := by norm_num
    exact hrat.trans houterSq
  let x := fifteenLocalPhi / 2
  have hxpos : 0 < x := by
    dsimp [x]
    exact div_pos fifteenLocalPhi_pos (by norm_num)
  have hxlo : (3 / 10 : ℝ) < x := by
    dsimp [x, fifteenLocalPhi]
    nlinarith [Real.pi_gt_three]
  have hxhi : x < 2 / 5 := by
    dsimp [x, fifteenLocalPhi]
    nlinarith [Real.pi_lt_four]
  have hxsin : (289 / 1000 : ℝ) < Real.sin x := by
    have hxle : 0 ≤ x := le_of_lt hxpos
    have hTaylor := Real.sin_ge_sub_cube hxle
    have hx2 : x ^ 2 < (2 / 5 : ℝ) ^ 2 := by
      exact (sq_lt_sq₀ hxle (by norm_num)).2 hxhi
    have hx3 : x ^ 3 < (2 / 5 : ℝ) ^ 3 := by
      calc
        x ^ 3 = x ^ 2 * x := by ring
        _ < (2 / 5 : ℝ) ^ 2 * x :=
          mul_lt_mul_of_pos_right hx2 hxpos
        _ < (2 / 5 : ℝ) ^ 2 * (2 / 5) :=
          mul_lt_mul_of_pos_left hxhi (by norm_num)
    nlinarith [hTaylor, hxlo, hx3]
  have hprod : 1 < fifteenCandidateOuterRadius * Real.sin x := by
    have hfirst : (1000 / 289 : ℝ) * (289 / 1000) <
        fifteenCandidateOuterRadius * (289 / 1000) :=
      mul_lt_mul_of_pos_right houterWide (by norm_num)
    have hsecond : fifteenCandidateOuterRadius * (289 / 1000) <
        fifteenCandidateOuterRadius * Real.sin x :=
      mul_lt_mul_of_pos_left hxsin fifteenCandidateOuterRadius_pos
    calc
      1 = (1000 / 289 : ℝ) * (289 / 1000) := by norm_num
      _ < fifteenCandidateOuterRadius * (289 / 1000) := hfirst
      _ < fifteenCandidateOuterRadius * Real.sin x := hsecond
  have hrecip : 1 / fifteenCandidateOuterRadius < Real.sin x := by
    rw [div_lt_iff₀ fifteenCandidateOuterRadius_pos]
    nlinarith [hprod]
  have harcsin : Real.arcsin (1 / fifteenCandidateOuterRadius) < x := by
    apply (Real.arcsin_lt_iff_lt_sin
      (show (1 / fifteenCandidateOuterRadius) ∈ Set.Icc (-1 : ℝ) 1 by
        constructor
        · have hpos := one_div_pos.mpr fifteenCandidateOuterRadius_pos
          linarith
        · rw [div_le_one fifteenCandidateOuterRadius_pos]
          exact fifteenCandidateOuterRadius_gt_one.le)
      (show x ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) by
        constructor
        · dsimp [x]
          linarith [fifteenLocalPhi_pos, Real.pi_pos]
        · dsimp [x, fifteenLocalPhi]
          nlinarith [Real.pi_pos])).2
    exact hrecip
  simpa [x, fifteenCandidateWallHalfAngle] using harcsin

private theorem fifteenCandidateCosineArgument_bounds
    {a b : ℝ}
    (ha : a = fifteenCandidateInnerRadius ∨
      a = fifteenCandidateOuterRadius)
    (hb : b = fifteenCandidateInnerRadius ∨
      b = fifteenCandidateOuterRadius) :
    -1 ≤ fifteenAngleCosineArgument a b ∧
      fifteenAngleCosineArgument a b ≤ 1 := by
  rcases ha with ha | ha
  · subst a
    rcases hb with hb | hb
    · subst b
      have hcos := Real.cos_mem_Icc (2 * fifteenLocalPhi)
      rw [fifteenCandidateAngleCosineArgument_eq]
      exact hcos
    · subst b
      have hcos := Real.cos_mem_Icc fifteenCandidateMixedGap
      rw [fifteenCandidateMixedAngleCosineArgument_eq]
      exact hcos
  · subst a
    rcases hb with hb | hb
    · subst b
      have hcos := Real.cos_mem_Icc fifteenCandidateMixedGap
      rw [fifteenAngleCosineArgument_symm,
        fifteenCandidateMixedAngleCosineArgument_eq]
      exact hcos
    · subst b
      have hcos := Real.cos_mem_Icc
        (2 * fifteenCandidateWallHalfAngle)
      rw [fifteenCandidateWallCosineArgument_eq]
      exact hcos

private theorem fifteenCandidateTouchAngle_symm (a b : ℝ) :
    fifteenTouchAngle a b = fifteenTouchAngle b a := by
  unfold fifteenTouchAngle
  rw [fifteenAngleCosineArgument_symm]

private theorem fifteenCandidateMixedTouchAngle_outerFirst_eq :
    fifteenTouchAngle fifteenCandidateOuterRadius
      fifteenCandidateInnerRadius =
        fifteenLocalPhi - fifteenCandidateWallHalfAngle := by
  rw [fifteenCandidateTouchAngle_symm,
    fifteenCandidateMixedTouchAngle_eq]

private theorem fifteenCandidatePair_cyclicAngleBounds
    (i j : Fin 15) (hij : i.1 < j.1) :
    fifteenTouchAngle (fifteenCandidateRadiusNat i.1)
        (fifteenCandidateRadiusNat j.1) ≤
        fifteenCandidateAngleNat j.1 - fifteenCandidateAngleNat i.1 ∧
      fifteenTouchAngle (fifteenCandidateRadiusNat i.1)
        (fifteenCandidateRadiusNat j.1) ≤
        2 * Real.pi -
          (fifteenCandidateAngleNat j.1 - fifteenCandidateAngleNat i.1) := by
  have hhalf := fifteenCandidateWallHalfAngle_lt_halfPhi
  have hwall := fifteenCandidateWallHalfAngle_pos
  have hphi := fifteenLocalPhi_pos
  have hperiod : 5 * fifteenLocalPhi = Real.pi := by
    unfold fifteenLocalPhi
    ring
  fin_cases i <;> fin_cases j <;>
    norm_num at hij <;>
    simp [fifteenCandidateAngleNat, fifteenCandidateRadiusNat,
      fifteenCandidateMixedGap, fifteenCandidateDirectAngle_eq,
      fifteenCandidateMixedTouchAngle_eq, fifteenCandidateWallTouchAngle_eq,
      fifteenCandidateMixedTouchAngle_outerFirst_eq] <;>
    first
    | (constructor <;> linarith [hhalf, hwall, hphi, hperiod])
    | linarith [hhalf, hwall, hphi, hperiod]

/-- A reversed mixed pair has the same distance as the inner-first version. -/
theorem fifteenCandidateMixedPair_outerFirst_separated_of_gap
    (alpha beta : ℝ)
    (hgap : fifteenCandidateMixedGap ≤ beta - alpha)
    (hgapPi : beta - alpha ≤ Real.pi) :
    4 ≤ pointNorm
      ((polarPoint fifteenCandidateOuterRadius alpha).1 -
          (polarPoint fifteenCandidateInnerRadius beta).1,
       (polarPoint fifteenCandidateOuterRadius alpha).2 -
          (polarPoint fifteenCandidateInnerRadius beta).2) ^ 2 := by
  have hangle : fifteenTouchAngle fifteenCandidateOuterRadius
      fifteenCandidateInnerRadius ≤ beta - alpha := by
    have hsymm : fifteenTouchAngle fifteenCandidateOuterRadius
        fifteenCandidateInnerRadius =
        fifteenTouchAngle fifteenCandidateInnerRadius
          fifteenCandidateOuterRadius := by
      unfold fifteenTouchAngle
      rw [fifteenAngleCosineArgument_symm]
    rw [hsymm, fifteenCandidateMixedTouchAngle_eq]
    exact hgap
  have hrange := Real.cos_mem_Icc fifteenCandidateMixedGap
  exact fifteenPolarPair_separated_of_touchAngle_le_gap
    fifteenCandidateOuterRadius fifteenCandidateInnerRadius alpha beta
    fifteenCandidateOuterRadius_pos fifteenCandidateInnerRadius_pos
    hgapPi hangle
    (by
      rw [fifteenAngleCosineArgument_symm,
        fifteenCandidateMixedAngleCosineArgument_eq]
      exact hrange.1)
    (by
      rw [fifteenAngleCosineArgument_symm,
        fifteenCandidateMixedAngleCosineArgument_eq]
      exact hrange.2)

/-- Every consecutive pair in the candidate cyclic order is separated.  The
statement includes the wraparound pair, represented by the angle at index 15. -/
theorem fifteenCandidateConsecutiveCenters_separated (n : ℕ) :
    4 ≤ pointNorm
      ((polarPoint (fifteenCandidateRadiusNat n)
          (fifteenCandidateAngleNat n)).1 -
        (polarPoint (fifteenCandidateRadiusNat (n + 1))
          (fifteenCandidateAngleNat (n + 1))).1,
       (polarPoint (fifteenCandidateRadiusNat n)
          (fifteenCandidateAngleNat n)).2 -
        (polarPoint (fifteenCandidateRadiusNat (n + 1))
          (fifteenCandidateAngleNat (n + 1))).2) ^ 2 := by
  have hstep := fifteenCandidateAngleNat_step n
  by_cases h0 : n % 3 = 0
  · have hgap : fifteenCandidateAngleNat (n + 1) -
        fifteenCandidateAngleNat n = fifteenCandidateMixedGap := by
      simpa [h0] using hstep
    have hnext : (n + 1) % 3 = 1 := by omega
    have hradius0 : fifteenCandidateRadiusNat n =
        fifteenCandidateInnerRadius := by simp [fifteenCandidateRadiusNat, h0]
    have hradius1 : fifteenCandidateRadiusNat (n + 1) =
        fifteenCandidateOuterRadius := by
      simp [fifteenCandidateRadiusNat, hnext]
    rw [hradius0, hradius1]
    have hgapPi : fifteenCandidateAngleNat (n + 1) -
        fifteenCandidateAngleNat n ≤ Real.pi := by
      rw [hgap]
      exact fifteenCandidateMixedGap_lt_pi.le
    exact fifteenCandidateMixedPair_separated_of_gap
      (fifteenCandidateAngleNat n) (fifteenCandidateAngleNat (n + 1))
      (by simpa [hgap, fifteenCandidateMixedGap]) hgapPi
  · by_cases h1 : n % 3 = 1
    · have hgap : fifteenCandidateAngleNat (n + 1) -
          fifteenCandidateAngleNat n =
            2 * fifteenCandidateWallHalfAngle := by
        simpa [h0, h1] using hstep
      have hnext : (n + 1) % 3 = 2 := by omega
      have hradius0 : fifteenCandidateRadiusNat n =
          fifteenCandidateOuterRadius := by
        simp [fifteenCandidateRadiusNat, h0]
      have hradius1 : fifteenCandidateRadiusNat (n + 1) =
          fifteenCandidateOuterRadius := by
        simp [fifteenCandidateRadiusNat, hnext]
      rw [hradius0, hradius1]
      have hgapPi : fifteenCandidateAngleNat (n + 1) -
          fifteenCandidateAngleNat n ≤ Real.pi := by
        rw [hgap]
        exact fifteenCandidateOuterGap_le_pi
      exact fifteenCandidateOuterPair_separated_of_gap
        (fifteenCandidateAngleNat n) (fifteenCandidateAngleNat (n + 1))
        (by simpa [hgap]) hgapPi
    · have h2 : n % 3 = 2 := by omega
      have hgap : fifteenCandidateAngleNat (n + 1) -
          fifteenCandidateAngleNat n = fifteenCandidateMixedGap := by
        simpa [h0, h1, h2] using hstep
      have hnext : (n + 1) % 3 = 0 := by omega
      have hradius0 : fifteenCandidateRadiusNat n =
          fifteenCandidateOuterRadius := by
        simp [fifteenCandidateRadiusNat, h0]
      have hradius1 : fifteenCandidateRadiusNat (n + 1) =
          fifteenCandidateInnerRadius := by
        simp [fifteenCandidateRadiusNat, hnext]
      rw [hradius0, hradius1]
      have hgapPi : fifteenCandidateAngleNat (n + 1) -
          fifteenCandidateAngleNat n ≤ Real.pi := by
        rw [hgap]
        exact fifteenCandidateMixedGap_lt_pi.le
      exact fifteenCandidateMixedPair_outerFirst_separated_of_gap
        (fifteenCandidateAngleNat n) (fifteenCandidateAngleNat (n + 1))
        (by simpa [hgap, fifteenCandidateMixedGap]) hgapPi

private theorem fifteenCandidateInnerRadius_lt_outerRadius :
    fifteenCandidateInnerRadius < fifteenCandidateOuterRadius := by
  have hratio : 0 < Real.cos fifteenLocalPhi / Real.sin fifteenLocalPhi :=
    div_pos fifteenLocalCos_pos fifteenLocalSin_pos
  have hbase : 2 < 2 + Real.cos fifteenLocalPhi / Real.sin fifteenLocalPhi :=
    lt_add_of_pos_right _ hratio
  have hbasePos : 0 < 2 + Real.cos fifteenLocalPhi / Real.sin fifteenLocalPhi := by
    linarith
  have houterSq : (2 : ℝ) ^ 2 < fifteenCandidateOuterRadius ^ 2 := by
    rw [fifteenCandidateOuterRadius_sq]
    nlinarith [sq_pos_of_pos hbasePos]
  have houter : 2 < fifteenCandidateOuterRadius := by
    apply (sq_lt_sq₀ (by norm_num) (le_of_lt fifteenCandidateOuterRadius_pos)).mp
    exact houterSq
  have hinner : fifteenCandidateInnerRadius < 2 := by
    exact lt_trans fifteenCandidateInnerRadius_lt_43_25 (by norm_num)
  exact lt_trans hinner houter

private theorem fifteenCandidateRadiusNat_type (n : ℕ) :
    fifteenCandidateRadiusNat n = fifteenCandidateInnerRadius ∨
      fifteenCandidateRadiusNat n = fifteenCandidateOuterRadius := by
  by_cases h : n % 3 = 0
  · left
    simp [fifteenCandidateRadiusNat, h]
  · right
    simp [fifteenCandidateRadiusNat, h]

private theorem fifteenCandidateRadiusNat_pos (n : ℕ) :
    0 < fifteenCandidateRadiusNat n := by
  rcases fifteenCandidateRadiusNat_type n with h | h
  · rw [h]
    exact fifteenCandidateInnerRadius_pos
  · rw [h]
    exact fifteenCandidateOuterRadius_pos

private theorem fifteenCandidateCenters_separated_ordered
    (i j : Fin 15) (hij : i.1 < j.1) :
    4 ≤ pointNorm
      ((polarPoint (fifteenCandidateRadiusNat i.1)
          (fifteenCandidateAngleNat i.1)).1 -
        (polarPoint (fifteenCandidateRadiusNat j.1)
          (fifteenCandidateAngleNat j.1)).1,
       (polarPoint (fifteenCandidateRadiusNat i.1)
          (fifteenCandidateAngleNat i.1)).2 -
        (polarPoint (fifteenCandidateRadiusNat j.1)
          (fifteenCandidateAngleNat j.1)).2) ^ 2 := by
  have htypes := fifteenCandidatePair_cyclicAngleBounds i j hij
  have harg := fifteenCandidateCosineArgument_bounds
    (fifteenCandidateRadiusNat_type i.1)
    (fifteenCandidateRadiusNat_type j.1)
  exact fifteenPolarPair_separated_of_touchAngle_le_cyclic_arcs
    (fifteenCandidateRadiusNat i.1) (fifteenCandidateRadiusNat j.1)
    (fifteenCandidateAngleNat i.1) (fifteenCandidateAngleNat j.1)
    (fifteenCandidateRadiusNat_pos i.1)
    (fifteenCandidateRadiusNat_pos j.1)
    harg.1 harg.2 htypes.1 htypes.2

private theorem fifteenCandidatePolarPair_distance_symm
    (a b alpha beta : ℝ) :
    pointNorm
        ((polarPoint a alpha).1 - (polarPoint b beta).1,
         (polarPoint a alpha).2 - (polarPoint b beta).2) ^ 2 =
      pointNorm
        ((polarPoint b beta).1 - (polarPoint a alpha).1,
         (polarPoint b beta).2 - (polarPoint a alpha).2) ^ 2 := by
  rw [fifteenPolarPair_distance_sq, fifteenPolarPair_distance_sq]
  rw [show beta - alpha = -(alpha - beta) by ring, Real.cos_neg]
  ring

private theorem fifteenCandidateCenters_separated
    (i j : Fin 15) (hij : i ≠ j) :
    4 ≤ pointNorm
      ((polarPoint (fifteenCandidateRadiusNat i.1)
          (fifteenCandidateAngleNat i.1)).1 -
        (polarPoint (fifteenCandidateRadiusNat j.1)
          (fifteenCandidateAngleNat j.1)).1,
       (polarPoint (fifteenCandidateRadiusNat i.1)
          (fifteenCandidateAngleNat i.1)).2 -
        (polarPoint (fifteenCandidateRadiusNat j.1)
          (fifteenCandidateAngleNat j.1)).2) ^ 2 := by
  by_cases hlt : i.1 < j.1
  · exact fifteenCandidateCenters_separated_ordered i j hlt
  · have hgt : j.1 < i.1 := by
      have hne : i.1 ≠ j.1 := fun h => hij (Fin.ext h)
      omega
    have hsep := fifteenCandidateCenters_separated_ordered j i hgt
    rw [fifteenCandidatePolarPair_distance_symm] at hsep
    exact hsep

/-- The classical fivefold-symmetric arrangement, expressed as a genuine
`Packing` in the exact candidate container.  The lower-bound theorem for this
problem then combines with this witness to identify the optimum. -/
noncomputable def fifteenCandidatePacking :
    Packing 15 (fifteenCandidateOuterRadius + 1) where
  circles := fun i =>
    ⟨polarPoint (fifteenCandidateRadiusNat i.1)
      (fifteenCandidateAngleNat i.1), 1, by norm_num⟩
  container_nonneg := by
    linarith [fifteenCandidateOuterRadius_pos]
  contained := by
    intro i
    change 1 ≤ fifteenCandidateOuterRadius + 1 ∧
      distSq
        (polarPoint (fifteenCandidateRadiusNat i.1)
          (fifteenCandidateAngleNat i.1)) (0, 0) ≤
        ((fifteenCandidateOuterRadius + 1) - 1) ^ 2
    constructor
    · linarith [fifteenCandidateOuterRadius_pos]
    · have hradius :
        fifteenCandidateRadiusNat i.1 ≤ fifteenCandidateOuterRadius := by
        rcases fifteenCandidateRadiusNat_type i.1 with h | h
        · rw [h]
          exact le_of_lt fifteenCandidateInnerRadius_lt_outerRadius
        · rw [h]
      have hnonneg := le_of_lt (fifteenCandidateRadiusNat_pos i.1)
      have houterNonneg := le_of_lt fifteenCandidateOuterRadius_pos
      have hsq : (fifteenCandidateRadiusNat i.1) ^ 2 ≤
          fifteenCandidateOuterRadius ^ 2 :=
        (sq_le_sq₀ hnonneg houterNonneg).2 hradius
      have hcenter :
          distSq
            (polarPoint (fifteenCandidateRadiusNat i.1)
              (fifteenCandidateAngleNat i.1)) (0, 0) =
            (fifteenCandidateRadiusNat i.1) ^ 2 := by
        simp only [distSq, polarPoint]
        nlinarith [Real.sin_sq_add_cos_sq
          (fifteenCandidateAngleNat i.1)]
      rw [hcenter, show (fifteenCandidateOuterRadius + 1) - 1 =
        fifteenCandidateOuterRadius by ring]
      exact hsq
  separated := by
    intro i j hij
    change (1 + 1) ^ 2 ≤
      distSq
        (polarPoint (fifteenCandidateRadiusNat i.1)
          (fifteenCandidateAngleNat i.1))
        (polarPoint (fifteenCandidateRadiusNat j.1)
          (fifteenCandidateAngleNat j.1))
    have hsep := fifteenCandidateCenters_separated i j hij
    norm_num at hsep ⊢
    simpa [distSq, pointNorm_sq] using hsep

theorem fifteenCandidatePacking_exists :
    Nonempty (Packing 15 (fifteenCandidateOuterRadius + 1)) :=
  ⟨fifteenCandidatePacking⟩

end CirclePacking
