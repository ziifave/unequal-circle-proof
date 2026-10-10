import CirclePacking.MainAngleNecessary
import CirclePacking.ArctanTaylor

/-!
# Quarter-angle form of the main barrier equations

The rational certificate evaluates the barriers using `4 * arctan(q)` rather
than direct numerical `arccos` calls. This file records the exact rewrite of
the two barrier expressions into that form and the Machin expansion for `2π`.
It does not assert any numerical sign: those still require the interval data.
-/

namespace CirclePacking

noncomputable section

def mainQuarterAlpha5 (t R : ℝ) : ℝ :=
  arccosQuarterParameter (touchCosine t (R - Real.sqrt 5)
    (Real.sqrt 10 + Real.sqrt 5))

def mainQuarterAlpha6 (t R : ℝ) : ℝ :=
  arccosQuarterParameter (touchCosine t (R - Real.sqrt 6)
    (Real.sqrt 10 + Real.sqrt 6))

def mainQuarterAlpha7 (t R : ℝ) : ℝ :=
  arccosQuarterParameter (touchCosine t (R - Real.sqrt 7)
    (Real.sqrt 10 + Real.sqrt 7))

def mainQuarterBeta57 (R : ℝ) : ℝ :=
  arccosQuarterParameter (touchCosine (R - Real.sqrt 5) (R - Real.sqrt 7)
    (Real.sqrt 5 + Real.sqrt 7))

def mainQuarterBeta79 (R : ℝ) : ℝ :=
  arccosQuarterParameter (touchCosine (R - Real.sqrt 7) (R - Real.sqrt 9)
    (Real.sqrt 7 + Real.sqrt 9))

def mainQuarterBeta92 (R : ℝ) : ℝ :=
  arccosQuarterParameter (touchCosine (R - Real.sqrt 9) (R - Real.sqrt 2)
    (Real.sqrt 9 + Real.sqrt 2))

def mainQuarterBeta28 (R : ℝ) : ℝ :=
  arccosQuarterParameter (touchCosine (R - Real.sqrt 2) (R - Real.sqrt 8)
    (Real.sqrt 2 + Real.sqrt 8))

def mainQuarterBeta86 (R : ℝ) : ℝ :=
  arccosQuarterParameter (touchCosine (R - Real.sqrt 8) (R - Real.sqrt 6)
    (Real.sqrt 8 + Real.sqrt 6))

/-- The squared tangent of half a contact angle has the usual side-length
formula. This exposes the rational expression that the interval certificate
evaluates before applying the quarter-angle square-root reduction. -/
theorem touchCosine_halfAngleRatio {a b d : ℝ}
    (ha : a ≠ 0) (hb : b ≠ 0)
    (hpoly : (a + b) ^ 2 - d ^ 2 ≠ 0) :
    (1 - touchCosine a b d) / (1 + touchCosine a b d) =
      (d ^ 2 - (a - b) ^ 2) / ((a + b) ^ 2 - d ^ 2) := by
  have hab : 2 * a * b ≠ 0 := by positivity
  unfold touchCosine
  have hnum : 1 - (a ^ 2 + b ^ 2 - d ^ 2) / (2 * a * b) =
      (d ^ 2 - (a - b) ^ 2) / (2 * a * b) := by
    field_simp [hab]
    ring
  have hden : 1 + (a ^ 2 + b ^ 2 - d ^ 2) / (2 * a * b) =
      ((a + b) ^ 2 - d ^ 2) / (2 * a * b) := by
    field_simp [hab]
    ring
  rw [hnum, hden]
  field_simp [hab, hpoly]

/-- Triangle inequalities alone certify that the cosine-law argument belongs
to the open domain of `arccos`. -/
theorem touchCosine_mem_Ioo_of_triangle_bounds {a b d : ℝ}
    (ha : 0 < a) (hb : 0 < b)
    (hdiff : |a - b| < d) (hsum : d < a + b) :
    touchCosine a b d ∈ Set.Ioo (-1) 1 := by
  have hdpos : 0 < d := lt_of_le_of_lt (abs_nonneg (a - b)) hdiff
  have hab : 0 < 2 * a * b := by positivity
  have hminusNum : 0 < d ^ 2 - (a - b) ^ 2 := by
    rcases abs_lt.mp hdiff with ⟨hleft, hright⟩
    have h₁ : 0 < d - (a - b) := sub_pos.mpr hright
    have h₂ : 0 < d + (a - b) := by linarith
    have hfactor : d ^ 2 - (a - b) ^ 2 =
        (d - (a - b)) * (d + (a - b)) := by ring
    rw [hfactor]
    exact mul_pos h₁ h₂
  have hplusNum : 0 < (a + b) ^ 2 - d ^ 2 := by
    have h₁ : 0 < a + b - d := sub_pos.mpr hsum
    have h₂ : 0 < a + b + d := by positivity
    have hfactor : (a + b) ^ 2 - d ^ 2 =
        (a + b - d) * (a + b + d) := by ring
    rw [hfactor]
    exact mul_pos h₁ h₂
  have hminus : 1 - touchCosine a b d =
      (d ^ 2 - (a - b) ^ 2) / (2 * a * b) := by
    unfold touchCosine
    field_simp [ne_of_gt ha, ne_of_gt hb]
    ring
  have hplus : 1 + touchCosine a b d =
      ((a + b) ^ 2 - d ^ 2) / (2 * a * b) := by
    unfold touchCosine
    field_simp [ne_of_gt ha, ne_of_gt hb]
    ring
  have hminusPos : 0 < 1 - touchCosine a b d := by
    rw [hminus]
    exact div_pos hminusNum hab
  have hplusPos : 0 < 1 + touchCosine a b d := by
    rw [hplus]
    exact div_pos hplusNum hab
  constructor <;> linarith

theorem mainBarrier_difference_quarter_arctan {t R : ℝ}
    (h5Lo : -1 < touchCosine t (R - Real.sqrt 5) (Real.sqrt 10 + Real.sqrt 5))
    (h5Hi : touchCosine t (R - Real.sqrt 5) (Real.sqrt 10 + Real.sqrt 5) < 1)
    (h57Lo : -1 < touchCosine (R - Real.sqrt 5) (R - Real.sqrt 7)
      (Real.sqrt 5 + Real.sqrt 7))
    (h57Hi : touchCosine (R - Real.sqrt 5) (R - Real.sqrt 7)
      (Real.sqrt 5 + Real.sqrt 7) < 1)
    (h7Lo : -1 < touchCosine t (R - Real.sqrt 7) (Real.sqrt 10 + Real.sqrt 7))
    (h7Hi : touchCosine t (R - Real.sqrt 7) (Real.sqrt 10 + Real.sqrt 7) < 1) :
    mainBarrierA t R - mainBarrierB t R =
      4 * (Real.arctan (mainQuarterAlpha5 t R) +
        Real.arctan (mainQuarterBeta57 R) -
        Real.arctan (mainQuarterAlpha7 t R)) := by
  have h5 := touchAngle_eq_four_arctan_quarterParameter h5Lo h5Hi
  have h57 := touchAngle_eq_four_arctan_quarterParameter h57Lo h57Hi
  have h7 := touchAngle_eq_four_arctan_quarterParameter h7Lo h7Hi
  unfold mainBarrierA mainBarrierB mainAlpha5 mainAlpha6 mainAlpha7
    mainBeta57 mainCommonWallAngles mainBeta79 mainBeta92 mainBeta28 mainBeta86
  rw [h5, h57, h7]
  unfold mainQuarterAlpha5 mainQuarterBeta57 mainQuarterAlpha7
  ring

theorem mainBarrierB_minus_two_pi_quarter_arctan {t R : ℝ}
    (h7Lo : -1 < touchCosine t (R - Real.sqrt 7) (Real.sqrt 10 + Real.sqrt 7))
    (h7Hi : touchCosine t (R - Real.sqrt 7) (Real.sqrt 10 + Real.sqrt 7) < 1)
    (h79Lo : -1 < touchCosine (R - Real.sqrt 7) (R - Real.sqrt 9)
      (Real.sqrt 7 + Real.sqrt 9))
    (h79Hi : touchCosine (R - Real.sqrt 7) (R - Real.sqrt 9)
      (Real.sqrt 7 + Real.sqrt 9) < 1)
    (h92Lo : -1 < touchCosine (R - Real.sqrt 9) (R - Real.sqrt 2)
      (Real.sqrt 9 + Real.sqrt 2))
    (h92Hi : touchCosine (R - Real.sqrt 9) (R - Real.sqrt 2)
      (Real.sqrt 9 + Real.sqrt 2) < 1)
    (h28Lo : -1 < touchCosine (R - Real.sqrt 2) (R - Real.sqrt 8)
      (Real.sqrt 2 + Real.sqrt 8))
    (h28Hi : touchCosine (R - Real.sqrt 2) (R - Real.sqrt 8)
      (Real.sqrt 2 + Real.sqrt 8) < 1)
    (h86Lo : -1 < touchCosine (R - Real.sqrt 8) (R - Real.sqrt 6)
      (Real.sqrt 8 + Real.sqrt 6))
    (h86Hi : touchCosine (R - Real.sqrt 8) (R - Real.sqrt 6)
      (Real.sqrt 8 + Real.sqrt 6) < 1)
    (h6Lo : -1 < touchCosine t (R - Real.sqrt 6) (Real.sqrt 10 + Real.sqrt 6))
    (h6Hi : touchCosine t (R - Real.sqrt 6) (Real.sqrt 10 + Real.sqrt 6) < 1) :
    mainBarrierB t R - 2 * Real.pi =
      4 * (Real.arctan (mainQuarterAlpha7 t R) +
        Real.arctan (mainQuarterBeta79 R) +
        Real.arctan (mainQuarterBeta92 R) +
        Real.arctan (mainQuarterBeta28 R) +
        Real.arctan (mainQuarterBeta86 R) +
        Real.arctan (mainQuarterAlpha6 t R)) - 2 * Real.pi := by
  have h7 := touchAngle_eq_four_arctan_quarterParameter h7Lo h7Hi
  have h79 := touchAngle_eq_four_arctan_quarterParameter h79Lo h79Hi
  have h92 := touchAngle_eq_four_arctan_quarterParameter h92Lo h92Hi
  have h28 := touchAngle_eq_four_arctan_quarterParameter h28Lo h28Hi
  have h86 := touchAngle_eq_four_arctan_quarterParameter h86Lo h86Hi
  have h6 := touchAngle_eq_four_arctan_quarterParameter h6Lo h6Hi
  unfold mainBarrierB mainAlpha7 mainAlpha6 mainCommonWallAngles
    mainBeta79 mainBeta92 mainBeta28 mainBeta86
  rw [h7, h79, h92, h28, h86, h6]
  unfold mainQuarterAlpha7 mainQuarterAlpha6 mainQuarterBeta79
    mainQuarterBeta92 mainQuarterBeta28 mainQuarterBeta86
  ring

theorem two_pi_machin_expansion :
    2 * Real.pi = 32 * Real.arctan (1 / 5 : ℝ) -
      8 * Real.arctan (1 / 239 : ℝ) := by
  have h := Real.four_mul_arctan_inv_5_sub_arctan_inv_239
  have h' : 4 * Real.arctan (1 / 5 : ℝ) -
      Real.arctan (1 / 239 : ℝ) = Real.pi / 4 := by
    simpa [one_div] using h
  calc
    2 * Real.pi = 8 * (Real.pi / 4) := by ring
    _ = 8 * (4 * Real.arctan (1 / 5 : ℝ) -
        Real.arctan (1 / 239 : ℝ)) := by rw [← h']
    _ = 32 * Real.arctan (1 / 5 : ℝ) -
        8 * Real.arctan (1 / 239 : ℝ) := by ring

def twoPiTaylorApprox (n : ℕ) : ℝ :=
  32 * arctanTaylorPartial (1 / 5 : ℝ) n -
    8 * arctanTaylorPartial (1 / 239 : ℝ) n

/-- The exact Machin expansion combined with the alternating-series theorem
gives a fully explicit error bound for a finite rational approximation to
`2π`. -/
theorem two_pi_taylor_approx_error (n : ℕ) :
    |2 * Real.pi - twoPiTaylorApprox n| ≤
      32 * arctanTaylorTerm (1 / 5 : ℝ) n +
        8 * arctanTaylorTerm (1 / 239 : ℝ) n := by
  rw [two_pi_machin_expansion]
  have h5 := arctanTaylor_error_bound
    (x := (1 / 5 : ℝ)) (by norm_num) (by norm_num) n
  have h239 := arctanTaylor_error_bound
    (x := (1 / 239 : ℝ)) (by norm_num) (by norm_num) n
  calc
    |32 * Real.arctan (1 / 5 : ℝ) - 8 * Real.arctan (1 / 239 : ℝ) -
        twoPiTaylorApprox n| =
        |32 * (Real.arctan (1 / 5 : ℝ) - arctanTaylorPartial (1 / 5 : ℝ) n) +
          (-8) * (Real.arctan (1 / 239 : ℝ) -
            arctanTaylorPartial (1 / 239 : ℝ) n)| := by
              congr 1
              simp [twoPiTaylorApprox]
              ring
    _ ≤ |32 * (Real.arctan (1 / 5 : ℝ) -
          arctanTaylorPartial (1 / 5 : ℝ) n)| +
        |(-8) * (Real.arctan (1 / 239 : ℝ) -
          arctanTaylorPartial (1 / 239 : ℝ) n)| := abs_add_le _ _
    _ = 32 * |Real.arctan (1 / 5 : ℝ) -
          arctanTaylorPartial (1 / 5 : ℝ) n| +
        8 * |Real.arctan (1 / 239 : ℝ) -
          arctanTaylorPartial (1 / 239 : ℝ) n| := by
            simp [abs_mul]
    _ ≤ 32 * arctanTaylorTerm (1 / 5 : ℝ) n +
        8 * arctanTaylorTerm (1 / 239 : ℝ) n :=
          add_le_add (mul_le_mul_of_nonneg_left h5 (by norm_num))
            (mul_le_mul_of_nonneg_left h239 (by norm_num))

def mainAlpha5TlowRmidQLo : ℝ :=
  1969086573001596154698 / 10000000000000000000000

def mainAlpha5TlowRmidQHi : ℝ :=
  1969086573001596154699 / 10000000000000000000000

/-- First concrete parameter enclosure from the exact interval certificate.
This is a pilot replay at the midpoint radius on the lower `t` edge. -/
theorem mainAlpha5_tlow_rmid_quarter_parameter_bounds :
    touchCosine 1.0037160860750841
        ((8.3034681221114890 + 8.3034681221114900) / 2 - Real.sqrt 5)
        (Real.sqrt 10 + Real.sqrt 5) ∈ Set.Ioo (-1) 1 ∧
      mainAlpha5TlowRmidQLo ≤
        mainQuarterAlpha5 1.0037160860750841
          ((8.3034681221114890 + 8.3034681221114900) / 2) ∧
      mainQuarterAlpha5 1.0037160860750841
          ((8.3034681221114890 + 8.3034681221114900) / 2) ≤
        mainAlpha5TlowRmidQHi := by
  let t : ℝ := 1.0037160860750841
  let R : ℝ := (8.3034681221114890 + 8.3034681221114900) / 2
  let r5 : ℝ := Real.sqrt 5
  let r10 : ℝ := Real.sqrt 10
  let a : ℝ := R - r5
  let d : ℝ := r10 + r5
  let N : ℝ := d ^ 2 - (a - t) ^ 2
  let D : ℝ := (a + t) ^ 2 - d ^ 2
  let z : ℝ := N / D
  have hr5sq : r5 ^ 2 = 5 := by
    dsimp [r5]
    exact Real.sq_sqrt (by norm_num)
  have hr10sq : r10 ^ 2 = 10 := by
    dsimp [r10]
    exact Real.sq_sqrt (by norm_num)
  have hr5 :
      2.236067977499789696409173 ≤ r5 ∧
        r5 ≤ 2.236067977499789696409174 := by
    constructor
    · apply (sq_le_sq₀ (by norm_num) (Real.sqrt_nonneg _)).mp
      nlinarith [hr5sq]
    · apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by norm_num)).mp
      nlinarith [hr5sq]
  have hr10 :
      3.162277660168379331998893 ≤ r10 ∧
        r10 ≤ 3.162277660168379331998894 := by
    constructor
    · apply (sq_le_sq₀ (by norm_num) (Real.sqrt_nonneg _)).mp
      nlinarith [hr10sq]
    · apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by norm_num)).mp
      nlinarith [hr10sq]
  have htpos : 0 < t := by norm_num [t]
  have hapos : 0 < a := by
    dsimp [a, R, r5]
    nlinarith [hr5.2]
  have hdpos : 0 < d := by
    dsimp [d, r5, r10]
    positivity
  have hDpos : 0 < D := by
    dsimp [D, a, d, R, t]
    nlinarith [hr5.1, hr5.2, hr10.1, hr10.2]
  have hdiff : |t - a| < d := by
    apply abs_lt.mpr
    constructor <;> dsimp [a, d, R, t] <;>
      nlinarith [hr5.1, hr5.2, hr10.1, hr10.2]
  have hsum : d < t + a := by
    dsimp [a, d, R, t]
    nlinarith [hr5.1, hr5.2, hr10.1, hr10.2]
  have hcos : touchCosine t a d ∈ Set.Ioo (-1) 1 :=
    touchCosine_mem_Ioo_of_triangle_bounds htpos hapos hdiff hsum
  have hratio :
      (1 - touchCosine t a d) / (1 + touchCosine t a d) = z := by
    have hside := touchCosine_halfAngleRatio
      (a := t) (b := a) (d := d) (by linarith [htpos]) (by linarith [hapos])
      (by dsimp [a, d, R, t]; nlinarith [hr5.1, hr5.2, hr10.1, hr10.2])
    dsimp [z, N, D]
    convert hside using 1
    ring
  have hQL : 0 ≤ mainAlpha5TlowRmidQLo := by
    norm_num [mainAlpha5TlowRmidQLo]
  have hQLt1 : mainAlpha5TlowRmidQLo < 1 := by
    norm_num [mainAlpha5TlowRmidQLo]
  have hQU0 : 0 ≤ mainAlpha5TlowRmidQHi := by
    norm_num [mainAlpha5TlowRmidQHi]
  have hQU : mainAlpha5TlowRmidQHi < 1 := by
    norm_num [mainAlpha5TlowRmidQHi]
  have hthresholdLo :
      ((1 + mainAlpha5TlowRmidQLo ^ 2) /
        (1 - mainAlpha5TlowRmidQLo ^ 2)) ^ 2 ≤ 1 + z := by
    have hcleared :
        (((1 + mainAlpha5TlowRmidQLo ^ 2) /
          (1 - mainAlpha5TlowRmidQLo ^ 2)) ^ 2 - 1) * D ≤ N := by
      dsimp [D, N, a, d, R, t, r5, r10]
      norm_num [mainAlpha5TlowRmidQLo]
      nlinarith [hr5.1, hr5.2, hr10.1, hr10.2, hr5sq, hr10sq]
    have hform : (((1 + mainAlpha5TlowRmidQLo ^ 2) /
          (1 - mainAlpha5TlowRmidQLo ^ 2)) ^ 2 - 1) ≤ z := by
      dsimp [z]
      exact (le_div_iff₀ hDpos).2 hcleared
    linarith
  have hthresholdHi :
      1 + z ≤ ((1 + mainAlpha5TlowRmidQHi ^ 2) /
        (1 - mainAlpha5TlowRmidQHi ^ 2)) ^ 2 := by
    have hcleared :
        N ≤ (((1 + mainAlpha5TlowRmidQHi ^ 2) /
          (1 - mainAlpha5TlowRmidQHi ^ 2)) ^ 2 - 1) * D := by
      dsimp [D, N, a, d, R, t, r5, r10]
      norm_num [mainAlpha5TlowRmidQHi]
      nlinarith [hr5.1, hr5.2, hr10.1, hr10.2, hr5sq, hr10sq]
    have hform : z ≤ (((1 + mainAlpha5TlowRmidQHi ^ 2) /
          (1 - mainAlpha5TlowRmidQHi ^ 2)) ^ 2 - 1) := by
      dsimp [z]
      exact (div_le_iff₀ hDpos).2 hcleared
    linarith
  have hlo := le_arccosQuarterParameter_of_ratio_bound
    hcos.1 hcos.2 hQL hQLt1 (by rw [hratio]; exact hthresholdLo)
  have hhi := arccosQuarterParameter_le_of_ratio_bound
    hcos.1 hcos.2 hQU0 hQU (by rw [hratio]; exact hthresholdHi)
  refine ⟨?_, ?_, ?_⟩
  · simpa [t, R, a, d, r5, r10] using hcos
  · simpa [mainQuarterAlpha5, t, R] using hlo
  · simpa [mainQuarterAlpha5, t, R] using hhi

/-- The first contact-angle value in the lower-edge sign check is bounded by
finite rational Taylor sums at the certified quarter-parameter endpoints. -/
theorem mainAlpha5_tlow_rmid_taylor_enclosure (n : ℕ) :
    4 * (arctanTaylorPartial mainAlpha5TlowRmidQLo n -
        arctanTaylorTerm mainAlpha5TlowRmidQLo n) ≤
      mainAlpha5 1.0037160860750841
        ((8.3034681221114890 + 8.3034681221114900) / 2) ∧
    mainAlpha5 1.0037160860750841
        ((8.3034681221114890 + 8.3034681221114900) / 2) ≤
      4 * (arctanTaylorPartial mainAlpha5TlowRmidQHi n +
        arctanTaylorTerm mainAlpha5TlowRmidQHi n) := by
  have hq := mainAlpha5_tlow_rmid_quarter_parameter_bounds
  have hangle := touchAngle_eq_four_arctan_quarterParameter hq.1.1 hq.1.2
  have hmonoLo := Real.arctan_mono hq.2.1
  have hmonoHi := Real.arctan_mono hq.2.2
  have hTaylorLo := arctanTaylor_error_bound
    (x := mainAlpha5TlowRmidQLo) (by norm_num [mainAlpha5TlowRmidQLo])
    (by norm_num [mainAlpha5TlowRmidQLo]) n
  have hTaylorHi := arctanTaylor_error_bound
    (x := mainAlpha5TlowRmidQHi) (by norm_num [mainAlpha5TlowRmidQHi])
    (by norm_num [mainAlpha5TlowRmidQHi]) n
  have hTaylorLo' :
      arctanTaylorPartial mainAlpha5TlowRmidQLo n -
        arctanTaylorTerm mainAlpha5TlowRmidQLo n ≤
          Real.arctan mainAlpha5TlowRmidQLo := by
    have h := (abs_le.mp hTaylorLo).1
    linarith
  have hTaylorHi' :
      Real.arctan mainAlpha5TlowRmidQHi ≤
        arctanTaylorPartial mainAlpha5TlowRmidQHi n +
          arctanTaylorTerm mainAlpha5TlowRmidQHi n := by
    have h := (abs_le.mp hTaylorHi).2
    linarith
  have hangle' : mainAlpha5 1.0037160860750841
      ((8.3034681221114890 + 8.3034681221114900) / 2) =
        4 * Real.arctan
          (arccosQuarterParameter (touchCosine 1.0037160860750841
            ((8.3034681221114890 + 8.3034681221114900) / 2 - Real.sqrt 5)
            (Real.sqrt 10 + Real.sqrt 5))) := by
    simpa [mainAlpha5] using hangle
  rw [hangle']
  constructor
  · calc
      4 * (arctanTaylorPartial mainAlpha5TlowRmidQLo n -
          arctanTaylorTerm mainAlpha5TlowRmidQLo n) ≤
          4 * Real.arctan mainAlpha5TlowRmidQLo :=
            mul_le_mul_of_nonneg_left hTaylorLo' (by norm_num)
      _ ≤ 4 * Real.arctan
          (arccosQuarterParameter (touchCosine 1.0037160860750841
            ((8.3034681221114890 + 8.3034681221114900) / 2 - Real.sqrt 5)
            (Real.sqrt 10 + Real.sqrt 5))) := by
            exact mul_le_mul_of_nonneg_left hmonoLo (by norm_num)
  · calc
      4 * Real.arctan
          (arccosQuarterParameter (touchCosine 1.0037160860750841
            ((8.3034681221114890 + 8.3034681221114900) / 2 - Real.sqrt 5)
            (Real.sqrt 10 + Real.sqrt 5))) ≤
          4 * Real.arctan mainAlpha5TlowRmidQHi :=
            mul_le_mul_of_nonneg_left hmonoHi (by norm_num)
      _ ≤ 4 * (arctanTaylorPartial mainAlpha5TlowRmidQHi n +
          arctanTaylorTerm mainAlpha5TlowRmidQHi n) :=
            mul_le_mul_of_nonneg_left hTaylorHi' (by norm_num)

/-- The first pilot angle is now enclosed by explicit rational endpoints.
The finite arithmetic is the only numerical step: Lean reduces both Taylor
sums and their first omitted terms exactly. -/
theorem mainAlpha5_tlow_rmid_rational_angle_bounds :
    (77768542231667638720 : ℝ) / 100000000000000000000 ≤
      mainAlpha5 1.0037160860750841
        ((8.3034681221114890 + 8.3034681221114900) / 2) ∧
    mainAlpha5 1.0037160860750841
        ((8.3034681221114890 + 8.3034681221114900) / 2) ≤
      (77768542231667638732 : ℝ) / 100000000000000000000 := by
  have hTaylor := mainAlpha5_tlow_rmid_taylor_enclosure 24
  have hnumLo :
      (77768542231667638720 : ℝ) / 100000000000000000000 ≤
        4 * (arctanTaylorPartial mainAlpha5TlowRmidQLo 24 -
          arctanTaylorTerm mainAlpha5TlowRmidQLo 24) := by
    norm_num [arctanTaylorPartial, arctanTaylorTerm,
      mainAlpha5TlowRmidQLo]
  have hnumHi :
      4 * (arctanTaylorPartial mainAlpha5TlowRmidQHi 24 +
          arctanTaylorTerm mainAlpha5TlowRmidQHi 24) ≤
        (77768542231667638732 : ℝ) / 100000000000000000000 := by
    norm_num [arctanTaylorPartial, arctanTaylorTerm,
      mainAlpha5TlowRmidQHi]
  exact ⟨le_trans hnumLo hTaylor.1, le_trans hTaylor.2 hnumHi⟩

def mainBeta57RmidQLo : ℝ :=
  2173786597031733212415 / 10000000000000000000000

def mainBeta57RmidQHi : ℝ :=
  2173786597031733212416 / 10000000000000000000000

/-- The contact angle between disks 5 and 7 at the radius-box midpoint has
an exact quarter-angle parameter in this rational interval. The half-angle
ratio simplifies to `sqrt 5 * sqrt 7 / (R * (R - sqrt 5 - sqrt 7))`. -/
theorem mainBeta57_rmid_quarter_parameter_bounds :
    touchCosine
        ((8.3034681221114890 + 8.3034681221114900) / 2 - Real.sqrt 5)
        ((8.3034681221114890 + 8.3034681221114900) / 2 - Real.sqrt 7)
        (Real.sqrt 5 + Real.sqrt 7) ∈ Set.Ioo (-1) 1 ∧
      mainBeta57RmidQLo ≤ mainQuarterBeta57
        ((8.3034681221114890 + 8.3034681221114900) / 2) ∧
      mainQuarterBeta57
        ((8.3034681221114890 + 8.3034681221114900) / 2) ≤
        mainBeta57RmidQHi := by
  let R : ℝ := (8.3034681221114890 + 8.3034681221114900) / 2
  let u : ℝ := Real.sqrt 5
  let v : ℝ := Real.sqrt 7
  let a : ℝ := R - u
  let b : ℝ := R - v
  let d : ℝ := u + v
  let den : ℝ := R * (R - u - v)
  let z : ℝ := u * v / den
  have huSq : u ^ 2 = 5 := by dsimp [u]; exact Real.sq_sqrt (by norm_num)
  have hvSq : v ^ 2 = 7 := by dsimp [v]; exact Real.sq_sqrt (by norm_num)
  have hu :
      2.236067977499789696409173 ≤ u ∧
        u ≤ 2.236067977499789696409174 := by
    constructor
    · apply (sq_le_sq₀ (by norm_num) (Real.sqrt_nonneg _)).mp
      nlinarith [huSq]
    · apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by norm_num)).mp
      nlinarith [huSq]
  have hv :
      2.645751311064590590501615 ≤ v ∧
        v ≤ 2.645751311064590590501616 := by
    constructor
    · apply (sq_le_sq₀ (by norm_num) (Real.sqrt_nonneg _)).mp
      nlinarith [hvSq]
    · apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by norm_num)).mp
      nlinarith [hvSq]
  have hRlo : (8.3034681221114895 : ℝ) ≤ R := by norm_num [R]
  have hRhi : R ≤ (8.3034681221114895 : ℝ) := by norm_num [R]
  have huPos : 0 < u := lt_of_lt_of_le (by norm_num) hu.1
  have hvPos : 0 < v := lt_of_lt_of_le (by norm_num) hv.1
  have haPos : 0 < a := by dsimp [a, R]; nlinarith [hu.2]
  have hbPos : 0 < b := by dsimp [b, R]; nlinarith [hv.2]
  have hdiff : |a - b| < d := by
    apply abs_lt.mpr
    constructor <;> dsimp [a, b, d] <;> nlinarith [hu.1, hu.2, hv.1, hv.2]
  have hsum : d < a + b := by
    dsimp [a, b, d, R]
    nlinarith [hu.2, hv.2]
  have hcos : touchCosine a b d ∈ Set.Ioo (-1) 1 :=
    touchCosine_mem_Ioo_of_triangle_bounds haPos hbPos hdiff hsum
  have hdenPos : 0 < den := by
    dsimp [den, R]
    nlinarith [hu.2, hv.2]
  have hpolyPos : 0 < (a + b) ^ 2 - d ^ 2 := by
    have hleft : 0 < a + b - d := by linarith [hsum]
    have hright : 0 < a + b + d := by positivity
    have hfactor : (a + b) ^ 2 - d ^ 2 =
        (a + b - d) * (a + b + d) := by ring
    rw [hfactor]
    exact mul_pos hleft hright
  have hratio :
      (1 - touchCosine a b d) / (1 + touchCosine a b d) = z := by
    have hside := touchCosine_halfAngleRatio
      (a := a) (b := b) (d := d) (ne_of_gt haPos) (ne_of_gt hbPos)
      (ne_of_gt hpolyPos)
    have hnum : d ^ 2 - (a - b) ^ 2 = 4 * u * v := by
      dsimp [a, b, d]
      ring_nf
    have hden : (a + b) ^ 2 - d ^ 2 = 4 * den := by
      dsimp [a, b, d, den]
      ring
    rw [hside, hnum, hden]
    dsimp [z]
    field_simp [ne_of_gt hdenPos]
  have huvLo :
      (2.236067977499789696409173 : ℝ) *
          2.645751311064590590501615 ≤ u * v :=
    mul_le_mul hu.1 hv.1 (by norm_num) (le_of_lt huPos)
  have huvHi : u * v ≤
      (2.236067977499789696409174 : ℝ) *
        2.645751311064590590501616 :=
    mul_le_mul hu.2 hv.2 (le_of_lt hvPos) (by norm_num)
  have hdenLo :
      (8.3034681221114895 : ℝ) *
          (8.3034681221114895 -
            2.236067977499789696409174 -
            2.645751311064590590501616) ≤ den := by
    dsimp [den, R]
    nlinarith [hu.1, hu.2, hv.1, hv.2]
  have hdenHi : den ≤
      (8.3034681221114895 : ℝ) *
        (8.3034681221114895 -
          2.236067977499789696409173 -
          2.645751311064590590501615) := by
    dsimp [den, R]
    nlinarith [hu.1, hu.2, hv.1, hv.2]
  have hqLo0 : 0 ≤ mainBeta57RmidQLo := by norm_num [mainBeta57RmidQLo]
  have hqLo1 : mainBeta57RmidQLo < 1 := by norm_num [mainBeta57RmidQLo]
  have hqHi0 : 0 ≤ mainBeta57RmidQHi := by norm_num [mainBeta57RmidQHi]
  have hqHi1 : mainBeta57RmidQHi < 1 := by norm_num [mainBeta57RmidQHi]
  have hthresholdLo :
      ((1 + mainBeta57RmidQLo ^ 2) /
        (1 - mainBeta57RmidQLo ^ 2)) ^ 2 ≤ 1 + z := by
    have hcleared :
        4 * mainBeta57RmidQLo ^ 2 * den ≤
          u * v * (1 - mainBeta57RmidQLo ^ 2) ^ 2 := by
      dsimp [mainBeta57RmidQLo]
      nlinarith [huvLo, huvHi, hdenLo, hdenHi]
    have hratio' : 4 * mainBeta57RmidQLo ^ 2 ≤
        z * (1 - mainBeta57RmidQLo ^ 2) ^ 2 := by
      calc
        4 * mainBeta57RmidQLo ^ 2 ≤
            u * v * (1 - mainBeta57RmidQLo ^ 2) ^ 2 / den :=
          (le_div_iff₀ hdenPos).2 hcleared
        _ = z * (1 - mainBeta57RmidQLo ^ 2) ^ 2 := by
          dsimp [z]
          ring
    have hform :
        ((1 + mainBeta57RmidQLo ^ 2) /
          (1 - mainBeta57RmidQLo ^ 2)) ^ 2 - 1 ≤ z := by
      have hqden : 0 < 1 - mainBeta57RmidQLo ^ 2 := by
        norm_num [mainBeta57RmidQLo]
      have hpos : 0 < (1 - mainBeta57RmidQLo ^ 2) ^ 2 := pow_pos hqden 2
      have hquot : 4 * mainBeta57RmidQLo ^ 2 /
          (1 - mainBeta57RmidQLo ^ 2) ^ 2 ≤ z :=
        (div_le_iff₀ hpos).2 hratio'
      have hiden :
          ((1 + mainBeta57RmidQLo ^ 2) /
            (1 - mainBeta57RmidQLo ^ 2)) ^ 2 - 1 =
            4 * mainBeta57RmidQLo ^ 2 /
              (1 - mainBeta57RmidQLo ^ 2) ^ 2 := by
        have hdenNe : 1 - mainBeta57RmidQLo ^ 2 ≠ 0 := by
          exact ne_of_gt hqden
        field_simp [hdenNe]
        ring
      rw [hiden]
      exact hquot
    linarith
  have hthresholdHi :
      1 + z ≤ ((1 + mainBeta57RmidQHi ^ 2) /
        (1 - mainBeta57RmidQHi ^ 2)) ^ 2 := by
    have hcleared :
        u * v * (1 - mainBeta57RmidQHi ^ 2) ^ 2 ≤
          4 * mainBeta57RmidQHi ^ 2 * den := by
      dsimp [mainBeta57RmidQHi]
      nlinarith [huvLo, huvHi, hdenLo, hdenHi]
    have hratio' : z * (1 - mainBeta57RmidQHi ^ 2) ^ 2 ≤
        4 * mainBeta57RmidQHi ^ 2 := by
      calc
        z * (1 - mainBeta57RmidQHi ^ 2) ^ 2 =
            u * v * (1 - mainBeta57RmidQHi ^ 2) ^ 2 / den := by
          dsimp [z]
          ring
        _ ≤ 4 * mainBeta57RmidQHi ^ 2 :=
          (div_le_iff₀ hdenPos).2 hcleared
    have hform : z ≤
        ((1 + mainBeta57RmidQHi ^ 2) /
          (1 - mainBeta57RmidQHi ^ 2)) ^ 2 - 1 := by
      have hqden : 0 < 1 - mainBeta57RmidQHi ^ 2 := by
        norm_num [mainBeta57RmidQHi]
      have hpos : 0 < (1 - mainBeta57RmidQHi ^ 2) ^ 2 := pow_pos hqden 2
      have hquot : z ≤ 4 * mainBeta57RmidQHi ^ 2 /
          (1 - mainBeta57RmidQHi ^ 2) ^ 2 := by
        apply (le_div_iff₀ hpos).2
        exact hratio'
      have hiden :
          ((1 + mainBeta57RmidQHi ^ 2) /
            (1 - mainBeta57RmidQHi ^ 2)) ^ 2 - 1 =
            4 * mainBeta57RmidQHi ^ 2 /
              (1 - mainBeta57RmidQHi ^ 2) ^ 2 := by
        have hdenNe : 1 - mainBeta57RmidQHi ^ 2 ≠ 0 := by
          exact ne_of_gt hqden
        field_simp [hdenNe]
        ring
      rw [hiden]
      exact hquot
    linarith
  have hlo := le_arccosQuarterParameter_of_ratio_bound
    hcos.1 hcos.2 hqLo0 hqLo1 (by rw [hratio]; exact hthresholdLo)
  have hhi := arccosQuarterParameter_le_of_ratio_bound
    hcos.1 hcos.2 hqHi0 hqHi1 (by rw [hratio]; exact hthresholdHi)
  refine ⟨?_, ?_, ?_⟩
  · simpa [a, b, d, R, u, v] using hcos
  · simpa [mainQuarterBeta57, R, u, v] using hlo
  · simpa [mainQuarterBeta57, R, u, v] using hhi

/-- Convert a rational interval for the quarter-angle parameter into a
rational Taylor enclosure for the corresponding contact angle. -/
theorem arccos_quarterTaylor_enclosure {c qLo qHi : ℝ}
    (hcLo : -1 < c) (hcHi : c < 1)
    (hqLo0 : 0 ≤ qLo) (hqHiHalf : qHi ≤ 1 / 2)
    (hqLo : qLo ≤ arccosQuarterParameter c)
    (hqHi : arccosQuarterParameter c ≤ qHi) (n : ℕ) :
    4 * (arctanTaylorPartial qLo n - arctanTaylorTerm qLo n) ≤
        Real.arccos c ∧
      Real.arccos c ≤
        4 * (arctanTaylorPartial qHi n + arctanTaylorTerm qHi n) := by
  have hangle := arccos_eq_four_arctan_quarterParameter hcLo hcHi
  have hmonoLo := Real.arctan_mono hqLo
  have hmonoHi := Real.arctan_mono hqHi
  have hTaylorLo := arctanTaylor_error_bound hqLo0 (by linarith) n
  have hTaylorHi := arctanTaylor_error_bound
    (le_trans hqLo0 (le_trans hqLo hqHi)) hqHiHalf n
  have hTaylorLo' :
      arctanTaylorPartial qLo n - arctanTaylorTerm qLo n ≤
        Real.arctan qLo := by
    have h := (abs_le.mp hTaylorLo).1
    linarith
  have hTaylorHi' :
      Real.arctan qHi ≤ arctanTaylorPartial qHi n +
        arctanTaylorTerm qHi n := by
    have h := (abs_le.mp hTaylorHi).2
    linarith
  rw [hangle]
  constructor
  · calc
      4 * (arctanTaylorPartial qLo n - arctanTaylorTerm qLo n) ≤
          4 * Real.arctan qLo :=
            mul_le_mul_of_nonneg_left hTaylorLo' (by norm_num)
      _ ≤ 4 * Real.arctan (arccosQuarterParameter c) :=
        mul_le_mul_of_nonneg_left hmonoLo (by norm_num)
  · calc
      4 * Real.arctan (arccosQuarterParameter c) ≤ 4 * Real.arctan qHi :=
        mul_le_mul_of_nonneg_left hmonoHi (by norm_num)
      _ ≤ 4 * (arctanTaylorPartial qHi n +
          arctanTaylorTerm qHi n) :=
        mul_le_mul_of_nonneg_left hTaylorHi' (by norm_num)

theorem mainBeta57_rmid_taylor_enclosure (n : ℕ) :
    4 * (arctanTaylorPartial mainBeta57RmidQLo n -
        arctanTaylorTerm mainBeta57RmidQLo n) ≤
      mainBeta57 ((8.3034681221114890 + 8.3034681221114900) / 2) ∧
    mainBeta57 ((8.3034681221114890 + 8.3034681221114900) / 2) ≤
      4 * (arctanTaylorPartial mainBeta57RmidQHi n +
        arctanTaylorTerm mainBeta57RmidQHi n) := by
  have hq := mainBeta57_rmid_quarter_parameter_bounds
  have hangle := arccos_quarterTaylor_enclosure
    hq.1.1 hq.1.2 (by norm_num [mainBeta57RmidQLo])
    (by norm_num [mainBeta57RmidQHi]) hq.2.1 hq.2.2 n
  simpa [mainBeta57, mainQuarterBeta57, touchAngle] using hangle

/-- Concrete rational endpoints for the disk-5/disk-7 contact angle at the
certified radius midpoint, obtained by exact finite Taylor-sum arithmetic. -/
theorem mainBeta57_rmid_rational_angle_bounds :
    (8561944379767423103489 : ℝ) / 10000000000000000000000 ≤
      mainBeta57 ((8.3034681221114890 + 8.3034681221114900) / 2) ∧
    mainBeta57 ((8.3034681221114890 + 8.3034681221114900) / 2) ≤
      (8561944379767423103494 : ℝ) / 10000000000000000000000 := by
  have hTaylor := mainBeta57_rmid_taylor_enclosure 24
  have hnumLo :
      (8561944379767423103489 : ℝ) / 10000000000000000000000 ≤
        4 * (arctanTaylorPartial mainBeta57RmidQLo 24 -
          arctanTaylorTerm mainBeta57RmidQLo 24) := by
    norm_num [arctanTaylorPartial, arctanTaylorTerm,
      mainBeta57RmidQLo]
  have hnumHi :
      4 * (arctanTaylorPartial mainBeta57RmidQHi 24 +
          arctanTaylorTerm mainBeta57RmidQHi 24) ≤
        (8561944379767423103494 : ℝ) / 10000000000000000000000 := by
    norm_num [arctanTaylorPartial, arctanTaylorTerm,
      mainBeta57RmidQHi]
  exact ⟨le_trans hnumLo hTaylor.1, le_trans hTaylor.2 hnumHi⟩

def mainAlpha7TlowRmidQLo : ℝ :=
  4328133469793697276198 / 10000000000000000000000

def mainAlpha7TlowRmidQHi : ℝ :=
  4328133469793697276199 / 10000000000000000000000

/-- The other contact angle in the lower-edge difference, evaluated at the
radius midpoint, has a certified quarter-angle parameter interval as well. -/
theorem mainAlpha7_tlow_rmid_quarter_parameter_bounds :
    touchCosine 1.0037160860750841
        ((8.3034681221114890 + 8.3034681221114900) / 2 - Real.sqrt 7)
        (Real.sqrt 10 + Real.sqrt 7) ∈ Set.Ioo (-1) 1 ∧
      mainAlpha7TlowRmidQLo ≤
        mainQuarterAlpha7 1.0037160860750841
          ((8.3034681221114890 + 8.3034681221114900) / 2) ∧
      mainQuarterAlpha7 1.0037160860750841
          ((8.3034681221114890 + 8.3034681221114900) / 2) ≤
        mainAlpha7TlowRmidQHi := by
  let t : ℝ := 1.0037160860750841
  let R : ℝ := (8.3034681221114890 + 8.3034681221114900) / 2
  let r7 : ℝ := Real.sqrt 7
  let r10 : ℝ := Real.sqrt 10
  let a : ℝ := R - r7
  let d : ℝ := r10 + r7
  let N : ℝ := d ^ 2 - (a - t) ^ 2
  let D : ℝ := (a + t) ^ 2 - d ^ 2
  let z : ℝ := N / D
  have hr7sq : r7 ^ 2 = 7 := by
    dsimp [r7]
    exact Real.sq_sqrt (by norm_num)
  have hr10sq : r10 ^ 2 = 10 := by
    dsimp [r10]
    exact Real.sq_sqrt (by norm_num)
  have hr7 :
      2.645751311064590590501615 ≤ r7 ∧
        r7 ≤ 2.645751311064590590501616 := by
    constructor
    · apply (sq_le_sq₀ (by norm_num) (Real.sqrt_nonneg _)).mp
      nlinarith [hr7sq]
    · apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by norm_num)).mp
      nlinarith [hr7sq]
  have hr10 :
      3.162277660168379331998893 ≤ r10 ∧
        r10 ≤ 3.162277660168379331998894 := by
    constructor
    · apply (sq_le_sq₀ (by norm_num) (Real.sqrt_nonneg _)).mp
      nlinarith [hr10sq]
    · apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by norm_num)).mp
      nlinarith [hr10sq]
  have htpos : 0 < t := by norm_num [t]
  have hapos : 0 < a := by
    dsimp [a, R, r7]
    nlinarith [hr7.2]
  have hdpos : 0 < d := by
    dsimp [d, r7, r10]
    positivity
  have hDpos : 0 < D := by
    dsimp [D, a, d, R, t]
    nlinarith [hr7.1, hr7.2, hr10.1, hr10.2]
  have hdiff : |t - a| < d := by
    apply abs_lt.mpr
    constructor <;> dsimp [a, d, R, t] <;>
      nlinarith [hr7.1, hr7.2, hr10.1, hr10.2]
  have hsum : d < t + a := by
    dsimp [a, d, R, t]
    nlinarith [hr7.1, hr7.2, hr10.1, hr10.2]
  have hcos : touchCosine t a d ∈ Set.Ioo (-1) 1 :=
    touchCosine_mem_Ioo_of_triangle_bounds htpos hapos hdiff hsum
  have hratio :
      (1 - touchCosine t a d) / (1 + touchCosine t a d) = z := by
    have hside := touchCosine_halfAngleRatio
      (a := t) (b := a) (d := d) (by linarith [htpos]) (by linarith [hapos])
      (by dsimp [a, d, R, t]; nlinarith [hr7.1, hr7.2, hr10.1, hr10.2])
    dsimp [z, N, D]
    convert hside using 1
    ring
  have hQL : 0 ≤ mainAlpha7TlowRmidQLo := by
    norm_num [mainAlpha7TlowRmidQLo]
  have hQLt1 : mainAlpha7TlowRmidQLo < 1 := by
    norm_num [mainAlpha7TlowRmidQLo]
  have hQU0 : 0 ≤ mainAlpha7TlowRmidQHi := by
    norm_num [mainAlpha7TlowRmidQHi]
  have hQU : mainAlpha7TlowRmidQHi < 1 := by
    norm_num [mainAlpha7TlowRmidQHi]
  have hthresholdLo :
      ((1 + mainAlpha7TlowRmidQLo ^ 2) /
        (1 - mainAlpha7TlowRmidQLo ^ 2)) ^ 2 ≤ 1 + z := by
    have hcleared :
        (((1 + mainAlpha7TlowRmidQLo ^ 2) /
          (1 - mainAlpha7TlowRmidQLo ^ 2)) ^ 2 - 1) * D ≤ N := by
      dsimp [D, N, a, d, R, t, r7, r10]
      norm_num [mainAlpha7TlowRmidQLo]
      nlinarith [hr7.1, hr7.2, hr10.1, hr10.2, hr7sq, hr10sq]
    have hform : (((1 + mainAlpha7TlowRmidQLo ^ 2) /
          (1 - mainAlpha7TlowRmidQLo ^ 2)) ^ 2 - 1) ≤ z := by
      dsimp [z]
      exact (le_div_iff₀ hDpos).2 hcleared
    linarith
  have hthresholdHi :
      1 + z ≤ ((1 + mainAlpha7TlowRmidQHi ^ 2) /
        (1 - mainAlpha7TlowRmidQHi ^ 2)) ^ 2 := by
    have hcleared :
        N ≤ (((1 + mainAlpha7TlowRmidQHi ^ 2) /
          (1 - mainAlpha7TlowRmidQHi ^ 2)) ^ 2 - 1) * D := by
      dsimp [D, N, a, d, R, t, r7, r10]
      norm_num [mainAlpha7TlowRmidQHi]
      nlinarith [hr7.1, hr7.2, hr10.1, hr10.2, hr7sq, hr10sq]
    have hform : z ≤ (((1 + mainAlpha7TlowRmidQHi ^ 2) /
          (1 - mainAlpha7TlowRmidQHi ^ 2)) ^ 2 - 1) := by
      dsimp [z]
      exact (div_le_iff₀ hDpos).2 hcleared
    linarith
  have hlo := le_arccosQuarterParameter_of_ratio_bound
    hcos.1 hcos.2 hQL hQLt1 (by rw [hratio]; exact hthresholdLo)
  have hhi := arccosQuarterParameter_le_of_ratio_bound
    hcos.1 hcos.2 hQU0 hQU (by rw [hratio]; exact hthresholdHi)
  refine ⟨?_, ?_, ?_⟩
  · simpa [t, R, a, d, r7, r10] using hcos
  · simpa [mainQuarterAlpha7, t, R] using hlo
  · simpa [mainQuarterAlpha7, t, R] using hhi

theorem mainAlpha7_tlow_rmid_taylor_enclosure (n : ℕ) :
    4 * (arctanTaylorPartial mainAlpha7TlowRmidQLo n -
        arctanTaylorTerm mainAlpha7TlowRmidQLo n) ≤
      mainAlpha7 1.0037160860750841
        ((8.3034681221114890 + 8.3034681221114900) / 2) ∧
    mainAlpha7 1.0037160860750841
        ((8.3034681221114890 + 8.3034681221114900) / 2) ≤
      4 * (arctanTaylorPartial mainAlpha7TlowRmidQHi n +
        arctanTaylorTerm mainAlpha7TlowRmidQHi n) := by
  have hq := mainAlpha7_tlow_rmid_quarter_parameter_bounds
  have h := arccos_quarterTaylor_enclosure hq.1.1 hq.1.2
    (by norm_num [mainAlpha7TlowRmidQLo])
    (by norm_num [mainAlpha7TlowRmidQHi]) hq.2.1 hq.2.2 n
  simpa [mainAlpha7, touchAngle] using h

theorem mainAlpha7_tlow_rmid_rational_angle_bounds :
    (16338798602934189657 : ℝ) / 10000000000000000000 ≤
      mainAlpha7 1.0037160860750841
        ((8.3034681221114890 + 8.3034681221114900) / 2) ∧
    mainAlpha7 1.0037160860750841
        ((8.3034681221114890 + 8.3034681221114900) / 2) ≤
      (16338798602934189662 : ℝ) / 10000000000000000000 := by
  have hTaylor := mainAlpha7_tlow_rmid_taylor_enclosure 24
  have hnumLo :
      (16338798602934189657 : ℝ) / 10000000000000000000 ≤
        4 * (arctanTaylorPartial mainAlpha7TlowRmidQLo 24 -
          arctanTaylorTerm mainAlpha7TlowRmidQLo 24) := by
    norm_num [arctanTaylorPartial, arctanTaylorTerm,
      mainAlpha7TlowRmidQLo]
  have hnumHi :
      4 * (arctanTaylorPartial mainAlpha7TlowRmidQHi 24 +
          arctanTaylorTerm mainAlpha7TlowRmidQHi 24) ≤
        (16338798602934189662 : ℝ) / 10000000000000000000 := by
    norm_num [arctanTaylorPartial, arctanTaylorTerm,
      mainAlpha7TlowRmidQHi]
  exact ⟨le_trans hnumLo hTaylor.1, le_trans hTaylor.2 hnumHi⟩

theorem mainBarrier_difference_eq_three_contacts (t R : ℝ) :
    mainBarrierA t R - mainBarrierB t R =
      mainAlpha5 t R + mainBeta57 R - mainAlpha7 t R := by
  unfold mainBarrierA mainBarrierB
  ring

/-- A first concrete replay of the lower-edge sign at the midpoint of the
certified radius box. This is a pointwise check, not yet the uniform edge
bound needed by the root-curve theorem. -/
theorem mainBarrier_difference_tlow_rmid_negative :
    mainBarrierA 1.0037160860750841
        ((8.3034681221114890 + 8.3034681221114900) / 2) -
      mainBarrierB 1.0037160860750841
        ((8.3034681221114890 + 8.3034681221114900) / 2) < 0 := by
  have h5 := mainAlpha5_tlow_rmid_rational_angle_bounds
  have h57 := mainBeta57_rmid_rational_angle_bounds
  have h7 := mainAlpha7_tlow_rmid_rational_angle_bounds
  have hsum :
      (77768542231667638732 : ℝ) / 100000000000000000000 +
        (8561944379767423103494 : ℝ) / 10000000000000000000000 <
          (16338798602934189657 : ℝ) / 10000000000000000000 := by
    norm_num
  rw [mainBarrier_difference_eq_three_contacts
    1.0037160860750841
      ((8.3034681221114890 + 8.3034681221114900) / 2)]
  linarith [h5.2, h57.2, h7.1]

end

end CirclePacking
