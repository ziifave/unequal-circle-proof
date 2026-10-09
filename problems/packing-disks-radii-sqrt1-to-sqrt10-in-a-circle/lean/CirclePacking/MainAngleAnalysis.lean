import CirclePacking.MainAngleNecessary
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv

/-!
# Monotonicity facts for the main angle barrier

The Python interval proof locates the critical pair in a small rational
rectangle and checks the signs of the angular derivatives. This file begins
the Lean replay with exact, derivative-free monotonicity lemmas for a single
contact angle. The contact angles to disks 5 and 6 increase with the radial
coordinate `t` on the certified rectangle; the angle to disk 7 decreases
there. This establishes the increasing-in-`t` half of the first barrier.
The later derivative lemmas prove the second barrier decreases in `t`.
-/

namespace CirclePacking

noncomputable section

def mainBarrierRadiusRange : Set ℝ := Set.Icc 8.303 8.304

def mainBarrierGlobalRadiusRange : Set ℝ := Set.Icc 7.9 8.304

def mainBarrierTRange : Set ℝ := Set.Icc 0.8588 1.1265

/-- Heron discriminant of the triangle with side lengths `t`, `a`, and `d`.
It is positive exactly in the strict triangle region used below. -/
def touchHeron (t a d : ℝ) : ℝ :=
  4 * a ^ 2 * t ^ 2 - (t ^ 2 + a ^ 2 - d ^ 2) ^ 2

private theorem touchHeron_eq_triangle_factor (t a d : ℝ) :
    touchHeron t a d = ((a + d) ^ 2 - t ^ 2) *
      (t ^ 2 - (a - d) ^ 2) := by
  unfold touchHeron
  ring

private theorem touchHeron_positive_of_triangle_bounds
    {t a d : ℝ} (ht : 0 < t) (hupper : t < a + d)
    (hdiff : |a - d| < t) : 0 < touchHeron t a d := by
  rw [touchHeron_eq_triangle_factor]
  have hleft₁ : 0 < a + d - t := sub_pos.mpr hupper
  have hleft₂ : 0 < a + d + t := by linarith
  have hleft := mul_pos hleft₁ hleft₂
  have habs := abs_lt.mp hdiff
  have hright₁ : 0 < t - (a - d) := by linarith
  have hright₂ : 0 < t + (a - d) := by linarith
  have hright := mul_pos hright₁ hright₂
  nlinarith

theorem touchCosine_sq_heron_identity {t a d : ℝ}
    (ha : 0 < a) (ht : 0 < t) :
    1 - touchCosine t a d ^ 2 =
      touchHeron t a d / (4 * a ^ 2 * t ^ 2) := by
  unfold touchCosine touchHeron
  field_simp [ne_of_gt ha, ne_of_gt ht]
  ; ring

theorem touchCosine_mem_Ioo_of_heron {t a d : ℝ}
    (ha : 0 < a) (ht : 0 < t) (hH : 0 < touchHeron t a d) :
    touchCosine t a d ∈ Set.Ioo (-1) 1 := by
  have hid := touchCosine_sq_heron_identity (t := t) (a := a) (d := d) ha ht
  have hden : 0 < 4 * a ^ 2 * t ^ 2 := by positivity
  have hpos : 0 < 1 - touchCosine t a d ^ 2 := by
    rw [hid]
    exact div_pos hH hden
  constructor <;> nlinarith

/-- Increasing the second side of a strict contact triangle decreases its
contact angle when the squared triangle margin stays positive. -/
theorem touchAngle_strictAnti_second_radius
    {t a₁ a₂ d : ℝ}
    (ht : 0 < t) (ha₁ : 0 < a₁) (ha₂ : 0 < a₂)
    (ha12 : a₁ < a₂)
    (hprod : t ^ 2 < a₁ * a₂ + d ^ 2)
    (hH₁ : 0 < touchHeron t a₁ d)
    (hH₂ : 0 < touchHeron t a₂ d) :
    touchAngle t a₂ d < touchAngle t a₁ d := by
  have hcrossIdentity :
      (t ^ 2 + a₂ ^ 2 - d ^ 2) * (2 * t * a₁) -
        (t ^ 2 + a₁ ^ 2 - d ^ 2) * (2 * t * a₂) =
          2 * t * (a₂ - a₁) * (a₁ * a₂ + d ^ 2 - t ^ 2) := by ring
  have hcrossPos : 0 <
      2 * t * (a₂ - a₁) * (a₁ * a₂ + d ^ 2 - t ^ 2) := by
    positivity
  have hcos : touchCosine t a₁ d < touchCosine t a₂ d := by
    apply (div_lt_div_iff₀ (by positivity : 0 < 2 * t * a₁)
      (by positivity : 0 < 2 * t * a₂)).2
    nlinarith [hcrossIdentity, hcrossPos]
  have hmem₁ : touchCosine t a₁ d ∈ Set.Icc (-1) 1 := by
    have h := touchCosine_mem_Ioo_of_heron ha₁ ht hH₁
    exact ⟨h.1.le, h.2.le⟩
  have hmem₂ : touchCosine t a₂ d ∈ Set.Icc (-1) 1 := by
    have h := touchCosine_mem_Ioo_of_heron ha₂ ht hH₂
    exact ⟨h.1.le, h.2.le⟩
  unfold touchAngle
  exact Real.strictAntiOn_arccos hmem₁ hmem₂ hcos

private theorem wallContactHeron_positive
    {R r s : ℝ} (hr : 0 < r) (hs : 0 < s)
    (hR : r + s < R) :
    0 < touchHeron (R - r) (R - s) (r + s) := by
  rw [touchHeron_eq_triangle_factor]
  have hleft : 0 < ((R - s) + (r + s)) ^ 2 - (R - r) ^ 2 := by
    have hid1 : ((R - s) + (r + s)) - (R - r) = 2 * r := by ring
    have hid2 : ((R - s) + (r + s)) + (R - r) = 2 * R := by ring
    have hfactor₁ : 0 < ((R - s) + (r + s)) - (R - r) := by
      rw [hid1]
      positivity
    have hfactor₂ : 0 < ((R - s) + (r + s)) + (R - r) := by
      rw [hid2]
      linarith [hR, hr, hs]
    have hfactor := mul_pos hfactor₁ hfactor₂
    nlinarith
  have hright : 0 < (R - r) ^ 2 - ((R - s) - (r + s)) ^ 2 := by
    have hid1 : (R - r) - ((R - s) - (r + s)) = 2 * s := by ring
    have hid2 : (R - r) + ((R - s) - (r + s)) = 2 * (R - r - s) := by ring
    have hfactor₁ : 0 < (R - r) - ((R - s) - (r + s)) := by
      rw [hid1]
      positivity
    have hfactor₂ : 0 < (R - r) + ((R - s) - (r + s)) := by
      rw [hid2]
      linarith
    have hfactor := mul_pos hfactor₁ hfactor₂
    nlinarith
  exact mul_pos hleft hright

theorem wallContactCosine_formula {R r s : ℝ}
    (hr : 0 < r) (hs : 0 < s) (hR : r + s < R) :
    touchCosine (R - r) (R - s) (r + s) =
      1 - (2 * r * s) / ((R - r) * (R - s)) := by
  have hRr : 0 < R - r := by linarith
  have hRs : 0 < R - s := by linarith
  unfold touchCosine
  field_simp [ne_of_gt hRr, ne_of_gt hRs]
  ; ring

/-- A wall-wall contact angle decreases strictly as the container radius
grows, provided the two disks fit strictly inside the container. -/
theorem wallContactAngle_strictAnti_radius
    {r s R₁ R₂ : ℝ} (hr : 0 < r) (hs : 0 < s)
    (hR₁ : r + s < R₁) (hR₁₂ : R₁ < R₂) :
    touchAngle (R₂ - r) (R₂ - s) (r + s) <
      touchAngle (R₁ - r) (R₁ - s) (r + s) := by
  have hR₂ : r + s < R₂ := lt_trans hR₁ hR₁₂
  have hab₁ : 0 < (R₁ - r) * (R₁ - s) :=
    mul_pos (by linarith) (by linarith)
  have hab₂ : 0 < (R₂ - r) * (R₂ - s) :=
    mul_pos (by linarith) (by linarith)
  have hab₁₂ : (R₁ - r) * (R₁ - s) < (R₂ - r) * (R₂ - s) := by
    have hfactor : 0 < (R₂ - R₁) * (R₁ + R₂ - r - s) := by
      apply mul_pos (sub_pos.mpr hR₁₂)
      linarith
    nlinarith [hfactor]
  have hfrac :
      (2 * r * s) / ((R₂ - r) * (R₂ - s)) <
        (2 * r * s) / ((R₁ - r) * (R₁ - s)) := by
    apply (div_lt_div_iff₀ hab₂ hab₁).2
    have hnum : 0 < 2 * r * s := by positivity
    nlinarith
  have hcos :
      touchCosine (R₁ - r) (R₁ - s) (r + s) <
        touchCosine (R₂ - r) (R₂ - s) (r + s) := by
    rw [wallContactCosine_formula hr hs hR₁,
      wallContactCosine_formula hr hs hR₂]
    linarith
  have hmem₁ :
      touchCosine (R₁ - r) (R₁ - s) (r + s) ∈ Set.Icc (-1) 1 := by
    have h := touchCosine_mem_Ioo_of_heron (by linarith) (by linarith)
      (wallContactHeron_positive hr hs hR₁)
    exact ⟨h.1.le, h.2.le⟩
  have hmem₂ :
      touchCosine (R₂ - r) (R₂ - s) (r + s) ∈ Set.Icc (-1) 1 := by
    have h := touchCosine_mem_Ioo_of_heron (by linarith) (by linarith)
      (wallContactHeron_positive hr hs hR₂)
    exact ⟨h.1.le, h.2.le⟩
  unfold touchAngle
  exact Real.strictAntiOn_arccos hmem₁ hmem₂ hcos

/-- Exact derivative of the contact angle with respect to its first radius.
The nonzero Heron discriminant keeps the cosine strictly inside `(-1,1)`,
so Mathlib's derivative theorem for `arccos` applies. -/
theorem hasDerivAt_touchAngle_first_radius
    {t a d : ℝ} (ha : 0 < a) (ht : 0 < t)
    (hH : 0 < touchHeron t a d) :
    HasDerivAt (fun x : ℝ => touchAngle x a d)
      ((a ^ 2 - d ^ 2 - t ^ 2) / (t * Real.sqrt (touchHeron t a d))) t := by
  have hdenSq : 4 * a ^ 2 * t ^ 2 = (2 * a * t) ^ 2 := by ring
  have hcosId :
      1 - touchCosine t a d ^ 2 =
        touchHeron t a d / (4 * a ^ 2 * t ^ 2) := by
    unfold touchCosine touchHeron
    field_simp [ne_of_gt ha, ne_of_gt ht]
    ; ring
  have hcosSq : touchCosine t a d ^ 2 < 1 := by
    have hden : 0 < 4 * a ^ 2 * t ^ 2 := by positivity
    have hpos : 0 < touchHeron t a d / (4 * a ^ 2 * t ^ 2) :=
      div_pos hH hden
    have hpos' : 0 < 1 - touchCosine t a d ^ 2 := by
      rw [hcosId]
      exact hpos
    linarith
  have hcosLo : -1 < touchCosine t a d := by nlinarith
  have hcosHi : touchCosine t a d < 1 := by nlinarith
  have hcosDeriv :
      HasDerivAt (fun x : ℝ => touchCosine x a d)
        ((2 * t * (2 * t * a) -
          (t ^ 2 + a ^ 2 - d ^ 2) * (2 * a)) / (2 * t * a) ^ 2) t := by
    have hnum : HasDerivAt (fun x : ℝ => x ^ 2 + a ^ 2 - d ^ 2)
        (2 * t) t := by
      convert ((hasDerivAt_id t).pow 2).add_const (a ^ 2 - d ^ 2) using 1
      · funext x
        simp
        ring
      · simp
    have hden : HasDerivAt (fun x : ℝ => 2 * x * a) (2 * a) t := by
      convert (hasDerivAt_id t).mul_const (2 * a) using 1
      · funext x
        change 2 * x * a = x * (2 * a)
        ring
      · simp
    convert hnum.div hden (by positivity) using 1
    · funext x
      simp [touchCosine]
  have hcosDerivSimplified :
      ((2 * t * (2 * t * a) -
          (t ^ 2 + a ^ 2 - d ^ 2) * (2 * a)) / (2 * t * a) ^ 2) =
        (t ^ 2 - (a ^ 2 - d ^ 2)) / (2 * a * t ^ 2) := by
    field_simp [ne_of_gt ha, ne_of_gt ht]
    ; ring
  have hangle : HasDerivAt (fun x : ℝ => touchAngle x a d)
      (-(1 / Real.sqrt (1 - touchCosine t a d ^ 2)) *
        ((2 * t * (2 * t * a) -
          (t ^ 2 + a ^ 2 - d ^ 2) * (2 * a)) / (2 * t * a) ^ 2)) t := by
    simpa [touchAngle, Function.comp_def] using (Real.hasDerivAt_arccos
      (by linarith : touchCosine t a d ≠ -1)
      (by linarith : touchCosine t a d ≠ 1)).comp t hcosDeriv
  have hroot :
      Real.sqrt (1 - touchCosine t a d ^ 2) =
        Real.sqrt (touchHeron t a d) / (2 * a * t) := by
    rw [hcosId, Real.sqrt_div hH.le, hdenSq, Real.sqrt_sq_eq_abs,
      abs_of_pos (by positivity : 0 < 2 * a * t)]
  rw [hcosDerivSimplified, hroot] at hangle
  convert hangle using 1
  field_simp [ne_of_gt ha, ne_of_gt ht,
    ne_of_gt (Real.sqrt_pos.2 hH)]
  ; ring

/-- The exact algebraic comparison used for the `B_t < 0` branch: if the
positive contribution from disk 6 is dominated after multiplying by its
opposite Heron scale, then the sum of the two angle derivatives is negative.
The key identity is the difference of squares displayed in the global proof. -/
theorem touchAngle_pair_derivative_sum_neg
    {t a6 d6 a7 d7 : ℝ}
    (ht : 0 < t)
    (hd6 : 0 < d6) (hd7 : 0 < d7)
    (hH6 : 0 < touchHeron t a6 d6)
    (hH7 : 0 < touchHeron t a7 d7)
    (hb6 : t ^ 2 < a6 ^ 2 - d6 ^ 2)
    (hb7 : a7 ^ 2 - d7 ^ 2 < t ^ 2)
    (hproduct : d6 * (t ^ 2 - (a7 ^ 2 - d7 ^ 2)) >
      d7 * ((a6 ^ 2 - d6 ^ 2) - t ^ 2)) :
    (a6 ^ 2 - d6 ^ 2 - t ^ 2) /
        (t * Real.sqrt (touchHeron t a6 d6)) +
      (a7 ^ 2 - d7 ^ 2 - t ^ 2) /
        (t * Real.sqrt (touchHeron t a7 d7)) < 0 := by
  let b6 : ℝ := a6 ^ 2 - d6 ^ 2
  let b7 : ℝ := a7 ^ 2 - d7 ^ 2
  let H6 : ℝ := touchHeron t a6 d6
  let H7 : ℝ := touchHeron t a7 d7
  have hb6' : t ^ 2 < b6 := by simpa [b6] using hb6
  have hb7' : b7 < t ^ 2 := by simpa [b7] using hb7
  have hprod : d7 * (b6 - t ^ 2) < d6 * (t ^ 2 - b7) := by
    simpa [b6, b7] using hproduct
  have hleftPos : 0 < d7 * (b6 - t ^ 2) :=
    mul_pos hd7 (sub_pos.mpr hb6')
  have hrightPos : 0 < d6 * (t ^ 2 - b7) :=
    mul_pos hd6 (sub_pos.mpr hb7')
  have hsq : (d7 * (b6 - t ^ 2)) ^ 2 <
      (d6 * (t ^ 2 - b7)) ^ 2 :=
    (sq_lt_sq₀ (le_of_lt hleftPos) (le_of_lt hrightPos)).2 hprod
  have hpoly :
      (t ^ 2 - b7) ^ 2 * H6 - (b6 - t ^ 2) ^ 2 * H7 =
        4 * t ^ 2 *
          (d6 ^ 2 * (t ^ 2 - b7) ^ 2 -
            d7 ^ 2 * (b6 - t ^ 2) ^ 2) := by
    dsimp [b6, b7, H6, H7, touchHeron]
    ring
  have hHeronDiff :
      (b6 - t ^ 2) ^ 2 * H7 < (t ^ 2 - b7) ^ 2 * H6 := by
    have hquad : 0 <
        d6 ^ 2 * (t ^ 2 - b7) ^ 2 - d7 ^ 2 * (b6 - t ^ 2) ^ 2 := by
      nlinarith [hsq]
    have hscale : 0 < 4 * t ^ 2 := by positivity
    have hdiff : 0 <
        (t ^ 2 - b7) ^ 2 * H6 - (b6 - t ^ 2) ^ 2 * H7 := by
      rw [hpoly]
      exact mul_pos hscale hquad
    linarith
  have hsqrt6 : Real.sqrt H6 ^ 2 = H6 := Real.sq_sqrt (le_of_lt hH6)
  have hsqrt7 : Real.sqrt H7 ^ 2 = H7 := Real.sq_sqrt (le_of_lt hH7)
  have hscaledSquares :
      ((b6 - t ^ 2) * Real.sqrt H7) ^ 2 <
        ((t ^ 2 - b7) * Real.sqrt H6) ^ 2 := by
    rw [mul_pow, hsqrt7, mul_pow, hsqrt6]
    exact hHeronDiff
  have hcrossLeft : 0 < (b6 - t ^ 2) * Real.sqrt H7 :=
    mul_pos (sub_pos.mpr hb6') (Real.sqrt_pos.2 hH7)
  have hcrossRight : 0 < (t ^ 2 - b7) * Real.sqrt H6 :=
    mul_pos (sub_pos.mpr hb7') (Real.sqrt_pos.2 hH6)
  have hcross :
      (b6 - t ^ 2) * Real.sqrt H7 <
        (t ^ 2 - b7) * Real.sqrt H6 :=
    (sq_lt_sq₀ (le_of_lt hcrossLeft) (le_of_lt hcrossRight)).1
      hscaledSquares
  have hratio :
      (b6 - t ^ 2) / Real.sqrt H6 <
        (t ^ 2 - b7) / Real.sqrt H7 := by
    rw [div_lt_div_iff₀ (Real.sqrt_pos.2 hH6) (Real.sqrt_pos.2 hH7)]
    exact hcross
  have hratioScaled :
      (b6 - t ^ 2) / (t * Real.sqrt H6) <
        (t ^ 2 - b7) / (t * Real.sqrt H7) := by
    rw [div_lt_div_iff₀ (mul_pos ht (Real.sqrt_pos.2 hH6))
      (mul_pos ht (Real.sqrt_pos.2 hH7))]
    have hmul := mul_lt_mul_of_pos_left hcross ht
    nlinarith
  have hderivSum :
      (b6 - t ^ 2) / (t * Real.sqrt H6) +
        (b7 - t ^ 2) / (t * Real.sqrt H7) < 0 := by
    have hneg : b7 - t ^ 2 = -(t ^ 2 - b7) := by ring
    rw [hneg, neg_div, ← sub_eq_add_neg]
    exact sub_neg.mpr hratioScaled
  simpa [b6, b7, H6, H7] using hderivSum

/-- If `t²` stays below `a²-d²`, increasing the first radius decreases the
law-of-cosines cosine and therefore increases its arccosine. -/
theorem touchAngle_mono_first_radius_of_sq_upper
    {t₁ t₂ a d : ℝ}
    (ha : 0 < a) (ht₁ : 0 < t₁) (ht₂ : 0 < t₂)
    (h12 : t₁ ≤ t₂)
    (hsq : t₂ ^ 2 ≤ a ^ 2 - d ^ 2) :
    touchAngle t₁ a d ≤ touchAngle t₂ a d := by
  have hprod : t₁ * t₂ ≤ a ^ 2 - d ^ 2 := by
    calc
      t₁ * t₂ ≤ t₂ * t₂ := mul_le_mul_of_nonneg_right h12 ht₂.le
      _ = t₂ ^ 2 := by ring
      _ ≤ a ^ 2 - d ^ 2 := hsq
  unfold touchAngle
  apply Real.antitone_arccos
  unfold touchCosine
  have hden₁ : 0 < 2 * t₁ * a := by positivity
  have hden₂ : 0 < 2 * t₂ * a := by positivity
  apply (div_le_div_iff₀ hden₂ hden₁).2
  have hcross :
      (t₁ ^ 2 + a ^ 2 - d ^ 2) * (2 * t₂ * a) -
        (t₂ ^ 2 + a ^ 2 - d ^ 2) * (2 * t₁ * a) =
        2 * a * (t₂ - t₁) * (a ^ 2 - d ^ 2 - t₁ * t₂) := by ring
  have hnonneg : 0 ≤ 2 * a * (t₂ - t₁) * (a ^ 2 - d ^ 2 - t₁ * t₂) :=
    mul_nonneg (mul_nonneg (by positivity) (sub_nonneg.mpr h12))
      (sub_nonneg.mpr hprod)
  nlinarith

/-- If `a²-d²` is already below `t₁²`, increasing the first radius decreases
the contact angle. -/
theorem touchAngle_antitone_first_radius_of_sq_lower
    {t₁ t₂ a d : ℝ}
    (ha : 0 < a) (ht₁ : 0 < t₁) (ht₂ : 0 < t₂)
    (h12 : t₁ ≤ t₂)
    (hsq : a ^ 2 - d ^ 2 ≤ t₁ ^ 2) :
    touchAngle t₂ a d ≤ touchAngle t₁ a d := by
  have hprod : a ^ 2 - d ^ 2 ≤ t₁ * t₂ := by
    calc
      a ^ 2 - d ^ 2 ≤ t₁ ^ 2 := hsq
      _ = t₁ * t₁ := by ring
      _ ≤ t₁ * t₂ := mul_le_mul_of_nonneg_left h12 ht₁.le
  unfold touchAngle
  apply Real.antitone_arccos
  unfold touchCosine
  have hden₁ : 0 < 2 * t₁ * a := by positivity
  have hden₂ : 0 < 2 * t₂ * a := by positivity
  apply (div_le_div_iff₀ hden₁ hden₂).2
  have hcross :
      (t₂ ^ 2 + a ^ 2 - d ^ 2) * (2 * t₁ * a) -
        (t₁ ^ 2 + a ^ 2 - d ^ 2) * (2 * t₂ * a) =
        2 * a * (t₂ - t₁) * (t₁ * t₂ - (a ^ 2 - d ^ 2)) := by ring
  have hnonneg : 0 ≤ 2 * a * (t₂ - t₁) * (t₁ * t₂ - (a ^ 2 - d ^ 2)) :=
    mul_nonneg (mul_nonneg (by positivity) (sub_nonneg.mpr h12))
      (sub_nonneg.mpr hprod)
  nlinarith

private theorem sqrt5_coarse_bounds :
    2.236 ≤ Real.sqrt 5 ∧ Real.sqrt 5 ≤ 2.237 := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num
  · rw [Real.sqrt_le_iff]
    norm_num

private theorem sqrt6_coarse_bounds :
    2.449 ≤ Real.sqrt 6 ∧ Real.sqrt 6 ≤ 2.450 := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num
  · rw [Real.sqrt_le_iff]
    norm_num

private theorem sqrt7_coarse_bounds :
    2.645 ≤ Real.sqrt 7 ∧ Real.sqrt 7 ≤ 2.646 := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num
  · rw [Real.sqrt_le_iff]
    norm_num

private theorem sqrt10_coarse_bounds :
    3.162 ≤ Real.sqrt 10 ∧ Real.sqrt 10 ≤ 3.163 := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num
  · rw [Real.sqrt_le_iff]
    norm_num

private theorem sqrt_two_lt_three : Real.sqrt 2 < 3 := by
  rw [Real.sqrt_lt (by norm_num) (by norm_num)]
  norm_num

private theorem sqrt_eight_lt_three : Real.sqrt 8 < 3 := by
  rw [Real.sqrt_lt (by norm_num) (by norm_num)]
  norm_num

private theorem sqrt_nine_eq_three : Real.sqrt 9 = 3 := by
  rw [Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)]
  norm_num

private theorem mainAlpha_heron_positive
    {t R r : ℝ} (hR : R ∈ mainBarrierGlobalRadiusRange)
    (ht : t ∈ mainBarrierTRange)
    (hdiff : |(R - Real.sqrt 10) - 2 * r| < t) :
    0 < touchHeron t (R - r) (Real.sqrt 10 + r) := by
  rcases hR with ⟨hRlo, hRhi⟩
  rcases ht with ⟨htlo, hthi⟩
  have hs10 := sqrt10_coarse_bounds.1
  have hsum : t < (R - r) + (Real.sqrt 10 + r) := by linarith
  have hdiff' : |(R - r) - (Real.sqrt 10 + r)| < t := by
    have hid : (R - r) - (Real.sqrt 10 + r) =
        (R - Real.sqrt 10) - 2 * r := by ring
    rw [hid]
    exact hdiff
  exact touchHeron_positive_of_triangle_bounds (by linarith) hsum hdiff'

private theorem mainAlpha5_heron_positive
    {t R : ℝ} (hR : R ∈ mainBarrierGlobalRadiusRange)
    (ht : t ∈ mainBarrierTRange) :
    0 < touchHeron t (R - Real.sqrt 5) (Real.sqrt 10 + Real.sqrt 5) := by
  rcases hR with ⟨hRlo, hRhi⟩
  rcases ht with ⟨htlo, hthi⟩
  have hs10lo := sqrt10_coarse_bounds.1
  have hs10hi := sqrt10_coarse_bounds.2
  have hs5lo := sqrt5_coarse_bounds.1
  have hs5hi := sqrt5_coarse_bounds.2
  have hdiffLo : -(0.8 : ℝ) < (R - Real.sqrt 10) - 2 * Real.sqrt 5 := by linarith
  have hdiffHi : (R - Real.sqrt 10) - 2 * Real.sqrt 5 < 0.8 := by linarith
  have hdiff : |(R - Real.sqrt 10) - 2 * Real.sqrt 5| < t := by
    have hbound : |(R - Real.sqrt 10) - 2 * Real.sqrt 5| < 0.8 :=
      abs_lt.mpr ⟨hdiffLo, hdiffHi⟩
    have hsmall : (0.8 : ℝ) < t := by linarith
    exact hbound.trans hsmall
  exact mainAlpha_heron_positive ⟨hRlo, hRhi⟩ ⟨htlo, hthi⟩ hdiff

private theorem mainAlpha6_heron_positive_global
    {t R : ℝ} (hR : R ∈ mainBarrierGlobalRadiusRange)
    (ht : t ∈ mainBarrierTRange) :
    0 < touchHeron t (R - Real.sqrt 6) (Real.sqrt 10 + Real.sqrt 6) := by
  have hRmem := hR
  have htmem := ht
  rcases hR with ⟨hRlo, hRhi⟩
  rcases ht with ⟨htlo, hthi⟩
  have hs10lo := sqrt10_coarse_bounds.1
  have hs10hi := sqrt10_coarse_bounds.2
  have hs6lo := sqrt6_coarse_bounds.1
  have hs6hi := sqrt6_coarse_bounds.2
  have hdiffLo : -(0.3 : ℝ) < (R - Real.sqrt 10) - 2 * Real.sqrt 6 := by linarith
  have hdiffHi : (R - Real.sqrt 10) - 2 * Real.sqrt 6 < 0.3 := by linarith
  have hdiff : |(R - Real.sqrt 10) - 2 * Real.sqrt 6| < t := by
    have hbound : |(R - Real.sqrt 10) - 2 * Real.sqrt 6| < 0.3 :=
      abs_lt.mpr ⟨hdiffLo, hdiffHi⟩
    have hsmall : (0.3 : ℝ) < t := by linarith
    exact hbound.trans hsmall
  exact mainAlpha_heron_positive hRmem htmem hdiff

private theorem mainAlpha7_heron_positive_global
    {t R : ℝ} (hR : R ∈ mainBarrierGlobalRadiusRange)
    (ht : t ∈ mainBarrierTRange) :
    0 < touchHeron t (R - Real.sqrt 7) (Real.sqrt 10 + Real.sqrt 7) := by
  have hRmem := hR
  have htmem := ht
  rcases hR with ⟨hRlo, hRhi⟩
  rcases ht with ⟨htlo, hthi⟩
  have hs10lo := sqrt10_coarse_bounds.1
  have hs10hi := sqrt10_coarse_bounds.2
  have hs7lo := sqrt7_coarse_bounds.1
  have hs7hi := sqrt7_coarse_bounds.2
  have hdiffLo : -(0.6 : ℝ) < (R - Real.sqrt 10) - 2 * Real.sqrt 7 := by linarith
  have hdiffHi : (R - Real.sqrt 10) - 2 * Real.sqrt 7 < 0.6 := by linarith
  have hdiff : |(R - Real.sqrt 10) - 2 * Real.sqrt 7| < t := by
    have hbound : |(R - Real.sqrt 10) - 2 * Real.sqrt 7| < 0.6 :=
      abs_lt.mpr ⟨hdiffLo, hdiffHi⟩
    have hsmall : (0.6 : ℝ) < t := by linarith
    exact hbound.trans hsmall
  exact mainAlpha_heron_positive hRmem htmem hdiff

private theorem mainAlpha_strictAnti_radius
    {t R₁ R₂ r : ℝ} (ht : t ∈ mainBarrierTRange)
    (hR₁ : R₁ ∈ mainBarrierGlobalRadiusRange)
    (hR₂ : R₂ ∈ mainBarrierGlobalRadiusRange)
    (hR₁₂ : R₁ < R₂) (hr : 0 < r) (hr3 : r < 3)
    (hH₁ : 0 < touchHeron t (R₁ - r) (Real.sqrt 10 + r))
    (hH₂ : 0 < touchHeron t (R₂ - r) (Real.sqrt 10 + r)) :
    touchAngle t (R₂ - r) (Real.sqrt 10 + r) <
      touchAngle t (R₁ - r) (Real.sqrt 10 + r) := by
  rcases ht with ⟨htlo, hthi⟩
  rcases hR₁ with ⟨hR₁lo, hR₁hi⟩
  rcases hR₂ with ⟨hR₂lo, hR₂hi⟩
  have ha₁ : 1 < R₁ - r := by linarith
  have ha₂ : 1 < R₂ - r := by linarith
  have ha₁pos : 0 < R₁ - r := by linarith
  have ha₂pos : 0 < R₂ - r := by linarith
  have ha₁₂ : R₁ - r < R₂ - r := by linarith
  have hd : 1 < Real.sqrt 10 + r := by
    have hs := sqrt10_coarse_bounds.1
    linarith
  have htSqHi : t ^ 2 ≤ (1.1265 : ℝ) ^ 2 :=
    (sq_le_sq₀ (by linarith [htlo]) (by norm_num)).2 hthi
  have htSqSmall : t ^ 2 < 1.27 := by norm_num at htSqHi ⊢; linarith
  have hmul := mul_pos (sub_pos.mpr ha₁) (sub_pos.mpr ha₂)
  have hprodRadii : 1 < (R₁ - r) * (R₂ - r) := by nlinarith [hmul]
  have hdSq : 1 < (Real.sqrt 10 + r) ^ 2 := by nlinarith
  have hprod : t ^ 2 < (R₁ - r) * (R₂ - r) +
      (Real.sqrt 10 + r) ^ 2 := by nlinarith
  exact touchAngle_strictAnti_second_radius (by linarith [htlo])
    ha₁pos ha₂pos ha₁₂ hprod hH₁ hH₂

private theorem mainAlpha5_sq_condition
    {t R : ℝ} (hR : R ∈ mainBarrierRadiusRange)
    (ht : t ∈ mainBarrierTRange) :
    t ^ 2 ≤ (R - Real.sqrt 5) ^ 2 - (Real.sqrt 10 + Real.sqrt 5) ^ 2 := by
  rcases hR with ⟨hRlo, hRhi⟩
  rcases ht with ⟨htlo, hthi⟩
  have ha : 6.066 ≤ R - Real.sqrt 5 := by
    have hs := sqrt5_coarse_bounds.2
    linarith
  have hd : Real.sqrt 10 + Real.sqrt 5 ≤ 5.400 := by
    have h10 := sqrt10_coarse_bounds.2
    have h5 := sqrt5_coarse_bounds.2
    linarith
  have haSq : (6.066 : ℝ) ^ 2 ≤ (R - Real.sqrt 5) ^ 2 :=
    (sq_le_sq₀ (by norm_num) (by linarith [ha])).2 ha
  have hdSq : (Real.sqrt 10 + Real.sqrt 5) ^ 2 ≤ (5.400 : ℝ) ^ 2 :=
    (sq_le_sq₀ (by positivity) (by norm_num)).2 hd
  have htSq : t ^ 2 ≤ (1.1265 : ℝ) ^ 2 :=
    (sq_le_sq₀ (by linarith [htlo]) (by norm_num)).2 hthi
  have hmargin : (1.1265 : ℝ) ^ 2 ≤ (6.066 : ℝ) ^ 2 - (5.400 : ℝ) ^ 2 := by
    norm_num
  nlinarith

private theorem mainAlpha6_sq_condition
    {t R : ℝ} (hR : R ∈ mainBarrierRadiusRange)
    (ht : t ∈ mainBarrierTRange) :
    t ^ 2 ≤ (R - Real.sqrt 6) ^ 2 - (Real.sqrt 10 + Real.sqrt 6) ^ 2 := by
  rcases hR with ⟨hRlo, hRhi⟩
  rcases ht with ⟨htlo, hthi⟩
  have ha : 5.853 ≤ R - Real.sqrt 6 := by
    have hs := sqrt6_coarse_bounds.2
    linarith
  have hd : Real.sqrt 10 + Real.sqrt 6 ≤ 5.613 := by
    have h10 := sqrt10_coarse_bounds.2
    have h6 := sqrt6_coarse_bounds.2
    linarith
  have haSq : (5.853 : ℝ) ^ 2 ≤ (R - Real.sqrt 6) ^ 2 :=
    (sq_le_sq₀ (by norm_num) (by linarith [ha])).2 ha
  have hdSq : (Real.sqrt 10 + Real.sqrt 6) ^ 2 ≤ (5.613 : ℝ) ^ 2 :=
    (sq_le_sq₀ (by positivity) (by norm_num)).2 hd
  have htSq : t ^ 2 ≤ (1.1265 : ℝ) ^ 2 :=
    (sq_le_sq₀ (by linarith [htlo]) (by norm_num)).2 hthi
  have hmargin : (1.1265 : ℝ) ^ 2 ≤ (5.853 : ℝ) ^ 2 - (5.613 : ℝ) ^ 2 := by
    norm_num
  nlinarith

private theorem mainAlpha7_sq_condition
    {t R : ℝ} (hR : R ∈ mainBarrierRadiusRange)
    (ht : t ∈ mainBarrierTRange) :
    (R - Real.sqrt 7) ^ 2 - (Real.sqrt 10 + Real.sqrt 7) ^ 2 ≤ t ^ 2 := by
  rcases hR with ⟨hRlo, hRhi⟩
  rcases ht with ⟨htlo, _⟩
  have ha : R - Real.sqrt 7 ≤ 5.659 := by
    have hs := sqrt7_coarse_bounds.1
    linarith
  have hd : 5.807 ≤ Real.sqrt 10 + Real.sqrt 7 := by
    have h10 := sqrt10_coarse_bounds.1
    have h7 := sqrt7_coarse_bounds.1
    linarith
  have haSq : (R - Real.sqrt 7) ^ 2 ≤ (5.659 : ℝ) ^ 2 :=
    (sq_le_sq₀ (by linarith [hRlo, sqrt7_coarse_bounds.2]) (by norm_num)).2 ha
  have hdSq : (5.807 : ℝ) ^ 2 ≤ (Real.sqrt 10 + Real.sqrt 7) ^ 2 :=
    (sq_le_sq₀ (by norm_num) (by positivity)).2 hd
  have htSq : 0 ≤ t ^ 2 := sq_nonneg t
  have hnegative : (5.659 : ℝ) ^ 2 - (5.807 : ℝ) ^ 2 ≤ 0 := by norm_num
  nlinarith

def mainBarrierD6 : ℝ := Real.sqrt 10 + Real.sqrt 6

def mainBarrierD7 : ℝ := Real.sqrt 10 + Real.sqrt 7

def mainBarrierB6Offset (R : ℝ) : ℝ :=
  (R - Real.sqrt 6) ^ 2 - mainBarrierD6 ^ 2

def mainBarrierB7Offset (R : ℝ) : ℝ :=
  (R - Real.sqrt 7) ^ 2 - mainBarrierD7 ^ 2

private theorem mainBarrierB6Offset_bounds
    {R : ℝ} (hR : R ∈ mainBarrierRadiusRange) :
    2.75 < mainBarrierB6Offset R ∧ mainBarrierB6Offset R < 2.8 := by
  rcases hR with ⟨hRlo, hRhi⟩
  have haLo : 5.853 ≤ R - Real.sqrt 6 := by
    have h6 := sqrt6_coarse_bounds.2
    linarith
  have haHi : R - Real.sqrt 6 ≤ 5.855 := by
    have h6 := sqrt6_coarse_bounds.1
    linarith
  have hdLo : 5.611 ≤ mainBarrierD6 := by
    have h10 := sqrt10_coarse_bounds.1
    have h6 := sqrt6_coarse_bounds.1
    dsimp [mainBarrierD6]
    linarith
  have hdHi : mainBarrierD6 ≤ 5.613 := by
    have h10 := sqrt10_coarse_bounds.2
    have h6 := sqrt6_coarse_bounds.2
    dsimp [mainBarrierD6]
    linarith
  have haPos : 0 < R - Real.sqrt 6 := by linarith [haLo]
  have haSqLo : (5.853 : ℝ) ^ 2 ≤ (R - Real.sqrt 6) ^ 2 :=
    (sq_le_sq₀ (by norm_num) (le_of_lt haPos)).2 haLo
  have haSqHi : (R - Real.sqrt 6) ^ 2 ≤ (5.855 : ℝ) ^ 2 :=
    (sq_le_sq₀ (le_of_lt haPos) (by norm_num)).2 haHi
  have hdPos : 0 < mainBarrierD6 := by linarith [hdLo]
  have hdSqLo : (5.611 : ℝ) ^ 2 ≤ mainBarrierD6 ^ 2 :=
    (sq_le_sq₀ (by norm_num) (le_of_lt hdPos)).2 hdLo
  have hdSqHi : mainBarrierD6 ^ 2 ≤ (5.613 : ℝ) ^ 2 :=
    (sq_le_sq₀ (le_of_lt hdPos) (by norm_num)).2 hdHi
  constructor <;> dsimp [mainBarrierB6Offset] <;> nlinarith

private theorem mainBarrierB7Offset_upper
    {R : ℝ} (hR : R ∈ mainBarrierRadiusRange) :
    mainBarrierB7Offset R < -1.6 := by
  rcases hR with ⟨hRlo, hRhi⟩
  have haLo : 0 < R - Real.sqrt 7 := by
    have h7 := sqrt7_coarse_bounds.2
    linarith
  have haHi : R - Real.sqrt 7 ≤ 5.659 := by
    have h7 := sqrt7_coarse_bounds.1
    linarith
  have hdLo : 5.807 ≤ mainBarrierD7 := by
    have h10 := sqrt10_coarse_bounds.1
    have h7 := sqrt7_coarse_bounds.1
    dsimp [mainBarrierD7]
    linarith
  have haSqHi : (R - Real.sqrt 7) ^ 2 ≤ (5.659 : ℝ) ^ 2 :=
    (sq_le_sq₀ (le_of_lt haLo) (by norm_num)).2 haHi
  have hdPos : 0 < mainBarrierD7 := by linarith [hdLo]
  have hdSqLo : (5.807 : ℝ) ^ 2 ≤ mainBarrierD7 ^ 2 :=
    (sq_le_sq₀ (by norm_num) (le_of_lt hdPos)).2 hdLo
  dsimp [mainBarrierB7Offset]
  nlinarith

/-- The rational product comparison used to prove that the negative motion
of the angle to disk 7 dominates the positive motion of the angle to disk 6.
This is the exact `X>Y` interval argument in the root certificate. -/
theorem mainBarrier_derivative_comparison_polynomial
    {t R : ℝ} (hR : R ∈ mainBarrierRadiusRange)
    (ht : t ∈ mainBarrierTRange) :
    mainBarrierD6 * (t ^ 2 - mainBarrierB7Offset R) >
      mainBarrierD7 * (mainBarrierB6Offset R - t ^ 2) := by
  rcases ht with ⟨htLo, htHi⟩
  have hb6 := mainBarrierB6Offset_bounds hR
  have hb7 := mainBarrierB7Offset_upper hR
  have hd6 : 5.6 < mainBarrierD6 := by
    have h10 := sqrt10_coarse_bounds.1
    have h6 := sqrt6_coarse_bounds.1
    dsimp [mainBarrierD6]
    linarith
  have hd7 : mainBarrierD7 < 5.9 := by
    have h10 := sqrt10_coarse_bounds.2
    have h7 := sqrt7_coarse_bounds.2
    dsimp [mainBarrierD7]
    linarith
  have htSqLo : (0.8588 : ℝ) ^ 2 ≤ t ^ 2 :=
    (sq_le_sq₀ (by norm_num) (by linarith [htLo])).2 htLo
  have htSqHi : t ^ 2 ≤ (1.1265 : ℝ) ^ 2 :=
    (sq_le_sq₀ (by linarith [htLo]) (by norm_num)).2 htHi
  have hzLo : 0.73 < t ^ 2 := by norm_num at htSqLo ⊢; linarith
  have hzHi : t ^ 2 < 1.27 := by norm_num at htSqHi ⊢; linarith
  have hqLo : 2.33 < t ^ 2 - mainBarrierB7Offset R := by linarith
  have hqHi : mainBarrierB6Offset R - t ^ 2 < 2.07 := by linarith
  have hqPos : 0 < mainBarrierB6Offset R - t ^ 2 := by linarith
  have hX : (13.048 : ℝ) <
      mainBarrierD6 * (t ^ 2 - mainBarrierB7Offset R) := by
    have h1 : 0 < (mainBarrierD6 - 5.6) *
        (t ^ 2 - mainBarrierB7Offset R) :=
      mul_pos (by linarith) (by linarith [hqLo])
    have h2 : 0 < 5.6 * (t ^ 2 - mainBarrierB7Offset R - 2.33) :=
      mul_pos (by norm_num) (by linarith [hqLo])
    nlinarith
  have hY : mainBarrierD7 * (mainBarrierB6Offset R - t ^ 2) < 12.213 := by
    calc
      mainBarrierD7 * (mainBarrierB6Offset R - t ^ 2) <
          5.9 * (mainBarrierB6Offset R - t ^ 2) :=
        mul_lt_mul_of_pos_right hd7 hqPos
      _ < 5.9 * 2.07 := mul_lt_mul_of_pos_left hqHi (by norm_num)
      _ = 12.213 := by norm_num
  norm_num at hX hY ⊢
  linarith

private theorem mainBarrier_heron6_positive
    {t R : ℝ} (hR : R ∈ mainBarrierRadiusRange)
    (ht : t ∈ mainBarrierTRange) :
    0 < touchHeron t (R - Real.sqrt 6)
      (Real.sqrt 10 + Real.sqrt 6) := by
  rcases hR with ⟨hRlo, hRhi⟩
  rcases ht with ⟨htlo, hthi⟩
  have h10lo := sqrt10_coarse_bounds.1
  have h10hi := sqrt10_coarse_bounds.2
  have h6lo := sqrt6_coarse_bounds.1
  have h6hi := sqrt6_coarse_bounds.2
  have hdiffLo : -(0.3 : ℝ) <
      (R - Real.sqrt 6) - (Real.sqrt 10 + Real.sqrt 6) := by
    linarith
  have hdiffHi :
      (R - Real.sqrt 6) - (Real.sqrt 10 + Real.sqrt 6) < 0.3 := by
    linarith
  have hdiffAbs :
      |(R - Real.sqrt 6) - (Real.sqrt 10 + Real.sqrt 6)| < 0.3 :=
    abs_lt.mpr ⟨hdiffLo, hdiffHi⟩
  have htpos : 0 < t := by linarith
  have hsum : t <
      (R - Real.sqrt 6) + (Real.sqrt 10 + Real.sqrt 6) := by
    linarith
  have hfactor1 : 0 <
      ((R - Real.sqrt 6) + (Real.sqrt 10 + Real.sqrt 6)) ^ 2 - t ^ 2 := by
    have hprod := mul_pos (sub_pos.mpr hsum)
      (add_pos htpos (by linarith : 0 <
        (R - Real.sqrt 6) + (Real.sqrt 10 + Real.sqrt 6)))
    nlinarith
  have hfactor2 : 0 <
      t ^ 2 - ((R - Real.sqrt 6) - (Real.sqrt 10 + Real.sqrt 6)) ^ 2 := by
    have hleft : 0 < t -
        ((R - Real.sqrt 6) - (Real.sqrt 10 + Real.sqrt 6)) := by
      have habs := abs_lt.mp hdiffAbs
      linarith
    have hright : 0 < t +
        ((R - Real.sqrt 6) - (Real.sqrt 10 + Real.sqrt 6)) := by
      have habs := abs_lt.mp hdiffAbs
      linarith
    have hprod := mul_pos hleft hright
    nlinarith
  rw [touchHeron_eq_triangle_factor]
  exact mul_pos hfactor1 hfactor2

private theorem mainBarrier_heron7_positive
    {t R : ℝ} (hR : R ∈ mainBarrierRadiusRange)
    (ht : t ∈ mainBarrierTRange) :
    0 < touchHeron t (R - Real.sqrt 7)
      (Real.sqrt 10 + Real.sqrt 7) := by
  rcases hR with ⟨hRlo, hRhi⟩
  rcases ht with ⟨htlo, hthi⟩
  have h10lo := sqrt10_coarse_bounds.1
  have h10hi := sqrt10_coarse_bounds.2
  have h7lo := sqrt7_coarse_bounds.1
  have h7hi := sqrt7_coarse_bounds.2
  have hdiffLo : -(0.3 : ℝ) <
      (R - Real.sqrt 7) - (Real.sqrt 10 + Real.sqrt 7) := by
    linarith
  have hdiffHi :
      (R - Real.sqrt 7) - (Real.sqrt 10 + Real.sqrt 7) < 0.3 := by
    linarith
  have hdiffAbs :
      |(R - Real.sqrt 7) - (Real.sqrt 10 + Real.sqrt 7)| < 0.3 :=
    abs_lt.mpr ⟨hdiffLo, hdiffHi⟩
  have htpos : 0 < t := by linarith
  have hsum : t <
      (R - Real.sqrt 7) + (Real.sqrt 10 + Real.sqrt 7) := by
    linarith
  have hfactor1 : 0 <
      ((R - Real.sqrt 7) + (Real.sqrt 10 + Real.sqrt 7)) ^ 2 - t ^ 2 := by
    have hprod := mul_pos (sub_pos.mpr hsum)
      (add_pos htpos (by linarith : 0 <
        (R - Real.sqrt 7) + (Real.sqrt 10 + Real.sqrt 7)))
    nlinarith
  have hfactor2 : 0 <
      t ^ 2 - ((R - Real.sqrt 7) - (Real.sqrt 10 + Real.sqrt 7)) ^ 2 := by
    have hleft : 0 < t -
        ((R - Real.sqrt 7) - (Real.sqrt 10 + Real.sqrt 7)) := by
      have habs := abs_lt.mp hdiffAbs
      linarith
    have hright : 0 < t +
        ((R - Real.sqrt 7) - (Real.sqrt 10 + Real.sqrt 7)) := by
      have habs := abs_lt.mp hdiffAbs
      linarith
    have hprod := mul_pos hleft hright
    nlinarith
  rw [touchHeron_eq_triangle_factor]
  exact mul_pos hfactor1 hfactor2

theorem mainBarrierB_deriv_neg_on_ranges
    {t R : ℝ} (hR : R ∈ mainBarrierRadiusRange)
    (ht : t ∈ mainBarrierTRange) :
    deriv (fun s : ℝ => mainBarrierB s R) t < 0 := by
  have hRmem := hR
  have htmem := ht
  rcases hR with ⟨hRlo, hRhi⟩
  rcases ht with ⟨htlo, hthi⟩
  have htpos : 0 < t := by linarith
  have htSqLo : (0.8588 : ℝ) ^ 2 ≤ t ^ 2 :=
    (sq_le_sq₀ (by norm_num) (by linarith)).2 htlo
  have htSqHi : t ^ 2 ≤ (1.1265 : ℝ) ^ 2 :=
    (sq_le_sq₀ (by linarith) (by norm_num)).2 hthi
  have hzLo : (0.73 : ℝ) < t ^ 2 := by norm_num at htSqLo ⊢; linarith
  have hzHi : t ^ 2 < (1.27 : ℝ) := by norm_num at htSqHi ⊢; linarith
  have hb6 := mainBarrierB6Offset_bounds hRmem
  have hb7 := mainBarrierB7Offset_upper hRmem
  rcases hb6 with ⟨hb6lo, hb6hi⟩
  have hb6pos : t ^ 2 <
      (R - Real.sqrt 6) ^ 2 - (Real.sqrt 10 + Real.sqrt 6) ^ 2 := by
    dsimp [mainBarrierB6Offset, mainBarrierD6] at hb6lo
    linarith
  have hb7neg :
      (R - Real.sqrt 7) ^ 2 - (Real.sqrt 10 + Real.sqrt 7) ^ 2 < t ^ 2 := by
    dsimp [mainBarrierB7Offset, mainBarrierD7] at hb7
    linarith
  have hpair := touchAngle_pair_derivative_sum_neg htpos
    (by positivity : 0 < Real.sqrt 10 + Real.sqrt 6)
    (by positivity : 0 < Real.sqrt 10 + Real.sqrt 7)
    (mainBarrier_heron6_positive hRmem htmem)
    (mainBarrier_heron7_positive hRmem htmem)
    hb6pos hb7neg (mainBarrier_derivative_comparison_polynomial hRmem htmem)
  have ha6 : 0 < R - Real.sqrt 6 := by
    have hs := sqrt6_coarse_bounds.2
    linarith
  have ha7 : 0 < R - Real.sqrt 7 := by
    have hs := sqrt7_coarse_bounds.2
    linarith
  let d6 : ℝ :=
    ( (R - Real.sqrt 6) ^ 2 - (Real.sqrt 10 + Real.sqrt 6) ^ 2 - t ^ 2) /
      (t * Real.sqrt (touchHeron t (R - Real.sqrt 6)
        (Real.sqrt 10 + Real.sqrt 6)))
  let d7 : ℝ :=
    ( (R - Real.sqrt 7) ^ 2 - (Real.sqrt 10 + Real.sqrt 7) ^ 2 - t ^ 2) /
      (t * Real.sqrt (touchHeron t (R - Real.sqrt 7)
        (Real.sqrt 10 + Real.sqrt 7)))
  have h6 : HasDerivAt (fun s : ℝ => mainAlpha6 s R) d6 t := by
    simpa [mainAlpha6, touchAngle, d6] using
      (hasDerivAt_touchAngle_first_radius ha6 htpos
        (mainBarrier_heron6_positive hRmem htmem))
  have h7 : HasDerivAt (fun s : ℝ => mainAlpha7 s R) d7 t := by
    simpa [mainAlpha7, touchAngle, d7] using
      (hasDerivAt_touchAngle_first_radius ha7 htpos
        (mainBarrier_heron7_positive hRmem htmem))
  have hsumBare : HasDerivAt
      (fun s : ℝ => mainAlpha7 s R + mainAlpha6 s R) (d7 + d6) t := by
    convert h7.add h6 using 1
  have hsum : HasDerivAt (fun s : ℝ => mainBarrierB s R) (d7 + d6) t := by
    convert hsumBare.add_const (mainCommonWallAngles R) using 1
    funext s
    dsimp [mainBarrierB, mainAlpha6, mainAlpha7]
    ring
  rw [hsum.deriv]
  have hrewrite : d7 + d6 =
      ((R - Real.sqrt 6) ^ 2 - (Real.sqrt 10 + Real.sqrt 6) ^ 2 - t ^ 2) /
          (t * Real.sqrt (touchHeron t (R - Real.sqrt 6)
            (Real.sqrt 10 + Real.sqrt 6))) +
        ((R - Real.sqrt 7) ^ 2 - (Real.sqrt 10 + Real.sqrt 7) ^ 2 - t ^ 2) /
          (t * Real.sqrt (touchHeron t (R - Real.sqrt 7)
            (Real.sqrt 10 + Real.sqrt 7))) := by
    simp [d6, d7]
    ring
  rw [hrewrite]
  exact hpair

theorem mainBarrierB_antitone_t_on_ranges
    {R t₁ t₂ : ℝ} (hR : R ∈ mainBarrierRadiusRange)
    (ht₁ : t₁ ∈ mainBarrierTRange) (ht₂ : t₂ ∈ mainBarrierTRange)
    (h12 : t₁ ≤ t₂) : mainBarrierB t₂ R ≤ mainBarrierB t₁ R := by
  let f : ℝ → ℝ := fun s => mainBarrierB s R
  have hcont : ContinuousOn f mainBarrierTRange := by
    intro s hs
    have hderiv := mainBarrierB_deriv_neg_on_ranges hR hs
    have hdiff : DifferentiableAt ℝ f s :=
      differentiableAt_of_deriv_ne_zero (by
        change deriv (fun x : ℝ => mainBarrierB x R) s ≠ 0
        exact ne_of_lt hderiv)
    exact hdiff.continuousAt.continuousWithinAt
  have hanti : StrictAntiOn f mainBarrierTRange := by
    apply strictAntiOn_of_deriv_neg (convex_Icc 0.8588 1.1265) hcont
    intro s hs
    apply mainBarrierB_deriv_neg_on_ranges hR
    exact interior_subset hs
  by_cases heq : t₁ = t₂
  · simp [heq]
  · have hlt : t₁ < t₂ := lt_of_le_of_ne h12 heq
    exact (hanti ht₁ ht₂ hlt).le

theorem mainBarrierB_strictAnti_t_on_ranges
    {R t₁ t₂ : ℝ} (hR : R ∈ mainBarrierRadiusRange)
    (ht₁ : t₁ ∈ mainBarrierTRange) (ht₂ : t₂ ∈ mainBarrierTRange)
    (h12 : t₁ < t₂) : mainBarrierB t₂ R < mainBarrierB t₁ R := by
  let f : ℝ → ℝ := fun s => mainBarrierB s R
  have hcont : ContinuousOn f mainBarrierTRange := by
    intro s hs
    have hderiv := mainBarrierB_deriv_neg_on_ranges hR hs
    have hdiff : DifferentiableAt ℝ f s :=
      differentiableAt_of_deriv_ne_zero (by
        change deriv (fun x : ℝ => mainBarrierB x R) s ≠ 0
        exact ne_of_lt hderiv)
    exact hdiff.continuousAt.continuousWithinAt
  have hanti : StrictAntiOn f mainBarrierTRange := by
    apply strictAntiOn_of_deriv_neg (convex_Icc 0.8588 1.1265) hcont
    intro s hs
    apply mainBarrierB_deriv_neg_on_ranges hR
    exact interior_subset hs
  exact hanti ht₁ ht₂ h12

theorem mainBarrierA_strictAnti_R_on_ranges
    {t R₁ R₂ : ℝ} (ht : t ∈ mainBarrierTRange)
    (hR₁ : R₁ ∈ mainBarrierGlobalRadiusRange)
    (hR₂ : R₂ ∈ mainBarrierGlobalRadiusRange)
    (hR₁₂ : R₁ < R₂) :
    mainBarrierA t R₂ < mainBarrierA t R₁ := by
  have hR₁mem := hR₁
  have hR₂mem := hR₂
  rcases hR₁ with ⟨hR₁lo, hR₁hi⟩
  have hs5 := sqrt5_coarse_bounds.2
  have hs6 := sqrt6_coarse_bounds.2
  have hs7 := sqrt7_coarse_bounds.2
  have hs10 := sqrt10_coarse_bounds.2
  have hs2 := sqrt_two_lt_three
  have hs8 := sqrt_eight_lt_three
  have hs9 := sqrt_nine_eq_three
  have hAlpha5 : mainAlpha5 t R₂ < mainAlpha5 t R₁ := by
    unfold mainAlpha5
    exact mainAlpha_strictAnti_radius ht hR₁mem hR₂mem hR₁₂
      (by positivity) (by linarith) (mainAlpha5_heron_positive hR₁mem ht)
      (mainAlpha5_heron_positive hR₂mem ht)
  have hAlpha6 : mainAlpha6 t R₂ < mainAlpha6 t R₁ := by
    unfold mainAlpha6
    exact mainAlpha_strictAnti_radius ht hR₁mem hR₂mem hR₁₂
      (by positivity) (by linarith)
      (mainAlpha6_heron_positive_global hR₁mem ht)
      (mainAlpha6_heron_positive_global hR₂mem ht)
  have hBeta57 : mainBeta57 R₂ < mainBeta57 R₁ := by
    unfold mainBeta57
    apply wallContactAngle_strictAnti_radius <;> try positivity
    · have hsmall : Real.sqrt 5 + Real.sqrt 7 < 6 := by linarith
      linarith
    · exact hR₁₂
  have hBeta79 : mainBeta79 R₂ < mainBeta79 R₁ := by
    unfold mainBeta79
    apply wallContactAngle_strictAnti_radius <;> try positivity
    · have hsmall : Real.sqrt 7 + Real.sqrt 9 < 6 := by linarith
      linarith
    · exact hR₁₂
  have hBeta92 : mainBeta92 R₂ < mainBeta92 R₁ := by
    unfold mainBeta92
    apply wallContactAngle_strictAnti_radius <;> try positivity
    · have hsmall : Real.sqrt 9 + Real.sqrt 2 < 6 := by linarith
      linarith
    · exact hR₁₂
  have hBeta28 : mainBeta28 R₂ < mainBeta28 R₁ := by
    unfold mainBeta28
    apply wallContactAngle_strictAnti_radius <;> try positivity
    · have hsmall : Real.sqrt 2 + Real.sqrt 8 < 6 := by linarith
      linarith
    · exact hR₁₂
  have hBeta86 : mainBeta86 R₂ < mainBeta86 R₁ := by
    unfold mainBeta86
    apply wallContactAngle_strictAnti_radius <;> try positivity
    · have hsmall : Real.sqrt 8 + Real.sqrt 6 < 6 := by linarith
      linarith
    · exact hR₁₂
  have hcommon : mainCommonWallAngles R₂ < mainCommonWallAngles R₁ := by
    unfold mainCommonWallAngles
    linarith
  unfold mainBarrierA
  linarith

theorem mainBarrierB_strictAnti_R_on_ranges
    {t R₁ R₂ : ℝ} (ht : t ∈ mainBarrierTRange)
    (hR₁ : R₁ ∈ mainBarrierGlobalRadiusRange)
    (hR₂ : R₂ ∈ mainBarrierGlobalRadiusRange)
    (hR₁₂ : R₁ < R₂) :
    mainBarrierB t R₂ < mainBarrierB t R₁ := by
  have hR₁mem := hR₁
  have hR₂mem := hR₂
  have hR₁lo : 7.9 ≤ R₁ := hR₁mem.1
  have hs6 := sqrt6_coarse_bounds.2
  have hs7 := sqrt7_coarse_bounds.2
  have hAlpha6 : mainAlpha6 t R₂ < mainAlpha6 t R₁ := by
    unfold mainAlpha6
    exact mainAlpha_strictAnti_radius ht hR₁mem hR₂mem hR₁₂
      (by positivity) (by linarith)
      (mainAlpha6_heron_positive_global hR₁mem ht)
      (mainAlpha6_heron_positive_global hR₂mem ht)
  have hAlpha7 : mainAlpha7 t R₂ < mainAlpha7 t R₁ := by
    unfold mainAlpha7
    exact mainAlpha_strictAnti_radius ht hR₁mem hR₂mem hR₁₂
      (by positivity) (by linarith)
      (mainAlpha7_heron_positive_global hR₁mem ht)
      (mainAlpha7_heron_positive_global hR₂mem ht)
  have hBeta79 : mainBeta79 R₂ < mainBeta79 R₁ := by
    unfold mainBeta79
    apply wallContactAngle_strictAnti_radius <;> try positivity
    · have hsmall : Real.sqrt 7 + Real.sqrt 9 < 6 := by
        have hs9 := sqrt_nine_eq_three
        linarith
      linarith
    · exact hR₁₂
  have hBeta92 : mainBeta92 R₂ < mainBeta92 R₁ := by
    unfold mainBeta92
    apply wallContactAngle_strictAnti_radius <;> try positivity
    · have hsmall : Real.sqrt 9 + Real.sqrt 2 < 6 := by
        have hs9 := sqrt_nine_eq_three
        linarith [sqrt_two_lt_three]
      linarith
    · exact hR₁₂
  have hBeta28 : mainBeta28 R₂ < mainBeta28 R₁ := by
    unfold mainBeta28
    apply wallContactAngle_strictAnti_radius <;> try positivity
    · have hsmall : Real.sqrt 2 + Real.sqrt 8 < 6 := by
        linarith [sqrt_two_lt_three, sqrt_eight_lt_three]
      linarith
    · exact hR₁₂
  have hBeta86 : mainBeta86 R₂ < mainBeta86 R₁ := by
    unfold mainBeta86
    apply wallContactAngle_strictAnti_radius <;> try positivity
    · have hsmall : Real.sqrt 8 + Real.sqrt 6 < 6 := by
        linarith [sqrt_eight_lt_three]
      linarith
    · exact hR₁₂
  have hcommon : mainCommonWallAngles R₂ < mainCommonWallAngles R₁ := by
    unfold mainCommonWallAngles
    linarith
  unfold mainBarrierB
  linarith

theorem mainAlpha5_mono_t_on_ranges
    {R t₁ t₂ : ℝ} (hR : R ∈ mainBarrierRadiusRange)
    (ht₁ : t₁ ∈ mainBarrierTRange) (ht₂ : t₂ ∈ mainBarrierTRange)
    (h12 : t₁ ≤ t₂) : mainAlpha5 t₁ R ≤ mainAlpha5 t₂ R := by
  rcases hR with ⟨hRlo, hRhi⟩
  rcases ht₁ with ⟨ht₁lo, ht₁hi⟩
  rcases ht₂ with ⟨ht₂lo, ht₂hi⟩
  have ha : 0 < R - Real.sqrt 5 := by
    have hs := sqrt5_coarse_bounds.2
    linarith
  unfold mainAlpha5
  exact touchAngle_mono_first_radius_of_sq_upper ha
    (by linarith) (by linarith) h12
    (mainAlpha5_sq_condition ⟨hRlo, hRhi⟩ ⟨ht₂lo, ht₂hi⟩)

theorem mainAlpha6_mono_t_on_ranges
    {R t₁ t₂ : ℝ} (hR : R ∈ mainBarrierRadiusRange)
    (ht₁ : t₁ ∈ mainBarrierTRange) (ht₂ : t₂ ∈ mainBarrierTRange)
    (h12 : t₁ ≤ t₂) : mainAlpha6 t₁ R ≤ mainAlpha6 t₂ R := by
  rcases hR with ⟨hRlo, hRhi⟩
  rcases ht₁ with ⟨ht₁lo, ht₁hi⟩
  rcases ht₂ with ⟨ht₂lo, ht₂hi⟩
  have ha : 0 < R - Real.sqrt 6 := by
    have hs := sqrt6_coarse_bounds.2
    linarith
  unfold mainAlpha6
  exact touchAngle_mono_first_radius_of_sq_upper ha
    (by linarith) (by linarith) h12
    (mainAlpha6_sq_condition ⟨hRlo, hRhi⟩ ⟨ht₂lo, ht₂hi⟩)

theorem mainAlpha7_antitone_t_on_ranges
    {R t₁ t₂ : ℝ} (hR : R ∈ mainBarrierRadiusRange)
    (ht₁ : t₁ ∈ mainBarrierTRange) (ht₂ : t₂ ∈ mainBarrierTRange)
    (h12 : t₁ ≤ t₂) : mainAlpha7 t₂ R ≤ mainAlpha7 t₁ R := by
  rcases hR with ⟨hRlo, hRhi⟩
  rcases ht₁ with ⟨ht₁lo, ht₁hi⟩
  rcases ht₂ with ⟨ht₂lo, ht₂hi⟩
  have ha : 0 < R - Real.sqrt 7 := by
    have hs := sqrt7_coarse_bounds.2
    linarith
  unfold mainAlpha7
  exact touchAngle_antitone_first_radius_of_sq_lower ha
    (by linarith) (by linarith) h12
    (mainAlpha7_sq_condition ⟨hRlo, hRhi⟩ ⟨ht₁lo, ht₁hi⟩)

theorem mainBarrierA_mono_t_on_ranges
    {R t₁ t₂ : ℝ} (hR : R ∈ mainBarrierRadiusRange)
    (ht₁ : t₁ ∈ mainBarrierTRange) (ht₂ : t₂ ∈ mainBarrierTRange)
    (h12 : t₁ ≤ t₂) : mainBarrierA t₁ R ≤ mainBarrierA t₂ R := by
  have h5 := mainAlpha5_mono_t_on_ranges hR ht₁ ht₂ h12
  have h6 := mainAlpha6_mono_t_on_ranges hR ht₁ ht₂ h12
  unfold mainBarrierA
  linarith

private theorem main_angle_no_two_roots_if_radius_lt
    {t₁ t₂ R₁ R₂ : ℝ}
    (hR₁ : R₁ ∈ mainBarrierRadiusRange)
    (hR₂ : R₂ ∈ mainBarrierRadiusRange)
    (ht₁ : t₁ ∈ mainBarrierTRange)
    (ht₂ : t₂ ∈ mainBarrierTRange)
    (hR₁₂ : R₁ < R₂)
    (hA₁ : mainBarrierA t₁ R₁ = 2 * Real.pi)
    (hB₁ : mainBarrierB t₁ R₁ = 2 * Real.pi)
    (hA₂ : mainBarrierA t₂ R₂ = 2 * Real.pi)
    (hB₂ : mainBarrierB t₂ R₂ = 2 * Real.pi) : False := by
  have hR₁global : R₁ ∈ mainBarrierGlobalRadiusRange := by
    constructor
    · linarith [hR₁.1]
    · exact hR₁.2
  have hR₂global : R₂ ∈ mainBarrierGlobalRadiusRange := by
    constructor
    · linarith [hR₂.1]
    · exact hR₂.2
  have hAdec := mainBarrierA_strictAnti_R_on_ranges ht₁ hR₁global hR₂global hR₁₂
  have hAatR₂ : mainBarrierA t₁ R₂ < 2 * Real.pi := by
    rw [← hA₁]
    exact hAdec
  have ht₁₂ : t₁ < t₂ := by
    by_contra hnot
    have ht₂₁ : t₂ ≤ t₁ := le_of_not_gt hnot
    have hAmono := mainBarrierA_mono_t_on_ranges hR₂ ht₂ ht₁ ht₂₁
    rw [hA₂] at hAmono
    linarith
  have hBdecT := mainBarrierB_strictAnti_t_on_ranges hR₂ ht₁ ht₂ ht₁₂
  have hBdecR := mainBarrierB_strictAnti_R_on_ranges ht₁ hR₁global hR₂global hR₁₂
  rw [hB₂] at hBdecT
  rw [hB₁] at hBdecR
  linarith

/-- The simultaneous angle equations have at most one solution in the
certified rectangle. This follows from the replayed strict radial decrease
of both barriers, weak increase of `A` in `t`, and strict decrease of `B` in
`t`. -/
theorem main_angle_critical_pair_unique
    {t₁ t₂ R₁ R₂ : ℝ}
    (hR₁ : R₁ ∈ mainBarrierRadiusRange)
    (hR₂ : R₂ ∈ mainBarrierRadiusRange)
    (ht₁ : t₁ ∈ mainBarrierTRange)
    (ht₂ : t₂ ∈ mainBarrierTRange)
    (hA₁ : mainBarrierA t₁ R₁ = 2 * Real.pi)
    (hB₁ : mainBarrierB t₁ R₁ = 2 * Real.pi)
    (hA₂ : mainBarrierA t₂ R₂ = 2 * Real.pi)
    (hB₂ : mainBarrierB t₂ R₂ = 2 * Real.pi) : t₁ = t₂ ∧ R₁ = R₂ := by
  have hR : R₁ = R₂ := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact False.elim (main_angle_no_two_roots_if_radius_lt
        hR₁ hR₂ ht₁ ht₂ hlt hA₁ hB₁ hA₂ hB₂)
    · exact False.elim (main_angle_no_two_roots_if_radius_lt
        hR₂ hR₁ ht₂ ht₁ hgt hA₂ hB₂ hA₁ hB₁)
  subst R₂
  have ht : t₁ = t₂ := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hB := mainBarrierB_strictAnti_t_on_ranges hR₁ ht₁ ht₂ hlt
      rw [hB₁, hB₂] at hB
      exact (lt_irrefl _ hB)
    · have hB := mainBarrierB_strictAnti_t_on_ranges hR₁ ht₂ ht₁ hgt
      rw [hB₁, hB₂] at hB
      exact (lt_irrefl _ hB)
  exact ⟨ht, rfl⟩

/-- The root comparison theorem specialized to the certified angular rectangle.
Both `t` and `R` monotonicity branches are discharged by Lean on the certified
domains; the exact root and geometric applicability remain separate inputs. -/
theorem main_angle_barrier_excludes_below_critical_on_ranges
    {t R tcrit Rcrit : ℝ}
    (hRlo : 7.9 ≤ R)
    (hRcrit : Rcrit ∈ mainBarrierRadiusRange)
    (ht : t ∈ mainBarrierTRange)
    (htcrit : tcrit ∈ mainBarrierTRange)
    (hR : R < Rcrit)
    (hAroot : mainBarrierA tcrit Rcrit = 2 * Real.pi)
    (hBroot : mainBarrierB tcrit Rcrit = 2 * Real.pi)
    (hA_geometry : mainBarrierA t R ≤ 2 * Real.pi)
    (hB_geometry : mainBarrierB t R ≤ 2 * Real.pi) :
    False := by
  have hA_mono : ∀ {t₁ t₂ : ℝ}, t₁ ≤ t₂ →
      t₁ ∈ mainBarrierTRange → t₂ ∈ mainBarrierTRange →
      mainBarrierA t₁ Rcrit ≤ mainBarrierA t₂ Rcrit := by
    intro t₁ t₂ h12 ht₁ ht₂
    exact mainBarrierA_mono_t_on_ranges hRcrit ht₁ ht₂ h12
  have hB_anti : ∀ {t₁ t₂ : ℝ}, t₁ ≤ t₂ →
      t₁ ∈ mainBarrierTRange → t₂ ∈ mainBarrierTRange →
      mainBarrierB t₂ Rcrit ≤ mainBarrierB t₁ Rcrit := by
    intro t₁ t₂ h12 ht₁ ht₂
    exact mainBarrierB_antitone_t_on_ranges hRcrit ht₁ ht₂ h12
  have hRglobal : R ∈ mainBarrierGlobalRadiusRange :=
    ⟨hRlo, le_trans (le_of_lt hR) hRcrit.2⟩
  have hRcritGlobal : Rcrit ∈ mainBarrierGlobalRadiusRange := by
    refine ⟨?_, hRcrit.2⟩
    linarith [hRcrit.1]
  have hA_anti_R : mainBarrierA t Rcrit < mainBarrierA t R :=
    mainBarrierA_strictAnti_R_on_ranges ht hRglobal hRcritGlobal hR
  have hB_anti_R : mainBarrierB t Rcrit < mainBarrierB t R :=
    mainBarrierB_strictAnti_R_on_ranges ht hRglobal hRcritGlobal hR
  exact main_angle_barrier_excludes_below_critical ht htcrit hAroot hBroot
    hA_mono hB_anti hA_anti_R hB_anti_R
    hA_geometry hB_geometry

end
end CirclePacking
