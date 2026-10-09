import CirclePacking.FifteenCertificate
import CirclePacking.CosineTaylor
import CirclePacking.CornerBound
import CirclePacking.GeometricAngle
import CirclePacking.PolarAngle
import CirclePacking.FifteenCycleSoundness
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Analytic soundness of rational angle ticks

The certificate checker works with rational arithmetic only. This module
proves that its degree-18 Taylor lower bound is below cosine and that a
regular tick accepted by the checker is therefore a lower bound on any angle
whose cosine obeys the checked contact cap. The remaining geometric work is to
derive that contact cap from the disk separation constraints and the corner
maximum for the radius intervals.
-/

namespace CirclePacking

open scoped BigOperators

theorem fifteenCosineTaylor18Remainder
    {a b x : ℝ} (hab : a < b) (hx : x ∈ Set.Icc a b) :
    ‖Real.cos x - taylorWithinEval Real.cos 18 (Set.Icc a b) a x‖ ≤
      (x - a) ^ 19 / ((Nat.factorial 18 : ℕ) : ℝ) := by
  have h := taylor_mean_remainder_bound (n := 18) (C := (1 : ℝ)) hab.le
      Real.contDiff_cos.contDiffOn hx (by
        intro y hy
        rw [show 18 + 1 = 19 by norm_num,
          Real.iteratedDerivWithin_cos_Icc 19 hab hy]
        simpa [Real.norm_eq_abs] using Real.abs_iteratedDeriv_cos_le_one 19 y)
  simpa using h

theorem fifteenCosineTaylor18AtZero
    {b x : ℝ} (hb : 0 < b) :
    taylorWithinEval Real.cos 18 (Set.Icc 0 b) 0 x =
      ∑ k ∈ Finset.range 10,
        (-1 : ℝ) ^ k * x ^ (2 * k) /
          ((Nat.factorial (2 * k) : ℕ) : ℝ) := by
  rw [taylor_within_apply]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero,
    Nat.factorial_zero, Nat.factorial_one, Nat.cast_one, inv_one]
  have hzero : (0 : ℝ) ∈ Set.Icc 0 b := ⟨le_rfl, hb.le⟩
  simp_rw [
    Real.iteratedDerivWithin_cos_Icc 0 hb hzero,
    Real.iteratedDerivWithin_cos_Icc 1 hb hzero,
    Real.iteratedDerivWithin_cos_Icc 2 hb hzero,
    Real.iteratedDerivWithin_cos_Icc 3 hb hzero,
    Real.iteratedDerivWithin_cos_Icc 4 hb hzero,
    Real.iteratedDerivWithin_cos_Icc 5 hb hzero,
    Real.iteratedDerivWithin_cos_Icc 6 hb hzero,
    Real.iteratedDerivWithin_cos_Icc 7 hb hzero,
    Real.iteratedDerivWithin_cos_Icc 8 hb hzero,
    Real.iteratedDerivWithin_cos_Icc 9 hb hzero,
    Real.iteratedDerivWithin_cos_Icc 10 hb hzero,
    Real.iteratedDerivWithin_cos_Icc 11 hb hzero,
    Real.iteratedDerivWithin_cos_Icc 12 hb hzero,
    Real.iteratedDerivWithin_cos_Icc 13 hb hzero,
    Real.iteratedDerivWithin_cos_Icc 14 hb hzero,
    Real.iteratedDerivWithin_cos_Icc 15 hb hzero,
    Real.iteratedDerivWithin_cos_Icc 16 hb hzero,
    Real.iteratedDerivWithin_cos_Icc 17 hb hzero,
    Real.iteratedDerivWithin_cos_Icc 18 hb hzero]
  norm_num [Real.iteratedDeriv_even_cos, Real.iteratedDeriv_odd_cos]
  ring

theorem fifteenRational_cast (q : Nat) :
    (fifteenRational q 2800 : ℝ) = (q : ℝ) / 2800 := by
  simp [fifteenRational, Rat.normalize_eq_mkRat,
    Rat.cast_mkRat_of_ne_zero]

theorem fifteenCosineLower_le_cos (q : Nat) (hq : q ≤ 8790) :
    (fifteenCosineLower q : ℝ) ≤ Real.cos ((q : ℝ) / 2800) := by
  let x : ℝ := (q : ℝ) / 2800
  have hx0 : 0 ≤ x := by positivity
  have hx4 : x ≤ 4 := by
    dsimp [x]
    calc
      (q : ℝ) / 2800 ≤ (8790 : ℝ) / 2800 := by
        exact div_le_div_of_nonneg_right (by exact_mod_cast hq) (by norm_num)
      _ ≤ 4 := by norm_num
  have hrem := fifteenCosineTaylor18Remainder (a := 0) (b := 4)
      (x := x) (by norm_num) ⟨hx0, hx4⟩
  have htaylor := fifteenCosineTaylor18AtZero (b := 4) (x := x) (by norm_num)
  have hTaylorPoly :
      (∑ k ∈ Finset.range 10,
        (-1 : ℝ) ^ k * x ^ (2 * k) /
          ((Nat.factorial (2 * k) : ℕ) : ℝ)) =
        1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720 + x ^ 8 / 40320 -
          x ^ 10 / 3628800 + x ^ 12 / 479001600 - x ^ 14 / 87178291200 +
          x ^ 16 / 20922789888000 - x ^ 18 / 6402373705728000 := by
    norm_num [Finset.sum_range_succ, Nat.factorial]
    ring
  have herr : ‖Real.cos x -
      ∑ k ∈ Finset.range 10,
        (-1 : ℝ) ^ k * x ^ (2 * k) /
          ((Nat.factorial (2 * k) : ℕ) : ℝ)‖ ≤ x ^ 19 / 6402373705728000 := by
    rw [← htaylor]
    have hfac : (Nat.factorial 18 : ℝ) = 6402373705728000 := by norm_num
    simpa [hfac] using hrem
  have hlow : (∑ k ∈ Finset.range 10,
      (-1 : ℝ) ^ k * x ^ (2 * k) /
        ((Nat.factorial (2 * k) : ℕ) : ℝ)) -
        x ^ 19 / 6402373705728000 ≤ Real.cos x := by
    have habs : |Real.cos x -
        ∑ k ∈ Finset.range 10,
          (-1 : ℝ) ^ k * x ^ (2 * k) /
            ((Nat.factorial (2 * k) : ℕ) : ℝ)| ≤ x ^ 19 / 6402373705728000 := by
      simpa [Real.norm_eq_abs] using herr
    have hleft := (abs_le.mp habs).1
    linarith
  rw [hTaylorPoly] at hlow
  have hcast : (fifteenCosineLower q : ℝ) =
      1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720 + x ^ 8 / 40320 -
        x ^ 10 / 3628800 + x ^ 12 / 479001600 - x ^ 14 / 87178291200 +
        x ^ 16 / 20922789888000 - x ^ 18 / 6402373705728000 -
        x ^ 19 / 6402373705728000 := by
    simp [fifteenCosineLower, fifteenRational_cast, x]
  rw [hcast]
  exact hlow

theorem fifteenAngleTick_lower_of_cosine_cap
    (q : Nat) (hq : q ≤ 8790) (angle cap : ℝ)
    (hangle0 : 0 ≤ angle) (hanglePi : angle ≤ Real.pi)
    (hcontact : Real.cos angle ≤ cap)
    (hcap : cap ≤ (fifteenCosineLower q : ℝ)) :
    (q : ℝ) / 2800 ≤ angle := by
  have hqReal : (q : ℝ) ≤ 8790 := by exact_mod_cast hq
  have ht0 : 0 ≤ (q : ℝ) / 2800 := by positivity
  have htPi : (q : ℝ) / 2800 ≤ Real.pi := by
    exact (calc
      (q : ℝ) / 2800 ≤ (8790 : ℝ) / 2800 :=
        div_le_div_of_nonneg_right hqReal (by norm_num)
      _ < (3.14 : ℝ) := by norm_num
      _ < Real.pi := Real.pi_gt_d2).le
  have hcosTick : (fifteenCosineLower q : ℝ) ≤
      Real.cos ((q : ℝ) / 2800) := fifteenCosineLower_le_cos q hq
  have hcos : Real.cos angle ≤ Real.cos ((q : ℝ) / 2800) :=
    le_trans hcontact (le_trans hcap hcosTick)
  exact (Real.strictAntiOn_cos.le_iff_ge ⟨hangle0, hanglePi⟩
    ⟨ht0, htPi⟩).1 hcos

theorem fifteenTickCertificateValid_regular_spec
    (x y : FifteenInterval) (ticks : Nat)
    (hsum : 2 ≤ x.2 + y.2)
    (hupper : fifteenBoxCosineCap x y < 1)
    (hlower : -1 < fifteenBoxCosineCap x y)
    (hvalid : fifteenTickCertificateValid x y false false ticks = true) :
    ticks ≤ 8790 ∧
      (fifteenBoxCosineCap x y : ℝ) ≤ (fifteenCosineLower ticks : ℝ) := by
  have hcheck : ticks ≤ 8790 ∧
      fifteenBoxCosineCap x y ≤ fifteenCosineLower ticks := by
    have hsum' : ¬ x.2 + y.2 < 2 := by linarith
    have hnotupper : ¬ 1 ≤ fifteenBoxCosineCap x y := by linarith
    have hnotlower : ¬ fifteenBoxCosineCap x y ≤ -1 := by linarith
    simpa [fifteenTickCertificateValid, hsum', hnotupper, hnotlower] using hvalid
  exact ⟨hcheck.1, by exact_mod_cast hcheck.2⟩

theorem fifteenRegularTick_gives_angle_lower_bound
    (x y : FifteenInterval) (ticks : Nat) (angle : ℝ)
    (hsum : 2 ≤ x.2 + y.2)
    (hupper : fifteenBoxCosineCap x y < 1)
    (hlower : -1 < fifteenBoxCosineCap x y)
    (hvalid : fifteenTickCertificateValid x y false false ticks = true)
    (hangle0 : 0 ≤ angle) (hanglePi : angle ≤ Real.pi)
    (hcontact : Real.cos angle ≤ (fifteenBoxCosineCap x y : ℝ)) :
    (ticks : ℝ) / 2800 ≤ angle := by
  have hspec := fifteenTickCertificateValid_regular_spec x y ticks
    hsum hupper hlower hvalid
  exact fifteenAngleTick_lower_of_cosine_cap ticks hspec.1 angle
    (fifteenBoxCosineCap x y : ℝ) hangle0 hanglePi hcontact hspec.2

theorem fifteenTickCertificateValid_exactZero_ticks
    (x y : FifteenInterval) (ticks : Nat)
    (hsum : 2 ≤ x.2 + y.2)
    (hvalid : fifteenTickCertificateValid x y false true ticks = true) :
    ticks = 0 := by
  have hnotSum : ¬ x.2 + y.2 < 2 := by linarith
  simpa [fifteenTickCertificateValid, hnotSum] using hvalid

theorem fifteenTickCertificateValid_sum_spec
    (x y : FifteenInterval) (positiveZero exactZero : Bool) (ticks : Nat)
    (hvalid : fifteenTickCertificateValid x y positiveZero exactZero ticks = true) :
    2 ≤ x.2 + y.2 := by
  by_contra hsum
  have hsmall : x.2 + y.2 < 2 := lt_of_not_ge hsum
  simp [fifteenTickCertificateValid, hsmall] at hvalid

theorem fifteenCosineRuleCap_cast (x y : Rat) :
    (fifteenCosineRuleCap x y : ℝ) =
      ((x : ℝ) ^ 2 + (y : ℝ) ^ 2 - 4) /
        (2 * (x : ℝ) * (y : ℝ)) := by
  norm_num [fifteenCosineRuleCap]

theorem fifteenPositiveZeroCosineCap_eq_cosineRuleCap
    (x y : FifteenInterval)
    (hzero : x.1 = 0 ∨ y.1 = 0)
    (hxUpperPositive : 0 < x.2) (hyUpperPositive : 0 < y.2)
    (hxUpperLeTwo : x.2 ≤ 2) (hyUpperLeTwo : y.2 ≤ 2) :
    fifteenPositiveZeroCosineCap x y = fifteenCosineRuleCap x.2 y.2 := by
  by_cases hxzero : x.1 = 0
  · simp [fifteenPositiveZeroCosineCap, hxzero, hyUpperPositive, hyUpperLeTwo]
  · have hyzero : y.1 = 0 := hzero.resolve_left hxzero
    simp [fifteenPositiveZeroCosineCap, hxzero, hxUpperPositive, hxUpperLeTwo]
    unfold fifteenCosineRuleCap
    ring

theorem fifteenPositiveZeroCosineCap_cast_eq_touchCosine
    (x y : FifteenInterval)
    (hzero : x.1 = 0 ∨ y.1 = 0)
    (hxUpperPositive : 0 < x.2) (hyUpperPositive : 0 < y.2)
    (hxUpperLeTwo : x.2 ≤ 2) (hyUpperLeTwo : y.2 ≤ 2) :
    (fifteenPositiveZeroCosineCap x y : ℝ) =
      touchCosine (x.2 : ℝ) (y.2 : ℝ) 2 := by
  rw [fifteenPositiveZeroCosineCap_eq_cosineRuleCap x y hzero
    hxUpperPositive hyUpperPositive hxUpperLeTwo hyUpperLeTwo,
    fifteenCosineRuleCap_cast]
  norm_num [touchCosine]

theorem touchCosine_mono_radii_of_le_two
    {a b A B : ℝ}
    (ha : 0 < a) (hb : 0 < b)
    (haA : a ≤ A) (hbB : b ≤ B)
    (hA : A ≤ 2) (hB : B ≤ 2) :
    touchCosine a b 2 ≤ touchCosine A B 2 := by
  have hApos : 0 < A := lt_of_lt_of_le ha haA
  have hBpos : 0 < B := lt_of_lt_of_le hb hbB
  have hbSq : b ^ 2 ≤ 4 := by
    calc
      b ^ 2 ≤ (2 : ℝ) ^ 2 :=
        (sq_le_sq₀ (le_of_lt hb) (by norm_num)).2 (le_trans hbB hB)
      _ = 4 := by norm_num
  have hASq : A ^ 2 ≤ 4 := by
    calc
      A ^ 2 ≤ (2 : ℝ) ^ 2 :=
        (sq_le_sq₀ (le_of_lt hApos) (by norm_num)).2 hA
      _ = 4 := by norm_num
  have hfirstFactor : 0 ≤ (A - a) * (a * A + 4 - b ^ 2) :=
    mul_nonneg (sub_nonneg.mpr haA) (by nlinarith)
  have hfirst : touchCosine a b 2 ≤ touchCosine A b 2 := by
    unfold touchCosine
    apply (div_le_div_iff₀ (by positivity) (by positivity)).2
    nlinarith [hfirstFactor]
  have hsecondFactor : 0 ≤ (B - b) * (b * B + 4 - A ^ 2) :=
    mul_nonneg (sub_nonneg.mpr hbB) (by nlinarith)
  have hsecond : touchCosine A b 2 ≤ touchCosine A B 2 := by
    unfold touchCosine
    apply (div_le_div_iff₀ (by positivity) (by positivity)).2
    nlinarith [hsecondFactor]
  exact le_trans hfirst hsecond

theorem fifteenPositiveZeroCosineCap_bounds_or_one
    (x y : FifteenInterval) (a b : ℝ)
    (hzero : x.1 = 0 ∨ y.1 = 0)
    (hzeroUpperLeTwo : (x.1 = 0 → x.2 ≤ 2) ∧ (y.1 = 0 → y.2 ≤ 2))
    (ha : 0 < a) (hb : 0 < b)
    (haUpper : a ≤ (x.2 : ℝ)) (hbUpper : b ≤ (y.2 : ℝ)) :
    (1 : ℝ) ≤ (fifteenPositiveZeroCosineCap x y : ℝ) ∨
      touchCosine a b 2 ≤ (fifteenPositiveZeroCosineCap x y : ℝ) := by
  have hxUpperPositive : 0 < x.2 := by exact_mod_cast lt_of_lt_of_le ha haUpper
  have hyUpperPositive : 0 < y.2 := by exact_mod_cast lt_of_lt_of_le hb hbUpper
  by_cases hxUpperLeTwo : x.2 ≤ 2
  · by_cases hyUpperLeTwo : y.2 ≤ 2
    · right
      rw [fifteenPositiveZeroCosineCap_cast_eq_touchCosine x y hzero
        hxUpperPositive hyUpperPositive hxUpperLeTwo hyUpperLeTwo]
      exact touchCosine_mono_radii_of_le_two ha hb haUpper hbUpper
        (by exact_mod_cast hxUpperLeTwo) (by exact_mod_cast hyUpperLeTwo)
    · left
      have hxzero : x.1 = 0 := by
        rcases hzero with hx | hy
        · exact hx
        · have hySmall := hzeroUpperLeTwo.2 hy
          exact False.elim ((not_le_of_gt (lt_of_not_ge hyUpperLeTwo)) hySmall)
      have hcapEq : fifteenPositiveZeroCosineCap x y = 1 := by
        simp [fifteenPositiveZeroCosineCap, hxzero, hyUpperLeTwo]
      simp [hcapEq]
  · left
    have hyzero : y.1 = 0 := by
      rcases hzero with hx | hy
      · have hxSmall := hzeroUpperLeTwo.1 hx
        exact False.elim ((not_le_of_gt (lt_of_not_ge hxUpperLeTwo)) hxSmall)
      · exact hy
    have hxNotZero : x.1 ≠ 0 := by
      intro hxzero
      have hxSmall := hzeroUpperLeTwo.1 hxzero
      exact (not_le_of_gt (lt_of_not_ge hxUpperLeTwo)) hxSmall
    have hcapEq : fifteenPositiveZeroCosineCap x y = 1 := by
      simp [fifteenPositiveZeroCosineCap, hxNotZero, hxUpperLeTwo]
    simp [hcapEq]

theorem fifteenPositiveZeroTick_lower_bounds_touch_angle
    (x y : FifteenInterval) (ticks : Nat) (a b : ℝ)
    (hsum : 2 ≤ x.2 + y.2)
    (hvalid : fifteenTickCertificateValid x y true false ticks = true)
    (hcapBound :
      (1 : ℝ) ≤ (fifteenPositiveZeroCosineCap x y : ℝ) ∨
        touchCosine a b 2 ≤ (fifteenPositiveZeroCosineCap x y : ℝ)) :
    (ticks : ℝ) / 2800 ≤ touchAngle a b 2 := by
  have hnotSum : ¬ x.2 + y.2 < 2 := by linarith
  let cap := fifteenPositiveZeroCosineCap x y
  by_cases hupper : 1 ≤ cap
  · have hticks : ticks = 0 := by
      simpa [fifteenTickCertificateValid, hnotSum, cap, hupper] using hvalid
    subst ticks
    simpa [touchAngle] using (Real.arccos_nonneg (touchCosine a b 2))
  · have hcapActual : touchCosine a b 2 ≤ (cap : ℝ) := by
      rcases hcapBound with htrivial | hbound
      · exact False.elim (hupper (by exact_mod_cast htrivial))
      · simpa [cap] using hbound
    by_cases hlower : cap ≤ -1
    · have hticks : ticks = 8700 := by
        simpa [fifteenTickCertificateValid, hnotSum, cap, hupper, hlower] using hvalid
      subst ticks
      have hcosPi : touchCosine a b 2 ≤ Real.cos Real.pi := by
        rw [Real.cos_pi]
        exact le_trans hcapActual (by exact_mod_cast hlower)
      have hpiLower : Real.pi ≤ touchAngle a b 2 :=
        certified_touch_angle_lower_bound (le_of_lt Real.pi_pos) le_rfl hcosPi
      have htickPi : (8700 : ℝ) / 2800 ≤ Real.pi := le_of_lt (by
        calc
          (8700 : ℝ) / 2800 < (3.14 : ℝ) := by norm_num
          _ < Real.pi := Real.pi_gt_d2)
      exact le_trans htickPi hpiLower
    · have hspec : ticks ≤ 8790 ∧ cap ≤ fifteenCosineLower ticks := by
        simpa [fifteenTickCertificateValid, hnotSum, cap, hupper, hlower] using hvalid
      have hcapTaylor : (cap : ℝ) ≤ (fifteenCosineLower ticks : ℝ) := by
        exact_mod_cast hspec.2
      have hcosTick : (fifteenCosineLower ticks : ℝ) ≤
          Real.cos ((ticks : ℝ) / 2800) :=
        fifteenCosineLower_le_cos ticks hspec.1
      have hangle0 : 0 ≤ (ticks : ℝ) / 2800 := by positivity
      have hanglePi : (ticks : ℝ) / 2800 ≤ Real.pi := by
        have ht : (ticks : ℝ) / 2800 ≤ (8790 : ℝ) / 2800 :=
          div_le_div_of_nonneg_right (by exact_mod_cast hspec.1) (by norm_num)
        have hbound : (8790 : ℝ) / 2800 < Real.pi := by
          calc
            (8790 : ℝ) / 2800 < (3.14 : ℝ) := by norm_num
            _ < Real.pi := Real.pi_gt_d2
        exact le_of_lt (lt_of_le_of_lt ht hbound)
      exact certified_touch_angle_lower_bound hangle0 hanglePi
        (le_trans hcapActual (le_trans hcapTaylor hcosTick))

theorem fifteenPositiveZeroTick_gives_angle_lower_bound
    (x y : FifteenInterval) (ticks : Nat) (angle : ℝ)
    (hsum : 2 ≤ x.2 + y.2)
    (hvalid : fifteenTickCertificateValid x y true false ticks = true)
    (hangle0 : 0 ≤ angle) (hanglePi : angle ≤ Real.pi)
    (hcontact : Real.cos angle ≤
      (fifteenPositiveZeroCosineCap x y : ℝ)) :
    (ticks : ℝ) / 2800 ≤ angle := by
  have hnotSum : ¬ x.2 + y.2 < 2 := by linarith
  let cap := fifteenPositiveZeroCosineCap x y
  by_cases hupper : 1 ≤ cap
  · have hticks : ticks = 0 := by
      simpa [fifteenTickCertificateValid, hnotSum, cap, hupper] using hvalid
    subst ticks
    simpa using hangle0
  · by_cases hlower : cap ≤ -1
    · have hticks : ticks = 8700 := by
        simpa [fifteenTickCertificateValid, hnotSum, cap, hupper, hlower] using hvalid
      subst ticks
      have hcapLow : (cap : ℝ) ≤ -1 := by exact_mod_cast hlower
      have hcontact' : Real.cos angle ≤ -1 := le_trans hcontact hcapLow
      have hcosPi : Real.cos angle ≤ Real.cos Real.pi := by
        rw [Real.cos_pi]
        exact hcontact'
      have hpiLe : Real.pi ≤ angle :=
        (Real.strictAntiOn_cos.le_iff_ge ⟨hangle0, hanglePi⟩
          ⟨Real.pi_nonneg, le_rfl⟩).1 hcosPi
      have htickPi : (8700 : ℝ) / 2800 ≤ Real.pi := le_of_lt (by
        calc
          (8700 : ℝ) / 2800 < (3.14 : ℝ) := by norm_num
          _ < Real.pi := Real.pi_gt_d2)
      exact le_trans htickPi hpiLe
    · have hspec : ticks ≤ 8790 ∧ cap ≤ fifteenCosineLower ticks := by
        simpa [fifteenTickCertificateValid, hnotSum, cap, hupper, hlower] using hvalid
      have hcap : (cap : ℝ) ≤ (fifteenCosineLower ticks : ℝ) := by
        exact_mod_cast hspec.2
      exact fifteenAngleTick_lower_of_cosine_cap ticks hspec.1 angle
        (cap : ℝ) hangle0 hanglePi hcontact hcap

theorem fifteenBoxCosineCap_corners (x y : FifteenInterval) :
    fifteenCosineRuleCap x.1 y.1 ≤ fifteenBoxCosineCap x y ∧
    fifteenCosineRuleCap x.1 y.2 ≤ fifteenBoxCosineCap x y ∧
    fifteenCosineRuleCap x.2 y.1 ≤ fifteenBoxCosineCap x y ∧
    fifteenCosineRuleCap x.2 y.2 ≤ fifteenBoxCosineCap x y := by
  unfold fifteenBoxCosineCap fifteenMax4
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact le_trans (le_max_left _ _) (le_max_left _ _)
  · exact le_trans (le_max_right _ _) (le_max_left _ _)
  · exact le_trans (le_max_left _ _) (le_max_right _ _)
  · exact le_trans (le_max_right _ _) (le_max_right _ _)

theorem fifteenCosineRule_scaled_bound
    {a b cap : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hcap : (a ^ 2 + b ^ 2 - 4) / (2 * a * b) ≤ cap) :
    a ^ 2 + b ^ 2 - 4 ≤ cap * (2 * a * b) := by
  have hden : 0 < 2 * a * b := by positivity
  exact (div_le_iff₀ hden).mp hcap

theorem fifteenBoxCosineCap_numerator_bounds (x y : FifteenInterval)
    (hxOrder : x.1 ≤ x.2) (hyOrder : y.1 ≤ y.2)
    (hx0 : 0 < (x.1 : ℝ)) (hy0 : 0 < (y.1 : ℝ)) :
    (x.1 : ℝ) ^ 2 + (y.1 : ℝ) ^ 2 - 4 ≤
        (fifteenBoxCosineCap x y : ℝ) * (2 * (x.1 : ℝ) * (y.1 : ℝ)) ∧
    (x.1 : ℝ) ^ 2 + (y.2 : ℝ) ^ 2 - 4 ≤
        (fifteenBoxCosineCap x y : ℝ) * (2 * (x.1 : ℝ) * (y.2 : ℝ)) ∧
    (x.2 : ℝ) ^ 2 + (y.1 : ℝ) ^ 2 - 4 ≤
        (fifteenBoxCosineCap x y : ℝ) * (2 * (x.2 : ℝ) * (y.1 : ℝ)) ∧
    (x.2 : ℝ) ^ 2 + (y.2 : ℝ) ^ 2 - 4 ≤
        (fifteenBoxCosineCap x y : ℝ) * (2 * (x.2 : ℝ) * (y.2 : ℝ)) := by
  have hc := fifteenBoxCosineCap_corners x y
  have hxa : 0 < (x.2 : ℝ) := lt_of_lt_of_le hx0 (by exact_mod_cast hxOrder)
  have hya : 0 < (y.2 : ℝ) := lt_of_lt_of_le hy0 (by exact_mod_cast hyOrder)
  have h00 :
      ((x.1 : ℝ) ^ 2 + (y.1 : ℝ) ^ 2 - 4) /
        (2 * (x.1 : ℝ) * (y.1 : ℝ)) ≤ (fifteenBoxCosineCap x y : ℝ) := by
    exact_mod_cast hc.1
  have h01 :
      ((x.1 : ℝ) ^ 2 + (y.2 : ℝ) ^ 2 - 4) /
        (2 * (x.1 : ℝ) * (y.2 : ℝ)) ≤ (fifteenBoxCosineCap x y : ℝ) := by
    exact_mod_cast hc.2.1
  have h10 :
      ((x.2 : ℝ) ^ 2 + (y.1 : ℝ) ^ 2 - 4) /
        (2 * (x.2 : ℝ) * (y.1 : ℝ)) ≤ (fifteenBoxCosineCap x y : ℝ) := by
    exact_mod_cast hc.2.2.1
  have h11 :
      ((x.2 : ℝ) ^ 2 + (y.2 : ℝ) ^ 2 - 4) /
        (2 * (x.2 : ℝ) * (y.2 : ℝ)) ≤ (fifteenBoxCosineCap x y : ℝ) := by
    exact_mod_cast hc.2.2.2
  exact ⟨fifteenCosineRule_scaled_bound hx0 hy0 h00,
    fifteenCosineRule_scaled_bound hx0 hya h01,
    fifteenCosineRule_scaled_bound hxa hy0 h10,
    fifteenCosineRule_scaled_bound hxa hya h11⟩

theorem fifteen_box_corners_certify_touch_angle
    {La Ua Lb Ub a b d ell cap : ℝ}
    (haL : La ≤ a) (haU : a ≤ Ua)
    (hbL : Lb ≤ b) (hbU : b ≤ Ub)
    (hLa : 0 < La) (hLb : 0 < Lb)
    (h00 : La ^ 2 + Lb ^ 2 - d ^ 2 ≤ cap * (2 * La * Lb))
    (h01 : La ^ 2 + Ub ^ 2 - d ^ 2 ≤ cap * (2 * La * Ub))
    (h10 : Ua ^ 2 + Lb ^ 2 - d ^ 2 ≤ cap * (2 * Ua * Lb))
    (h11 : Ua ^ 2 + Ub ^ 2 - d ^ 2 ≤ cap * (2 * Ua * Ub))
    (hell0 : 0 ≤ ell) (hellpi : ell ≤ Real.pi)
    (hcap : cap ≤ Real.cos ell) :
    ell ≤ touchAngle a b d := by
  apply certified_touch_angle_lower_bound hell0 hellpi
  exact le_trans (corner_touch_cosine_bound haL haU hbL hbU hLa hLb
    h00 h01 h10 h11) hcap

theorem fifteenRegularTick_lower_bounds_touch_angle
    (x y : FifteenInterval) (ticks : Nat) (a b : ℝ)
    (hsum : 2 ≤ x.2 + y.2)
    (hcapUpper : fifteenBoxCosineCap x y < 1)
    (hcapLower : -1 < fifteenBoxCosineCap x y)
    (hvalid : fifteenTickCertificateValid x y false false ticks = true)
    (hxOrder : x.1 ≤ x.2) (hyOrder : y.1 ≤ y.2)
    (hx0 : 0 < (x.1 : ℝ)) (hy0 : 0 < (y.1 : ℝ))
    (haL : (x.1 : ℝ) ≤ a) (haU : a ≤ (x.2 : ℝ))
    (hbL : (y.1 : ℝ) ≤ b) (hbU : b ≤ (y.2 : ℝ)) :
    (ticks : ℝ) / 2800 ≤ touchAngle a b 2 := by
  have hspec := fifteenTickCertificateValid_regular_spec x y ticks
    hsum hcapUpper hcapLower hvalid
  have hangle0 : 0 ≤ (ticks : ℝ) / 2800 := by positivity
  have hanglePi : (ticks : ℝ) / 2800 ≤ Real.pi := by
    have ht : (ticks : ℝ) / 2800 ≤ (8790 : ℝ) / 2800 :=
      div_le_div_of_nonneg_right (by exact_mod_cast hspec.1) (by norm_num)
    have hpi : (8790 : ℝ) / 2800 < Real.pi := by
      calc
        (8790 : ℝ) / 2800 < (3.14 : ℝ) := by norm_num
        _ < Real.pi := Real.pi_gt_d2
    exact le_of_lt (lt_of_le_of_lt ht hpi)
  have hcosTick : (fifteenCosineLower ticks : ℝ) ≤
      Real.cos ((ticks : ℝ) / 2800) := fifteenCosineLower_le_cos ticks hspec.1
  have hcapCos : (fifteenBoxCosineCap x y : ℝ) ≤
      Real.cos ((ticks : ℝ) / 2800) := le_trans hspec.2 hcosTick
  have hcorners := fifteenBoxCosineCap_numerator_bounds x y
    hxOrder hyOrder hx0 hy0
  have hcornerData :
      (x.1 : ℝ) ^ 2 + (y.1 : ℝ) ^ 2 - (2 : ℝ) ^ 2 ≤
          (fifteenBoxCosineCap x y : ℝ) * (2 * (x.1 : ℝ) * (y.1 : ℝ)) ∧
      (x.1 : ℝ) ^ 2 + (y.2 : ℝ) ^ 2 - (2 : ℝ) ^ 2 ≤
          (fifteenBoxCosineCap x y : ℝ) * (2 * (x.1 : ℝ) * (y.2 : ℝ)) ∧
      (x.2 : ℝ) ^ 2 + (y.1 : ℝ) ^ 2 - (2 : ℝ) ^ 2 ≤
          (fifteenBoxCosineCap x y : ℝ) * (2 * (x.2 : ℝ) * (y.1 : ℝ)) ∧
      (x.2 : ℝ) ^ 2 + (y.2 : ℝ) ^ 2 - (2 : ℝ) ^ 2 ≤
          (fifteenBoxCosineCap x y : ℝ) * (2 * (x.2 : ℝ) * (y.2 : ℝ)) := by
    have htwo : (2 : ℝ) ^ 2 = 4 := by norm_num
    simpa [htwo] using hcorners
  have htouch : (ticks : ℝ) / 2800 ≤ touchAngle a b 2 :=
    fifteen_box_corners_certify_touch_angle haL haU hbL hbU hx0 hy0
      hcornerData.1 hcornerData.2.1 hcornerData.2.2.1 hcornerData.2.2.2
      hangle0 hanglePi hcapCos
  exact htouch

theorem fifteenRegularTick_lower_bounds_center_angle
    (x y : FifteenInterval) (ticks : Nat) (a b : ℝ) (p q : Point)
    (hsum : 2 ≤ x.2 + y.2)
    (hcapUpper : fifteenBoxCosineCap x y < 1)
    (hcapLower : -1 < fifteenBoxCosineCap x y)
    (hvalid : fifteenTickCertificateValid x y false false ticks = true)
    (hxOrder : x.1 ≤ x.2) (hyOrder : y.1 ≤ y.2)
    (hx0 : 0 < (x.1 : ℝ)) (hy0 : 0 < (y.1 : ℝ))
    (haL : (x.1 : ℝ) ≤ a) (haU : a ≤ (x.2 : ℝ))
    (hbL : (y.1 : ℝ) ≤ b) (hbU : b ≤ (y.2 : ℝ))
    (hpa : pointNorm p = a) (hqb : pointNorm q = b)
    (hsep : 4 ≤ pointNorm (p.1 - q.1, p.2 - q.2) ^ 2) :
    (ticks : ℝ) / 2800 ≤ centerAngle p q := by
  have htouch := fifteenRegularTick_lower_bounds_touch_angle x y ticks a b
    hsum hcapUpper hcapLower hvalid hxOrder hyOrder hx0 hy0 haL haU hbL hbU
  have ha : 0 < a := lt_of_lt_of_le hx0 haL
  have hb : 0 < b := lt_of_lt_of_le hy0 hbL
  have hsep' : (2 : ℝ) ^ 2 ≤ pointNorm (p.1 - q.1, p.2 - q.2) ^ 2 := by
    have htwo : (2 : ℝ) ^ 2 = 4 := by norm_num
    simpa [htwo] using hsep
  have hcenter := touch_angle_le_center_angle ha hb hpa hqb hsep'
  exact le_trans htouch hcenter

theorem fifteen_centerAngle_symm (p q : Point) :
    centerAngle p q = centerAngle q p := by
  unfold centerAngle centerCosine
  congr 1
  ring

theorem fifteen_touchAngle_symm (a b d : ℝ) :
    touchAngle a b d = touchAngle b a d := by
  unfold touchAngle touchCosine
  congr 1
  ring

theorem fifteen_centerAngle_polar_reverse_sub
    {a b alpha beta : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hlo : 0 ≤ 2 * Real.pi - (alpha - beta))
    (hhi : 2 * Real.pi - (alpha - beta) ≤ Real.pi) :
    centerAngle (polarPoint a alpha) (polarPoint b beta) =
      2 * Real.pi - (alpha - beta) := by
  have hcos : Real.cos (alpha - beta) =
      Real.cos (2 * Real.pi - (alpha - beta)) := by
    conv_rhs => rw [Real.cos_sub]
    simp
  unfold centerAngle
  rw [centerCosine_polar ha hb, hcos]
  exact Real.arccos_cos hlo hhi

theorem fifteen_polar_touch_angle_ordered_gap
    {a b d ell alpha beta : ℝ}
    (ha : 0 < a) (hb : 0 < b)
    (hellpi : ell ≤ Real.pi)
    (hdelta0 : 0 ≤ beta - alpha)
    (hdelta2 : beta - alpha ≤ 2 * Real.pi)
    (hsep : d ^ 2 ≤ pointNorm
      ((polarPoint a alpha).1 - (polarPoint b beta).1,
       (polarPoint a alpha).2 - (polarPoint b beta).2) ^ 2)
    (hell : ell ≤ touchAngle a b d) :
    ell ≤ beta - alpha ∧ beta - alpha ≤ 2 * Real.pi - ell := by
  have hcenterLower :
      ell ≤ centerAngle (polarPoint a alpha) (polarPoint b beta) := by
    exact le_trans hell (touch_angle_le_center_angle ha hb
      (pointNorm_polarPoint (le_of_lt ha))
      (pointNorm_polarPoint (le_of_lt hb)) hsep)
  by_cases hsmall : beta - alpha ≤ Real.pi
  · have hcenter :
        centerAngle (polarPoint a alpha) (polarPoint b beta) = beta - alpha := by
      calc
        centerAngle (polarPoint a alpha) (polarPoint b beta) =
            centerAngle (polarPoint b beta) (polarPoint a alpha) :=
              fifteen_centerAngle_symm _ _
        _ = beta - alpha := centerAngle_polar_sub hb ha hdelta0 hsmall
    constructor
    · rw [hcenter] at hcenterLower
      exact hcenterLower
    · nlinarith [Real.pi_pos]
  · have hlarge : Real.pi < beta - alpha := lt_of_not_ge hsmall
    have hwrap0 : 0 ≤ 2 * Real.pi - (beta - alpha) := by nlinarith
    have hwrapPi : 2 * Real.pi - (beta - alpha) ≤ Real.pi := by nlinarith
    have hcenter :
        centerAngle (polarPoint a alpha) (polarPoint b beta) =
          2 * Real.pi - (beta - alpha) := by
      calc
        centerAngle (polarPoint a alpha) (polarPoint b beta) =
            centerAngle (polarPoint b beta) (polarPoint a alpha) :=
              fifteen_centerAngle_symm _ _
        _ = 2 * Real.pi - (beta - alpha) :=
          fifteen_centerAngle_polar_reverse_sub hb ha hwrap0 hwrapPi
    constructor
    · exact le_trans hellpi (le_of_lt hlarge)
    · rw [hcenter] at hcenterLower
      linarith

theorem fifteen_polar_edge_respects_angular_bound
    (theta : Fin 15 → ℝ) (tauUpper : ℝ)
    (e : FifteenAngularEdge) (a b d : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hellpi : e.lower ≤ Real.pi)
    (hneq : e.src ≠ e.dst)
    (hsorted : ∀ i j : Fin 15, i.1 < j.1 → theta i ≤ theta j)
    (hthetaLo : ∀ i : Fin 15, 0 ≤ theta i)
    (hthetaHi : ∀ i : Fin 15, theta i ≤ 2 * Real.pi)
    (hsep : d ^ 2 ≤ pointNorm
      ((polarPoint a (theta e.src)).1 - (polarPoint b (theta e.dst)).1,
       (polarPoint a (theta e.src)).2 - (polarPoint b (theta e.dst)).2) ^ 2)
    (hell : e.lower ≤ touchAngle a b d)
    (htau : 2 * Real.pi ≤ tauUpper) :
    theta e.dst - theta e.src ≤ fifteenAngularEdgeUpper tauUpper e := by
  by_cases hforward : e.src.1 < e.dst.1
  · have hdelta0 : 0 ≤ theta e.dst - theta e.src :=
      sub_nonneg.mpr (hsorted e.src e.dst hforward)
    have hdelta2 : theta e.dst - theta e.src ≤ 2 * Real.pi := by
      have hhi := hthetaHi e.dst
      have hlo := hthetaLo e.src
      nlinarith
    have hgap := fifteen_polar_touch_angle_ordered_gap ha hb hellpi
      hdelta0 hdelta2 hsep hell
    simp [fifteenAngularEdgeUpper, hforward]
    linarith [hgap.2, htau]
  · have hback : e.dst.1 < e.src.1 := by
      have hne : e.src.1 ≠ e.dst.1 := fun heq => hneq (Fin.ext heq)
      omega
    have hdelta0 : 0 ≤ theta e.src - theta e.dst :=
      sub_nonneg.mpr (hsorted e.dst e.src hback)
    have hdelta2 : theta e.src - theta e.dst ≤ 2 * Real.pi := by
      have hhi := hthetaHi e.src
      have hlo := hthetaLo e.dst
      nlinarith
    have hdistSymm :
        pointNorm
          ((polarPoint b (theta e.dst)).1 - (polarPoint a (theta e.src)).1,
           (polarPoint b (theta e.dst)).2 - (polarPoint a (theta e.src)).2) ^ 2 =
        pointNorm
          ((polarPoint a (theta e.src)).1 - (polarPoint b (theta e.dst)).1,
           (polarPoint a (theta e.src)).2 - (polarPoint b (theta e.dst)).2) ^ 2 := by
      rw [pointNorm_sq, pointNorm_sq]
      ring
    have hsep' : d ^ 2 ≤ pointNorm
        ((polarPoint b (theta e.dst)).1 - (polarPoint a (theta e.src)).1,
         (polarPoint b (theta e.dst)).2 - (polarPoint a (theta e.src)).2) ^ 2 := by
      rw [hdistSymm]
      exact hsep
    have htouchSymm : e.lower ≤ touchAngle b a d := by
      rw [← fifteen_touchAngle_symm a b d]
      exact hell
    have hgap := fifteen_polar_touch_angle_ordered_gap hb ha hellpi
      hdelta0 hdelta2 hsep' htouchSymm
    simp [fifteenAngularEdgeUpper, hforward]
    linarith

theorem fifteenRegularTick_gives_polar_edge_bound
    (x y : FifteenInterval) (ticks : Nat) (e : FifteenAngularEdge)
    (theta : Fin 15 → ℝ) (a b : ℝ) (tauUpper : ℝ)
    (hsum : 2 ≤ x.2 + y.2)
    (hcapUpper : fifteenBoxCosineCap x y < 1)
    (hcapLower : -1 < fifteenBoxCosineCap x y)
    (hvalid : fifteenTickCertificateValid x y false false ticks = true)
    (hxOrder : x.1 ≤ x.2) (hyOrder : y.1 ≤ y.2)
    (hx0 : 0 < (x.1 : ℝ)) (hy0 : 0 < (y.1 : ℝ))
    (haL : (x.1 : ℝ) ≤ a) (haU : a ≤ (x.2 : ℝ))
    (hbL : (y.1 : ℝ) ≤ b) (hbU : b ≤ (y.2 : ℝ))
    (hlower : e.lower = (ticks : ℝ) / 2800)
    (hneq : e.src ≠ e.dst)
    (hsorted : ∀ i j : Fin 15, i.1 < j.1 → theta i ≤ theta j)
    (hthetaLo : ∀ i : Fin 15, 0 ≤ theta i)
    (hthetaHi : ∀ i : Fin 15, theta i ≤ 2 * Real.pi)
    (hsep : 4 ≤ pointNorm
      ((polarPoint a (theta e.src)).1 - (polarPoint b (theta e.dst)).1,
       (polarPoint a (theta e.src)).2 - (polarPoint b (theta e.dst)).2) ^ 2)
    (htau : 2 * Real.pi ≤ tauUpper) :
    theta e.dst - theta e.src ≤ fifteenAngularEdgeUpper tauUpper e := by
  have hell := fifteenRegularTick_lower_bounds_touch_angle x y ticks a b
    hsum hcapUpper hcapLower hvalid hxOrder hyOrder hx0 hy0 haL haU hbL hbU
  have hell' : e.lower ≤ touchAngle a b 2 := by
    rw [hlower]
    exact hell
  have hpi : e.lower ≤ Real.pi := by
    rw [hlower]
    have htick := (fifteenTickCertificateValid_regular_spec x y ticks
      hsum hcapUpper hcapLower hvalid).1
    have ht : (ticks : ℝ) / 2800 ≤ (8790 : ℝ) / 2800 :=
      div_le_div_of_nonneg_right (by exact_mod_cast htick) (by norm_num)
    have hbound : (8790 : ℝ) / 2800 < Real.pi := by
      calc
        (8790 : ℝ) / 2800 < (3.14 : ℝ) := by norm_num
        _ < Real.pi := Real.pi_gt_d2
    exact le_trans ht (le_of_lt hbound)
  have ha : 0 < a := lt_of_lt_of_le hx0 haL
  have hb : 0 < b := lt_of_lt_of_le hy0 hbL
  have hsep' : (2 : ℝ) ^ 2 ≤ pointNorm
      ((polarPoint a (theta e.src)).1 - (polarPoint b (theta e.dst)).1,
       (polarPoint a (theta e.src)).2 - (polarPoint b (theta e.dst)).2) ^ 2 := by
    norm_num at hsep ⊢
    exact hsep
  exact fifteen_polar_edge_respects_angular_bound theta tauUpper e a b 2
    ha hb hpi hneq hsorted hthetaLo hthetaHi hsep' hell' htau

theorem fifteenPositiveZeroTick_lower_bounds_touch_angle_of_box
    (x y : FifteenInterval) (ticks : Nat) (a b : ℝ)
    (hsum : 2 ≤ x.2 + y.2)
    (hvalid : fifteenTickCertificateValid x y true false ticks = true)
    (hzero : x.1 = 0 ∨ y.1 = 0)
    (hzeroUpperLeTwo : (x.1 = 0 → x.2 ≤ 2) ∧ (y.1 = 0 → y.2 ≤ 2))
    (ha : 0 < a) (hb : 0 < b)
    (haUpper : a ≤ (x.2 : ℝ)) (hbUpper : b ≤ (y.2 : ℝ)) :
    (ticks : ℝ) / 2800 ≤ touchAngle a b 2 := by
  have hcap := fifteenPositiveZeroCosineCap_bounds_or_one x y a b
    hzero hzeroUpperLeTwo ha hb haUpper hbUpper
  exact fifteenPositiveZeroTick_lower_bounds_touch_angle x y ticks a b
    hsum hvalid hcap

theorem fifteenPositiveZeroTick_gives_polar_edge_bound
    (x y : FifteenInterval) (ticks : Nat) (e : FifteenAngularEdge)
    (theta : Fin 15 → ℝ) (a b : ℝ) (tauUpper : ℝ)
    (hsum : 2 ≤ x.2 + y.2)
    (hvalid : fifteenTickCertificateValid x y true false ticks = true)
    (hzero : x.1 = 0 ∨ y.1 = 0)
    (hzeroUpperLeTwo : (x.1 = 0 → x.2 ≤ 2) ∧ (y.1 = 0 → y.2 ≤ 2))
    (ha : 0 < a) (hb : 0 < b)
    (haUpper : a ≤ (x.2 : ℝ)) (hbUpper : b ≤ (y.2 : ℝ))
    (hlower : e.lower = (ticks : ℝ) / 2800)
    (hneq : e.src ≠ e.dst)
    (hsorted : ∀ i j : Fin 15, i.1 < j.1 → theta i ≤ theta j)
    (hthetaLo : ∀ i : Fin 15, 0 ≤ theta i)
    (hthetaHi : ∀ i : Fin 15, theta i ≤ 2 * Real.pi)
    (hsep : 4 ≤ pointNorm
      ((polarPoint a (theta e.src)).1 - (polarPoint b (theta e.dst)).1,
       (polarPoint a (theta e.src)).2 - (polarPoint b (theta e.dst)).2) ^ 2)
    (htau : 2 * Real.pi ≤ tauUpper) :
    theta e.dst - theta e.src ≤ fifteenAngularEdgeUpper tauUpper e := by
  have hell := fifteenPositiveZeroTick_lower_bounds_touch_angle_of_box x y
    ticks a b hsum hvalid hzero hzeroUpperLeTwo ha hb haUpper hbUpper
  have hell' : e.lower ≤ touchAngle a b 2 := by
    rw [hlower]
    exact hell
  have hpi : e.lower ≤ Real.pi := le_trans hell' (Real.arccos_le_pi _)
  have hsep' : (2 : ℝ) ^ 2 ≤ pointNorm
      ((polarPoint a (theta e.src)).1 - (polarPoint b (theta e.dst)).1,
       (polarPoint a (theta e.src)).2 - (polarPoint b (theta e.dst)).2) ^ 2 := by
    norm_num at hsep ⊢
    exact hsep
  exact fifteen_polar_edge_respects_angular_bound theta tauUpper e a b 2
    ha hb hpi hneq hsorted hthetaLo hthetaHi hsep' hell' htau

theorem fifteenZeroTick_gives_polar_edge_bound
    (theta : Fin 15 → ℝ) (tauUpper : ℝ) (e : FifteenAngularEdge)
    (hlower : e.lower = 0) (hneq : e.src ≠ e.dst)
    (hsorted : ∀ i j : Fin 15, i.1 < j.1 → theta i ≤ theta j)
    (hthetaLo : ∀ i : Fin 15, 0 ≤ theta i)
    (hthetaHi : ∀ i : Fin 15, theta i ≤ 2 * Real.pi)
    (htau : 2 * Real.pi ≤ tauUpper) :
    theta e.dst - theta e.src ≤ fifteenAngularEdgeUpper tauUpper e := by
  by_cases hforward : e.src.1 < e.dst.1
  · have hdelta2 : theta e.dst - theta e.src ≤ 2 * Real.pi := by
      have hhi := hthetaHi e.dst
      have hlo := hthetaLo e.src
      nlinarith
    simp [fifteenAngularEdgeUpper, hforward, hlower]
    linarith
  · have hback : e.dst.1 < e.src.1 := by
      have hne : e.src.1 ≠ e.dst.1 := fun heq => hneq (Fin.ext heq)
      omega
    have hordered : theta e.dst ≤ theta e.src := hsorted e.dst e.src hback
    simp [fifteenAngularEdgeUpper, hforward, hlower]
    linarith

end CirclePacking
