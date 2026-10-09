import CirclePacking.FifteenCertificate
import CirclePacking.CosineTaylor
import CirclePacking.CornerBound
import CirclePacking.GeometricAngle
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
  have ha : 0 < a := lt_of_lt_of_le hx0 haL
  have hb : 0 < b := lt_of_lt_of_le hy0 hbL
  have hsep' : (2 : ℝ) ^ 2 ≤ pointNorm (p.1 - q.1, p.2 - q.2) ^ 2 := by
    have htwo : (2 : ℝ) ^ 2 = 4 := by norm_num
    simpa [htwo] using hsep
  have hcenter := touch_angle_le_center_angle ha hb hpa hqb hsep'
  exact le_trans htouch hcenter

end CirclePacking
