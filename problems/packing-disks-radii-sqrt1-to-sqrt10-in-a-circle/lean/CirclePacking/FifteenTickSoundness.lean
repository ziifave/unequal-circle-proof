import CirclePacking.FifteenCertificate
import CirclePacking.CosineTaylor
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

end CirclePacking
