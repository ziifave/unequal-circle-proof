import CirclePacking.CosineCertificate
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

namespace CirclePacking

open scoped BigOperators

/-! A rigorous Taylor remainder bound for the cosine function.

The polynomial itself is still represented by Mathlib's Taylor evaluator.  A
separate normalization lemma can later rewrite the order-two polynomial at
the origin to `1 - x^2 / 2`; the analytic remainder estimate is already
kernel-checked here.
-/

theorem cosine_taylor_two_remainder
    {a b x : ℝ}
    (hab : a < b)
    (hx : x ∈ Set.Icc a b) :
    ‖Real.cos x -
        taylorWithinEval Real.cos 2 (Set.Icc a b) a x‖
      ≤ (x - a) ^ 3 / ((Nat.factorial 2 : ℕ) : ℝ) := by
  have h := taylor_mean_remainder_bound (n := 2) (C := (1 : ℝ)) hab.le
      Real.contDiff_cos.contDiffOn hx (by
        intro y hy
        rw [show 2 + 1 = 3 by norm_num,
          Real.iteratedDerivWithin_cos_Icc 3 hab hy]
        simpa [Real.norm_eq_abs] using Real.abs_iteratedDeriv_cos_le_one 3 y)
  simpa using h

theorem cosine_taylor_six_remainder
    {a b x : ℝ}
    (hab : a < b)
    (hx : x ∈ Set.Icc a b) :
    ‖Real.cos x -
        taylorWithinEval Real.cos 6 (Set.Icc a b) a x‖
      ≤ (x - a) ^ 7 / ((Nat.factorial 6 : ℕ) : ℝ) := by
  have h := taylor_mean_remainder_bound (n := 6) (C := (1 : ℝ)) hab.le
      Real.contDiff_cos.contDiffOn hx (by
        intro y hy
        rw [show 6 + 1 = 7 by norm_num,
          Real.iteratedDerivWithin_cos_Icc 7 hab hy]
        simpa [Real.norm_eq_abs] using Real.abs_iteratedDeriv_cos_le_one 7 y)
  simpa using h

theorem lower_bound_of_taylor_error
    {c t e z : ℝ}
    (herror : ‖z - t‖ ≤ e)
    (hcertificate : c + e ≤ t) :
    c ≤ z := by
  have habs : |z - t| ≤ e := by
    simpa [Real.norm_eq_abs] using herror
  have hleft : -e ≤ z - t := (abs_le.mp habs).1
  linarith

theorem cosine_lower_of_taylor_certificate
    {a b x c : ℝ}
    (hab : a < b)
    (hx : x ∈ Set.Icc a b)
    (hcertificate :
      c + (x - a) ^ 3 / ((Nat.factorial 2 : ℕ) : ℝ) ≤
        taylorWithinEval Real.cos 2 (Set.Icc a b) a x) :
    c ≤ Real.cos x := by
  apply lower_bound_of_taylor_error
    (cosine_taylor_two_remainder hab hx)
  exact hcertificate

theorem cosine_taylor_two_at_zero
    {b x : ℝ}
    (hb : 0 < b) :
    taylorWithinEval Real.cos 2 (Set.Icc 0 b) 0 x = 1 - x ^ 2 / 2 := by
  rw [taylor_within_apply]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial_zero,
    Nat.factorial_one, Nat.cast_one, inv_one]
  · have hzero : (0 : ℝ) ∈ Set.Icc 0 b := ⟨le_rfl, hb.le⟩
    rw [Real.iteratedDerivWithin_cos_Icc 0 hb hzero,
      Real.iteratedDerivWithin_cos_Icc 1 hb hzero,
      Real.iteratedDerivWithin_cos_Icc 2 hb hzero]
    norm_num [Real.iteratedDeriv_even_cos]
    ring

theorem cosine_taylor_six_at_zero
    {b x : ℝ}
    (hb : 0 < b) :
    taylorWithinEval Real.cos 6 (Set.Icc 0 b) 0 x =
      1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720 := by
  rw [taylor_within_apply]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial_zero,
    Nat.factorial_one, Nat.cast_one, inv_one]
  have hzero : (0 : ℝ) ∈ Set.Icc 0 b := ⟨le_rfl, hb.le⟩
  rw [Real.iteratedDerivWithin_cos_Icc 0 hb hzero,
    Real.iteratedDerivWithin_cos_Icc 1 hb hzero,
    Real.iteratedDerivWithin_cos_Icc 2 hb hzero,
    Real.iteratedDerivWithin_cos_Icc 3 hb hzero,
    Real.iteratedDerivWithin_cos_Icc 4 hb hzero,
    Real.iteratedDerivWithin_cos_Icc 5 hb hzero,
    Real.iteratedDerivWithin_cos_Icc 6 hb hzero]
  norm_num [Real.iteratedDeriv_even_cos, Real.iteratedDeriv_odd_cos]
  ring

theorem cosine_lower_of_quadratic_bound
    {b x c : ℝ}
    (hb : 0 < b)
    (hx : x ∈ Set.Icc 0 b)
    (hpoly : c + x ^ 3 / 2 ≤ 1 - x ^ 2 / 2) :
    c ≤ Real.cos x := by
  apply cosine_lower_of_taylor_certificate hb hx
  rw [cosine_taylor_two_at_zero hb]
  simpa using hpoly

theorem certified_cosine_of_quadratic_bound
    {b x c : ℝ}
    (hb : 0 < b)
    (hx : x ∈ Set.Icc 0 b)
    (hpi : x ≤ Real.pi)
    (hpoly : c + x ^ 3 / 2 ≤ 1 - x ^ 2 / 2) :
    CertifiedCosineLowerBound c x := by
  refine ⟨hx.1, hpi, cosine_lower_of_quadratic_bound hb hx hpoly⟩

theorem cosine_nonnegative_at_one_tenth :
    0 ≤ Real.cos (1 / 10 : ℝ) := by
  apply cosine_lower_of_taylor_certificate (a := 0) (b := 1) (x := 1 / 10) (c := 0)
    (by norm_num) (by norm_num)
  rw [cosine_taylor_two_at_zero (b := 1) (x := 1 / 10) (by norm_num)]
  norm_num

end CirclePacking
