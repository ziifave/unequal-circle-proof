import CirclePacking.CosineCertificate
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

set_option maxRecDepth 100000

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

/-! The order-48 polynomial is used by the finite 7.9 certificate replay.
The remainder bound is intentionally stated in the same form as the lower
order lemmas, so the numerical certificate only has to discharge rational
polynomial inequalities. -/

theorem cosine_taylor_forty_eight_remainder
    {a b x : ℝ}
    (hab : a < b)
    (hx : x ∈ Set.Icc a b) :
    ‖Real.cos x -
        taylorWithinEval Real.cos 48 (Set.Icc a b) a x‖
      ≤ (x - a) ^ 49 / ((Nat.factorial 48 : ℕ) : ℝ) := by
  have h := taylor_mean_remainder_bound (n := 48) (C := (1 : ℝ)) hab.le
      Real.contDiff_cos.contDiffOn hx (by
        intro y hy
        rw [show 48 + 1 = 49 by norm_num,
          Real.iteratedDerivWithin_cos_Icc 49 hab hy]
        simpa [Real.norm_eq_abs] using Real.abs_iteratedDeriv_cos_le_one 49 y)
  simpa using h

theorem cosine_taylor_forty_eight_at_zero
    {b x : ℝ} (hb : 0 < b) :
    taylorWithinEval Real.cos 48 (Set.Icc 0 b) 0 x =
      Finset.sum (Finset.range 25) (fun k =>
        (-1 : ℝ)^k * x ^ (2 * k) /
          ((Nat.factorial (2 * k) : ℕ) : ℝ)) := by
  rw [taylor_within_apply]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial_zero,
    Nat.factorial_one, Nat.cast_one, inv_one]
  have hzero : (0 : ℝ) ∈ Set.Icc 0 b := ⟨le_rfl, hb.le⟩
  -- The finite Taylor sum is normalized by the parity formula for the
  -- iterated derivatives of cosine.  `simp` expands the 49 terms; `ring`
  -- then puts the result in the displayed alternating-sum form.
  simp_rw [Real.iteratedDerivWithin_cos_Icc 0 hb hzero,
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
    Real.iteratedDerivWithin_cos_Icc 18 hb hzero,
    Real.iteratedDerivWithin_cos_Icc 19 hb hzero,
    Real.iteratedDerivWithin_cos_Icc 20 hb hzero,
    Real.iteratedDerivWithin_cos_Icc 21 hb hzero,
    Real.iteratedDerivWithin_cos_Icc 22 hb hzero,
    Real.iteratedDerivWithin_cos_Icc 23 hb hzero,
    Real.iteratedDerivWithin_cos_Icc 24 hb hzero,
    Real.iteratedDerivWithin_cos_Icc 25 hb hzero,
    Real.iteratedDerivWithin_cos_Icc 26 hb hzero,
    Real.iteratedDerivWithin_cos_Icc 27 hb hzero,
    Real.iteratedDerivWithin_cos_Icc 28 hb hzero,
    Real.iteratedDerivWithin_cos_Icc 29 hb hzero,
    Real.iteratedDerivWithin_cos_Icc 30 hb hzero,
    Real.iteratedDerivWithin_cos_Icc 31 hb hzero,
    Real.iteratedDerivWithin_cos_Icc 32 hb hzero,
    Real.iteratedDerivWithin_cos_Icc 33 hb hzero,
    Real.iteratedDerivWithin_cos_Icc 34 hb hzero,
    Real.iteratedDerivWithin_cos_Icc 35 hb hzero,
    Real.iteratedDerivWithin_cos_Icc 36 hb hzero,
    Real.iteratedDerivWithin_cos_Icc 37 hb hzero,
    Real.iteratedDerivWithin_cos_Icc 38 hb hzero,
    Real.iteratedDerivWithin_cos_Icc 39 hb hzero,
    Real.iteratedDerivWithin_cos_Icc 40 hb hzero,
    Real.iteratedDerivWithin_cos_Icc 41 hb hzero,
    Real.iteratedDerivWithin_cos_Icc 42 hb hzero,
    Real.iteratedDerivWithin_cos_Icc 43 hb hzero,
    Real.iteratedDerivWithin_cos_Icc 44 hb hzero,
    Real.iteratedDerivWithin_cos_Icc 45 hb hzero,
    Real.iteratedDerivWithin_cos_Icc 46 hb hzero,
    Real.iteratedDerivWithin_cos_Icc 47 hb hzero,
    Real.iteratedDerivWithin_cos_Icc 48 hb hzero]
  norm_num [Real.iteratedDeriv_even_cos, Real.iteratedDeriv_odd_cos]
  ring

theorem cosine_taylor_ninety_six_remainder
    {a b x : ℝ}
    (hab : a < b)
    (hx : x ∈ Set.Icc a b) :
    ‖Real.cos x -
        taylorWithinEval Real.cos 96 (Set.Icc a b) a x‖
      ≤ (x - a) ^ 97 / ((Nat.factorial 96 : ℕ) : ℝ) := by
  have h := taylor_mean_remainder_bound (n := 96) (C := (1 : ℝ)) hab.le
      Real.contDiff_cos.contDiffOn hx (by
        intro y hy
        rw [show 96 + 1 = 97 by norm_num,
          Real.iteratedDerivWithin_cos_Icc 97 hab hy]
        simpa [Real.norm_eq_abs] using Real.abs_iteratedDeriv_cos_le_one 97 y)
  simpa using h

theorem cosine_taylor_ninety_six_at_zero
    {b x : ℝ} (hb : 0 < b) :
    taylorWithinEval Real.cos 96 (Set.Icc 0 b) 0 x =
      Finset.sum (Finset.range 49) (fun k =>
        (-1 : ℝ)^k * x ^ (2 * k) /
          ((Nat.factorial (2 * k) : ℕ) : ℝ)) := by
  rw [taylor_within_apply]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial_zero,
    Nat.factorial_one, Nat.cast_one, inv_one]
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
    Real.iteratedDerivWithin_cos_Icc 18 hb hzero,
    Real.iteratedDerivWithin_cos_Icc 19 hb hzero,
    Real.iteratedDerivWithin_cos_Icc 20 hb hzero,
    Real.iteratedDerivWithin_cos_Icc 21 hb hzero,
    Real.iteratedDerivWithin_cos_Icc 22 hb hzero,
    Real.iteratedDerivWithin_cos_Icc 23 hb hzero,
    Real.iteratedDerivWithin_cos_Icc 24 hb hzero,
    Real.iteratedDerivWithin_cos_Icc 25 hb hzero,
    Real.iteratedDerivWithin_cos_Icc 26 hb hzero,
    Real.iteratedDerivWithin_cos_Icc 27 hb hzero,
    Real.iteratedDerivWithin_cos_Icc 28 hb hzero,
    Real.iteratedDerivWithin_cos_Icc 29 hb hzero,
    Real.iteratedDerivWithin_cos_Icc 30 hb hzero,
    Real.iteratedDerivWithin_cos_Icc 31 hb hzero,
    Real.iteratedDerivWithin_cos_Icc 32 hb hzero,
    Real.iteratedDerivWithin_cos_Icc 33 hb hzero,
    Real.iteratedDerivWithin_cos_Icc 34 hb hzero,
    Real.iteratedDerivWithin_cos_Icc 35 hb hzero,
    Real.iteratedDerivWithin_cos_Icc 36 hb hzero,
    Real.iteratedDerivWithin_cos_Icc 37 hb hzero,
    Real.iteratedDerivWithin_cos_Icc 38 hb hzero,
    Real.iteratedDerivWithin_cos_Icc 39 hb hzero,
    Real.iteratedDerivWithin_cos_Icc 40 hb hzero,
    Real.iteratedDerivWithin_cos_Icc 41 hb hzero,
    Real.iteratedDerivWithin_cos_Icc 42 hb hzero,
    Real.iteratedDerivWithin_cos_Icc 43 hb hzero,
    Real.iteratedDerivWithin_cos_Icc 44 hb hzero,
    Real.iteratedDerivWithin_cos_Icc 45 hb hzero,
    Real.iteratedDerivWithin_cos_Icc 46 hb hzero,
    Real.iteratedDerivWithin_cos_Icc 47 hb hzero,
    Real.iteratedDerivWithin_cos_Icc 48 hb hzero,
    Real.iteratedDerivWithin_cos_Icc 49 hb hzero,
    Real.iteratedDerivWithin_cos_Icc 50 hb hzero,
    Real.iteratedDerivWithin_cos_Icc 51 hb hzero,
    Real.iteratedDerivWithin_cos_Icc 52 hb hzero,
    Real.iteratedDerivWithin_cos_Icc 53 hb hzero,
    Real.iteratedDerivWithin_cos_Icc 54 hb hzero,
    Real.iteratedDerivWithin_cos_Icc 55 hb hzero,
    Real.iteratedDerivWithin_cos_Icc 56 hb hzero,
    Real.iteratedDerivWithin_cos_Icc 57 hb hzero,
    Real.iteratedDerivWithin_cos_Icc 58 hb hzero,
    Real.iteratedDerivWithin_cos_Icc 59 hb hzero,
    Real.iteratedDerivWithin_cos_Icc 60 hb hzero,
    Real.iteratedDerivWithin_cos_Icc 61 hb hzero,
    Real.iteratedDerivWithin_cos_Icc 62 hb hzero,
    Real.iteratedDerivWithin_cos_Icc 63 hb hzero,
    Real.iteratedDerivWithin_cos_Icc 64 hb hzero,
    Real.iteratedDerivWithin_cos_Icc 65 hb hzero,
    Real.iteratedDerivWithin_cos_Icc 66 hb hzero,
    Real.iteratedDerivWithin_cos_Icc 67 hb hzero,
    Real.iteratedDerivWithin_cos_Icc 68 hb hzero,
    Real.iteratedDerivWithin_cos_Icc 69 hb hzero,
    Real.iteratedDerivWithin_cos_Icc 70 hb hzero,
    Real.iteratedDerivWithin_cos_Icc 71 hb hzero,
    Real.iteratedDerivWithin_cos_Icc 72 hb hzero,
    Real.iteratedDerivWithin_cos_Icc 73 hb hzero,
    Real.iteratedDerivWithin_cos_Icc 74 hb hzero,
    Real.iteratedDerivWithin_cos_Icc 75 hb hzero,
    Real.iteratedDerivWithin_cos_Icc 76 hb hzero,
    Real.iteratedDerivWithin_cos_Icc 77 hb hzero,
    Real.iteratedDerivWithin_cos_Icc 78 hb hzero,
    Real.iteratedDerivWithin_cos_Icc 79 hb hzero,
    Real.iteratedDerivWithin_cos_Icc 80 hb hzero,
    Real.iteratedDerivWithin_cos_Icc 81 hb hzero,
    Real.iteratedDerivWithin_cos_Icc 82 hb hzero,
    Real.iteratedDerivWithin_cos_Icc 83 hb hzero,
    Real.iteratedDerivWithin_cos_Icc 84 hb hzero,
    Real.iteratedDerivWithin_cos_Icc 85 hb hzero,
    Real.iteratedDerivWithin_cos_Icc 86 hb hzero,
    Real.iteratedDerivWithin_cos_Icc 87 hb hzero,
    Real.iteratedDerivWithin_cos_Icc 88 hb hzero,
    Real.iteratedDerivWithin_cos_Icc 89 hb hzero,
    Real.iteratedDerivWithin_cos_Icc 90 hb hzero,
    Real.iteratedDerivWithin_cos_Icc 91 hb hzero,
    Real.iteratedDerivWithin_cos_Icc 92 hb hzero,
    Real.iteratedDerivWithin_cos_Icc 93 hb hzero,
    Real.iteratedDerivWithin_cos_Icc 94 hb hzero,
    Real.iteratedDerivWithin_cos_Icc 95 hb hzero,
    Real.iteratedDerivWithin_cos_Icc 96 hb hzero]
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
