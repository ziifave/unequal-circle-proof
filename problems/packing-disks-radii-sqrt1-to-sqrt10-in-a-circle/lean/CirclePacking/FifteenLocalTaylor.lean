import Mathlib.Analysis.Calculus.Taylor

/-! A reusable one-variable Taylor bridge for the 15-disk local barrier.
It converts a certified bound on the second derivative into the quadratic
remainder used by the five-cycle argument. The application-specific work is to
establish the derivative bound and identify the first Taylor coefficient for
the geometric angle functions. -/

namespace CirclePacking

open Set

theorem fifteen_taylor_lower_of_second_derivative_bound
    (f : ℝ → ℝ) (a x slope M : ℝ)
    (hcont : ContDiffOn ℝ 2 f (uIcc a x))
    (hlinear : taylorWithinEval f 1 (uIcc a x) a x =
      f a + slope * (x - a))
    (hsecond : ∀ z ∈ uIcc a x, |iteratedDeriv 2 f z| ≤ M)
    (hM : 0 ≤ M) :
    f x ≥ f a + slope * (x - a) - (M / 2) * (x - a) ^ 2 := by
  by_cases hne : a = x
  · subst x
    simp at hlinear
    nlinarith
  · obtain ⟨z, hz, hrem⟩ :=
      taylor_mean_remainder_lagrange_iteratedDeriv (n := 1) hne hcont
    have hzIcc : z ∈ uIcc a x := uIoo_subset_uIcc_self hz
    have hremBound :
        |f x - taylorWithinEval f 1 (uIcc a x) a x| ≤
          (M / 2) * (x - a) ^ 2 := by
      rw [hrem]
      have hsecondZ := hsecond z hzIcc
      rw [abs_div, abs_mul, abs_of_nonneg (sq_nonneg (x - a))]
      norm_num [Nat.factorial] at hsecondZ ⊢
      nlinarith
    have hremLower := (abs_le.mp hremBound).1
    rw [hlinear] at hremLower
    nlinarith

end CirclePacking
