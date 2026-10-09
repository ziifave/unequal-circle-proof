import CirclePacking.Certificate
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

namespace CirclePacking

noncomputable section

/-! Certified angular lower bounds are expressed through cosine inequalities.

The numerical layer may provide a rational lower angle `ell` and prove
`c ≤ cos ell`.  This lemma then converts that fact into the desired
`ell ≤ arccos c` without trusting a floating-point `arccos` evaluation.
-/

theorem angle_lower_bound_of_cosine
    {c ell : ℝ}
    (hell_nonneg : 0 ≤ ell)
    (hell_le_pi : ell ≤ Real.pi)
    (hcos : c ≤ Real.cos ell) :
    ell ≤ Real.arccos c := by
  have h := Real.antitone_arccos hcos
  rw [Real.arccos_cos hell_nonneg hell_le_pi] at h
  exact h

def touchCosine (a b d : ℝ) : ℝ :=
  (a ^ 2 + b ^ 2 - d ^ 2) / (2 * a * b)

def touchAngle (a b d : ℝ) : ℝ :=
  Real.arccos (touchCosine a b d)

theorem certified_touch_angle_lower_bound
    {a b d ell : ℝ}
    (hell_nonneg : 0 ≤ ell)
    (hell_le_pi : ell ≤ Real.pi)
    (hcos : touchCosine a b d ≤ Real.cos ell) :
    ell ≤ touchAngle a b d := by
  exact angle_lower_bound_of_cosine hell_nonneg hell_le_pi hcos

end
end CirclePacking
