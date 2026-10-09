import CirclePacking.FiniteOptimality
import Mathlib.Basic.Real.Basic

namespace CirclePacking

/-!
# Optimality assembly

The 11Squares-style final theorem separates a certified witness at the target
radius from a finite exhaustive exclusion below that radius.  No numerical
method is trusted by this layer; it only consumes those two propositions.
-/

structure OptimalityCertificate
    (Feasible : ℝ → Prop) (R0 : ℝ) where
  witness : Feasible R0
  exclusion : ∀ R, R < R0 → ¬ Feasible R

theorem OptimalityCertificate.isLeast
    {Feasible : ℝ → Prop} {R0 : ℝ}
    (cert : OptimalityCertificate Feasible R0) :
    IsLeast {R : ℝ | Feasible R} R0 := by
  refine ⟨cert.witness, ?_⟩
  intro R hR
  by_contra hnot
  exact cert.exclusion R (lt_of_not_ge hnot) hR

theorem isLeast_of_lower_bound_and_finite_exclusion
    {Feasible : ℝ → Prop} {R0 L : ℝ}
    (hupper : Feasible R0)
    (hlower : ∀ R, R < L → ¬ Feasible R)
    (hfinite : ∀ R, L ≤ R → R < R0 → ¬ Feasible R) :
    IsLeast {R : ℝ | Feasible R} R0 := by
  apply OptimalityCertificate.isLeast
  refine ⟨hupper, ?_⟩
  intro R hR
  by_cases hRL : R < L
  · exact hlower R hRL
  · exact hfinite R (le_of_not_gt hRL) hR

end CirclePacking
