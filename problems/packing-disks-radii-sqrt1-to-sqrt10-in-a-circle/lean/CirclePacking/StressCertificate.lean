import CirclePacking.AngularCellCertificate

namespace CirclePacking

open scoped BigOperators

/-!
# A proof-safe finite positive-stress certificate

The numerical layer may provide the rows of an active-constraint Jacobian and
their nonnegative multipliers.  This file records only the finite algebraic
consequence: a strict direction violating every active linearized constraint
cannot improve the objective.  No LICQ or genericity assumption is used here.

The signs are deliberately abstract.  `a e` is the signed row used by the
certificate, and `target` is the objective row.  A caller chooses the signs
so that an improving direction has `a e · v ≤ 0` and `target · v > 0`.
-/

structure PositiveStressCertificate (s d : ℕ) where
  a : Fin s → (Fin d → ℝ)
  lambda : Fin s → ℝ
  target : Fin d → ℝ
  nonnegative : ∀ e, 0 ≤ lambda e
  equilibrium : ∀ k, ∑ e, lambda e * a e k = target k

theorem positive_stress_blocks_strict_direction
    {s d : ℕ} (cert : PositiveStressCertificate s d)
    {v : Fin d → ℝ}
    (hactive : ∀ e, dotProduct (cert.a e) v ≤ 0)
    (hobjective : 0 < dotProduct cert.target v) :
    False := by
  have hsum : dotProduct cert.target v =
      ∑ e, cert.lambda e * dotProduct (cert.a e) v := by
    have hEq : cert.target = (fun k => ∑ e, cert.lambda e * cert.a e k) :=
      funext (fun k => (cert.equilibrium k).symm)
    rw [hEq]
    simp only [dotProduct]
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    simp_rw [Finset.mul_sum]
    simp [mul_assoc, mul_comm]
  rw [hsum] at hobjective
  have hterm : ∀ e, cert.lambda e * dotProduct (cert.a e) v ≤ 0 := by
    intro e
    exact mul_nonpos_of_nonneg_of_nonpos (cert.nonnegative e) (hactive e)
  exact (not_lt_of_ge (Finset.sum_nonpos (fun e _ => hterm e))) hobjective

end CirclePacking
