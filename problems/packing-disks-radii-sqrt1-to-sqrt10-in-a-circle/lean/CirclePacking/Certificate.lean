import CirclePacking.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Basic

namespace CirclePacking

open scoped BigOperators

/-!
  A small, proof-oriented interface for Farkas certificates.

  The numerical layer may discover a certificate using MPFI or another
  validated arithmetic library.  Lean only needs to replay the finite
  inequalities and the exact weighted balance supplied with that certificate.
-/

def dotProduct {d : ℕ} (u v : Fin d → ℝ) : ℝ :=
  ∑ k, u k * v k

theorem farkas_contradiction
    {n d : ℕ}
    {a : Fin n → (Fin d → ℝ)}
    {b y : Fin n → ℝ}
    {x : Fin d → ℝ}
    (hineq : ∀ i, b i ≤ dotProduct (a i) x)
    (hweight : ∀ i, 0 ≤ y i)
    (hbalance : ∑ i, y i * dotProduct (a i) x = 0)
    (hpositive : 0 < ∑ i, y i * b i) : False := by
  have hnonneg : 0 ≤ ∑ i, y i * (dotProduct (a i) x - b i) := by
    apply Finset.sum_nonneg
    intro i hi
    exact mul_nonneg (hweight i) (sub_nonneg.mpr (hineq i))
  have hcontradiction : 0 ≤ -(∑ i, y i * b i) := by
    simpa [mul_sub, Finset.sum_sub_distrib, hbalance] using hnonneg
  exact (not_lt_of_ge hcontradiction) (neg_lt_zero.mpr hpositive)

end CirclePacking
