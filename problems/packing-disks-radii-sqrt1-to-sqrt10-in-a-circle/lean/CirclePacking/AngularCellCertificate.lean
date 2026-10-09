import CirclePacking.Angular

namespace CirclePacking

open scoped BigOperators

/- A cell-level certificate for one fixed cyclic order.  The numerical layer
   supplies q, b, and y; the geometric layer supplies the gap inequalities and
   the fact that the gaps form one turn. -/
structure AngularCellCertificate (g k : ℕ) where
  q : Fin g → (Fin k → ℝ)
  lower : Fin g → ℝ
  weight : Fin g → ℝ
  dual : ∀ j, ∑ i, weight i * q i j ≤ 1
  nonnegative : ∀ i, 0 ≤ weight i
  positive : 2 * Real.pi < ∑ i, weight i * lower i

theorem angular_cell_refuted
    {g k : ℕ} (cert : AngularCellCertificate g k)
    {gap : Fin k → ℝ}
    (hgap_nonneg : ∀ j, 0 ≤ gap j)
    (hgap_sum : ∑ j, gap j = 2 * Real.pi)
    (hineq : ∀ i, cert.lower i ≤ dotProduct (cert.q i) gap) :
    False := by
  exact angular_farkas_contradiction
    hineq cert.nonnegative hgap_nonneg hgap_sum cert.dual cert.positive

end CirclePacking
