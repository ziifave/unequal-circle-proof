import CirclePacking.Angle

namespace CirclePacking

open scoped BigOperators

/-!
  The finite angular part of the certificate.

  `q g` is the incidence vector of a directed angular path and `b g` is a
  certified lower bound for that path.  The theorem is deliberately generic:
  the order enumeration and the numerical production of `q`, `b`, and `y`
  remain finite data supplied by the certificate generator.
-/

theorem angular_farkas_contradiction
    {g k : ℕ}
    {q : Fin g → (Fin k → ℝ)}
    {b y : Fin g → ℝ}
    {gap : Fin k → ℝ}
    (hineq : ∀ i, b i ≤ dotProduct (q i) gap)
    (hweight : ∀ i, 0 ≤ y i)
    (hgap_nonneg : ∀ j, 0 ≤ gap j)
    (hgap_sum : ∑ j, gap j = 2 * Real.pi)
    (hdual : ∀ j, ∑ i, y i * q i j ≤ 1)
    (hpositive : 2 * Real.pi < ∑ i, y i * b i) : False := by
  have hweighted :
      (∑ i, y i * b i) ≤ ∑ i, y i * dotProduct (q i) gap := by
    apply Finset.sum_le_sum
    intro i hi
    exact mul_le_mul_of_nonneg_left (hineq i) (hweight i)
  have hrearrange :
      (∑ i, y i * dotProduct (q i) gap)
        = ∑ j, (∑ i, y i * q i j) * gap j := by
    simp only [dotProduct, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro i hi
    ac_rfl
  have hupper :
      (∑ i, y i * dotProduct (q i) gap) ≤ 2 * Real.pi := by
    rw [hrearrange]
    calc
      (∑ j, (∑ i, y i * q i j) * gap j)
          ≤ ∑ j, (1 : ℝ) * gap j := by
            apply Finset.sum_le_sum
            intro j hj
            exact mul_le_mul_of_nonneg_right (hdual j) (hgap_nonneg j)
      _ = 2 * Real.pi := by simpa using hgap_sum
  exact (not_lt_of_ge (le_trans hweighted hupper)) hpositive

end CirclePacking
