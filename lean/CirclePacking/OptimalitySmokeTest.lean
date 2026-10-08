import CirclePacking.Optimality
import CirclePacking.AngularCellCertificate
import Mathlib.Analysis.Real.Pi.Bounds

namespace CirclePacking

open scoped BigOperators

/- A one-row exact Farkas certificate.  This is intentionally a smoke test for
   the 11Squares-style assembly, not a claim about the circle instance. -/
def smokeAngularCertificate : AngularCellCertificate 1 1 where
  q := fun _ _ => 1
  lower := fun _ => 9
  weight := fun _ => 1
  dual := by
    intro j
    simp
  nonnegative := by
    intro i
    simp
  positive := by
    simp
    have hpi : Real.pi < 4 := Real.pi_lt_four
    nlinarith

theorem smoke_no_gap :
    ¬ ∃ gap : Fin 1 → ℝ,
      (∀ j, 0 ≤ gap j) ∧
      (∑ j, gap j = 2 * Real.pi) ∧
      (∀ i, smokeAngularCertificate.lower i ≤
        dotProduct (smokeAngularCertificate.q i) gap) := by
  rintro ⟨gap, hnonneg, hsum, hineq⟩
  exact angular_cell_refuted smokeAngularCertificate hnonneg hsum hineq

def smokeCell (x : Fin 1 → ℝ) : Prop :=
  ∀ j, 0 ≤ x j

theorem smoke_cell_refuted :
    ¬ ∃ x : Fin 1 → ℝ,
      smokeCell x ∧
      (∑ j, x j = 2 * Real.pi) ∧
      (∀ i, smokeAngularCertificate.lower i ≤
        dotProduct (smokeAngularCertificate.q i) x) := by
  rintro ⟨x, hx, hsum, hineq⟩
  exact angular_cell_refuted smokeAngularCertificate hx hsum hineq

theorem smoke_finite_cover_assembly :
    ¬ ∃ x : Fin 1 → ℝ,
      smokeCell x ∧
      (∑ j, x j = 2 * Real.pi) ∧
      (∀ i, smokeAngularCertificate.lower i ≤
        dotProduct (smokeAngularCertificate.q i) x) := by
  exact smoke_cell_refuted

def smokeFeasible (x : Fin 1 → ℝ) : Prop :=
  smokeCell x ∧
    (∑ j, x j = 2 * Real.pi) ∧
    (∀ i, smokeAngularCertificate.lower i ≤
      dotProduct (smokeAngularCertificate.q i) x)

def smokeFiniteCertificate :
    FiniteCoverCertificate (Fin 1 → ℝ) 1 smokeFeasible where
  cell := fun _ _ => True
  covered := by
    intro x hx
    exact ⟨0, trivial⟩
  cell_refuted := by
    intro i h
    rcases h with ⟨x, hx, _⟩
    exact smoke_cell_refuted ⟨x, hx.1, hx.2.1, hx.2.2⟩

theorem smoke_finite_cover_theorem :
    ¬ ∃ x, smokeFeasible x := by
  exact no_feasible_of_finite_cover smokeFiniteCertificate

end CirclePacking
