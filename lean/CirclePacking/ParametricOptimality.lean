import CirclePacking.Optimality

namespace CirclePacking

/-!
# Parametric finite exclusion below a certified target radius

For the actual packing problem the radius is not fixed at the proof stage:
we must exclude every `R < R0`.  This structure records a finite cell cover
whose cells may depend on `R`, together with a uniform refutation obligation.
-/

structure ParametricFiniteCertificate
    (X : Type) (n : ℕ)
    (Feasible : ℝ → X → Prop)
    (L R0 : ℝ) where
  cell : Fin n → ℝ → X → Prop
  covered : ∀ R, L ≤ R → R < R0 → ∀ x, Feasible R x →
    ∃ i, cell i R x
  refuted : ∀ i R, L ≤ R → R < R0 →
    ¬ ∃ x, Feasible R x ∧ cell i R x

theorem ParametricFiniteCertificate.exclude
    {X : Type} {n : ℕ}
    {Feasible : ℝ → X → Prop} {L R0 : ℝ}
    (cert : ParametricFiniteCertificate X n Feasible L R0) :
    ∀ R, L ≤ R → R < R0 → ¬ ∃ x, Feasible R x := by
  intro R hL hR
  rintro ⟨x, hx⟩
  rcases cert.covered R hL hR x hx with ⟨i, hcell⟩
  exact cert.refuted i R hL hR ⟨x, hx, hcell⟩

theorem isLeast_of_parametric_finite_certificate
    {X : Type} {n : ℕ}
    {Feasible : ℝ → X → Prop} {L R0 : ℝ}
    (hupper : ∃ x, Feasible R0 x)
    (hlower : ∀ R, R < L → ¬ ∃ x, Feasible R x)
    (cert : ParametricFiniteCertificate X n Feasible L R0) :
    IsLeast {R : ℝ | ∃ x, Feasible R x} R0 := by
  apply isLeast_of_lower_bound_and_finite_exclusion hupper
  · exact hlower
  · exact cert.exclude

end CirclePacking
