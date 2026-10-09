import Mathlib.Data.Fintype.Basic

namespace CirclePacking

/-!
# Finite certificate assembly

This is the 11Squares-style logical layer: a continuous feasibility problem is
covered by finitely many cells, and every cell is refuted separately.  The
geometry and numerical arithmetic live in the hypotheses supplied by a replay
certificate; this theorem only assembles their consequences.
-/

structure FiniteCoverCertificate
    (X : Type) (n : ℕ)
    (Feasible : X → Prop) where
  cell : Fin n → X → Prop
  covered : ∀ x, Feasible x → ∃ i, cell i x
  cell_refuted : ∀ i, ¬ ∃ x, Feasible x ∧ cell i x

theorem no_feasible_of_finite_cover
    {X : Type} {n : ℕ} {Feasible : X → Prop}
    (cert : FiniteCoverCertificate X n Feasible) :
    ¬ ∃ x, Feasible x := by
  rintro ⟨x, hx⟩
  rcases cert.covered x hx with ⟨i, hcell⟩
  exact cert.cell_refuted i ⟨x, hx, hcell⟩

theorem no_feasible_of_finite_cover_pointwise
    {X : Type} {n : ℕ} {Feasible : X → Prop}
    (cell : Fin n → X → Prop)
    (covered : ∀ x, Feasible x → ∃ i, cell i x)
    (refuted : ∀ i x, cell i x → ¬ Feasible x) :
    ¬ ∃ x, Feasible x := by
  refine no_feasible_of_finite_cover
    { cell := cell
      covered := covered
      cell_refuted := ?_ }
  intro i h
  rcases h with ⟨x, hx, hcell⟩
  exact refuted i x hcell hx

end CirclePacking
