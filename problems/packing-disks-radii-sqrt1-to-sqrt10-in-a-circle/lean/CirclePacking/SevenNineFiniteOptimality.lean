import CirclePacking.FiniteOptimality
import CirclePacking.SevenNineCoverage

namespace CirclePacking

noncomputable section

/-! A seven-circle radial cell.  The cell is indexed by the seven binary
   choices used by the MPFI partition; no Cartesian grid is involved. -/
def sevenNineCell (state : Fin 7 → Nat)
    (P : Packing 7 (79 / 10 : ℝ)) : Prop :=
  ∀ i,
    state i ≤ 1 ∧
      (sevenNineCut i (state i) 0 : ℝ) ≤ sevenNineCenterRadius P i ∧
      sevenNineCenterRadius P i ≤ (sevenNineCut i (state i) 1 : ℝ)

theorem sevenNine_no_packing_of_cell_refutations
    (cell_refuted : ∀ state : Fin 7 → Nat,
      ¬ ∃ P : Packing 7 (79 / 10 : ℝ),
        (∀ i, (P.circles i).radius = sevenNineRadius i) ∧
        sevenNineCell state P) :
    ¬ ∃ P : Packing 7 (79 / 10 : ℝ),
      ∀ i, (P.circles i).radius = sevenNineRadius i := by
  rintro ⟨P, hRadius⟩
  rcases sevenNine_packing_is_covered P hRadius with ⟨state, hstate⟩
  exact cell_refuted state ⟨P, hRadius, hstate⟩

end
end CirclePacking
