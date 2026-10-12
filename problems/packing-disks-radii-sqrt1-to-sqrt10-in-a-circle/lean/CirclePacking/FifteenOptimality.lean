import CirclePacking.FifteenCandidatePacking
import CirclePacking.FifteenStage4StrictCycle

/-! The explicit candidate packing supplies the upper bound.  The finite
reduction and strict wall obstruction supply the matching lower bound. -/

namespace CirclePacking

/-- A radius admits a packing of fifteen unit disks exactly when it is at
least the classical fivefold-symmetric candidate radius. -/
theorem fifteen_unit_packing_radius_iff_ge_candidate {R : ℝ} :
    (∃ P : Packing 15 R, ∀ i, (P.circles i).radius = 1) ↔
      fifteenCandidateOuterRadius + 1 ≤ R := by
  constructor
  · rintro ⟨P, hunit⟩
    by_contra hnot
    have hsmall : R < fifteenCandidateOuterRadius + 1 :=
      lt_of_not_ge hnot
    exact (fifteen_unit_packing_stage4_strict_wall_impossible
      P hunit hsmall).elim
  · intro hR
    refine ⟨fifteenCandidatePacking.enlarge hR, ?_⟩
    intro i
    rfl

end CirclePacking
