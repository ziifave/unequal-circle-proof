import CirclePacking.FifteenLocalAngleGeometry
import CirclePacking.FifteenPackingSortedGeometry
import CirclePacking.FifteenCandidateBoxLocalBarrier
import CirclePacking.FifteenCandidateSmoothness

/-! Packing-level interface for the local five-cycle argument.  The geometric
angle budget is now obtained from a genuine unit-disk `Packing`; the remaining
radial-pattern and analytic hypotheses are stated explicitly. -/

namespace CirclePacking

/-- A unit disk center at radial distance `b` forces the containing circle to
have radius at least `1 + b`. -/
theorem fifteen_unit_packing_radius_lower_bound_of_sorted_center
    {R b : ℝ} (P : Packing 15 R)
    (hunit : ∀ i, (P.circles i).radius = 1)
    (k : Fin 15)
    (hcenter : fifteenPackingSortedRadius P k = b) :
    1 + b ≤ R := by
  have hcontainer := fifteen_unit_packing_center_radius_le_container P hunit
    (fifteenPackingSortedIndex P k)
  have hradial : fifteenPackingSortedRadius P k ≤ R - 1 := by
    simpa [fifteenPackingSortedRadius] using hcontainer
  rw [hcenter] at hradial
  linarith

/-- Specialization to the candidate outer-center distance. -/
theorem fifteen_unit_packing_radius_lower_bound_of_candidate_outer_center
    {R : ℝ} (P : Packing 15 R)
    (hunit : ∀ i, (P.circles i).radius = 1)
    (houter : fifteenPackingSortedRadius P 1 = fifteenCandidateOuterRadius) :
    1 + fifteenCandidateOuterRadius ≤ R := by
  exact fifteen_unit_packing_radius_lower_bound_of_sorted_center P hunit 1 houter

/-- An actual unit-disk packing whose angle-sorted centers have the cyclic
radial pattern `(I,O,O)^5` satisfies the five-sector local angle budget.
The ten outer radii are assumed equal, as they are after the wall-pushing
reduction; the theorem itself uses only pairwise separation and polar order. -/
theorem fifteen_unit_packing_ordered_pattern_angle_budget
    {R : ℝ} (P : Packing 15 R)
    (hunit : ∀ i, (P.circles i).radius = 1)
    (r₀ r₁ r₂ r₃ r₄ b : ℝ)
    (hR₀ : fifteenPackingSortedRadius P 0 = r₀)
    (hR₁ : fifteenPackingSortedRadius P 1 = b)
    (hR₂ : fifteenPackingSortedRadius P 2 = b)
    (hR₃ : fifteenPackingSortedRadius P 3 = r₁)
    (hR₄ : fifteenPackingSortedRadius P 4 = b)
    (hR₅ : fifteenPackingSortedRadius P 5 = b)
    (hR₆ : fifteenPackingSortedRadius P 6 = r₂)
    (hR₇ : fifteenPackingSortedRadius P 7 = b)
    (hR₈ : fifteenPackingSortedRadius P 8 = b)
    (hR₉ : fifteenPackingSortedRadius P 9 = r₃)
    (hR₁₀ : fifteenPackingSortedRadius P 10 = b)
    (hR₁₁ : fifteenPackingSortedRadius P 11 = b)
    (hR₁₂ : fifteenPackingSortedRadius P 12 = r₄)
    (hR₁₃ : fifteenPackingSortedRadius P 13 = b)
    (hR₁₄ : fifteenPackingSortedRadius P 14 = b)
    (hr₀ : 0 < r₀) (hr₁ : 0 < r₁) (hr₂ : 0 < r₂)
    (hr₃ : 0 < r₃) (hr₄ : 0 < r₄) (hb : 0 < b) :
    max (fifteenTouchAngle r₀ r₁)
        (fifteenDetourAngle b r₀ r₁) +
      max (fifteenTouchAngle r₁ r₂)
        (fifteenDetourAngle b r₁ r₂) +
      max (fifteenTouchAngle r₂ r₃)
        (fifteenDetourAngle b r₂ r₃) +
      max (fifteenTouchAngle r₃ r₄)
        (fifteenDetourAngle b r₃ r₄) +
      max (fifteenTouchAngle r₄ r₀)
        (fifteenDetourAngle b r₄ r₀) ≤ 5 * (2 * fifteenLocalPhi) := by
  have hpositive : ∀ i : Fin 15, 0 < fifteenPackingSortedRadius P i := by
    intro i
    fin_cases i <;> simp_all
  exact fifteenOrderedPattern_packing_angle_budget
    (radius := fun i => fifteenPackingSortedRadius P i)
    (theta := fun i => fifteenPackingSortedAngle P i)
    r₀ r₁ r₂ r₃ r₄ b
    hR₀ hR₁ hR₂ hR₃ hR₄ hR₅ hR₆ hR₇ hR₈ hR₉ hR₁₀ hR₁₁ hR₁₂ hR₁₃ hR₁₄
    (fun i j hij => fifteenPackingSortedAngle_monotone P hij)
    (fun i => (fifteenPackingSortedAngle_range P i).1)
    (fun i => (fifteenPackingSortedAngle_range P i).2)
    hpositive
    (fun i j hij =>
      fifteen_unit_packing_sorted_pair_separated P hunit
        (i := i) (j := j) hij)

/-- Local rigidity for an actual packing in the certified five-inner radial
box.  The angular budget follows from packing separation and sorted polar
order.  Smoothness and the `(I,O,O)^5` radial pattern remain explicit inputs;
both second-derivative estimates are proved internally from the candidate
angle bounds. -/
theorem fifteen_unit_packing_local_rigidity_of_survivor_pattern
    {R : ℝ} (P : Packing 15 R)
    (hunit : ∀ i, (P.circles i).radius = 1)
    (r₀ r₁ r₂ r₃ r₄ : ℝ)
    (hR₀ : fifteenPackingSortedRadius P 0 = r₀)
    (hR₁ : fifteenPackingSortedRadius P 1 = fifteenCandidateOuterRadius)
    (hR₂ : fifteenPackingSortedRadius P 2 = fifteenCandidateOuterRadius)
    (hR₃ : fifteenPackingSortedRadius P 3 = r₁)
    (hR₄ : fifteenPackingSortedRadius P 4 = fifteenCandidateOuterRadius)
    (hR₅ : fifteenPackingSortedRadius P 5 = fifteenCandidateOuterRadius)
    (hR₆ : fifteenPackingSortedRadius P 6 = r₂)
    (hR₇ : fifteenPackingSortedRadius P 7 = fifteenCandidateOuterRadius)
    (hR₈ : fifteenPackingSortedRadius P 8 = fifteenCandidateOuterRadius)
    (hR₉ : fifteenPackingSortedRadius P 9 = r₃)
    (hR₁₀ : fifteenPackingSortedRadius P 10 = fifteenCandidateOuterRadius)
    (hR₁₁ : fifteenPackingSortedRadius P 11 = fifteenCandidateOuterRadius)
    (hR₁₂ : fifteenPackingSortedRadius P 12 = r₄)
    (hR₁₃ : fifteenPackingSortedRadius P 13 = fifteenCandidateOuterRadius)
    (hR₁₄ : fifteenPackingSortedRadius P 14 = fifteenCandidateOuterRadius)
    (hr₀ : r₀ ∈ Set.Icc (42 / 25 : ℝ) (43 / 25))
    (hr₁ : r₁ ∈ Set.Icc (42 / 25 : ℝ) (43 / 25))
    (hr₂ : r₂ ∈ Set.Icc (42 / 25 : ℝ) (43 / 25))
    (hr₃ : r₃ ∈ Set.Icc (42 / 25 : ℝ) (43 / 25))
    (hr₄ : r₄ ∈ Set.Icc (42 / 25 : ℝ) (43 / 25))
    : (r₀ = fifteenCandidateInnerRadius ∧
      r₁ = fifteenCandidateInnerRadius ∧
      r₂ = fifteenCandidateInnerRadius ∧
      r₃ = fifteenCandidateInnerRadius ∧
      r₄ = fifteenCandidateInnerRadius) ∧
      1 + fifteenCandidateOuterRadius ≤ R := by
  have hbudget := fifteen_unit_packing_ordered_pattern_angle_budget
    P hunit r₀ r₁ r₂ r₃ r₄ fifteenCandidateOuterRadius
    hR₀ hR₁ hR₂ hR₃ hR₄ hR₅ hR₆ hR₇ hR₈ hR₉ hR₁₀ hR₁₁ hR₁₂ hR₁₃ hR₁₄
    (by linarith [hr₀.1]) (by linarith [hr₁.1]) (by linarith [hr₂.1])
    (by linarith [hr₃.1]) (by linarith [hr₄.1])
    fifteenCandidateOuterRadius_pos
  have hDirectCont : ∀ dx dy : ℝ,
      |dx| ≤ (11 / 500 : ℝ) → |dy| ≤ (11 / 500 : ℝ) →
      ContDiffOn ℝ 2
        (fun t : ℝ => fifteenTouchAngle
          (fifteenCandidateInnerRadius + t * dx)
          (fifteenCandidateInnerRadius + t * dy))
        (Set.uIcc 0 1) := by
    intro dx dy hdx hdy
    exact fifteenCandidateDirectAngle_contDiffOn dx dy hdx hdy
  have hDetourCont : ∀ dx dy : ℝ,
      |dx| ≤ (11 / 500 : ℝ) → |dy| ≤ (11 / 500 : ℝ) →
      ContDiffOn ℝ 2
        (fun t : ℝ => fifteenDetourAngleAlongSegment
          fifteenCandidateOuterRadius fifteenCandidateInnerRadius
          fifteenCandidateInnerRadius dx dy t)
        (Set.uIcc 0 1) := by
    intro dx dy hdx hdy
    exact fifteenCandidateDetourAngle_contDiffOn dx dy hdx hdy
  have hrigid := fifteenCandidateLocalBarrier_rigidity_of_box
    r₀ r₁ r₂ r₃ r₄ hr₀ hr₁ hr₂ hr₃ hr₄
    hDirectCont hDetourCont hbudget
  have hradius := fifteen_unit_packing_radius_lower_bound_of_candidate_outer_center
    P hunit hR₁
  exact ⟨hrigid, hradius⟩

end CirclePacking
