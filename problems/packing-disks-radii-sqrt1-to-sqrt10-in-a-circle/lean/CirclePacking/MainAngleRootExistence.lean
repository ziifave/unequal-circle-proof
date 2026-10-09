import CirclePacking.MainAngleAnalysis
import Mathlib.Topology.Order.IntermediateValue

/-!
# Existence of the simultaneous angle root from a continuous root curve

The exact root certificate first solves the contact-route equation
`A(t,R) = B(t,R)` for `t` as a function of `R`.  The remaining closure
equation is then a one-dimensional intermediate-value argument.  This file
formalizes that topological assembly; the rational edge evaluations and the
construction and continuity of the root curve are separate analytic inputs.
-/

namespace CirclePacking

noncomputable section

/-- A continuous curve of solutions to `A = B`, with opposite closure signs
at the radius endpoints, contains a simultaneous solution of `A = B = 2π`.
The rectangle and all angle evaluations are kept explicit so a later
interval-arithmetic certificate can supply the hypotheses without introducing
rounded root coordinates. -/
theorem exists_main_angle_critical_pair_of_continuous_root_curve
    {tcurve : ℝ → ℝ}
    (htcont : ContinuousOn tcurve mainBarrierRadiusRange)
    (htmem : ∀ R ∈ mainBarrierRadiusRange, tcurve R ∈ mainBarrierTRange)
    (hFzero : ∀ R ∈ mainBarrierRadiusRange,
      mainBarrierA (tcurve R) R = mainBarrierB (tcurve R) R)
    (hBcont : ContinuousOn
      (fun p : ℝ × ℝ => mainBarrierB p.1 p.2)
      (mainBarrierTRange ×ˢ mainBarrierRadiusRange))
    (hBleft : 2 * Real.pi < mainBarrierB (tcurve 8.303) 8.303)
    (hBright : mainBarrierB (tcurve 8.304) 8.304 < 2 * Real.pi) :
    ∃ t R, t ∈ mainBarrierTRange ∧ R ∈ mainBarrierRadiusRange ∧
      mainBarrierA t R = 2 * Real.pi ∧ mainBarrierB t R = 2 * Real.pi := by
  let H : ℝ → ℝ := fun R => mainBarrierB (tcurve R) R - 2 * Real.pi
  have hpairCont : ContinuousOn (fun R => (tcurve R, R))
      mainBarrierRadiusRange := htcont.prodMk continuousOn_id
  have hpairMem : Set.MapsTo (fun R => (tcurve R, R)) mainBarrierRadiusRange
      (mainBarrierTRange ×ˢ mainBarrierRadiusRange) := by
    intro R hR
    exact ⟨htmem R hR, hR⟩
  have hBcurve : ContinuousOn
      (fun R => mainBarrierB (tcurve R) R) mainBarrierRadiusRange := by
    have hcomp := hBcont.comp hpairCont hpairMem
    convert hcomp using 1
    ext R
    rfl
  have hHcont : ContinuousOn H mainBarrierRadiusRange := by
    change ContinuousOn
      ((fun R => mainBarrierB (tcurve R) R) - fun _ => 2 * Real.pi)
      mainBarrierRadiusRange
    exact hBcurve.sub continuousOn_const
  have hRle : (8.303 : ℝ) ≤ 8.304 := by norm_num
  have hzero : (0 : ℝ) ∈ Set.Icc (H 8.304) (H 8.303) := by
    constructor
    · dsimp [H]
      linarith [hBright]
    · dsimp [H]
      linarith [hBleft]
  obtain ⟨R, hR, hHroot⟩ :=
    intermediate_value_Icc' hRle hHcont hzero
  have hRmem : R ∈ mainBarrierRadiusRange := hR
  have hBroot : mainBarrierB (tcurve R) R = 2 * Real.pi := by
    dsimp [H] at hHroot
    linarith
  exact ⟨tcurve R, R, htmem R hRmem, hRmem,
    by rw [hFzero R hRmem, hBroot], hBroot⟩

/-- In particular, the root produced by the continuous-curve existence
argument is the only simultaneous root in the certified rectangle. -/
theorem exists_unique_main_angle_critical_pair_of_continuous_root_curve
    {tcurve : ℝ → ℝ}
    (htcont : ContinuousOn tcurve mainBarrierRadiusRange)
    (htmem : ∀ R ∈ mainBarrierRadiusRange, tcurve R ∈ mainBarrierTRange)
    (hFzero : ∀ R ∈ mainBarrierRadiusRange,
      mainBarrierA (tcurve R) R = mainBarrierB (tcurve R) R)
    (hBcont : ContinuousOn
      (fun p : ℝ × ℝ => mainBarrierB p.1 p.2)
      (mainBarrierTRange ×ˢ mainBarrierRadiusRange))
    (hBleft : 2 * Real.pi < mainBarrierB (tcurve 8.303) 8.303)
    (hBright : mainBarrierB (tcurve 8.304) 8.304 < 2 * Real.pi) :
    ∃ t R, t ∈ mainBarrierTRange ∧ R ∈ mainBarrierRadiusRange ∧
      mainBarrierA t R = 2 * Real.pi ∧ mainBarrierB t R = 2 * Real.pi ∧
      ∀ t' R', t' ∈ mainBarrierTRange → R' ∈ mainBarrierRadiusRange →
        mainBarrierA t' R' = 2 * Real.pi →
        mainBarrierB t' R' = 2 * Real.pi → t' = t ∧ R' = R := by
  obtain ⟨t, R, ht, hR, hA, hB⟩ :=
    exists_main_angle_critical_pair_of_continuous_root_curve
      htcont htmem hFzero hBcont hBleft hBright
  refine ⟨t, R, ht, hR, hA, hB, ?_⟩
  intro t' R' ht' hR' hA' hB'
  obtain ⟨htEq, hREq⟩ := main_angle_critical_pair_unique
    hR hR' ht ht' hA hB hA' hB'
  exact ⟨htEq.symm, hREq.symm⟩

end
end CirclePacking
