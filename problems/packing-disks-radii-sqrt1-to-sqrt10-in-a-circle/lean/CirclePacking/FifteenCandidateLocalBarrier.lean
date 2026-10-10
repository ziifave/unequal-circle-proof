import CirclePacking.FifteenLocalBarrierCycle
import CirclePacking.FifteenCandidateDetour

/-! The abstract local five-cycle theorem instantiated at the exact symmetric
candidate.  Only the smoothness and segment-Hessian estimates remain as
geometric hypotheses. -/

namespace CirclePacking

/-- At the candidate radii, exact angle and derivative identities discharge
all algebraic inputs to the local rigidity theorem.  The four segment
regularity/curvature families and the angular budget are kept explicit: they
are the remaining analytic/geometric obligations for this local result. -/
theorem fifteenCandidateLocalBarrier_rigidity
    (δ₀ δ₁ δ₂ δ₃ δ₄ : ℝ)
    (hδ₀ : |δ₀| ≤ (11 / 500 : ℝ))
    (hδ₁ : |δ₁| ≤ (11 / 500 : ℝ))
    (hδ₂ : |δ₂| ≤ (11 / 500 : ℝ))
    (hδ₃ : |δ₃| ≤ (11 / 500 : ℝ))
    (hδ₄ : |δ₄| ≤ (11 / 500 : ℝ))
    (hDirectCont : ∀ dx dy : ℝ,
      |dx| ≤ (11 / 500 : ℝ) → |dy| ≤ (11 / 500 : ℝ) →
      ContDiffOn ℝ 2
        (fun t : ℝ => fifteenTouchAngle
          (fifteenCandidateInnerRadius + t * dx)
          (fifteenCandidateInnerRadius + t * dy))
        (Set.uIcc 0 1))
    (hDirectSecond : ∀ dx dy : ℝ,
      |dx| ≤ (11 / 500 : ℝ) → |dy| ≤ (11 / 500 : ℝ) →
      ∀ t ∈ Set.uIcc 0 1,
        |iteratedDeriv 2
          (fun s : ℝ => fifteenTouchAngle
            (fifteenCandidateInnerRadius + s * dx)
            (fifteenCandidateInnerRadius + s * dy)) t| ≤
          5 * (dx ^ 2 + dy ^ 2))
    (hDetourCont : ∀ dx dy : ℝ,
      |dx| ≤ (11 / 500 : ℝ) → |dy| ≤ (11 / 500 : ℝ) →
      ContDiffOn ℝ 2
        (fun t : ℝ => fifteenDetourAngleAlongSegment
          fifteenCandidateOuterRadius fifteenCandidateInnerRadius
          fifteenCandidateInnerRadius dx dy t)
        (Set.uIcc 0 1))
    (hDetourSecond : ∀ dx dy : ℝ,
      |dx| ≤ (11 / 500 : ℝ) → |dy| ≤ (11 / 500 : ℝ) →
      ∀ t ∈ Set.uIcc 0 1,
        |iteratedDeriv 2
          (fun s : ℝ => fifteenDetourAngleAlongSegment
            fifteenCandidateOuterRadius fifteenCandidateInnerRadius
            fifteenCandidateInnerRadius dx dy s) t| ≤
          5 * (dx ^ 2 + dy ^ 2))
    (hbudget :
      max (fifteenTouchAngle
            (fifteenCandidateInnerRadius + δ₀)
            (fifteenCandidateInnerRadius + δ₁))
          (fifteenDetourAngle fifteenCandidateOuterRadius
            (fifteenCandidateInnerRadius + δ₀)
            (fifteenCandidateInnerRadius + δ₁)) +
        max (fifteenTouchAngle
            (fifteenCandidateInnerRadius + δ₁)
            (fifteenCandidateInnerRadius + δ₂))
          (fifteenDetourAngle fifteenCandidateOuterRadius
            (fifteenCandidateInnerRadius + δ₁)
            (fifteenCandidateInnerRadius + δ₂)) +
        max (fifteenTouchAngle
            (fifteenCandidateInnerRadius + δ₂)
            (fifteenCandidateInnerRadius + δ₃))
          (fifteenDetourAngle fifteenCandidateOuterRadius
            (fifteenCandidateInnerRadius + δ₂)
            (fifteenCandidateInnerRadius + δ₃)) +
        max (fifteenTouchAngle
            (fifteenCandidateInnerRadius + δ₃)
            (fifteenCandidateInnerRadius + δ₄))
          (fifteenDetourAngle fifteenCandidateOuterRadius
            (fifteenCandidateInnerRadius + δ₃)
            (fifteenCandidateInnerRadius + δ₄)) +
        max (fifteenTouchAngle
            (fifteenCandidateInnerRadius + δ₄)
            (fifteenCandidateInnerRadius + δ₀))
          (fifteenDetourAngle fifteenCandidateOuterRadius
            (fifteenCandidateInnerRadius + δ₄)
            (fifteenCandidateInnerRadius + δ₀)) ≤
          5 * (2 * fifteenLocalPhi)) :
    δ₀ = 0 ∧ δ₁ = 0 ∧ δ₂ = 0 ∧ δ₃ = 0 ∧ δ₄ = 0 := by
  have ha : fifteenCandidateInnerRadius ≠ 0 :=
    fifteenCandidateInnerRadius_pos.ne'
  have hb : fifteenCandidateOuterRadius ≠ 0 :=
    fifteenCandidateOuterRadius_pos.ne'
  have hc : (21 / 50 : ℝ) < fifteenCandidateDirectCoefficient :=
    fifteenCandidateDirectCoefficient_gt_21_50
  have hcd : fifteenCandidateDirectCoefficient ≤
      fifteenCandidateDetourCoefficient :=
    fifteenCandidateDetourCoefficient_gt_direct.le
  have hminusAB :
      fifteenAngleCosineArgument fifteenCandidateInnerRadius
        fifteenCandidateOuterRadius ≠ -1 := by
    intro h
    rw [fifteenCandidateMixedAngleCosineArgument_eq] at h
    have hα := Real.sin_sq_add_cos_sq
      (fifteenLocalPhi - fifteenCandidateWallHalfAngle)
    have hsin :
        0 < Real.sin
          (fifteenLocalPhi - fifteenCandidateWallHalfAngle) :=
      Real.sin_pos_of_pos_of_lt_pi
        (sub_pos.mpr fifteenCandidateWallHalfAngle_lt_localPhi)
        (lt_of_le_of_lt
          (by linarith [fifteenCandidateWallHalfAngle_pos])
          fifteenLocalPhi_lt_pi)
    nlinarith
  have hplusAB :
      fifteenAngleCosineArgument fifteenCandidateInnerRadius
        fifteenCandidateOuterRadius ≠ 1 := by
    intro h
    rw [fifteenCandidateMixedAngleCosineArgument_eq] at h
    have hα := Real.sin_sq_add_cos_sq
      (fifteenLocalPhi - fifteenCandidateWallHalfAngle)
    have hsin :
        0 < Real.sin
          (fifteenLocalPhi - fifteenCandidateWallHalfAngle) :=
      Real.sin_pos_of_pos_of_lt_pi
        (sub_pos.mpr fifteenCandidateWallHalfAngle_lt_localPhi)
        (lt_of_le_of_lt
          (by linarith [fifteenCandidateWallHalfAngle_pos])
          fifteenLocalPhi_lt_pi)
    nlinarith
  exact fifteenLocalBarrier_rigidity_from_segment_bounds
    fifteenCandidateInnerRadius fifteenCandidateOuterRadius
    (2 * fifteenLocalPhi) fifteenCandidateDirectCoefficient
    fifteenCandidateDetourCoefficient
    δ₀ δ₁ δ₂ δ₃ δ₄ ha hb hc hcd
    hδ₀ hδ₁ hδ₂ hδ₃ hδ₄
    fifteenCandidateDirectAngle_eq fifteenCandidateDetourBase_eq
    fifteenCandidateAngleCosineArgument_ne_neg_one
    fifteenCandidateAngleCosineArgument_ne_one
    hminusAB hplusAB
    fifteenCandidateDirectSlopeLeft_eq
    fifteenCandidateDirectSlopeRight_eq
    fifteenCandidateDetourSlope_eq
    hDirectCont hDirectSecond hDetourCont hDetourSecond hbudget

end CirclePacking
