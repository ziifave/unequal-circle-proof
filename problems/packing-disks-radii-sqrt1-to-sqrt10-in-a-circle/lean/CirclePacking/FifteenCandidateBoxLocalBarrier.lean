import CirclePacking.FifteenCandidateBounds
import CirclePacking.FifteenCandidateLocalBarrier

/-! Converts radii in the certified survivor box into the deviation hypotheses
of the exact-candidate local rigidity theorem. -/

namespace CirclePacking

theorem fifteenCandidateLocalBarrier_rigidity_of_box
    (r₀ r₁ r₂ r₃ r₄ : ℝ)
    (hr₀ : r₀ ∈ Set.Icc (42 / 25 : ℝ) (43 / 25))
    (hr₁ : r₁ ∈ Set.Icc (42 / 25 : ℝ) (43 / 25))
    (hr₂ : r₂ ∈ Set.Icc (42 / 25 : ℝ) (43 / 25))
    (hr₃ : r₃ ∈ Set.Icc (42 / 25 : ℝ) (43 / 25))
    (hr₄ : r₄ ∈ Set.Icc (42 / 25 : ℝ) (43 / 25))
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
      max (fifteenTouchAngle r₀ r₁)
          (fifteenDetourAngle fifteenCandidateOuterRadius r₀ r₁) +
        max (fifteenTouchAngle r₁ r₂)
          (fifteenDetourAngle fifteenCandidateOuterRadius r₁ r₂) +
        max (fifteenTouchAngle r₂ r₃)
          (fifteenDetourAngle fifteenCandidateOuterRadius r₂ r₃) +
        max (fifteenTouchAngle r₃ r₄)
          (fifteenDetourAngle fifteenCandidateOuterRadius r₃ r₄) +
        max (fifteenTouchAngle r₄ r₀)
          (fifteenDetourAngle fifteenCandidateOuterRadius r₄ r₀) ≤
          5 * (2 * fifteenLocalPhi)) :
    r₀ = fifteenCandidateInnerRadius ∧
      r₁ = fifteenCandidateInnerRadius ∧
      r₂ = fifteenCandidateInnerRadius ∧
      r₃ = fifteenCandidateInnerRadius ∧
      r₄ = fifteenCandidateInnerRadius := by
  let δ₀ := r₀ - fifteenCandidateInnerRadius
  let δ₁ := r₁ - fifteenCandidateInnerRadius
  let δ₂ := r₂ - fifteenCandidateInnerRadius
  let δ₃ := r₃ - fifteenCandidateInnerRadius
  let δ₄ := r₄ - fifteenCandidateInnerRadius
  have hδ₀ : |δ₀| ≤ (11 / 500 : ℝ) := by
    dsimp [δ₀]
    exact fifteenCandidateDeviation_abs_le_of_mem_local_interval r₀ hr₀
  have hδ₁ : |δ₁| ≤ (11 / 500 : ℝ) := by
    dsimp [δ₁]
    exact fifteenCandidateDeviation_abs_le_of_mem_local_interval r₁ hr₁
  have hδ₂ : |δ₂| ≤ (11 / 500 : ℝ) := by
    dsimp [δ₂]
    exact fifteenCandidateDeviation_abs_le_of_mem_local_interval r₂ hr₂
  have hδ₃ : |δ₃| ≤ (11 / 500 : ℝ) := by
    dsimp [δ₃]
    exact fifteenCandidateDeviation_abs_le_of_mem_local_interval r₃ hr₃
  have hδ₄ : |δ₄| ≤ (11 / 500 : ℝ) := by
    dsimp [δ₄]
    exact fifteenCandidateDeviation_abs_le_of_mem_local_interval r₄ hr₄
  have hbudget' :
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
          5 * (2 * fifteenLocalPhi) := by
    simpa [δ₀, δ₁, δ₂, δ₃, δ₄] using hbudget
  have hrigid := fifteenCandidateLocalBarrier_rigidity
    δ₀ δ₁ δ₂ δ₃ δ₄ hδ₀ hδ₁ hδ₂ hδ₃ hδ₄
    hDirectCont hDirectSecond hDetourCont hDetourSecond hbudget'
  rcases hrigid with ⟨h₀, h₁, h₂, h₃, h₄⟩
  simp only [δ₀, δ₁, δ₂, δ₃, δ₄] at h₀ h₁ h₂ h₃ h₄
  refine ⟨?_, ?_⟩
  · linarith
  · refine ⟨?_, ?_⟩
    · linarith
    · refine ⟨?_, ?_⟩
      · linarith
      · refine ⟨?_, ?_⟩
        · linarith
        · linarith

end CirclePacking
