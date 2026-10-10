import CirclePacking.FifteenLocalBarrierAnalytic

/-! Conditional geometric closure of the five-sector local barrier. Once the
base-angle identities, first-order coefficients, and segment Hessian bounds
are certified, the existing odd-cycle algebra proves all five radii equal. -/

namespace CirclePacking

/-- Converts segment smoothness and Hessian bounds for the two geometric routes
into the Taylor hypotheses of the algebraic five-cycle rigidity theorem. -/
theorem fifteenLocalBarrier_rigidity_from_segment_bounds
    (a b base c d : ℝ)
    (δ₀ δ₁ δ₂ δ₃ δ₄ : ℝ)
    (ha : a ≠ 0) (hb : b ≠ 0)
    (hc : (21 / 50 : ℝ) < c) (hcd : c ≤ d)
    (hδ₀ : |δ₀| ≤ (11 / 500 : ℝ))
    (hδ₁ : |δ₁| ≤ (11 / 500 : ℝ))
    (hδ₂ : |δ₂| ≤ (11 / 500 : ℝ))
    (hδ₃ : |δ₃| ≤ (11 / 500 : ℝ))
    (hδ₄ : |δ₄| ≤ (11 / 500 : ℝ))
    (hbaseDirect : fifteenTouchAngle a a = base)
    (hbaseDetour : fifteenDetourAngle b a a = base)
    (hminusAA : fifteenAngleCosineArgument a a ≠ -1)
    (hplusAA : fifteenAngleCosineArgument a a ≠ 1)
    (hminusAB : fifteenAngleCosineArgument a b ≠ -1)
    (hplusAB : fifteenAngleCosineArgument a b ≠ 1)
    (hslopeDirectLeft : fifteenDirectSlopeLeft a = -c)
    (hslopeDirectRight : fifteenDirectSlopeRight a = -c)
    (hslopeDetour : fifteenDetourSlope a b = d)
    (hDirectCont : ∀ dx dy : ℝ,
      |dx| ≤ (11 / 500 : ℝ) → |dy| ≤ (11 / 500 : ℝ) →
      ContDiffOn ℝ 2
        (fun t : ℝ => fifteenTouchAngle (a + t * dx) (a + t * dy))
        (Set.uIcc 0 1))
    (hDirectSecond : ∀ dx dy : ℝ,
      |dx| ≤ (11 / 500 : ℝ) → |dy| ≤ (11 / 500 : ℝ) →
      ∀ t ∈ Set.uIcc 0 1,
        |iteratedDeriv 2
          (fun s : ℝ => fifteenTouchAngle (a + s * dx) (a + s * dy)) t| ≤
            5 * (dx ^ 2 + dy ^ 2))
    (hDetourCont : ∀ dx dy : ℝ,
      |dx| ≤ (11 / 500 : ℝ) → |dy| ≤ (11 / 500 : ℝ) →
      ContDiffOn ℝ 2
        (fun t : ℝ => fifteenDetourAngleAlongSegment b a a dx dy t)
        (Set.uIcc 0 1))
    (hDetourSecond : ∀ dx dy : ℝ,
      |dx| ≤ (11 / 500 : ℝ) → |dy| ≤ (11 / 500 : ℝ) →
      ∀ t ∈ Set.uIcc 0 1,
        |iteratedDeriv 2
          (fun s : ℝ => fifteenDetourAngleAlongSegment b a a dx dy s) t| ≤
            5 * (dx ^ 2 + dy ^ 2))
    (hbudget :
      max (fifteenTouchAngle (a + δ₀) (a + δ₁))
          (fifteenDetourAngle b (a + δ₀) (a + δ₁)) +
        max (fifteenTouchAngle (a + δ₁) (a + δ₂))
          (fifteenDetourAngle b (a + δ₁) (a + δ₂)) +
        max (fifteenTouchAngle (a + δ₂) (a + δ₃))
          (fifteenDetourAngle b (a + δ₂) (a + δ₃)) +
        max (fifteenTouchAngle (a + δ₃) (a + δ₄))
          (fifteenDetourAngle b (a + δ₃) (a + δ₄)) +
        max (fifteenTouchAngle (a + δ₄) (a + δ₀))
          (fifteenDetourAngle b (a + δ₄) (a + δ₀)) ≤ 5 * base) :
    δ₀ = 0 ∧ δ₁ = 0 ∧ δ₂ = 0 ∧ δ₃ = 0 ∧ δ₄ = 0 := by
  let σ₀ : ℝ := δ₀ + δ₁
  let σ₁ : ℝ := δ₁ + δ₂
  let σ₂ : ℝ := δ₂ + δ₃
  let σ₃ : ℝ := δ₃ + δ₄
  let σ₄ : ℝ := δ₄ + δ₀
  let h₀ : ℝ := fifteenTouchAngle (a + δ₀) (a + δ₁)
  let h₁ : ℝ := fifteenTouchAngle (a + δ₁) (a + δ₂)
  let h₂ : ℝ := fifteenTouchAngle (a + δ₂) (a + δ₃)
  let h₃ : ℝ := fifteenTouchAngle (a + δ₃) (a + δ₄)
  let h₄ : ℝ := fifteenTouchAngle (a + δ₄) (a + δ₀)
  let k₀ : ℝ := fifteenDetourAngle b (a + δ₀) (a + δ₁)
  let k₁ : ℝ := fifteenDetourAngle b (a + δ₁) (a + δ₂)
  let k₂ : ℝ := fifteenDetourAngle b (a + δ₂) (a + δ₃)
  let k₃ : ℝ := fifteenDetourAngle b (a + δ₃) (a + δ₄)
  let k₄ : ℝ := fifteenDetourAngle b (a + δ₄) (a + δ₀)
  have hH₀ : base - c * σ₀ - (5 / 2 : ℝ) * (δ₀ ^ 2 + δ₁ ^ 2) ≤ h₀ := by
    simpa [h₀, σ₀] using fifteenLocalDirectPair_taylor_bound
      a base c δ₀ δ₁ ha hminusAA hplusAA hbaseDirect
      hslopeDirectLeft hslopeDirectRight
      (hDirectCont δ₀ δ₁ hδ₀ hδ₁)
      (hDirectSecond δ₀ δ₁ hδ₀ hδ₁)
  have hH₁ : base - c * σ₁ - (5 / 2 : ℝ) * (δ₁ ^ 2 + δ₂ ^ 2) ≤ h₁ := by
    simpa [h₁, σ₁] using fifteenLocalDirectPair_taylor_bound
      a base c δ₁ δ₂ ha hminusAA hplusAA hbaseDirect
      hslopeDirectLeft hslopeDirectRight
      (hDirectCont δ₁ δ₂ hδ₁ hδ₂)
      (hDirectSecond δ₁ δ₂ hδ₁ hδ₂)
  have hH₂ : base - c * σ₂ - (5 / 2 : ℝ) * (δ₂ ^ 2 + δ₃ ^ 2) ≤ h₂ := by
    simpa [h₂, σ₂] using fifteenLocalDirectPair_taylor_bound
      a base c δ₂ δ₃ ha hminusAA hplusAA hbaseDirect
      hslopeDirectLeft hslopeDirectRight
      (hDirectCont δ₂ δ₃ hδ₂ hδ₃)
      (hDirectSecond δ₂ δ₃ hδ₂ hδ₃)
  have hH₃ : base - c * σ₃ - (5 / 2 : ℝ) * (δ₃ ^ 2 + δ₄ ^ 2) ≤ h₃ := by
    simpa [h₃, σ₃] using fifteenLocalDirectPair_taylor_bound
      a base c δ₃ δ₄ ha hminusAA hplusAA hbaseDirect
      hslopeDirectLeft hslopeDirectRight
      (hDirectCont δ₃ δ₄ hδ₃ hδ₄)
      (hDirectSecond δ₃ δ₄ hδ₃ hδ₄)
  have hH₄ : base - c * σ₄ - (5 / 2 : ℝ) * (δ₄ ^ 2 + δ₀ ^ 2) ≤ h₄ := by
    simpa [h₄, σ₄] using fifteenLocalDirectPair_taylor_bound
      a base c δ₄ δ₀ ha hminusAA hplusAA hbaseDirect
      hslopeDirectLeft hslopeDirectRight
      (hDirectCont δ₄ δ₀ hδ₄ hδ₀)
      (hDirectSecond δ₄ δ₀ hδ₄ hδ₀)
  have hK₀ : base + d * σ₀ - (5 / 2 : ℝ) * (δ₀ ^ 2 + δ₁ ^ 2) ≤ k₀ := by
    simpa [k₀, σ₀] using fifteenLocalDetourPair_taylor_bound
      a b base d δ₀ δ₁ ha hb hminusAB hplusAB hbaseDetour hslopeDetour
      (hDetourCont δ₀ δ₁ hδ₀ hδ₁)
      (hDetourSecond δ₀ δ₁ hδ₀ hδ₁)
  have hK₁ : base + d * σ₁ - (5 / 2 : ℝ) * (δ₁ ^ 2 + δ₂ ^ 2) ≤ k₁ := by
    simpa [k₁, σ₁] using fifteenLocalDetourPair_taylor_bound
      a b base d δ₁ δ₂ ha hb hminusAB hplusAB hbaseDetour hslopeDetour
      (hDetourCont δ₁ δ₂ hδ₁ hδ₂)
      (hDetourSecond δ₁ δ₂ hδ₁ hδ₂)
  have hK₂ : base + d * σ₂ - (5 / 2 : ℝ) * (δ₂ ^ 2 + δ₃ ^ 2) ≤ k₂ := by
    simpa [k₂, σ₂] using fifteenLocalDetourPair_taylor_bound
      a b base d δ₂ δ₃ ha hb hminusAB hplusAB hbaseDetour hslopeDetour
      (hDetourCont δ₂ δ₃ hδ₂ hδ₃)
      (hDetourSecond δ₂ δ₃ hδ₂ hδ₃)
  have hK₃ : base + d * σ₃ - (5 / 2 : ℝ) * (δ₃ ^ 2 + δ₄ ^ 2) ≤ k₃ := by
    simpa [k₃, σ₃] using fifteenLocalDetourPair_taylor_bound
      a b base d δ₃ δ₄ ha hb hminusAB hplusAB hbaseDetour hslopeDetour
      (hDetourCont δ₃ δ₄ hδ₃ hδ₄)
      (hDetourSecond δ₃ δ₄ hδ₃ hδ₄)
  have hK₄ : base + d * σ₄ - (5 / 2 : ℝ) * (δ₄ ^ 2 + δ₀ ^ 2) ≤ k₄ := by
    simpa [k₄, σ₄] using fifteenLocalDetourPair_taylor_bound
      a b base d δ₄ δ₀ ha hb hminusAB hplusAB hbaseDetour hslopeDetour
      (hDetourCont δ₄ δ₀ hδ₄ hδ₀)
      (hDetourSecond δ₄ δ₀ hδ₄ hδ₀)
  have hbudget' : max h₀ k₀ + max h₁ k₁ + max h₂ k₂ +
      max h₃ k₃ + max h₄ k₄ ≤ 5 * base := by
    simpa [h₀, h₁, h₂, h₃, h₄, k₀, k₁, k₂, k₃, k₄] using hbudget
  exact fifteenLocalBarrier_rigidity_of_taylor_bounds
    base c d δ₀ δ₁ δ₂ δ₃ δ₄ σ₀ σ₁ σ₂ σ₃ σ₄
    h₀ h₁ h₂ h₃ h₄ k₀ k₁ k₂ k₃ k₄ hc hcd
    hδ₀ hδ₁ hδ₂ hδ₃ hδ₄ rfl rfl rfl rfl rfl
    hH₀ hH₁ hH₂ hH₃ hH₄ hK₀ hK₁ hK₂ hK₃ hK₄ hbudget'

end CirclePacking
