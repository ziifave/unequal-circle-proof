import CirclePacking.FifteenLocalBarrierAlgebra

/-! This theorem closes the algebraic implication in the five-inner-center
local argument.  The Taylor inequalities are explicit hypotheses here; the
separate analytic task is to establish them for the geometric touch-angle
function on the certified radius box. -/

namespace CirclePacking

theorem fifteenLocalBarrier_rigidity_of_taylor_bounds
    (base c d : ℝ)
    (δ₀ δ₁ δ₂ δ₃ δ₄ : ℝ)
    (σ₀ σ₁ σ₂ σ₃ σ₄ : ℝ)
    (h₀ h₁ h₂ h₃ h₄ k₀ k₁ k₂ k₃ k₄ : ℝ)
    (hc : (21 / 50 : ℝ) < c)
    (hcd : c ≤ d)
    (hδ₀ : |δ₀| ≤ (11 / 500 : ℝ))
    (hδ₁ : |δ₁| ≤ (11 / 500 : ℝ))
    (hδ₂ : |δ₂| ≤ (11 / 500 : ℝ))
    (hδ₃ : |δ₃| ≤ (11 / 500 : ℝ))
    (hδ₄ : |δ₄| ≤ (11 / 500 : ℝ))
    (hσ₀ : σ₀ = δ₀ + δ₁)
    (hσ₁ : σ₁ = δ₁ + δ₂)
    (hσ₂ : σ₂ = δ₂ + δ₃)
    (hσ₃ : σ₃ = δ₃ + δ₄)
    (hσ₄ : σ₄ = δ₄ + δ₀)
    (hH₀ : base - c * σ₀ - (5 / 2 : ℝ) * (δ₀ ^ 2 + δ₁ ^ 2) ≤ h₀)
    (hH₁ : base - c * σ₁ - (5 / 2 : ℝ) * (δ₁ ^ 2 + δ₂ ^ 2) ≤ h₁)
    (hH₂ : base - c * σ₂ - (5 / 2 : ℝ) * (δ₂ ^ 2 + δ₃ ^ 2) ≤ h₂)
    (hH₃ : base - c * σ₃ - (5 / 2 : ℝ) * (δ₃ ^ 2 + δ₄ ^ 2) ≤ h₃)
    (hH₄ : base - c * σ₄ - (5 / 2 : ℝ) * (δ₄ ^ 2 + δ₀ ^ 2) ≤ h₄)
    (hK₀ : base + d * σ₀ - (5 / 2 : ℝ) * (δ₀ ^ 2 + δ₁ ^ 2) ≤ k₀)
    (hK₁ : base + d * σ₁ - (5 / 2 : ℝ) * (δ₁ ^ 2 + δ₂ ^ 2) ≤ k₁)
    (hK₂ : base + d * σ₂ - (5 / 2 : ℝ) * (δ₂ ^ 2 + δ₃ ^ 2) ≤ k₂)
    (hK₃ : base + d * σ₃ - (5 / 2 : ℝ) * (δ₃ ^ 2 + δ₄ ^ 2) ≤ k₃)
    (hK₄ : base + d * σ₄ - (5 / 2 : ℝ) * (δ₄ ^ 2 + δ₀ ^ 2) ≤ k₄)
    (hbudget : max h₀ k₀ + max h₁ k₁ + max h₂ k₂ +
      max h₃ k₃ + max h₄ k₄ ≤ 5 * base) :
    δ₀ = 0 ∧ δ₁ = 0 ∧ δ₂ = 0 ∧ δ₃ = 0 ∧ δ₄ = 0 := by
  let η : ℝ := 11 / 500
  let D : ℝ := |δ₀| + |δ₁| + |δ₂| + |δ₃| + |δ₄|
  let S : ℝ := |σ₀| + |σ₁| + |σ₂| + |σ₃| + |σ₄|
  let e₀ : ℝ := (5 / 2 : ℝ) * (δ₀ ^ 2 + δ₁ ^ 2)
  let e₁ : ℝ := (5 / 2 : ℝ) * (δ₁ ^ 2 + δ₂ ^ 2)
  let e₂ : ℝ := (5 / 2 : ℝ) * (δ₂ ^ 2 + δ₃ ^ 2)
  let e₃ : ℝ := (5 / 2 : ℝ) * (δ₃ ^ 2 + δ₄ ^ 2)
  let e₄ : ℝ := (5 / 2 : ℝ) * (δ₄ ^ 2 + δ₀ ^ 2)
  let M : ℝ := max h₀ k₀ + max h₁ k₁ + max h₂ k₂ +
    max h₃ k₃ + max h₄ k₄
  have hm₀ : base + c * |σ₀| - e₀ ≤ max h₀ k₀ :=
    fifteenTaylorPairMaxLower base c d σ₀ e₀ h₀ k₀ hcd
      (by simpa [e₀] using hH₀) (by simpa [e₀] using hK₀)
  have hm₁ : base + c * |σ₁| - e₁ ≤ max h₁ k₁ :=
    fifteenTaylorPairMaxLower base c d σ₁ e₁ h₁ k₁ hcd
      (by simpa [e₁] using hH₁) (by simpa [e₁] using hK₁)
  have hm₂ : base + c * |σ₂| - e₂ ≤ max h₂ k₂ :=
    fifteenTaylorPairMaxLower base c d σ₂ e₂ h₂ k₂ hcd
      (by simpa [e₂] using hH₂) (by simpa [e₂] using hK₂)
  have hm₃ : base + c * |σ₃| - e₃ ≤ max h₃ k₃ :=
    fifteenTaylorPairMaxLower base c d σ₃ e₃ h₃ k₃ hcd
      (by simpa [e₃] using hH₃) (by simpa [e₃] using hK₃)
  have hm₄ : base + c * |σ₄| - e₄ ≤ max h₄ k₄ :=
    fifteenTaylorPairMaxLower base c d σ₄ e₄ h₄ k₄ hcd
      (by simpa [e₄] using hH₄) (by simpa [e₄] using hK₄)
  have hsumTaylor : 5 * base + c * S - (e₀ + e₁ + e₂ + e₃ + e₄) ≤ M := by
    dsimp [S, M]
    linarith [hm₀, hm₁, hm₂, hm₃, hm₄]
  have hodd := fifteenOddFiveCycleL1 δ₀ δ₁ δ₂ δ₃ δ₄ σ₀ σ₁ σ₂ σ₃ σ₄
    hσ₀ hσ₁ hσ₂ hσ₃ hσ₄
  have hodd' : (2 / 5 : ℝ) * D ≤ S := by
    simpa [D, S, fifteenAbsFive] using hodd
  have hq₀ := fifteenSquareLeEtaAbs δ₀ η (by simpa [η] using hδ₀)
  have hq₁ := fifteenSquareLeEtaAbs δ₁ η (by simpa [η] using hδ₁)
  have hq₂ := fifteenSquareLeEtaAbs δ₂ η (by simpa [η] using hδ₂)
  have hq₃ := fifteenSquareLeEtaAbs δ₃ η (by simpa [η] using hδ₃)
  have hq₄ := fifteenSquareLeEtaAbs δ₄ η (by simpa [η] using hδ₄)
  have hqsum : δ₀ ^ 2 + δ₁ ^ 2 + δ₂ ^ 2 + δ₃ ^ 2 + δ₄ ^ 2 ≤ η * D := by
    dsimp [D]
    linarith [hq₀, hq₁, hq₂, hq₃, hq₄]
  have herrors : e₀ + e₁ + e₂ + e₃ + e₄ =
      5 * (δ₀ ^ 2 + δ₁ ^ 2 + δ₂ ^ 2 + δ₃ ^ 2 + δ₄ ^ 2) := by
    dsimp [e₀, e₁, e₂, e₃, e₄]
    ring
  have hquad : 5 * (δ₀ ^ 2 + δ₁ ^ 2 + δ₂ ^ 2 + δ₃ ^ 2 + δ₄ ^ 2) ≤
      5 * η * D := by
    calc
      5 * (δ₀ ^ 2 + δ₁ ^ 2 + δ₂ ^ 2 + δ₃ ^ 2 + δ₄ ^ 2) ≤
          5 * (η * D) :=
        mul_le_mul_of_nonneg_left hqsum (by norm_num : 0 ≤ (5 : ℝ))
      _ = 5 * η * D := by ring
  have hcPos : 0 < c := by linarith
  have hlinear : c * ((2 / 5 : ℝ) * D) ≤ c * S :=
    mul_le_mul_of_nonneg_left hodd' hcPos.le
  have hsumLower : 5 * base + c * ((2 / 5 : ℝ) * D) -
      5 * η * D ≤ M := by
    have hsumTaylor' : 5 * base + c * S -
        5 * (δ₀ ^ 2 + δ₁ ^ 2 + δ₂ ^ 2 + δ₃ ^ 2 + δ₄ ^ 2) ≤ M := by
      rw [← herrors]
      exact hsumTaylor
    have hlinearMove : 5 * base + c * ((2 / 5 : ℝ) * D) -
        5 * η * D ≤ 5 * base + c * S - 5 * η * D := by
      linarith [hlinear]
    have hquadraticMove : 5 * base + c * S - 5 * η * D ≤
        5 * base + c * S -
          5 * (δ₀ ^ 2 + δ₁ ^ 2 + δ₂ ^ 2 + δ₃ ^ 2 + δ₄ ^ 2) := by
      linarith [hquad]
    exact le_trans hlinearMove (le_trans hquadraticMove hsumTaylor')
  have hstrong : 5 * base + ((2 / 5 : ℝ) * c - 5 * η) * D ≤ M := by
    convert hsumLower using 1
    ring
  have hbudget' : M ≤ 5 * base := by simpa [M] using hbudget
  have hmargin := fifteenLocalBarrierPositiveMargin c hc
  have hcoef : 0 < (2 / 5 : ℝ) * c - 5 * η := by
    dsimp [η]
    linarith
  have hnotzero (hneq : δ₀ ≠ 0 ∨ δ₁ ≠ 0 ∨ δ₂ ≠ 0 ∨ δ₃ ≠ 0 ∨ δ₄ ≠ 0) : False := by
    have hD : 0 < D := by
      rcases hneq with h0 | h1 | h2 | h3 | h4
      · dsimp [D]
        have hp : 0 < |δ₀| := abs_pos.mpr h0
        positivity
      · dsimp [D]
        have hp : 0 < |δ₁| := abs_pos.mpr h1
        positivity
      · dsimp [D]
        have hp : 0 < |δ₂| := abs_pos.mpr h2
        positivity
      · dsimp [D]
        have hp : 0 < |δ₃| := abs_pos.mpr h3
        positivity
      · dsimp [D]
        have hp : 0 < |δ₄| := abs_pos.mpr h4
        positivity
    have hprod : 0 < ((2 / 5 : ℝ) * c - 5 * η) * D := mul_pos hcoef hD
    have hstrict : 5 * base < M := by
      calc
        5 * base < 5 * base + ((2 / 5 : ℝ) * c - 5 * η) * D := by
          linarith [hprod]
        _ ≤ M := hstrong
    exact (not_lt_of_ge hbudget') hstrict
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · by_contra h
    exact hnotzero (Or.inl h)
  · by_contra h
    exact hnotzero (Or.inr (Or.inl h))
  · by_contra h
    exact hnotzero (Or.inr (Or.inr (Or.inl h)))
  · by_contra h
    exact hnotzero (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · by_contra h
    exact hnotzero (Or.inr (Or.inr (Or.inr (Or.inr h))))

end CirclePacking
