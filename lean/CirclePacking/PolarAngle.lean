import CirclePacking.GeometricAngle

namespace CirclePacking

noncomputable section

def polarPoint (a θ : ℝ) : Point :=
  (a * Real.cos θ, a * Real.sin θ)

lemma pointNorm_polarPoint {a θ : ℝ} (ha : 0 ≤ a) :
    pointNorm (polarPoint a θ) = a := by
  have htrig : Real.cos θ ^ 2 + Real.sin θ ^ 2 = 1 := by
    simpa [pow_two] using Real.cos_sq_add_sin_sq θ
  unfold pointNorm polarPoint
  rw [show (a * Real.cos θ) ^ 2 + (a * Real.sin θ) ^ 2 = a ^ 2 by
    rw [mul_pow, mul_pow]
    nlinarith]
  rw [Real.sqrt_sq_eq_abs, abs_of_nonneg ha]

theorem centerCosine_polar
    {a b α β : ℝ} (ha : 0 < a) (hb : 0 < b) :
    centerCosine (polarPoint a α) (polarPoint b β) =
      Real.cos (α - β) := by
  have hpa : pointNorm (polarPoint a α) = a :=
    pointNorm_polarPoint (le_of_lt ha)
  have hpb : pointNorm (polarPoint b β) = b :=
    pointNorm_polarPoint (le_of_lt hb)
  unfold centerCosine
  rw [hpa, hpb]
  simp only [polarPoint, Prod.fst, Prod.snd]
  have hfactor :
      a * Real.cos α * (b * Real.cos β) +
        a * Real.sin α * (b * Real.sin β) =
      (a * b) * (Real.cos α * Real.cos β + Real.sin α * Real.sin β) := by
    ring
  rw [hfactor, ← Real.cos_sub]
  field_simp

theorem centerAngle_polar_sub
    {a b α β : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hlo : 0 ≤ α - β) (hhi : α - β ≤ Real.pi) :
    centerAngle (polarPoint a α) (polarPoint b β) = α - β := by
  unfold centerAngle
  rw [centerCosine_polar ha hb]
  exact Real.arccos_cos hlo hhi

end
end CirclePacking
