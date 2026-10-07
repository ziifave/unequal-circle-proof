import CirclePacking.Angle

namespace CirclePacking

/-! A cosine bound is data only after its inequality has been proved.

This boundary prevents a decimal produced by MPFI from being silently treated
as a theorem.  A future Taylor/interval replay routine must construct the
`value` field before the angular certificate can be accepted.
-/

structure CertifiedCosineLowerBound (c ell : ℝ) : Prop where
  ell_nonneg : 0 ≤ ell
  ell_le_pi : ell ≤ Real.pi
  value : c ≤ Real.cos ell

theorem CertifiedCosineLowerBound.angle_lower
    {c ell : ℝ} (h : CertifiedCosineLowerBound c ell) :
    ell ≤ Real.arccos c := by
  exact angle_lower_bound_of_cosine h.ell_nonneg h.ell_le_pi h.value

theorem certified_cosine_zero {c : ℝ} (hc : c ≤ 1) :
    CertifiedCosineLowerBound c 0 := by
  refine ⟨le_refl 0, ?_, ?_⟩
  · exact le_of_lt Real.pi_pos
  · simpa using hc

end CirclePacking
