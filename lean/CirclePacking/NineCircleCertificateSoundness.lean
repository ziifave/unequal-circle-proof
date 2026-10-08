import CirclePacking.NineCircleTaylor
import CirclePacking.NineCircleGeometry

namespace CirclePacking

theorem nineEdgeCorner_margin_of_spec
    {cert : NineCircleCertificate} {box : NineRadialBox}
    {edge : NineCycleEdge} {xy : Nat × Nat}
    (hspec : nineEdgeAngleSpec cert box edge)
    (hticks : edge.2.2 ≠ 0)
    (hmem : xy ∈ nineCornerPairs box[edge.1]! box[edge.2.1]!)
    (hx : 0 < xy.1) (hy : 0 < xy.2) :
    (nineCosineNumerator cert.radiiLower[edge.1]!
        cert.radiiLower[edge.2.1]! xy.1 xy.2 : ℝ) /
        (2 * (xy.1 : ℝ) * (xy.2 : ℝ)) +
      ((edge.2.2 : ℝ) / nineAngleScale) ^ 19 /
        ((Nat.factorial 18 : ℕ) : ℝ) <
      nineTaylorReal edge.2.2 := by
  unfold nineEdgeAngleSpec at hspec
  rcases hspec with ⟨_, _, _, _, hzero | ⟨_, _, _, hcorners⟩⟩
  · exact (hticks hzero).elim
  · have hcorner := hcorners xy hmem
    have hcornerCast :
        (nineTaylorNumerator edge.2.2 : ℝ) *
            (2 * (xy.1 : ℝ) * (xy.2 : ℝ) * nineAngleScale) >
          (nineCosineNumerator cert.radiiLower[edge.1]!
              cert.radiiLower[edge.2.1]! xy.1 xy.2 : ℝ) *
              (nineTaylorDenominator * nineAngleScale) +
            2 * (xy.1 : ℝ) * (xy.2 : ℝ) * (edge.2.2 : ℝ) ^ 19 := by
      exact_mod_cast hcorner
    have hxR : 0 < (xy.1 : ℝ) := by exact_mod_cast hx
    have hyR : 0 < (xy.2 : ℝ) := by exact_mod_cast hy
    have hdenEq : (nineTaylorDenominator : ℝ) =
        (nineAngleScale : ℝ) ^ 18 *
          ((Nat.factorial 18 : ℕ) : ℝ) := by
      simp [nineTaylorDenominator]
    have hscaleR : 0 < (nineAngleScale : ℝ) := by norm_num [nineAngleScale]
    have hdenR : 0 < (nineTaylorDenominator : ℝ) := by
      rw [hdenEq]
      exact mul_pos (pow_pos hscaleR 18) (by positivity)
    rw [hdenEq] at hdenR
    have hclear := hcornerCast
    rw [hdenEq] at hclear
    have hscaled := mul_lt_mul_of_pos_right hclear hdenR
    unfold nineTaylorReal
    rw [hdenEq]
    field_simp [ne_of_gt hxR, ne_of_gt hyR, ne_of_gt hscaleR,
      show (0 : ℝ) < (Nat.factorial 18 : ℕ) by positivity]
    nlinarith [hscaled]

theorem nineEdgeCorner_cosine_lt_of_spec
    {cert : NineCircleCertificate} {box : NineRadialBox}
    {edge : NineCycleEdge} {xy : Nat × Nat}
    (hspec : nineEdgeAngleSpec cert box edge)
    (hticks : edge.2.2 ≠ 0)
    (htickBound : edge.2.2 ≤ 314159)
    (hmem : xy ∈ nineCornerPairs box[edge.1]! box[edge.2.1]!)
    (hx : 0 < xy.1) (hy : 0 < xy.2) :
    (nineCosineNumerator cert.radiiLower[edge.1]!
        cert.radiiLower[edge.2.1]! xy.1 xy.2 : ℝ) /
        (2 * (xy.1 : ℝ) * (xy.2 : ℝ)) <
      Real.cos ((edge.2.2 : ℝ) / nineAngleScale) := by
  have hmargin := nineEdgeCorner_margin_of_spec hspec hticks hmem hx hy
  have hTaylor := nineTaylor_lower_cosine_with_error edge.2.2 htickBound
  linarith

end CirclePacking
