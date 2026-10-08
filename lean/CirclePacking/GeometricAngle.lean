import CirclePacking.SevenNineCoverage

namespace CirclePacking

noncomputable section

def centerCosine (p q : Point) : ℝ :=
  (p.1 * q.1 + p.2 * q.2) /
    (pointNorm p * pointNorm q)

def centerAngle (p q : Point) : ℝ :=
  Real.arccos (centerCosine p q)

theorem center_cosine_le_touch_cosine
    {p q : Point} {a b d : ℝ}
    (ha : 0 < a) (hb : 0 < b)
    (hpa : pointNorm p = a) (hqb : pointNorm q = b)
    (hsep : d ^ 2 ≤ pointNorm (p.1 - q.1, p.2 - q.2) ^ 2) :
    centerCosine p q ≤ touchCosine a b d := by
  have hab : 0 < a * b := mul_pos ha hb
  have hdot :
      p.1 * q.1 + p.2 * q.2 ≤ (a ^ 2 + b ^ 2 - d ^ 2) / 2 := by
    have hp := pointNorm_sq p
    have hq := pointNorm_sq q
    have hd := pointNorm_sq (p.1 - q.1, p.2 - q.2)
    rw [hpa] at hp
    rw [hqb] at hq
    nlinarith
  unfold centerCosine touchCosine
  rw [hpa, hqb]
  have hmul :
      (p.1 * q.1 + p.2 * q.2) * (2 * (a * b)) ≤
        (a ^ 2 + b ^ 2 - d ^ 2) * (a * b) := by
    nlinarith
  have hfrac := (div_le_div_iff₀ hab
    (mul_pos (by norm_num : (0 : ℝ) < 2) hab)).2 hmul
  simpa [mul_assoc] using hfrac

theorem touch_angle_le_center_angle
    {p q : Point} {a b d : ℝ}
    (ha : 0 < a) (hb : 0 < b)
    (hpa : pointNorm p = a) (hqb : pointNorm q = b)
    (hsep : d ^ 2 ≤ pointNorm (p.1 - q.1, p.2 - q.2) ^ 2) :
    touchAngle a b d ≤ centerAngle p q := by
  apply Real.antitone_arccos
  exact center_cosine_le_touch_cosine ha hb hpa hqb hsep

end
end CirclePacking
