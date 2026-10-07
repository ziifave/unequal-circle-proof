import CirclePacking.AngularCellCertificate

namespace CirclePacking

open scoped BigOperators

noncomputable section

def cyclicGap7 (theta : Fin 7 → ℝ) (j : Fin 7) : ℝ :=
  if hj : j.1 < 6 then
    theta ⟨j.1 + 1, by omega⟩ - theta j
  else
    2 * Real.pi + theta 0 - theta j

theorem cyclicGap7_nonneg
    {theta : Fin 7 → ℝ}
    (hsorted : ∀ j : Fin 7, j.1 < 6 →
      theta j ≤ theta ⟨j.1 + 1, by omega⟩)
    (hwrap : theta 6 ≤ 2 * Real.pi + theta 0) :
    ∀ j, 0 ≤ cyclicGap7 theta j := by
  intro j
  by_cases hj : j.1 < 6
  · simp [cyclicGap7, hj]
    exact sub_nonneg.mpr (hsorted j hj)
  · have hj6 : j = (⟨6, by decide⟩ : Fin 7) := by
      apply Fin.ext
      omega
    subst j
    simp [cyclicGap7, hwrap]

theorem cyclicGap7_sum
    (theta : Fin 7 → ℝ) :
    ∑ j, cyclicGap7 theta j = 2 * Real.pi := by
  have h0 : (0 : Fin 7).1 < 6 := by decide
  have h1 : (1 : Fin 7).1 < 6 := by decide
  have h2 : (2 : Fin 7).1 < 6 := by decide
  have h3 : (3 : Fin 7).1 < 6 := by decide
  have h4 : (4 : Fin 7).1 < 6 := by decide
  have h5 : (5 : Fin 7).1 < 6 := by decide
  simp only [Fin.sum_univ_succ, cyclicGap7, h0, h1, h2, h3, h4, h5]
  ring

theorem cyclicGap7_cell_refuted
    {g : ℕ} (cert : AngularCellCertificate g 7)
    {theta : Fin 7 → ℝ}
    (hsorted : ∀ j : Fin 7, j.1 < 6 →
      theta j ≤ theta ⟨j.1 + 1, by omega⟩)
    (hwrap : theta 6 ≤ 2 * Real.pi + theta 0)
    (hineq : ∀ i,
      cert.lower i ≤ dotProduct cert.q (cyclicGap7 theta)) :
    False := by
  apply angular_cell_refuted cert
  · exact cyclicGap7_nonneg hsorted hwrap
  · exact cyclicGap7_sum theta
  · exact hineq

def pathGap7 (theta : Fin 7 → ℝ) (a b : Fin 7) : ℝ :=
  ∑ t in Finset.Ico a.1 b.1,
    cyclicGap7 theta ⟨t, by omega⟩

theorem pathGap7_eq_theta_sub
    (theta : Fin 7 → ℝ) {a b : Fin 7} (hab : a.1 < b.1) :
    pathGap7 theta a b = theta b - theta a := by
  fin_cases a <;> fin_cases b <;>
    simp_all [pathGap7, cyclicGap7] <;> ring

theorem touch_angle_le_pathGap7
    {a b d : ℝ} {theta : Fin 7 → ℝ}
    {i j : Fin 7} (hij : i.1 < j.1)
    (ha : 0 < a) (hb : 0 < b)
    (hsep : d ^ 2 ≤ pointNorm
      ((polarPoint a (theta i)).1 - (polarPoint b (theta j)).1,
       (polarPoint a (theta i)).2 - (polarPoint b (theta j)).2) ^ 2)
    (hlo : 0 ≤ theta j - theta i)
    (hhi : theta j - theta i ≤ Real.pi) :
    touchAngle a b d ≤ pathGap7 theta i j := by
  calc
    touchAngle a b d ≤
        centerAngle (polarPoint a (theta i)) (polarPoint b (theta j)) := by
      exact touch_angle_le_center_angle ha hb rfl rfl hsep
    _ = theta j - theta i := by
      exact centerAngle_polar_sub ha hb hlo hhi
    _ = pathGap7 theta i j := by
      symm
      exact pathGap7_eq_theta_sub theta hij

end
end CirclePacking
