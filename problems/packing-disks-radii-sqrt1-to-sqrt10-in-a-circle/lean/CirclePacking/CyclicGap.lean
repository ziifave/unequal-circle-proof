import CirclePacking.PolarAngle
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
    (hsorted : ∀ (j : Fin 7) (hj : j.1 < 6),
      theta j ≤ theta ⟨j.1 + 1, by omega⟩)
    (hwrap : theta 6 ≤ 2 * Real.pi + theta 0) :
    ∀ j, 0 ≤ cyclicGap7 theta j := by
  intro j
  by_cases hj : j.1 < 6
  · simpa [cyclicGap7, hj] using hsorted j hj
  · have hj6 : j = (⟨6, by decide⟩ : Fin 7) := by
      have hjval : j.1 = 6 := by
        have hjbound := j.isLt
        omega
      exact Fin.ext hjval
    subst j
    simp [cyclicGap7, hwrap]

theorem cyclicGap7_sum
    (theta : Fin 7 → ℝ) :
    ∑ j, cyclicGap7 theta j = 2 * Real.pi := by
  simp [Fin.sum_univ_succ, cyclicGap7]

theorem cyclicGap7_cell_refuted
    {g : ℕ} (cert : AngularCellCertificate g 7)
    {theta : Fin 7 → ℝ}
    (hsorted : ∀ (j : Fin 7) (hj : j.1 < 6),
      theta j ≤ theta ⟨j.1 + 1, by omega⟩)
    (hwrap : theta 6 ≤ 2 * Real.pi + theta 0)
    (hineq : ∀ i,
      cert.lower i ≤ dotProduct (cert.q i) (cyclicGap7 theta)) :
    False := by
  apply angular_cell_refuted cert
  · exact cyclicGap7_nonneg hsorted hwrap
  · exact cyclicGap7_sum theta
  · exact hineq

def pathGap7 (theta : Fin 7 → ℝ) (a b : Fin 7) : ℝ :=
  ∑ t : Fin 7, if a.1 ≤ t.1 ∧ t.1 < b.1 then cyclicGap7 theta t else 0

theorem pathGap7_eq_theta_sub
    (theta : Fin 7 → ℝ) {a b : Fin 7} (hab : a.1 < b.1) :
    pathGap7 theta a b = theta b - theta a := by
  fin_cases a <;> fin_cases b <;>
    simp_all [pathGap7, cyclicGap7, Fin.sum_univ_succ]

theorem centerAngle_polar_gap
    {a b α β : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hlo : 0 ≤ β - α) (hhi : β - α ≤ Real.pi) :
    centerAngle (polarPoint a α) (polarPoint b β) = β - α := by
  unfold centerAngle
  rw [centerCosine_polar ha hb]
  rw [show α - β = -(β - α) by ring, Real.cos_neg]
  exact Real.arccos_cos hlo hhi

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
  have hpa : pointNorm (polarPoint a (theta i)) = a :=
    pointNorm_polarPoint (le_of_lt ha)
  have hpb : pointNorm (polarPoint b (theta j)) = b :=
    pointNorm_polarPoint (le_of_lt hb)
  calc
    touchAngle a b d ≤
        centerAngle (polarPoint a (theta i)) (polarPoint b (theta j)) := by
      exact touch_angle_le_center_angle ha hb hpa hpb hsep
    _ = theta j - theta i := by
      exact centerAngle_polar_gap ha hb hlo hhi
    _ = pathGap7 theta i j := by
      symm
      exact pathGap7_eq_theta_sub theta hij

theorem certified_path_lower_of_touch_lower
    {a b d ell : ℝ} {theta : Fin 7 → ℝ}
    {i j : Fin 7} (hij : i.1 < j.1)
    (ha : 0 < a) (hb : 0 < b)
    (hsep : d ^ 2 ≤ pointNorm
      ((polarPoint a (theta i)).1 - (polarPoint b (theta j)).1,
       (polarPoint a (theta i)).2 - (polarPoint b (theta j)).2) ^ 2)
    (hlo : 0 ≤ theta j - theta i)
    (hhi : theta j - theta i ≤ Real.pi)
    (htouch : ell ≤ touchAngle a b d) :
    ell ≤ pathGap7 theta i j := by
  exact le_trans htouch (touch_angle_le_pathGap7 hij ha hb hsep hlo hhi)

def reversePathGap7 (theta : Fin 7 → ℝ) (a b : Fin 7) : ℝ :=
  2 * Real.pi - pathGap7 theta a b

theorem reversePathGap7_eq
    (theta : Fin 7 → ℝ) {a b : Fin 7} (hab : a.1 < b.1) :
    reversePathGap7 theta a b =
      2 * Real.pi - (theta b - theta a) := by
  simp [reversePathGap7, pathGap7_eq_theta_sub theta hab]

theorem centerAngle_polar_reverse_sub_gap7
    {a b α β : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hlo : 0 ≤ 2 * Real.pi - (β - α))
    (hhi : 2 * Real.pi - (β - α) ≤ Real.pi) :
    centerAngle (polarPoint a α) (polarPoint b β) =
      2 * Real.pi - (β - α) := by
  have hcos : Real.cos (α - β) =
      Real.cos (2 * Real.pi - (β - α)) := by
    rw [show 2 * Real.pi - (β - α) = 2 * Real.pi + (α - β) by ring,
      Real.cos_add]
    simp [Real.cos_two_pi, Real.sin_two_pi]
  unfold centerAngle
  rw [centerCosine_polar ha hb, hcos]
  exact Real.arccos_cos hlo hhi

theorem touch_angle_le_reversePathGap7
    {a b d : ℝ} {theta : Fin 7 → ℝ}
    {i j : Fin 7} (hij : i.1 < j.1)
    (ha : 0 < a) (hb : 0 < b)
    (hsep : d ^ 2 ≤ pointNorm
      ((polarPoint a (theta i)).1 - (polarPoint b (theta j)).1,
       (polarPoint a (theta i)).2 - (polarPoint b (theta j)).2) ^ 2)
    (hdelta : theta j - theta i ≤ 2 * Real.pi) :
    touchAngle a b d ≤ reversePathGap7 theta i j := by
  have hpa : pointNorm (polarPoint a (theta i)) = a :=
    pointNorm_polarPoint (le_of_lt ha)
  have hpb : pointNorm (polarPoint b (theta j)) = b :=
    pointNorm_polarPoint (le_of_lt hb)
  by_cases hsmall : 2 * Real.pi - (theta j - theta i) ≤ Real.pi
  · have hnonneg : 0 ≤ 2 * Real.pi - (theta j - theta i) := by linarith
    have hcenter := centerAngle_polar_reverse_sub_gap7 ha hb hnonneg hsmall
    have htouch := touch_angle_le_center_angle ha hb hpa hpb hsep
    rw [hcenter] at htouch
    rw [reversePathGap7_eq theta hij]
    exact htouch
  · have hpi : touchAngle a b d ≤ Real.pi := Real.arccos_le_pi _
    rw [reversePathGap7_eq theta hij]
    linarith

def forwardPathQ7 (a b : Fin 7) : Fin 7 → ℝ :=
  fun j => if a.1 ≤ j.1 ∧ j.1 < b.1 then 1 else 0

def reversePathQ7 (a b : Fin 7) : Fin 7 → ℝ :=
  fun j => 1 - forwardPathQ7 a b j

theorem dot_forwardPathQ7
    {gap : Fin 7 → ℝ} {a b : Fin 7} :
    dotProduct (forwardPathQ7 a b) gap =
      ∑ j : Fin 7, if a.1 ≤ j.1 ∧ j.1 < b.1 then gap j else 0 := by
  classical
  simp [dotProduct, forwardPathQ7]

theorem dot_reversePathQ7
    {gap : Fin 7 → ℝ} {a b : Fin 7}
    (hgap_sum : ∑ j, gap j = 2 * Real.pi) :
    dotProduct (reversePathQ7 a b) gap =
      2 * Real.pi -
        (∑ j : Fin 7, if a.1 ≤ j.1 ∧ j.1 < b.1 then gap j else 0) := by
  change (∑ j, (1 - forwardPathQ7 a b j) * gap j) =
    2 * Real.pi -
      (∑ j : Fin 7, if a.1 ≤ j.1 ∧ j.1 < b.1 then gap j else 0)
  calc
    (∑ j, (1 - forwardPathQ7 a b j) * gap j) =
        (∑ j, gap j) - ∑ j, forwardPathQ7 a b j * gap j := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ = 2 * Real.pi -
        (∑ j : Fin 7, if a.1 ≤ j.1 ∧ j.1 < b.1 then gap j else 0) := by
      rw [hgap_sum]
      have hforward :
          (∑ j, forwardPathQ7 a b j * gap j) =
            (∑ j : Fin 7, if a.1 ≤ j.1 ∧ j.1 < b.1 then gap j else 0) := by
        simpa [dotProduct] using
          (dot_forwardPathQ7 (gap := gap) (a := a) (b := b))
      rw [hforward]

theorem angular_cell_refuted_of_path_bounds
    {g : ℕ} (cert : AngularCellCertificate g 7)
    (rowI rowJ : Fin g → Fin 7)
    (rowReverse : Fin g → Bool)
    {theta radial d : Fin 7 → ℝ}
    (horder : ∀ r, (rowI r).1 < (rowJ r).1)
    (hq : ∀ r, cert.q r =
      if rowReverse r then
        reversePathQ7 (rowI r) (rowJ r)
      else
        forwardPathQ7 (rowI r) (rowJ r))
    (hpositive : ∀ i, 0 < radial i)
    (hsep : ∀ r, (d (rowI r) + d (rowJ r)) ^ 2 ≤
      pointNorm ((polarPoint (radial (rowI r)) (theta (rowI r))).1 -
        (polarPoint (radial (rowJ r)) (theta (rowJ r))).1,
        (polarPoint (radial (rowI r)) (theta (rowI r))).2 -
        (polarPoint (radial (rowJ r)) (theta (rowJ r))).2) ^ 2)
    (hlower : ∀ r, cert.lower r ≤
      touchAngle (radial (rowI r)) (radial (rowJ r))
        (d (rowI r) + d (rowJ r)))
    (hlo : ∀ r, 0 ≤ theta (rowJ r) - theta (rowI r))
    (hhi : ∀ r, theta (rowJ r) - theta (rowI r) ≤ Real.pi)
    (hdelta : ∀ r, theta (rowJ r) - theta (rowI r) ≤ 2 * Real.pi)
    {gap : Fin 7 → ℝ}
    (hgap_nonneg : ∀ j, 0 ≤ gap j)
    (hgap_sum : ∑ j, gap j = 2 * Real.pi)
    (hgap : gap = cyclicGap7 theta) :
    False := by
  apply angular_cell_refuted cert hgap_nonneg hgap_sum
  intro r
  rw [hq r]
  by_cases hr : rowReverse r
  · rw [ite_eq_left hr, dot_reversePathQ7 hgap_sum, hgap]
    change cert.lower r ≤ reversePathGap7 theta (rowI r) (rowJ r)
    have hpath := touch_angle_le_reversePathGap7
      (horder r) (hpositive _) (hpositive _)
      (hsep r) (hdelta r)
    exact le_trans (hlower r) hpath
  · rw [ite_eq_right hr, dot_forwardPathQ7, hgap]
    change cert.lower r ≤ pathGap7 theta (rowI r) (rowJ r)
    have hpath := touch_angle_le_pathGap7
      (horder r) (hpositive _) (hpositive _)
      (hsep r) (hlo r) (hhi r)
    exact le_trans (hlower r) hpath

end
end CirclePacking
