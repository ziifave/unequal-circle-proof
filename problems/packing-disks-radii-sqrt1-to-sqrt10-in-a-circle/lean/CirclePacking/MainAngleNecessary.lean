import CirclePacking.CyclicGap

/-!
# Necessary angle inequalities for the main seven-disk order

This file formalizes the geometric side of the main angle barrier.  For a
wall-pushed core in cyclic order `(10, 5, 7, 9, 2, 8, 6)`, pairwise
non-overlap implies that each contact angle is at most the corresponding
directed angular arc.  Summing along the two routes used by the analytic
barrier gives `A(t,R) ≤ 2π` and `B(t,R) ≤ 2π`.

The exact root, derivative signs, wall-push hypotheses, and radial-tree
applicability are separate obligations; this module supplies the verified
geometry-to-angle-inequality bridge.
-/

namespace CirclePacking

noncomputable section

def mainAlpha5 (t R : ℝ) : ℝ :=
  touchAngle t (R - Real.sqrt 5) (Real.sqrt 10 + Real.sqrt 5)

def mainAlpha6 (t R : ℝ) : ℝ :=
  touchAngle t (R - Real.sqrt 6) (Real.sqrt 10 + Real.sqrt 6)

def mainAlpha7 (t R : ℝ) : ℝ :=
  touchAngle t (R - Real.sqrt 7) (Real.sqrt 10 + Real.sqrt 7)

def mainBeta57 (R : ℝ) : ℝ :=
  touchAngle (R - Real.sqrt 5) (R - Real.sqrt 7)
    (Real.sqrt 5 + Real.sqrt 7)

def mainBeta79 (R : ℝ) : ℝ :=
  touchAngle (R - Real.sqrt 7) (R - Real.sqrt 9)
    (Real.sqrt 7 + Real.sqrt 9)

def mainBeta92 (R : ℝ) : ℝ :=
  touchAngle (R - Real.sqrt 9) (R - Real.sqrt 2)
    (Real.sqrt 9 + Real.sqrt 2)

def mainBeta28 (R : ℝ) : ℝ :=
  touchAngle (R - Real.sqrt 2) (R - Real.sqrt 8)
    (Real.sqrt 2 + Real.sqrt 8)

def mainBeta86 (R : ℝ) : ℝ :=
  touchAngle (R - Real.sqrt 8) (R - Real.sqrt 6)
    (Real.sqrt 8 + Real.sqrt 6)

def mainCommonWallAngles (R : ℝ) : ℝ :=
  mainBeta79 R + mainBeta92 R + mainBeta28 R + mainBeta86 R

def mainBarrierA (t R : ℝ) : ℝ :=
  mainAlpha5 t R + mainBeta57 R + mainCommonWallAngles R + mainAlpha6 t R

def mainBarrierB (t R : ℝ) : ℝ :=
  mainAlpha7 t R + mainCommonWallAngles R + mainAlpha6 t R

/-- Separation of two centers represented in polar coordinates. -/
def polarSeparated7 (radial theta : Fin 7 → ℝ) (i j : Fin 7) (d : ℝ) : Prop :=
  d ^ 2 ≤ pointNorm
    ((polarPoint (radial i) (theta i)).1 -
        (polarPoint (radial j) (theta j)).1,
      (polarPoint (radial i) (theta i)).2 -
        (polarPoint (radial j) (theta j)).2) ^ 2

theorem pathGap7_next_eq_cyclicGap7
    (theta : Fin 7 → ℝ) {i j : Fin 7}
    (hnext : j.1 = i.1 + 1) :
    pathGap7 theta i j = cyclicGap7 theta i := by
  have hi : i.1 < 6 := by omega
  have hij : i.1 < j.1 := by omega
  rw [pathGap7_eq_theta_sub theta hij]
  have hj : j = ⟨i.1 + 1, by omega⟩ := Fin.ext hnext
  rw [hj]
  simp [cyclicGap7, hi]

/-- A disk-pair separation gives a lower bound on the forward arc, even if
that arc exceeds `π`; in that case the universal `arccos ≤ π` bound suffices. -/
theorem touch_angle_le_ordered_pathGap7
    {a b d : ℝ} {theta : Fin 7 → ℝ}
    {i j : Fin 7} (hij : i.1 < j.1)
    (ha : 0 < a) (hb : 0 < b)
    (hsep : d ^ 2 ≤ pointNorm
      ((polarPoint a (theta i)).1 - (polarPoint b (theta j)).1,
       (polarPoint a (theta i)).2 - (polarPoint b (theta j)).2) ^ 2)
    (hlo : 0 ≤ theta j - theta i) :
    touchAngle a b d ≤ pathGap7 theta i j := by
  rw [pathGap7_eq_theta_sub theta hij]
  by_cases hhi : theta j - theta i ≤ Real.pi
  · calc
      touchAngle a b d ≤
          centerAngle (polarPoint a (theta i)) (polarPoint b (theta j)) :=
        touch_angle_le_center_angle ha hb
          (pointNorm_polarPoint (le_of_lt ha))
          (pointNorm_polarPoint (le_of_lt hb)) hsep
      _ = theta j - theta i := centerAngle_polar_gap ha hb hlo hhi
  · have hangle : touchAngle a b d ≤ Real.pi := by
      exact Real.arccos_le_pi _
    linarith

theorem touch_angle_le_adjacent_cyclicGap7
    {radial theta : Fin 7 → ℝ} {i j : Fin 7} {d : ℝ}
    (hnext : j.1 = i.1 + 1)
    (horder : ∀ k, ∀ hk : k.1 < 6,
      theta k ≤ theta ⟨k.1 + 1, by omega⟩)
    (hpositive : ∀ k, 0 < radial k)
    (hsep : polarSeparated7 radial theta i j d) :
    touchAngle (radial i) (radial j) d ≤ cyclicGap7 theta i := by
  have hij : i.1 < j.1 := by omega
  have hj : j = ⟨i.1 + 1, by omega⟩ := Fin.ext hnext
  have hmono := horder i (by omega)
  rw [← hj] at hmono
  have hpath := touch_angle_le_ordered_pathGap7 hij
    (hpositive i) (hpositive j) hsep (sub_nonneg.mpr hmono)
  rw [pathGap7_next_eq_cyclicGap7 theta hnext] at hpath
  exact hpath

theorem touch_angle_le_shortcut_pathGap7
    {radial theta : Fin 7 → ℝ} {i j : Fin 7} {d : ℝ}
    (hij : i.1 < j.1)
    (hpositive : ∀ k, 0 < radial k)
    (hsep : polarSeparated7 radial theta i j d)
    (hordered : theta i ≤ theta j) :
    touchAngle (radial i) (radial j) d ≤ pathGap7 theta i j := by
  exact touch_angle_le_ordered_pathGap7 hij
    (hpositive i) (hpositive j) hsep (sub_nonneg.mpr hordered)

theorem touch_angle_le_wrap_cyclicGap7
    {radial theta : Fin 7 → ℝ} {d : ℝ}
    (hpositive : ∀ k, 0 < radial k)
    (hsep : polarSeparated7 radial theta 0 6 d)
    (hdelta : theta 6 - theta 0 ≤ 2 * Real.pi) :
    touchAngle (radial 0) (radial 6) d ≤ cyclicGap7 theta 6 := by
  have hpath := touch_angle_le_reversePathGap7
    (by norm_num : (0 : Fin 7).1 < (6 : Fin 7).1)
    (hpositive 0) (hpositive 6) hsep hdelta
  have heq : reversePathGap7 theta 0 6 = cyclicGap7 theta 6 := by
    rw [reversePathGap7_eq theta (by norm_num : (0 : Fin 7).1 < (6 : Fin 7).1)]
    simp [cyclicGap7]
    ring
  rw [heq] at hpath
  exact hpath

private theorem mainCyclicGaps_sum (theta : Fin 7 → ℝ) :
    cyclicGap7 theta 0 + cyclicGap7 theta 1 + cyclicGap7 theta 2 +
      cyclicGap7 theta 3 + cyclicGap7 theta 4 + cyclicGap7 theta 5 +
      cyclicGap7 theta 6 = 2 * Real.pi := by
  rw [← cyclicGap7_sum theta]
  simp [Fin.sum_univ_succ, cyclicGap7]

/-- The first loop `10→5→7→9→2→8→6→10` forces the first barrier
quantity below one full turn. The radial equalities say that disks 5,7,9,2,8,6
have been moved to the container wall. -/
theorem mainBarrierA_le_two_pi
    {t R : ℝ} {radial theta : Fin 7 → ℝ}
    (hr0 : radial 0 = t)
    (hr1 : radial 1 = R - Real.sqrt 5)
    (hr2 : radial 2 = R - Real.sqrt 7)
    (hr3 : radial 3 = R - Real.sqrt 9)
    (hr4 : radial 4 = R - Real.sqrt 2)
    (hr5 : radial 5 = R - Real.sqrt 8)
    (hr6 : radial 6 = R - Real.sqrt 6)
    (hpositive : ∀ k, 0 < radial k)
    (horder : ∀ k, ∀ hk : k.1 < 6,
      theta k ≤ theta ⟨k.1 + 1, by omega⟩)
    (hwrap : theta 6 ≤ 2 * Real.pi + theta 0)
    (hsep01 : polarSeparated7 radial theta 0 1 (Real.sqrt 10 + Real.sqrt 5))
    (hsep12 : polarSeparated7 radial theta 1 2 (Real.sqrt 5 + Real.sqrt 7))
    (hsep23 : polarSeparated7 radial theta 2 3 (Real.sqrt 7 + Real.sqrt 9))
    (hsep34 : polarSeparated7 radial theta 3 4 (Real.sqrt 9 + Real.sqrt 2))
    (hsep45 : polarSeparated7 radial theta 4 5 (Real.sqrt 2 + Real.sqrt 8))
    (hsep56 : polarSeparated7 radial theta 5 6 (Real.sqrt 8 + Real.sqrt 6))
    (hsep06 : polarSeparated7 radial theta 0 6 (Real.sqrt 10 + Real.sqrt 6)) :
    mainBarrierA t R ≤ 2 * Real.pi := by
  have hg0 : mainAlpha5 t R ≤ cyclicGap7 theta 0 := by
    have h := touch_angle_le_adjacent_cyclicGap7
      (radial := radial) (theta := theta) (i := 0) (j := 1)
      (d := Real.sqrt 10 + Real.sqrt 5) (by norm_num) horder hpositive hsep01
    simpa [mainAlpha5, hr0, hr1] using h
  have hg1 : mainBeta57 R ≤ cyclicGap7 theta 1 := by
    have h := touch_angle_le_adjacent_cyclicGap7
      (radial := radial) (theta := theta) (i := 1) (j := 2)
      (d := Real.sqrt 5 + Real.sqrt 7) (by norm_num) horder hpositive hsep12
    simpa [mainBeta57, hr1, hr2] using h
  have hg2 : mainBeta79 R ≤ cyclicGap7 theta 2 := by
    have h := touch_angle_le_adjacent_cyclicGap7
      (radial := radial) (theta := theta) (i := 2) (j := 3)
      (d := Real.sqrt 7 + Real.sqrt 9) (by norm_num) horder hpositive hsep23
    simpa [mainBeta79, hr2, hr3] using h
  have hg3 : mainBeta92 R ≤ cyclicGap7 theta 3 := by
    have h := touch_angle_le_adjacent_cyclicGap7
      (radial := radial) (theta := theta) (i := 3) (j := 4)
      (d := Real.sqrt 9 + Real.sqrt 2) (by norm_num) horder hpositive hsep34
    simpa [mainBeta92, hr3, hr4] using h
  have hg4 : mainBeta28 R ≤ cyclicGap7 theta 4 := by
    have h := touch_angle_le_adjacent_cyclicGap7
      (radial := radial) (theta := theta) (i := 4) (j := 5)
      (d := Real.sqrt 2 + Real.sqrt 8) (by norm_num) horder hpositive hsep45
    simpa [mainBeta28, hr4, hr5] using h
  have hg5 : mainBeta86 R ≤ cyclicGap7 theta 5 := by
    have h := touch_angle_le_adjacent_cyclicGap7
      (radial := radial) (theta := theta) (i := 5) (j := 6)
      (d := Real.sqrt 8 + Real.sqrt 6) (by norm_num) horder hpositive hsep56
    simpa [mainBeta86, hr5, hr6] using h
  have hg6 : mainAlpha6 t R ≤ cyclicGap7 theta 6 := by
    have h := touch_angle_le_wrap_cyclicGap7
      (radial := radial) (theta := theta)
      (d := Real.sqrt 10 + Real.sqrt 6) hpositive hsep06 (by linarith)
    simpa [mainAlpha6, hr0, hr6] using h
  have hsum := mainCyclicGaps_sum theta
  unfold mainBarrierA mainCommonWallAngles
  linarith

/-- Skipping disk 5 in the angular accounting gives the second necessary
inequality. Disk 5 remains present in the separation assumptions. -/
theorem mainBarrierB_le_two_pi
    {t R : ℝ} {radial theta : Fin 7 → ℝ}
    (hr0 : radial 0 = t)
    (hr2 : radial 2 = R - Real.sqrt 7)
    (hr3 : radial 3 = R - Real.sqrt 9)
    (hr4 : radial 4 = R - Real.sqrt 2)
    (hr5 : radial 5 = R - Real.sqrt 8)
    (hr6 : radial 6 = R - Real.sqrt 6)
    (hpositive : ∀ k, 0 < radial k)
    (horder : ∀ k, ∀ hk : k.1 < 6,
      theta k ≤ theta ⟨k.1 + 1, by omega⟩)
    (hwrap : theta 6 ≤ 2 * Real.pi + theta 0)
    (hsep02 : polarSeparated7 radial theta 0 2 (Real.sqrt 10 + Real.sqrt 7))
    (hsep23 : polarSeparated7 radial theta 2 3 (Real.sqrt 7 + Real.sqrt 9))
    (hsep34 : polarSeparated7 radial theta 3 4 (Real.sqrt 9 + Real.sqrt 2))
    (hsep45 : polarSeparated7 radial theta 4 5 (Real.sqrt 2 + Real.sqrt 8))
    (hsep56 : polarSeparated7 radial theta 5 6 (Real.sqrt 8 + Real.sqrt 6))
    (hsep06 : polarSeparated7 radial theta 0 6 (Real.sqrt 10 + Real.sqrt 6)) :
    mainBarrierB t R ≤ 2 * Real.pi := by
  have hg01 : mainAlpha7 t R ≤
      cyclicGap7 theta 0 + cyclicGap7 theta 1 := by
    have h := touch_angle_le_shortcut_pathGap7
      (radial := radial) (theta := theta) (i := 0) (j := 2)
      (d := Real.sqrt 10 + Real.sqrt 7) (by norm_num) hpositive hsep02
      (le_trans (horder 0 (by norm_num)) (horder 1 (by norm_num)))
    have hp : pathGap7 theta (0 : Fin 7) 2 =
        cyclicGap7 theta 0 + cyclicGap7 theta 1 := by
      rw [pathGap7_eq_theta_sub theta (by norm_num)]
      simp [cyclicGap7]
    rw [hp] at h
    simpa [mainAlpha7, hr0, hr2] using h
  have hg2 : mainBeta79 R ≤ cyclicGap7 theta 2 := by
    have h := touch_angle_le_adjacent_cyclicGap7
      (radial := radial) (theta := theta) (i := 2) (j := 3)
      (d := Real.sqrt 7 + Real.sqrt 9) (by norm_num) horder hpositive hsep23
    simpa [mainBeta79, hr2, hr3] using h
  have hg3 : mainBeta92 R ≤ cyclicGap7 theta 3 := by
    have h := touch_angle_le_adjacent_cyclicGap7
      (radial := radial) (theta := theta) (i := 3) (j := 4)
      (d := Real.sqrt 9 + Real.sqrt 2) (by norm_num) horder hpositive hsep34
    simpa [mainBeta92, hr3, hr4] using h
  have hg4 : mainBeta28 R ≤ cyclicGap7 theta 4 := by
    have h := touch_angle_le_adjacent_cyclicGap7
      (radial := radial) (theta := theta) (i := 4) (j := 5)
      (d := Real.sqrt 2 + Real.sqrt 8) (by norm_num) horder hpositive hsep45
    simpa [mainBeta28, hr4, hr5] using h
  have hg5 : mainBeta86 R ≤ cyclicGap7 theta 5 := by
    have h := touch_angle_le_adjacent_cyclicGap7
      (radial := radial) (theta := theta) (i := 5) (j := 6)
      (d := Real.sqrt 8 + Real.sqrt 6) (by norm_num) horder hpositive hsep56
    simpa [mainBeta86, hr5, hr6] using h
  have hg6 : mainAlpha6 t R ≤ cyclicGap7 theta 6 := by
    have h := touch_angle_le_wrap_cyclicGap7
      (radial := radial) (theta := theta)
      (d := Real.sqrt 10 + Real.sqrt 6) hpositive hsep06 (by linarith)
    simpa [mainAlpha6, hr0, hr6] using h
  have hsum := mainCyclicGaps_sum theta
  unfold mainBarrierB mainCommonWallAngles
  linarith

/-- Abstract final step of the angle barrier. The numerical root checker is
responsible for the monotonicity premises; once they hold, the two geometric
necessary inequalities exclude every smaller container radius. -/
theorem main_angle_barrier_excludes_below_critical
    {t R tcrit Rcrit : ℝ}
    (hR : R < Rcrit)
    (hAroot : mainBarrierA tcrit Rcrit = 2 * Real.pi)
    (hBroot : mainBarrierB tcrit Rcrit = 2 * Real.pi)
    (hA_mono_t : ∀ {t₁ t₂ : ℝ}, t₁ ≤ t₂ →
      mainBarrierA t₁ R ≤ mainBarrierA t₂ R)
    (hB_antitone_t : ∀ {t₁ t₂ : ℝ}, t₁ ≤ t₂ →
      mainBarrierB t₂ R ≤ mainBarrierB t₁ R)
    (hA_anti_R : ∀ {r₁ r₂ : ℝ}, r₁ < r₂ →
      mainBarrierA tcrit r₂ < mainBarrierA tcrit r₁)
    (hB_anti_R : ∀ {r₁ r₂ : ℝ}, r₁ < r₂ →
      mainBarrierB tcrit r₂ < mainBarrierB tcrit r₁)
    (hA_geometry : mainBarrierA t R ≤ 2 * Real.pi)
    (hB_geometry : mainBarrierB t R ≤ 2 * Real.pi) :
    False := by
  by_cases hcrit : tcrit ≤ t
  · have hAnti : mainBarrierA tcrit Rcrit < mainBarrierA tcrit R :=
      hA_anti_R hR
    have hrootStrict : 2 * Real.pi < mainBarrierA tcrit R := by
      rw [← hAroot]
      exact hAnti
    have hmon := hA_mono_t hcrit
    linarith
  · have hle : t ≤ tcrit := le_of_not_ge hcrit
    have hAnti : mainBarrierB tcrit Rcrit < mainBarrierB tcrit R :=
      hB_anti_R hR
    have hrootStrict : 2 * Real.pi < mainBarrierB tcrit R := by
      rw [← hBroot]
      exact hAnti
    have hmon := hB_antitone_t hle
    linarith

end
end CirclePacking
