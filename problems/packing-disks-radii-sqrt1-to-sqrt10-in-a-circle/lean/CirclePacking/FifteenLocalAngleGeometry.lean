import CirclePacking.FifteenCandidateBoxLocalBarrier
import CirclePacking.FifteenTickSoundness

/-! Geometric lower bounds for the direct and three-edge detour routes.  These
lemmas turn pairwise non-overlap into the local angular budget used by the
five-cycle rigidity theorem. -/

namespace CirclePacking

theorem fifteenTouchAngle_eq_touchAngle_two (a b : ℝ) :
    fifteenTouchAngle a b = touchAngle a b 2 := by
  unfold fifteenTouchAngle fifteenAngleCosineArgument touchAngle touchCosine
  congr 1
  ring

theorem fifteenTouchAngle_symm (a b : ℝ) :
    fifteenTouchAngle a b = fifteenTouchAngle b a := by
  unfold fifteenTouchAngle
  rw [fifteenAngleCosineArgument_symm]

theorem fifteenPolarPoint_add_two_pi (r theta : ℝ) :
    polarPoint r (theta + 2 * Real.pi) = polarPoint r theta := by
  ext <;> simp [polarPoint, Real.cos_add_two_pi, Real.sin_add_two_pi]

/-- A separated pair whose polar angles are in the positive cyclic order
requires at least the cosine-rule touch angle. -/
theorem fifteenTouchAngle_le_ordered_polar_gap
    {a b alpha beta : ℝ}
    (ha : 0 < a) (hb : 0 < b)
    (hgap0 : 0 ≤ beta - alpha)
    (hgap2 : beta - alpha ≤ 2 * Real.pi)
    (hsep : 4 ≤ pointNorm
      ((polarPoint a alpha).1 - (polarPoint b beta).1,
       (polarPoint a alpha).2 - (polarPoint b beta).2) ^ 2) :
    fifteenTouchAngle a b ≤ beta - alpha := by
  have hsep' : (2 : ℝ) ^ 2 ≤ pointNorm
      ((polarPoint a alpha).1 - (polarPoint b beta).1,
       (polarPoint a alpha).2 - (polarPoint b beta).2) ^ 2 := by
    have htwo : (2 : ℝ) ^ 2 = 4 := by norm_num
    rw [htwo]
    exact hsep
  have hangle := fifteen_polar_touch_angle_ordered_gap
    (a := a) (b := b) (d := 2) (ell := touchAngle a b 2)
    ha hb (Real.arccos_le_pi _) hgap0 hgap2 hsep' le_rfl
  rw [fifteenTouchAngle_eq_touchAngle_two]
  exact hangle.1

theorem fifteenDetourAngle_le_three_ordered_gaps
    (a b c alpha beta gamma delta : ℝ)
    (hleft : fifteenTouchAngle a b ≤ beta - alpha)
    (hmiddle : fifteenTouchAngle b b ≤ gamma - beta)
    (hright : fifteenTouchAngle c b ≤ delta - gamma) :
    fifteenDetourAngle b a c ≤ delta - alpha := by
  unfold fifteenDetourAngle
  linarith

/-- For one sector, the direct inner chord and the route through two outer
centers are both bounded by the same three consecutive polar gaps. -/
theorem fifteenLocalSector_max_le_gap
    {a b c alpha beta gamma delta : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hgapAB0 : 0 ≤ beta - alpha)
    (hgapAB2 : beta - alpha ≤ 2 * Real.pi)
    (hgapBC0 : 0 ≤ gamma - beta)
    (hgapBC2 : gamma - beta ≤ 2 * Real.pi)
    (hgapCD0 : 0 ≤ delta - gamma)
    (hgapCD2 : delta - gamma ≤ 2 * Real.pi)
    (hgapAD2 : delta - alpha ≤ 2 * Real.pi)
    (hsepAC : 4 ≤ pointNorm
      ((polarPoint a alpha).1 - (polarPoint c delta).1,
       (polarPoint a alpha).2 - (polarPoint c delta).2) ^ 2)
    (hsepAB : 4 ≤ pointNorm
      ((polarPoint a alpha).1 - (polarPoint b beta).1,
       (polarPoint a alpha).2 - (polarPoint b beta).2) ^ 2)
    (hsepBB : 4 ≤ pointNorm
      ((polarPoint b beta).1 - (polarPoint b gamma).1,
       (polarPoint b beta).2 - (polarPoint b gamma).2) ^ 2)
    (hsepBC : 4 ≤ pointNorm
      ((polarPoint b gamma).1 - (polarPoint c delta).1,
       (polarPoint b gamma).2 - (polarPoint c delta).2) ^ 2) :
    max (fifteenTouchAngle a c) (fifteenDetourAngle b a c) ≤
      (beta - alpha) + (gamma - beta) + (delta - gamma) := by
  have hgapAD0 : 0 ≤ delta - alpha := by linarith
  have hdirect := fifteenTouchAngle_le_ordered_polar_gap
    ha hc hgapAD0 hgapAD2 hsepAC
  have hleft := fifteenTouchAngle_le_ordered_polar_gap
    ha hb hgapAB0 hgapAB2 hsepAB
  have hmiddle := fifteenTouchAngle_le_ordered_polar_gap
    hb hb hgapBC0 hgapBC2 hsepBB
  have hright' := fifteenTouchAngle_le_ordered_polar_gap
    hb hc hgapCD0 hgapCD2 hsepBC
  have hright : fifteenTouchAngle c b ≤ delta - gamma := by
    rw [fifteenTouchAngle_symm]
    exact hright'
  have hdetour := fifteenDetourAngle_le_three_ordered_gaps
    a b c alpha beta gamma delta hleft hmiddle hright
  have hmax : max (fifteenTouchAngle a c)
      (fifteenDetourAngle b a c) ≤ delta - alpha := max_le hdirect hdetour
  linarith

/-- Five sector bounds sum to the complete angular budget around the circle. -/
theorem fifteenLocalAngleBudget_of_sector_bounds
    (r₀ r₁ r₂ r₃ r₄ b : ℝ)
    (g₀ g₁ g₂ g₃ g₄ g₅ g₆ g₇ g₈ g₉ g₁₀ g₁₁ g₁₂ g₁₃ g₁₄ : ℝ)
    (hsector₀ : max (fifteenTouchAngle r₀ r₁)
        (fifteenDetourAngle b r₀ r₁) ≤ g₀ + g₁ + g₂)
    (hsector₁ : max (fifteenTouchAngle r₁ r₂)
        (fifteenDetourAngle b r₁ r₂) ≤ g₃ + g₄ + g₅)
    (hsector₂ : max (fifteenTouchAngle r₂ r₃)
        (fifteenDetourAngle b r₂ r₃) ≤ g₆ + g₇ + g₈)
    (hsector₃ : max (fifteenTouchAngle r₃ r₄)
        (fifteenDetourAngle b r₃ r₄) ≤ g₉ + g₁₀ + g₁₁)
    (hsector₄ : max (fifteenTouchAngle r₄ r₀)
        (fifteenDetourAngle b r₄ r₀) ≤ g₁₂ + g₁₃ + g₁₄)
    (hgapSum : g₀ + g₁ + g₂ + g₃ + g₄ + g₅ + g₆ + g₇ + g₈ + g₉ +
      g₁₀ + g₁₁ + g₁₂ + g₁₃ + g₁₄ = 2 * Real.pi) :
    max (fifteenTouchAngle r₀ r₁) (fifteenDetourAngle b r₀ r₁) +
      max (fifteenTouchAngle r₁ r₂) (fifteenDetourAngle b r₁ r₂) +
      max (fifteenTouchAngle r₂ r₃) (fifteenDetourAngle b r₂ r₃) +
      max (fifteenTouchAngle r₃ r₄) (fifteenDetourAngle b r₃ r₄) +
      max (fifteenTouchAngle r₄ r₀) (fifteenDetourAngle b r₄ r₀) ≤
      5 * (2 * fifteenLocalPhi) := by
  calc
    _ ≤ (g₀ + g₁ + g₂) + (g₃ + g₄ + g₅) +
        (g₆ + g₇ + g₈) + (g₉ + g₁₀ + g₁₁) +
        (g₁₂ + g₁₃ + g₁₄) := by
      linarith [hsector₀, hsector₁, hsector₂, hsector₃, hsector₄]
    _ = 2 * Real.pi := by rw [← hgapSum]; ring
    _ = 5 * (2 * fifteenLocalPhi) := by
      unfold fifteenLocalPhi
      ring

/-- A polar 15-cycle with pattern `(I,O,O)^5`, pairwise separation, and a
common radius for the ten outer centers satisfies the five-sector angle
budget.  The final sector uses the periodic copy of the first center at angle
`theta 0 + 2π`. -/
theorem fifteenOrderedPattern_packing_angle_budget
    (radius : Fin 15 → ℝ) (theta : Fin 15 → ℝ)
    (r₀ r₁ r₂ r₃ r₄ b : ℝ)
    (hR₀ : radius 0 = r₀)
    (hR₁ : radius 1 = b)
    (hR₂ : radius 2 = b)
    (hR₃ : radius 3 = r₁)
    (hR₄ : radius 4 = b)
    (hR₅ : radius 5 = b)
    (hR₆ : radius 6 = r₂)
    (hR₇ : radius 7 = b)
    (hR₈ : radius 8 = b)
    (hR₉ : radius 9 = r₃)
    (hR₁₀ : radius 10 = b)
    (hR₁₁ : radius 11 = b)
    (hR₁₂ : radius 12 = r₄)
    (hR₁₃ : radius 13 = b)
    (hR₁₄ : radius 14 = b)
    (hangleOrder : ∀ i j : Fin 15, i.1 < j.1 → theta i ≤ theta j)
    (hangleLo : ∀ i : Fin 15, 0 ≤ theta i)
    (hangleHi : ∀ i : Fin 15, theta i ≤ 2 * Real.pi)
    (hradiusPos : ∀ i : Fin 15, 0 < radius i)
    (hseparated : ∀ i j : Fin 15, i ≠ j →
      4 ≤ pointNorm
        ((polarPoint (radius i) (theta i)).1 -
            (polarPoint (radius j) (theta j)).1,
         (polarPoint (radius i) (theta i)).2 -
            (polarPoint (radius j) (theta j)).2) ^ 2) :
    max (fifteenTouchAngle r₀ r₁) (fifteenDetourAngle b r₀ r₁) +
      max (fifteenTouchAngle r₁ r₂) (fifteenDetourAngle b r₁ r₂) +
      max (fifteenTouchAngle r₂ r₃) (fifteenDetourAngle b r₂ r₃) +
      max (fifteenTouchAngle r₃ r₄) (fifteenDetourAngle b r₃ r₄) +
      max (fifteenTouchAngle r₄ r₀) (fifteenDetourAngle b r₄ r₀) ≤
      5 * (2 * fifteenLocalPhi) := by
  let θ₀ := theta (0 : Fin 15)
  let θ₁ := theta (1 : Fin 15)
  let θ₂ := theta (2 : Fin 15)
  let θ₃ := theta (3 : Fin 15)
  let θ₄ := theta (4 : Fin 15)
  let θ₅ := theta (5 : Fin 15)
  let θ₆ := theta (6 : Fin 15)
  let θ₇ := theta (7 : Fin 15)
  let θ₈ := theta (8 : Fin 15)
  let θ₉ := theta (9 : Fin 15)
  let θ₁₀ := theta (10 : Fin 15)
  let θ₁₁ := theta (11 : Fin 15)
  let θ₁₂ := theta (12 : Fin 15)
  let θ₁₃ := theta (13 : Fin 15)
  let θ₁₄ := theta (14 : Fin 15)
  let g₀ := θ₁ - θ₀
  let g₁ := θ₂ - θ₁
  let g₂ := θ₃ - θ₂
  let g₃ := θ₄ - θ₃
  let g₄ := θ₅ - θ₄
  let g₅ := θ₆ - θ₅
  let g₆ := θ₇ - θ₆
  let g₇ := θ₈ - θ₇
  let g₈ := θ₉ - θ₈
  let g₉ := θ₁₀ - θ₉
  let g₁₀ := θ₁₁ - θ₁₀
  let g₁₁ := θ₁₂ - θ₁₁
  let g₁₂ := θ₁₃ - θ₁₂
  let g₁₃ := θ₁₄ - θ₁₃
  let g₁₄ := θ₀ + 2 * Real.pi - θ₁₄
  have hpos₀ : 0 < r₀ := by rw [← hR₀]; exact hradiusPos 0
  have hpos₁ : 0 < r₁ := by rw [← hR₃]; exact hradiusPos 3
  have hpos₂ : 0 < r₂ := by rw [← hR₆]; exact hradiusPos 6
  have hpos₃ : 0 < r₃ := by rw [← hR₉]; exact hradiusPos 9
  have hpos₄ : 0 < r₄ := by rw [← hR₁₂]; exact hradiusPos 12
  have hposB : 0 < b := by rw [← hR₁]; exact hradiusPos 1
  have hseparation i j (hij : i ≠ j) : 4 ≤ pointNorm
      ((polarPoint (radius i) (theta i)).1 -
          (polarPoint (radius j) (theta j)).1,
       (polarPoint (radius i) (theta i)).2 -
          (polarPoint (radius j) (theta j)).2) ^ 2 :=
    hseparated i j hij
  have hpair₀₃ := hseparation (0 : Fin 15) 3 (by decide)
  have hpair₀₁ := hseparation (0 : Fin 15) 1 (by decide)
  have hpair₁₂ := hseparation (1 : Fin 15) 2 (by decide)
  have hpair₂₃ := hseparation (2 : Fin 15) 3 (by decide)
  have hpair₃₆ := hseparation (3 : Fin 15) 6 (by decide)
  have hpair₃₄ := hseparation (3 : Fin 15) 4 (by decide)
  have hpair₄₅ := hseparation (4 : Fin 15) 5 (by decide)
  have hpair₅₆ := hseparation (5 : Fin 15) 6 (by decide)
  have hpair₆₉ := hseparation (6 : Fin 15) 9 (by decide)
  have hpair₆₇ := hseparation (6 : Fin 15) 7 (by decide)
  have hpair₇₈ := hseparation (7 : Fin 15) 8 (by decide)
  have hpair₈₉ := hseparation (8 : Fin 15) 9 (by decide)
  have hpair₉₁₂ := hseparation (9 : Fin 15) 12 (by decide)
  have hpair₉₁₀ := hseparation (9 : Fin 15) 10 (by decide)
  have hpair₁₀₁₁ := hseparation (10 : Fin 15) 11 (by decide)
  have hpair₁₁₁₂ := hseparation (11 : Fin 15) 12 (by decide)
  have hpair₁₂₀ := hseparation (12 : Fin 15) 0 (by decide)
  have hpair₁₂₁₃ := hseparation (12 : Fin 15) 13 (by decide)
  have hpair₁₃₁₄ := hseparation (13 : Fin 15) 14 (by decide)
  have hpair₁₄₀ := hseparation (14 : Fin 15) 0 (by decide)
  rw [hR₀, hR₃] at hpair₀₃
  rw [hR₀, hR₁] at hpair₀₁
  rw [hR₁, hR₂] at hpair₁₂
  rw [hR₂, hR₃] at hpair₂₃
  rw [hR₃, hR₆] at hpair₃₆
  rw [hR₃, hR₄] at hpair₃₄
  rw [hR₄, hR₅] at hpair₄₅
  rw [hR₅, hR₆] at hpair₅₆
  rw [hR₆, hR₉] at hpair₆₉
  rw [hR₆, hR₇] at hpair₆₇
  rw [hR₇, hR₈] at hpair₇₈
  rw [hR₈, hR₉] at hpair₈₉
  rw [hR₉, hR₁₂] at hpair₉₁₂
  rw [hR₉, hR₁₀] at hpair₉₁₀
  rw [hR₁₀, hR₁₁] at hpair₁₀₁₁
  rw [hR₁₁, hR₁₂] at hpair₁₁₁₂
  rw [hR₁₂, hR₀] at hpair₁₂₀
  rw [hR₁₂, hR₁₃] at hpair₁₂₁₃
  rw [hR₁₃, hR₁₄] at hpair₁₃₁₄
  rw [hR₁₄, hR₀] at hpair₁₄₀
  have hpair₁₂₀' : 4 ≤ pointNorm
      ((polarPoint r₄ θ₁₂).1 -
        (polarPoint r₀ (θ₀ + 2 * Real.pi)).1,
       (polarPoint r₄ θ₁₂).2 -
        (polarPoint r₀ (θ₀ + 2 * Real.pi)).2) ^ 2 := by
    simpa [θ₀, θ₁₂, fifteenPolarPoint_add_two_pi] using hpair₁₂₀
  have hpair₁₄₀' : 4 ≤ pointNorm
      ((polarPoint b θ₁₄).1 -
        (polarPoint r₀ (θ₀ + 2 * Real.pi)).1,
       (polarPoint b θ₁₄).2 -
        (polarPoint r₀ (θ₀ + 2 * Real.pi)).2) ^ 2 := by
    simpa [θ₀, θ₁₄, fifteenPolarPoint_add_two_pi] using hpair₁₄₀
  have ho₀₁ : θ₀ ≤ θ₁ := hangleOrder 0 1 (by decide)
  have ho₁₂ : θ₁ ≤ θ₂ := hangleOrder 1 2 (by decide)
  have ho₂₃ : θ₂ ≤ θ₃ := hangleOrder 2 3 (by decide)
  have ho₃₄ : θ₃ ≤ θ₄ := hangleOrder 3 4 (by decide)
  have ho₄₅ : θ₄ ≤ θ₅ := hangleOrder 4 5 (by decide)
  have ho₅₆ : θ₅ ≤ θ₆ := hangleOrder 5 6 (by decide)
  have ho₆₇ : θ₆ ≤ θ₇ := hangleOrder 6 7 (by decide)
  have ho₇₈ : θ₇ ≤ θ₈ := hangleOrder 7 8 (by decide)
  have ho₈₉ : θ₈ ≤ θ₉ := hangleOrder 8 9 (by decide)
  have ho₉₁₀ : θ₉ ≤ θ₁₀ := hangleOrder 9 10 (by decide)
  have ho₁₀₁₁ : θ₁₀ ≤ θ₁₁ := hangleOrder 10 11 (by decide)
  have ho₁₁₁₂ : θ₁₁ ≤ θ₁₂ := hangleOrder 11 12 (by decide)
  have ho₁₂₁₃ : θ₁₂ ≤ θ₁₃ := hangleOrder 12 13 (by decide)
  have ho₁₃₁₄ : θ₁₃ ≤ θ₁₄ := hangleOrder 13 14 (by decide)
  have ho₀₃ : θ₀ ≤ θ₃ := le_trans ho₀₁ (le_trans ho₁₂ ho₂₃)
  have ho₀₁₂ : θ₀ ≤ θ₁₂ := hangleOrder 0 12 (by decide)
  have ho₀₁₄ : θ₀ ≤ θ₁₄ := hangleOrder 0 14 (by decide)
  have ho₃₆ : θ₃ ≤ θ₆ := le_trans ho₃₄ (le_trans ho₄₅ ho₅₆)
  have ho₆₉ : θ₆ ≤ θ₉ := le_trans ho₆₇ (le_trans ho₇₈ ho₈₉)
  have ho₉₁₂ : θ₉ ≤ θ₁₂ := le_trans ho₉₁₀ (le_trans ho₁₀₁₁ ho₁₁₁₂)
  have ho₁₂₁₄ : θ₁₂ ≤ θ₁₄ := le_trans ho₁₂₁₃ ho₁₃₁₄
  have hsector₀ : max (fifteenTouchAngle r₀ r₁)
      (fifteenDetourAngle b r₀ r₁) ≤ g₀ + g₁ + g₂ := by
    dsimp [g₀, g₁, g₂]
    exact fifteenLocalSector_max_le_gap hpos₀ hposB hpos₁
      (by dsimp [θ₀, θ₁]; linarith [ho₀₁])
      (by dsimp [θ₀, θ₁]; linarith [hangleHi 1, hangleLo 0])
      (by dsimp [θ₁, θ₂]; linarith [ho₁₂])
      (by dsimp [θ₁, θ₂]; linarith [hangleHi 2, hangleLo 1])
      (by dsimp [θ₂, θ₃]; linarith [ho₂₃])
      (by dsimp [θ₂, θ₃]; linarith [hangleHi 3, hangleLo 2])
      (by dsimp [θ₀, θ₃]; linarith [hangleHi 3, hangleLo 0])
      hpair₀₃ hpair₀₁ hpair₁₂ hpair₂₃
  have hsector₁ : max (fifteenTouchAngle r₁ r₂)
      (fifteenDetourAngle b r₁ r₂) ≤ g₃ + g₄ + g₅ := by
    dsimp [g₃, g₄, g₅]
    exact fifteenLocalSector_max_le_gap hpos₁ hposB hpos₂
      (by dsimp [θ₃, θ₄]; linarith [ho₃₄])
      (by dsimp [θ₃, θ₄]; linarith [hangleHi 4, hangleLo 3])
      (by dsimp [θ₄, θ₅]; linarith [ho₄₅])
      (by dsimp [θ₄, θ₅]; linarith [hangleHi 5, hangleLo 4])
      (by dsimp [θ₅, θ₆]; linarith [ho₅₆])
      (by dsimp [θ₅, θ₆]; linarith [hangleHi 6, hangleLo 5])
      (by dsimp [θ₃, θ₆]; linarith [hangleHi 6, hangleLo 3])
      hpair₃₆ hpair₃₄ hpair₄₅ hpair₅₆
  have hsector₂ : max (fifteenTouchAngle r₂ r₃)
      (fifteenDetourAngle b r₂ r₃) ≤ g₆ + g₇ + g₈ := by
    dsimp [g₆, g₇, g₈]
    exact fifteenLocalSector_max_le_gap hpos₂ hposB hpos₃
      (by dsimp [θ₆, θ₇]; linarith [ho₆₇])
      (by dsimp [θ₆, θ₇]; linarith [hangleHi 7, hangleLo 6])
      (by dsimp [θ₇, θ₈]; linarith [ho₇₈])
      (by dsimp [θ₇, θ₈]; linarith [hangleHi 8, hangleLo 7])
      (by dsimp [θ₈, θ₉]; linarith [ho₈₉])
      (by dsimp [θ₈, θ₉]; linarith [hangleHi 9, hangleLo 8])
      (by dsimp [θ₆, θ₉]; linarith [hangleHi 9, hangleLo 6])
      hpair₆₉ hpair₆₇ hpair₇₈ hpair₈₉
  have hsector₃ : max (fifteenTouchAngle r₃ r₄)
      (fifteenDetourAngle b r₃ r₄) ≤ g₉ + g₁₀ + g₁₁ := by
    dsimp [g₉, g₁₀, g₁₁]
    exact fifteenLocalSector_max_le_gap hpos₃ hposB hpos₄
      (by dsimp [θ₉, θ₁₀]; linarith [ho₉₁₀])
      (by dsimp [θ₉, θ₁₀]; linarith [hangleHi 10, hangleLo 9])
      (by dsimp [θ₁₀, θ₁₁]; linarith [ho₁₀₁₁])
      (by dsimp [θ₁₀, θ₁₁]; linarith [hangleHi 11, hangleLo 10])
      (by dsimp [θ₁₁, θ₁₂]; linarith [ho₁₁₁₂])
      (by dsimp [θ₁₁, θ₁₂]; linarith [hangleHi 12, hangleLo 11])
      (by dsimp [θ₉, θ₁₂]; linarith [hangleHi 12, hangleLo 9])
      hpair₉₁₂ hpair₉₁₀ hpair₁₀₁₁ hpair₁₁₁₂
  have hsector₄ : max (fifteenTouchAngle r₄ r₀)
      (fifteenDetourAngle b r₄ r₀) ≤ g₁₂ + g₁₃ + g₁₄ := by
    dsimp [g₁₂, g₁₃, g₁₄]
    exact fifteenLocalSector_max_le_gap hpos₄ hposB hpos₀
      (by dsimp [θ₁₂, θ₁₃]; linarith [ho₁₂₁₃])
      (by dsimp [θ₁₂, θ₁₃]; linarith [hangleHi 13, hangleLo 12])
      (by dsimp [θ₁₃, θ₁₄]; linarith [ho₁₃₁₄])
      (by dsimp [θ₁₃, θ₁₄]; linarith [hangleHi 14, hangleLo 13])
      (by dsimp [θ₁₄]; linarith [hangleHi 14, hangleLo 0])
      (by dsimp [θ₀, θ₁₄]; linarith [hangleHi 0, hangleLo 14, ho₀₁₄])
      (by dsimp [θ₀, θ₁₂]; linarith [hangleHi 0, hangleLo 12, ho₀₁₂])
      hpair₁₂₀' hpair₁₂₁₃ hpair₁₃₁₄ hpair₁₄₀'
  have hgapSum : g₀ + g₁ + g₂ + g₃ + g₄ + g₅ + g₆ + g₇ + g₈ + g₉ +
      g₁₀ + g₁₁ + g₁₂ + g₁₃ + g₁₄ = 2 * Real.pi := by
    dsimp [g₀, g₁, g₂, g₃, g₄, g₅, g₆, g₇, g₈, g₉, g₁₀,
      g₁₁, g₁₂, g₁₃, g₁₄, θ₀, θ₁, θ₂, θ₃, θ₄, θ₅, θ₆, θ₇,
      θ₈, θ₉, θ₁₀, θ₁₁, θ₁₂, θ₁₃, θ₁₄]
    ring
  exact fifteenLocalAngleBudget_of_sector_bounds r₀ r₁ r₂ r₃ r₄ b
    g₀ g₁ g₂ g₃ g₄ g₅ g₆ g₇ g₈ g₉ g₁₀ g₁₁ g₁₂ g₁₃ g₁₄
    hsector₀ hsector₁ hsector₂ hsector₃ hsector₄ hgapSum

end CirclePacking
