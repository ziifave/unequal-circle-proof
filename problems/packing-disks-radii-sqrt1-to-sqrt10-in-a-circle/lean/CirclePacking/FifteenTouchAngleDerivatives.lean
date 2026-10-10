import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv

/-! Differentiation rules for the cosine-rule touch angle used in the local
15-disk barrier. Interval estimates for these formulas are a separate exact
rational-arithmetic task. -/

namespace CirclePacking

noncomputable def fifteenAngleCosineArgument (x y : ℝ) : ℝ :=
  (x ^ 2 + y ^ 2 - 4) / (2 * x * y)

noncomputable def fifteenTouchAngle (x y : ℝ) : ℝ :=
  Real.arccos (fifteenAngleCosineArgument x y)

/-- Angular cost of the route from one inner center to the next through two
outer centers on the pushed-out circle of center radius `b`. -/
noncomputable def fifteenDetourAngle (b x y : ℝ) : ℝ :=
  fifteenTouchAngle x b + fifteenTouchAngle b b + fifteenTouchAngle y b

theorem fifteenAngleCosineArgument_symm (x y : ℝ) :
    fifteenAngleCosineArgument x y = fifteenAngleCosineArgument y x := by
  unfold fifteenAngleCosineArgument
  ring

theorem fifteenAngleCosineArgument_hasDerivAt_left
    (x y : ℝ) (hx : x ≠ 0) (hy : y ≠ 0) :
    HasDerivAt (fun t : ℝ => fifteenAngleCosineArgument t y)
      ((x ^ 2 - y ^ 2 + 4) / (2 * x ^ 2 * y)) x := by
  have hnum : HasDerivAt (fun t : ℝ => t ^ 2 + y ^ 2 - 4) (2 * x) x := by
    convert ((hasDerivAt_id x).pow 2).add_const (y ^ 2 - 4) using 1
    · ext t
      simp [id]
      ring
    · simp
  have hden : HasDerivAt (fun t : ℝ => 2 * t * y) (2 * y) x := by
    convert (hasDerivAt_id x).const_mul (2 * y) using 1
    · ext t
      simp [id]
      ring
    · simp [mul_comm, mul_left_comm]
  have hden0 : 2 * x * y ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num) hx) hy
  have hq := hnum.div hden hden0
  have hq' : deriv (fun t : ℝ => (t ^ 2 + y ^ 2 - 4) / (2 * t * y)) x =
      (x ^ 2 - y ^ 2 + 4) / (2 * x ^ 2 * y) := by
    have hderiv := hq.deriv
    convert hderiv using 1 <;> field_simp <;> ring
  have hqDeriv :
      (2 * x * (2 * x * y) - (x ^ 2 + y ^ 2 - 4) * (2 * y)) /
          (2 * x * y) ^ 2 =
        (x ^ 2 - y ^ 2 + 4) / (2 * x ^ 2 * y) := by
    calc
      _ = deriv (fun t : ℝ => (t ^ 2 + y ^ 2 - 4) / (2 * t * y)) x := hq.deriv.symm
      _ = _ := hq'
  have hqFinal := hq.congr_deriv hqDeriv
  have hqManual : HasDerivAt
      (fun t : ℝ => (t ^ 2 + y ^ 2 - 4) / (2 * t * y))
      ((x ^ 2 - y ^ 2 + 4) / (2 * x ^ 2 * y)) x := by
    convert hqFinal using 1
  exact hqManual.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => by
    simp [fifteenAngleCosineArgument])

theorem fifteenTouchAngle_hasDerivAt_left
    (x y : ℝ) (hx : x ≠ 0) (hy : y ≠ 0)
    (hminus : fifteenAngleCosineArgument x y ≠ -1)
    (hplus : fifteenAngleCosineArgument x y ≠ 1) :
    HasDerivAt (fun t : ℝ => fifteenTouchAngle t y)
      (-(1 / Real.sqrt (1 - fifteenAngleCosineArgument x y ^ 2)) *
        ((x ^ 2 - y ^ 2 + 4) / (2 * x ^ 2 * y))) x := by
  have hcap := fifteenAngleCosineArgument_hasDerivAt_left x y hx hy
  have harccos := Real.hasDerivAt_arccos hminus hplus
  change HasDerivAt
    (Real.arccos ∘ fun t : ℝ => fifteenAngleCosineArgument t y)
    _ x
  exact harccos.comp x hcap

theorem fifteenTouchAngle_hasDerivAt_right
    (x y : ℝ) (hx : x ≠ 0) (hy : y ≠ 0)
    (hminus : fifteenAngleCosineArgument y x ≠ -1)
    (hplus : fifteenAngleCosineArgument y x ≠ 1) :
    HasDerivAt (fun t : ℝ => fifteenTouchAngle x t)
      (-(1 / Real.sqrt (1 - fifteenAngleCosineArgument y x ^ 2)) *
        ((y ^ 2 - x ^ 2 + 4) / (2 * y ^ 2 * x))) y := by
  have hleft := fifteenTouchAngle_hasDerivAt_left y x hy hx hminus hplus
  apply hleft.congr_of_eventuallyEq
  filter_upwards with t
  unfold fifteenTouchAngle
  rw [fifteenAngleCosineArgument_symm]

/-- Varying the first inner radius in the detour route differentiates only its
first contact angle; the two remaining angles are constant in that variable. -/
theorem fifteenDetourAngle_hasDerivAt_left
    (b x y : ℝ) (hx : x ≠ 0) (hb : b ≠ 0)
    (hminus : fifteenAngleCosineArgument x b ≠ -1)
    (hplus : fifteenAngleCosineArgument x b ≠ 1) :
    HasDerivAt (fun t : ℝ => fifteenDetourAngle b t y)
      (-(1 / Real.sqrt (1 - fifteenAngleCosineArgument x b ^ 2)) *
        ((x ^ 2 - b ^ 2 + 4) / (2 * x ^ 2 * b))) x := by
  simpa [fifteenDetourAngle, add_assoc] using
    (fifteenTouchAngle_hasDerivAt_left x b hx hb hminus hplus).add_const
      (fifteenTouchAngle b b + fifteenTouchAngle y b)

/-- Varying the second inner radius in the detour route differentiates only
its final contact angle. -/
theorem fifteenDetourAngle_hasDerivAt_right
    (b x y : ℝ) (hy : y ≠ 0) (hb : b ≠ 0)
    (hminus : fifteenAngleCosineArgument y b ≠ -1)
    (hplus : fifteenAngleCosineArgument y b ≠ 1) :
    HasDerivAt (fun t : ℝ => fifteenDetourAngle b x t)
      (-(1 / Real.sqrt (1 - fifteenAngleCosineArgument y b ^ 2)) *
        ((y ^ 2 - b ^ 2 + 4) / (2 * y ^ 2 * b))) y := by
  simpa [fifteenDetourAngle, add_assoc] using
    (fifteenTouchAngle_hasDerivAt_left y b hy hb hminus hplus).const_add
      (fifteenTouchAngle x b + fifteenTouchAngle b b)

end CirclePacking
