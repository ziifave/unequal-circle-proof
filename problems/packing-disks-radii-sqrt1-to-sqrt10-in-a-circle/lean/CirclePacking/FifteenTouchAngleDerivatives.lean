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

noncomputable def fifteenDetourAngleAlongSegment
    (b x y dx dy t : ℝ) : ℝ :=
  fifteenDetourAngle b (x + t * dx) (y + t * dy)

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

/-- First variation of the contact angle when both radii move along a line.
The formula is the sum of the two partial derivatives, with no symmetry
assumption on the direction `(dx, dy)`. -/
theorem fifteenTouchAngleAlongSegment_hasDerivAt
    (x y dx dy : ℝ) (hx : x ≠ 0) (hy : y ≠ 0)
    (hminus : fifteenAngleCosineArgument x y ≠ -1)
    (hplus : fifteenAngleCosineArgument x y ≠ 1) :
    HasDerivAt
      (fun t : ℝ => fifteenTouchAngle (x + t * dx) (y + t * dy))
      (-(1 / Real.sqrt (1 - fifteenAngleCosineArgument x y ^ 2)) *
        (((x ^ 2 - y ^ 2 + 4) / (2 * x ^ 2 * y)) * dx +
          ((y ^ 2 - x ^ 2 + 4) / (2 * x * y ^ 2)) * dy)) 0 := by
  let X : ℝ → ℝ := fun t => x + t * dx
  let Y : ℝ → ℝ := fun t => y + t * dy
  have hX : HasDerivAt X dx 0 := by
    convert ((hasDerivAt_id 0).const_mul dx).const_add x using 1
    · ext t
      simp [X]
      ring
    · simp
  have hY : HasDerivAt Y dy 0 := by
    convert ((hasDerivAt_id 0).const_mul dy).const_add y using 1
    · ext t
      simp [Y]
      ring
    · simp
  have hnum : HasDerivAt (fun t : ℝ => X t ^ 2 + Y t ^ 2 - 4)
      (2 * x * dx + 2 * y * dy) 0 := by
    have h := ((hX.pow 2).add (hY.pow 2)).sub_const 4
    convert h using 1 <;> simp [X, Y]
  have hden : HasDerivAt (fun t : ℝ => 2 * X t * Y t)
      (2 * (dx * y + x * dy)) 0 := by
    have h := (hX.mul hY).const_mul 2
    convert h using 1
    · ext t
      simp [X, Y]
      ring
    · simp [X, Y]
  have hX0 : X 0 = x := by simp [X]
  have hY0 : Y 0 = y := by simp [Y]
  have hden0 : 2 * X 0 * Y 0 ≠ 0 := by
    rw [hX0, hY0]
    exact mul_ne_zero (mul_ne_zero (by norm_num) hx) hy
  have hquotient := hnum.div hden hden0
  have hquotientDeriv :
      ((2 * x * dx + 2 * y * dy) * (2 * X 0 * Y 0) -
        (X 0 ^ 2 + Y 0 ^ 2 - 4) * (2 * (dx * y + x * dy))) /
          (2 * X 0 * Y 0) ^ 2 =
        ((x ^ 2 - y ^ 2 + 4) / (2 * x ^ 2 * y)) * dx +
          ((y ^ 2 - x ^ 2 + 4) / (2 * x * y ^ 2)) * dy := by
    rw [hX0, hY0]
    field_simp [hx, hy]
    ring
  have hquotient' := hquotient.congr_deriv hquotientDeriv
  have hquotientPoint : HasDerivAt
      (fun t : ℝ => (X t ^ 2 + Y t ^ 2 - 4) / (2 * X t * Y t))
      (((x ^ 2 - y ^ 2 + 4) / (2 * x ^ 2 * y)) * dx +
        ((y ^ 2 - x ^ 2 + 4) / (2 * x * y ^ 2)) * dy) 0 := by
    convert hquotient' using 1
  have hquotientAt0 :
      (X 0 ^ 2 + Y 0 ^ 2 - 4) / (2 * X 0 * Y 0) =
        fifteenAngleCosineArgument x y := by
    rw [hX0, hY0]
    rfl
  have hminus' :
      (X 0 ^ 2 + Y 0 ^ 2 - 4) / (2 * X 0 * Y 0) ≠ -1 := by
    rw [hquotientAt0]
    exact hminus
  have hplus' :
      (X 0 ^ 2 + Y 0 ^ 2 - 4) / (2 * X 0 * Y 0) ≠ 1 := by
    rw [hquotientAt0]
    exact hplus
  have hangle := (Real.hasDerivAt_arccos hminus' hplus').comp 0 hquotientPoint
  change HasDerivAt
    (Real.arccos ∘ fun t : ℝ =>
      (X t ^ 2 + Y t ^ 2 - 4) / (2 * X t * Y t))
    _ 0 at hangle
  convert hangle using 1
  · ext t
    simp [fifteenTouchAngle, fifteenAngleCosineArgument, X, Y]
  · rw [← hquotientAt0]

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

/-- First variation of the two-outer-center route when both endpoint radii
move. Its slope is the sum of the endpoint contact-angle slopes. -/
theorem fifteenDetourAngleAlongSegment_hasDerivAt
    (b x y dx dy : ℝ) (hb : b ≠ 0) (hx : x ≠ 0) (hy : y ≠ 0)
    (hminusX : fifteenAngleCosineArgument x b ≠ -1)
    (hplusX : fifteenAngleCosineArgument x b ≠ 1)
    (hminusY : fifteenAngleCosineArgument y b ≠ -1)
    (hplusY : fifteenAngleCosineArgument y b ≠ 1) :
    HasDerivAt
      (fun t : ℝ => fifteenDetourAngleAlongSegment b x y dx dy t)
      (-(1 / Real.sqrt (1 - fifteenAngleCosineArgument x b ^ 2)) *
          ((x ^ 2 - b ^ 2 + 4) / (2 * x ^ 2 * b)) * dx +
        -(1 / Real.sqrt (1 - fifteenAngleCosineArgument y b ^ 2)) *
          ((y ^ 2 - b ^ 2 + 4) / (2 * y ^ 2 * b)) * dy) 0 := by
  have hfirst := fifteenTouchAngleAlongSegment_hasDerivAt x b dx 0 hx hb
    hminusX hplusX
  have hfirst' : HasDerivAt
      (fun t : ℝ => fifteenTouchAngle (x + t * dx) b)
      (-(1 / Real.sqrt (1 - fifteenAngleCosineArgument x b ^ 2)) *
        ((x ^ 2 - b ^ 2 + 4) / (2 * x ^ 2 * b)) * dx) 0 := by
    convert hfirst using 1 <;> simp [mul_assoc]
  have hsecond := fifteenTouchAngleAlongSegment_hasDerivAt y b dy 0 hy hb
    hminusY hplusY
  have hsecond' : HasDerivAt
      (fun t : ℝ => fifteenTouchAngle (y + t * dy) b)
      (-(1 / Real.sqrt (1 - fifteenAngleCosineArgument y b ^ 2)) *
        ((y ^ 2 - b ^ 2 + 4) / (2 * y ^ 2 * b)) * dy) 0 := by
    convert hsecond using 1 <;> simp [mul_assoc]
  have hsum := (hfirst'.add_const (fifteenTouchAngle b b)).add hsecond'
  convert hsum using 1
  ext t
  simp [fifteenDetourAngleAlongSegment, fifteenDetourAngle]

end CirclePacking
