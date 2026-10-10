import CirclePacking.FifteenLocalTaylor
import CirclePacking.FifteenTouchAngleDerivatives

/-! Taylor lower bounds for the two angular routes in the fifteen-disk local
barrier. The analytic interval estimates are supplied as explicit hypotheses;
this file connects those estimates to the actual contact-angle functions. -/

namespace CirclePacking

open Set

/-- A certified second-derivative bound on the straight radial segment gives
the first-order Taylor lower bound for the direct inner-inner contact angle. -/
theorem fifteenTouchAngle_taylor_lower_along_segment
    (x y dx dy M : ℝ) (hx : x ≠ 0) (hy : y ≠ 0)
    (hminus : fifteenAngleCosineArgument x y ≠ -1)
    (hplus : fifteenAngleCosineArgument x y ≠ 1)
    (hcont : ContDiffOn ℝ 2
      (fun t : ℝ => fifteenTouchAngle (x + t * dx) (y + t * dy))
      (uIcc 0 1))
    (hsecond : ∀ t ∈ uIcc 0 1,
      |iteratedDeriv 2
        (fun s : ℝ => fifteenTouchAngle (x + s * dx) (y + s * dy)) t| ≤ M) :
    fifteenTouchAngle (x + dx) (y + dy) ≥
      fifteenTouchAngle x y -
        (1 / Real.sqrt (1 - fifteenAngleCosineArgument x y ^ 2)) *
          (((x ^ 2 - y ^ 2 + 4) / (2 * x ^ 2 * y)) * dx +
            ((y ^ 2 - x ^ 2 + 4) / (2 * x * y ^ 2)) * dy) - M / 2 := by
  let g : ℝ → ℝ := fun t => fifteenTouchAngle (x + t * dx) (y + t * dy)
  let slope : ℝ :=
    -(1 / Real.sqrt (1 - fifteenAngleCosineArgument x y ^ 2)) *
      (((x ^ 2 - y ^ 2 + 4) / (2 * x ^ 2 * y)) * dx +
        ((y ^ 2 - x ^ 2 + 4) / (2 * x * y ^ 2)) * dy)
  have hgDeriv : HasDerivAt g slope 0 := by
    simpa [g, slope] using
      fifteenTouchAngleAlongSegment_hasDerivAt x y dx dy hx hy hminus hplus
  have hgCont : ContDiffOn ℝ 2 g (uIcc 0 1) := by
    simpa [g] using hcont
  have hgSecond : ∀ t ∈ uIcc 0 1, |iteratedDeriv 2 g t| ≤ M := by
    simpa [g] using hsecond
  have hTaylor := fifteen_taylor_lower_of_second_derivative_bound
    g 0 1 slope M (by norm_num) hgCont hgDeriv hgSecond
  simpa [g, slope] using hTaylor

/-- The same Taylor bridge for the route through two outer centers. The
constant outer-outer angle contributes no first-order term. -/
theorem fifteenDetourAngle_taylor_lower_along_segment
    (b x y dx dy M : ℝ) (hb : b ≠ 0) (hx : x ≠ 0) (hy : y ≠ 0)
    (hminusX : fifteenAngleCosineArgument x b ≠ -1)
    (hplusX : fifteenAngleCosineArgument x b ≠ 1)
    (hminusY : fifteenAngleCosineArgument y b ≠ -1)
    (hplusY : fifteenAngleCosineArgument y b ≠ 1)
    (hcont : ContDiffOn ℝ 2
      (fun t : ℝ => fifteenDetourAngleAlongSegment b x y dx dy t)
      (uIcc 0 1))
    (hsecond : ∀ t ∈ uIcc 0 1,
      |iteratedDeriv 2
        (fun s : ℝ => fifteenDetourAngleAlongSegment b x y dx dy s) t| ≤ M) :
    fifteenDetourAngle b (x + dx) (y + dy) ≥
      fifteenDetourAngle b x y -
        (1 / Real.sqrt (1 - fifteenAngleCosineArgument x b ^ 2)) *
          ((x ^ 2 - b ^ 2 + 4) / (2 * x ^ 2 * b)) * dx -
        (1 / Real.sqrt (1 - fifteenAngleCosineArgument y b ^ 2)) *
          ((y ^ 2 - b ^ 2 + 4) / (2 * y ^ 2 * b)) * dy - M / 2 := by
  let g : ℝ → ℝ := fun t => fifteenDetourAngleAlongSegment b x y dx dy t
  let slope : ℝ :=
    -(1 / Real.sqrt (1 - fifteenAngleCosineArgument x b ^ 2)) *
        ((x ^ 2 - b ^ 2 + 4) / (2 * x ^ 2 * b)) * dx +
      -(1 / Real.sqrt (1 - fifteenAngleCosineArgument y b ^ 2)) *
        ((y ^ 2 - b ^ 2 + 4) / (2 * y ^ 2 * b)) * dy
  have hgDeriv : HasDerivAt g slope 0 := by
    simpa [g, slope] using
      fifteenDetourAngleAlongSegment_hasDerivAt b x y dx dy hb hx hy
        hminusX hplusX hminusY hplusY
  have hgCont : ContDiffOn ℝ 2 g (uIcc 0 1) := by
    simpa [g] using hcont
  have hgSecond : ∀ t ∈ uIcc 0 1, |iteratedDeriv 2 g t| ≤ M := by
    simpa [g] using hsecond
  have hTaylor := fifteen_taylor_lower_of_second_derivative_bound
    g 0 1 slope M (by norm_num) hgCont hgDeriv hgSecond
  have hTaylor' : g 0 + slope ≤ g 1 + M / 2 := by linarith [hTaylor]
  have hg0 : g 0 = fifteenDetourAngle b x y := by
    simp [g, fifteenDetourAngleAlongSegment, fifteenDetourAngle]
  have hg1 : g 1 = fifteenDetourAngle b (x + dx) (y + dy) := by
    simp [g, fifteenDetourAngleAlongSegment, fifteenDetourAngle]
  rw [hg0, hg1] at hTaylor'
  dsimp [slope] at hTaylor'
  linarith

end CirclePacking
