import CirclePacking.FifteenLocalBarrierRigidity
import CirclePacking.FifteenTouchAngleTaylor

/-! Pairwise Taylor estimates needed by the five-sector local barrier. The
remaining numerical inputs are the certified smoothness and second-derivative
bounds for the two angle routes. -/

namespace CirclePacking

noncomputable def fifteenDirectSlopeLeft (a : ℝ) : ℝ :=
  -(1 / Real.sqrt (1 - fifteenAngleCosineArgument a a ^ 2)) *
    ((a ^ 2 - a ^ 2 + 4) / (2 * a ^ 2 * a))

noncomputable def fifteenDirectSlopeRight (a : ℝ) : ℝ :=
  -(1 / Real.sqrt (1 - fifteenAngleCosineArgument a a ^ 2)) *
    ((a ^ 2 - a ^ 2 + 4) / (2 * a * a ^ 2))

noncomputable def fifteenDetourSlope (a b : ℝ) : ℝ :=
  -(1 / Real.sqrt (1 - fifteenAngleCosineArgument a b ^ 2)) *
    ((a ^ 2 - b ^ 2 + 4) / (2 * a ^ 2 * b))

/-- The direct inner-inner route has the local Taylor lower bound used by the
algebraic five-cycle rigidity theorem, once its two partial slopes and segment
Hessian bound are certified. -/
theorem fifteenLocalDirectPair_taylor_bound
    (a base c dx dy : ℝ) (ha : a ≠ 0)
    (hminus : fifteenAngleCosineArgument a a ≠ -1)
    (hplus : fifteenAngleCosineArgument a a ≠ 1)
    (hbase : fifteenTouchAngle a a = base)
    (hslopeLeft : fifteenDirectSlopeLeft a = -c)
    (hslopeRight : fifteenDirectSlopeRight a = -c)
    (hcont : ContDiffOn ℝ 2
      (fun t : ℝ => fifteenTouchAngle (a + t * dx) (a + t * dy))
      (Set.uIcc 0 1))
    (hsecond : ∀ t ∈ Set.uIcc 0 1,
      |iteratedDeriv 2
        (fun s : ℝ => fifteenTouchAngle (a + s * dx) (a + s * dy)) t| ≤
          5 * (dx ^ 2 + dy ^ 2)) :
    base - c * (dx + dy) - (5 / 2 : ℝ) * (dx ^ 2 + dy ^ 2) ≤
      fifteenTouchAngle (a + dx) (a + dy) := by
  have hTaylor := fifteenTouchAngle_taylor_lower_along_segment
    a a dx dy (5 * (dx ^ 2 + dy ^ 2)) ha ha hminus hplus hcont hsecond
  have hlinear :
      -((1 / Real.sqrt (1 - fifteenAngleCosineArgument a a ^ 2)) *
        (((a ^ 2 - a ^ 2 + 4) / (2 * a ^ 2 * a)) * dx +
          ((a ^ 2 - a ^ 2 + 4) / (2 * a * a ^ 2)) * dy)) =
        -c * (dx + dy) := by
    calc
      _ = fifteenDirectSlopeLeft a * dx +
          fifteenDirectSlopeRight a * dy := by
            dsimp [fifteenDirectSlopeLeft, fifteenDirectSlopeRight]
            ring
      _ = -c * (dx + dy) := by rw [hslopeLeft, hslopeRight]; ring
  have hquad :
      (5 / 2 : ℝ) * (dx ^ 2 + dy ^ 2) =
        (5 * (dx ^ 2 + dy ^ 2)) / 2 := by ring
  have hrewrite :
      base - c * (dx + dy) - (5 / 2 : ℝ) * (dx ^ 2 + dy ^ 2) =
        fifteenTouchAngle a a -
          (1 / Real.sqrt (1 - fifteenAngleCosineArgument a a ^ 2)) *
            (((a ^ 2 - a ^ 2 + 4) / (2 * a ^ 2 * a)) * dx +
              ((a ^ 2 - a ^ 2 + 4) / (2 * a * a ^ 2)) * dy) -
          (5 * (dx ^ 2 + dy ^ 2)) / 2 := by
    rw [hbase, hquad]
    linarith [hlinear]
  rw [hrewrite]
  exact hTaylor

/-- The outer-center detour has the corresponding increasing linear term. -/
theorem fifteenLocalDetourPair_taylor_bound
    (a b base d dx dy : ℝ) (ha : a ≠ 0) (hb : b ≠ 0)
    (hminus : fifteenAngleCosineArgument a b ≠ -1)
    (hplus : fifteenAngleCosineArgument a b ≠ 1)
    (hbase : fifteenDetourAngle b a a = base)
    (hslope : fifteenDetourSlope a b = d)
    (hcont : ContDiffOn ℝ 2
      (fun t : ℝ => fifteenDetourAngleAlongSegment b a a dx dy t)
      (Set.uIcc 0 1))
    (hsecond : ∀ t ∈ Set.uIcc 0 1,
      |iteratedDeriv 2
        (fun s : ℝ => fifteenDetourAngleAlongSegment b a a dx dy s) t| ≤
          5 * (dx ^ 2 + dy ^ 2)) :
    base + d * (dx + dy) - (5 / 2 : ℝ) * (dx ^ 2 + dy ^ 2) ≤
      fifteenDetourAngle b (a + dx) (a + dy) := by
  have hTaylor := fifteenDetourAngle_taylor_lower_along_segment
    b a a dx dy (5 * (dx ^ 2 + dy ^ 2)) hb ha ha
    hminus hplus hminus hplus hcont hsecond
  have hlinear :
      -(1 / Real.sqrt (1 - fifteenAngleCosineArgument a b ^ 2)) *
          ((a ^ 2 - b ^ 2 + 4) / (2 * a ^ 2 * b)) * dx +
        -(1 / Real.sqrt (1 - fifteenAngleCosineArgument a b ^ 2)) *
          ((a ^ 2 - b ^ 2 + 4) / (2 * a ^ 2 * b)) * dy =
        d * (dx + dy) := by
    calc
      _ = fifteenDetourSlope a b * dx + fifteenDetourSlope a b * dy := by
        dsimp [fifteenDetourSlope]
      _ = d * (dx + dy) := by rw [hslope]; ring
  have hquad :
      (5 / 2 : ℝ) * (dx ^ 2 + dy ^ 2) =
        (5 * (dx ^ 2 + dy ^ 2)) / 2 := by ring
  have hrewrite :
      base + d * (dx + dy) - (5 / 2 : ℝ) * (dx ^ 2 + dy ^ 2) =
        fifteenDetourAngle b a a -
          (1 / Real.sqrt (1 - fifteenAngleCosineArgument a b ^ 2)) *
            ((a ^ 2 - b ^ 2 + 4) / (2 * a ^ 2 * b)) * dx -
          (1 / Real.sqrt (1 - fifteenAngleCosineArgument a b ^ 2)) *
            ((a ^ 2 - b ^ 2 + 4) / (2 * a ^ 2 * b)) * dy -
          (5 * (dx ^ 2 + dy ^ 2)) / 2 := by
    rw [hbase, hquad]
    linarith [hlinear]
  rw [hrewrite]
  exact hTaylor

end CirclePacking
