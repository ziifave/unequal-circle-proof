import CirclePacking.FifteenPackingPolarCoordinates
import CirclePacking.FifteenCandidateDetour

/-! Reusable geometry for formalizing the explicit fivefold-symmetric
15-disk construction.  The candidate contact-angle identities are already
available; this file turns a lower bound on a polar gap into the corresponding
Euclidean separation inequality. -/

namespace CirclePacking

/-- If the smaller polar gap is at least the cosine-rule touch angle, the
centers are separated by at least the prescribed distance.  The range premise
ensures `arccos` is an actual inverse of cosine at the contact argument. -/
theorem fifteenPolarPair_separated_of_touchAngle_le_gap
    (a b alpha beta : ℝ)
    (ha : 0 < a) (hb : 0 < b)
    (hgapPi : beta - alpha ≤ Real.pi)
    (hangle : fifteenTouchAngle a b ≤ beta - alpha)
    (hargLo : -1 ≤ fifteenAngleCosineArgument a b)
    (hargHi : fifteenAngleCosineArgument a b ≤ 1) :
    4 ≤ pointNorm
      ((polarPoint a alpha).1 - (polarPoint b beta).1,
       (polarPoint a alpha).2 - (polarPoint b beta).2) ^ 2 := by
  have hcosGap : Real.cos (beta - alpha) ≤
      Real.cos (fifteenTouchAngle a b) :=
    Real.cos_le_cos_of_nonneg_of_le_pi (Real.arccos_nonneg _)
      hgapPi hangle
  rw [fifteenPolarPair_distance_sq]
  unfold fifteenTouchAngle at hcosGap
  rw [Real.cos_arccos hargLo hargHi] at hcosGap
  unfold fifteenAngleCosineArgument at hcosGap
  have hab : 0 < 2 * a * b := by positivity
  have hscaled := mul_le_mul_of_nonneg_left hcosGap (le_of_lt hab)
  have hcancel : 2 * a * b *
      ((a ^ 2 + b ^ 2 - 4) / (2 * a * b)) =
        a ^ 2 + b ^ 2 - 4 := by
    field_simp [ne_of_gt hab]
  rw [hcancel] at hscaled
  have hcosEq : Real.cos (alpha - beta) = Real.cos (beta - alpha) := by
    rw [show alpha - beta = -(beta - alpha) by ring, Real.cos_neg]
  rw [hcosEq]
  nlinarith [hscaled]

/-- Candidate inner centers separated by their regular-pentagon angular gap. -/
theorem fifteenCandidateInnerPair_separated_of_gap
    (alpha beta : ℝ)
    (hgap : 2 * fifteenLocalPhi ≤ beta - alpha)
    (hgapPi : beta - alpha ≤ Real.pi) :
    4 ≤ pointNorm
      ((polarPoint fifteenCandidateInnerRadius alpha).1 -
          (polarPoint fifteenCandidateInnerRadius beta).1,
       (polarPoint fifteenCandidateInnerRadius alpha).2 -
          (polarPoint fifteenCandidateInnerRadius beta).2) ^ 2 := by
  have hangle : fifteenTouchAngle fifteenCandidateInnerRadius
      fifteenCandidateInnerRadius ≤ beta - alpha := by
    rw [fifteenCandidateDirectAngle_eq]
    exact hgap
  have hrange := Real.cos_mem_Icc (2 * fifteenLocalPhi)
  exact fifteenPolarPair_separated_of_touchAngle_le_gap
    fifteenCandidateInnerRadius fifteenCandidateInnerRadius alpha beta
    fifteenCandidateInnerRadius_pos fifteenCandidateInnerRadius_pos
    hgapPi hangle
    (by rw [fifteenCandidateAngleCosineArgument_eq]; exact hrange.1)
    (by rw [fifteenCandidateAngleCosineArgument_eq]; exact hrange.2)

/-- Candidate inner/outer centers separated by their construction angle. -/
theorem fifteenCandidateMixedPair_separated_of_gap
    (alpha beta : ℝ)
    (hgap : fifteenLocalPhi - fifteenCandidateWallHalfAngle ≤ beta - alpha)
    (hgapPi : beta - alpha ≤ Real.pi) :
    4 ≤ pointNorm
      ((polarPoint fifteenCandidateInnerRadius alpha).1 -
          (polarPoint fifteenCandidateOuterRadius beta).1,
       (polarPoint fifteenCandidateInnerRadius alpha).2 -
          (polarPoint fifteenCandidateOuterRadius beta).2) ^ 2 := by
  have hangle : fifteenTouchAngle fifteenCandidateInnerRadius
      fifteenCandidateOuterRadius ≤ beta - alpha := by
    rw [fifteenCandidateMixedTouchAngle_eq]
    exact hgap
  have hrange := Real.cos_mem_Icc
    (fifteenLocalPhi - fifteenCandidateWallHalfAngle)
  exact fifteenPolarPair_separated_of_touchAngle_le_gap
    fifteenCandidateInnerRadius fifteenCandidateOuterRadius alpha beta
    fifteenCandidateInnerRadius_pos fifteenCandidateOuterRadius_pos
    hgapPi hangle
    (by rw [fifteenCandidateMixedAngleCosineArgument_eq]; exact hrange.1)
    (by rw [fifteenCandidateMixedAngleCosineArgument_eq]; exact hrange.2)

/-- Candidate outer centers separated by the smaller outer-ring gap. -/
theorem fifteenCandidateOuterPair_separated_of_gap
    (alpha beta : ℝ)
    (hgap : 2 * fifteenCandidateWallHalfAngle ≤ beta - alpha)
    (hgapPi : beta - alpha ≤ Real.pi) :
    4 ≤ pointNorm
      ((polarPoint fifteenCandidateOuterRadius alpha).1 -
          (polarPoint fifteenCandidateOuterRadius beta).1,
       (polarPoint fifteenCandidateOuterRadius alpha).2 -
          (polarPoint fifteenCandidateOuterRadius beta).2) ^ 2 := by
  have hangle : fifteenTouchAngle fifteenCandidateOuterRadius
      fifteenCandidateOuterRadius ≤ beta - alpha := by
    rw [fifteenCandidateWallTouchAngle_eq]
    exact hgap
  have hrange := Real.cos_mem_Icc
    (2 * fifteenCandidateWallHalfAngle)
  exact fifteenPolarPair_separated_of_touchAngle_le_gap
    fifteenCandidateOuterRadius fifteenCandidateOuterRadius alpha beta
    fifteenCandidateOuterRadius_pos fifteenCandidateOuterRadius_pos
    hgapPi hangle
    (by rw [fifteenCandidateWallCosineArgument_eq]; exact hrange.1)
    (by rw [fifteenCandidateWallCosineArgument_eq]; exact hrange.2)

end CirclePacking
