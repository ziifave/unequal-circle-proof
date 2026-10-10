import CirclePacking.FifteenStageZero
import CirclePacking.FifteenTickSoundness

/-!
# Geometric meaning of the coarse 15-disk angle table

The stage-zero replay checks the coarse angle table with the same rational
Taylor and corner-cap calculation used by the refined certificate.  This file
turns each positive table entry into an actual contact-angle lower bound over
its full radial rectangle, so the finite graph witnesses have a geometric
interface.
-/

namespace CirclePacking

theorem fifteenStage0OuterTypeBox_bounds :
    ((fifteenStage0CoarseTypeBox (0 : Fin 4)).1 : ℝ) =
        (2385 : ℝ) / 1000 ∧
      ((fifteenStage0CoarseTypeBox (0 : Fin 4)).2 : ℝ) =
        (3522 : ℝ) / 1000 := by
  rcases fifteenStage0OuterTypeBox_rat_bounds with ⟨hlo, hhi⟩
  constructor
  · rw [hlo]
    simp [fifteenRational, Rat.normalize_eq_mkRat,
      Rat.cast_mkRat_of_ne_zero]
  · rw [hhi]
    simp [fifteenRational, Rat.normalize_eq_mkRat,
      Rat.cast_mkRat_of_ne_zero]

theorem fifteenStage0CoarsePair_numeric_spec
    (typeI typeJ : Fin 4)
    (hpositive : 0 < fifteenStage0CoarseAngleTick typeI typeJ) :
    let x := fifteenStage0CoarseTypeBox typeI
    let y := fifteenStage0CoarseTypeBox typeJ
    2 ≤ x.2 + y.2 ∧
    fifteenBoxCosineCap x y < 1 ∧
    -1 < fifteenBoxCosineCap x y ∧
    fifteenTickCertificateValid x y false false
      (fifteenStage0CoarseAngleTick typeI typeJ) = true ∧
    x.1 ≤ x.2 ∧ y.1 ≤ y.2 ∧ 0 < x.1 ∧ 0 < y.1 := by
  fin_cases typeI <;> fin_cases typeJ <;>
    simp_all [fifteenStage0CoarseAngleTick, fifteenStage0CoarseQ] <;>
    native_decide

theorem fifteenStage0CoarsePair_lower_bounds_touch_angle
    (typeI typeJ : Fin 4)
    (hpositive : 0 < fifteenStage0CoarseAngleTick typeI typeJ)
    (a b : ℝ)
    (haL : ((fifteenStage0CoarseTypeBox typeI).1 : ℝ) ≤ a)
    (haU : a ≤ ((fifteenStage0CoarseTypeBox typeI).2 : ℝ))
    (hbL : ((fifteenStage0CoarseTypeBox typeJ).1 : ℝ) ≤ b)
    (hbU : b ≤ ((fifteenStage0CoarseTypeBox typeJ).2 : ℝ)) :
    (fifteenStage0CoarseAngleTick typeI typeJ : ℝ) / 2800 ≤
      touchAngle a b 2 := by
  let x := fifteenStage0CoarseTypeBox typeI
  let y := fifteenStage0CoarseTypeBox typeJ
  have hspec := fifteenStage0CoarsePair_numeric_spec typeI typeJ hpositive
  dsimp only at hspec
  rcases hspec with
    ⟨hsum, hcapUpper, hcapLower, hvalid, hxOrder, hyOrder, hx0, hy0⟩
  exact fifteenRegularTick_lower_bounds_touch_angle x y
    (fifteenStage0CoarseAngleTick typeI typeJ) a b hsum
    (by exact_mod_cast hcapUpper)
    (by exact_mod_cast hcapLower)
    hvalid hxOrder hyOrder
    (by exact_mod_cast hx0)
    (by exact_mod_cast hy0)
    haL haU hbL hbU

theorem fifteenStage0CoarsePair_gives_polar_edge_bound
    (typeI typeJ : Fin 4)
    (hpositive : 0 < fifteenStage0CoarseAngleTick typeI typeJ)
    (edge : FifteenAngularEdge) (theta : Fin 15 → ℝ)
    (a b tauUpper : ℝ)
    (haL : ((fifteenStage0CoarseTypeBox typeI).1 : ℝ) ≤ a)
    (haU : a ≤ ((fifteenStage0CoarseTypeBox typeI).2 : ℝ))
    (hbL : ((fifteenStage0CoarseTypeBox typeJ).1 : ℝ) ≤ b)
    (hbU : b ≤ ((fifteenStage0CoarseTypeBox typeJ).2 : ℝ))
    (hlower : edge.lower =
      (fifteenStage0CoarseAngleTick typeI typeJ : ℝ) / 2800)
    (hneq : edge.src ≠ edge.dst)
    (hsorted : ∀ i j : Fin 15, i.1 < j.1 → theta i ≤ theta j)
    (hthetaLo : ∀ i : Fin 15, 0 ≤ theta i)
    (hthetaHi : ∀ i : Fin 15, theta i ≤ 2 * Real.pi)
    (hsep : 4 ≤ pointNorm
      ((polarPoint a (theta edge.src)).1 - (polarPoint b (theta edge.dst)).1,
       (polarPoint a (theta edge.src)).2 - (polarPoint b (theta edge.dst)).2) ^ 2)
    (htau : 2 * Real.pi ≤ tauUpper) :
    theta edge.dst - theta edge.src ≤ fifteenAngularEdgeUpper tauUpper edge := by
  let x := fifteenStage0CoarseTypeBox typeI
  let y := fifteenStage0CoarseTypeBox typeJ
  have hspec := fifteenStage0CoarsePair_numeric_spec typeI typeJ hpositive
  dsimp only at hspec
  rcases hspec with
    ⟨hsum, hcapUpper, hcapLower, hvalid, hxOrder, hyOrder, hx0, hy0⟩
  exact fifteenRegularTick_gives_polar_edge_bound x y
    (fifteenStage0CoarseAngleTick typeI typeJ) edge theta a b tauUpper
    hsum
    (by exact_mod_cast hcapUpper)
    (by exact_mod_cast hcapLower)
    hvalid hxOrder hyOrder
    (by exact_mod_cast hx0)
    (by exact_mod_cast hy0)
    haL haU hbL hbU hlower hneq hsorted hthetaLo hthetaHi hsep htau

theorem fifteenStage0ZeroTick_gives_polar_edge_bound
    (edge : FifteenAngularEdge) (theta : Fin 15 → ℝ) (tauUpper : ℝ)
    (hzero : edge.lower = 0) (hneq : edge.src ≠ edge.dst)
    (hsorted : ∀ i j : Fin 15, i.1 < j.1 → theta i ≤ theta j)
    (hthetaLo : ∀ i : Fin 15, 0 ≤ theta i)
    (hthetaHi : ∀ i : Fin 15, theta i ≤ 2 * Real.pi)
    (htau : 2 * Real.pi ≤ tauUpper) :
    theta edge.dst - theta edge.src ≤ fifteenAngularEdgeUpper tauUpper edge := by
  by_cases hforward : edge.src.1 < edge.dst.1
  · have hhi := hthetaHi edge.dst
    have hlo := hthetaLo edge.src
    simp [fifteenAngularEdgeUpper, hforward, hzero]
    linarith
  · have hback : edge.dst.1 < edge.src.1 := by
      have hindices : edge.src.1 ≠ edge.dst.1 := by
        intro heq
        apply hneq
        exact Fin.ext heq
      omega
    have horder := hsorted edge.dst edge.src hback
    simp [fifteenAngularEdgeUpper, hforward, hzero]
    linarith

end CirclePacking
