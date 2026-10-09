import CirclePacking.FifteenTickSoundness
import CirclePacking.FifteenCycleSoundness
import CirclePacking.FifteenPackingSortedGeometry

/-! Convert the analytic contact-angle estimate on one radial rectangle into
the exact edge-weight bound consumed by the negative-cycle theorem. The
packing-specific module supplies the ordered polar data and pair separation;
the remaining hypotheses here are precisely the radial-box assignment for
this edge. -/

namespace CirclePacking

theorem fifteenRegularTick_cycleEdge_weight_bound
    (edge : FifteenCycleEdge) (x y : FifteenInterval)
    (theta : Fin 15 → ℝ) (a b tauUpper : ℝ)
    (hshape : fifteenCycleEdgeShape edge = true)
    (hregular : (edge.kind = "L" ∧ edge.source > edge.target) ∨
      (edge.kind = "U" ∧ edge.source < edge.target))
    (hsum : 2 ≤ x.2 + y.2)
    (hvalid : fifteenTickCertificateValid x y false false edge.ticks = true)
    (hxOrder : x.1 ≤ x.2) (hyOrder : y.1 ≤ y.2)
    (hx0 : 0 < (x.1 : ℝ)) (hy0 : 0 < (y.1 : ℝ))
    (haL : (x.1 : ℝ) ≤ a) (haU : a ≤ (x.2 : ℝ))
    (hbL : (y.1 : ℝ) ≤ b) (hbU : b ≤ (y.2 : ℝ))
    (hsorted : ∀ i j : Fin 15, i.1 < j.1 → theta i ≤ theta j)
    (hthetaLo : ∀ i : Fin 15, 0 ≤ theta i)
    (hthetaHi : ∀ i : Fin 15, theta i ≤ 2 * Real.pi)
    (hsep : 4 ≤ pointNorm
      ((polarPoint a (theta (fifteenCycleFin edge.source))).1 -
          (polarPoint b (theta (fifteenCycleFin edge.target))).1,
       (polarPoint a (theta (fifteenCycleFin edge.source))).2 -
          (polarPoint b (theta (fifteenCycleFin edge.target))).2) ^ 2)
    (htau : 2 * Real.pi ≤ tauUpper)
    (htauUpper : tauUpper =
      (fifteenPiUpperTicks : ℝ) / fifteenAngleScale) :
    theta (fifteenCycleFin edge.target) -
        theta (fifteenCycleFin edge.source) ≤
      (fifteenCycleEdgeWeight edge : ℝ) / fifteenAngleScale := by
  let angularEdge := fifteenCycleAngularEdge edge
  have hspec := fifteenCycleEdgeShape_spec edge hshape
  have hsource : edge.source < 15 := hspec.1
  have htarget : edge.target < 15 := hspec.2.1
  have hticks : edge.ticks ≤ fifteenPiUpperTicks := hspec.2.2.1
  have hsemantic : fifteenCycleEdgeSemanticallyValid edge := by
    rcases hregular with hlower | hupper
    · exact Or.inr (Or.inl hlower)
    · exact Or.inr (Or.inr hupper)
  have hsourceNeTarget : edge.source ≠ edge.target := by
    rcases hregular with hlower | hupper
    · exact Nat.ne_of_gt hlower.2
    · exact Nat.ne_of_lt hupper.2
  have hangularNe : angularEdge.src ≠ angularEdge.dst := by
    intro h
    apply hsourceNeTarget
    have hsrc : (fifteenCycleFin edge.source).val = edge.source :=
      Nat.mod_eq_of_lt hsource
    have hdst : (fifteenCycleFin edge.target).val = edge.target :=
      Nat.mod_eq_of_lt htarget
    calc
      edge.source = (fifteenCycleFin edge.source).val := hsrc.symm
      _ = (fifteenCycleFin edge.target).val := by
        simpa [angularEdge, fifteenCycleAngularEdge] using congrArg Fin.val h
      _ = edge.target := hdst
  have hlower : angularEdge.lower = (edge.ticks : ℝ) / 2800 := by
    simp [angularEdge, fifteenCycleAngularEdge, fifteenAngleScale]
  have hpolar := fifteenRegularTick_gives_polar_edge_bound_all_caps
    x y edge.ticks angularEdge theta a b tauUpper hsum hvalid
    hxOrder hyOrder hx0 hy0 haL haU hbL hbU hlower hangularNe
    hsorted hthetaLo hthetaHi hsep htau
  rw [htauUpper] at hpolar
  have hweight := fifteenCycleAngularEdge_upper_eq_weight edge
    hsource htarget hsemantic hticks
  rw [hweight] at hpolar
  simpa [angularEdge, fifteenCycleAngularEdge] using hpolar

end CirclePacking
