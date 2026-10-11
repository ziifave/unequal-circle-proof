import CirclePacking.FifteenStage3TickSoundness
import CirclePacking.FifteenPackingCycleBridge

/-! Convert Stage 3 owner-pair ticks into the angular upper bounds consumed
by the negative-cycle argument. Labels outside the eight radial table bins
(the origin and unassigned sentinel) carry tick zero. -/

namespace CirclePacking

def fifteenStage3OwnerPairTick
    (labels : Fin 15 → Nat) (i j : Fin 15) : Nat :=
  if labels i ≥ 8 || labels j ≥ 8 then 0
  else (fifteenStage3Q[labels i]!)[labels j]!

/-- The checked Stage 3 table is symmetric, so reversing an owner pair
preserves its tick. The certificate uses the reversed lookup on lower edges. -/
theorem fifteenStage3Q_entry_symmetric (i j : Nat) (hi : i < 8) (hj : j < 8) :
    (fifteenStage3Q[i]!)[j]! = (fifteenStage3Q[j]!)[i]! := by
  interval_cases i <;> interval_cases j <;> decide

theorem fifteenStage3OwnerPairTick_comm
    (labels : Fin 15 → Nat) (i j : Fin 15) :
    fifteenStage3OwnerPairTick labels i j =
      fifteenStage3OwnerPairTick labels j i := by
  by_cases hi : 8 ≤ labels i
  · simp [fifteenStage3OwnerPairTick, hi]
  · by_cases hj : 8 ≤ labels j
    · simp [fifteenStage3OwnerPairTick, hj]
    · have hi' : labels i < 8 := by omega
      have hj' : labels j < 8 := by omega
      simp [fifteenStage3OwnerPairTick, hi, hj,
        fifteenStage3Q_entry_symmetric (labels i) (labels j) hi' hj']

private theorem fifteenStage3OwnerSpec_radius_positive
    (label : Nat) (r : ℝ) (hlabel : label < 8)
    (howner : fifteenStage3OwnerSpec label r) : 0 < r := by
  have hwall := fifteenCandidateOuterRadius_gt_one
  unfold fifteenStage3OwnerSpec at howner
  split at howner <;> simp_all <;> linarith

/-- For any actual owner pair, the Stage 3 table tick gives the angular
upper bound associated with a directed edge. This is the local analytic
bridge needed to interpret a verified cycle's edge weights. -/
theorem fifteenStage3OwnerPair_angular_bound
    (radii : Fin 15 → ℝ) (labels : Fin 15 → Nat)
    (howners : ∀ i, labels i < 8 →
      fifteenStage3OwnerSpec (labels i) (radii i))
    (hsum : ∀ i j, i ≠ j → 2 ≤ radii i + radii j)
    (theta : Fin 15 → ℝ) (tauUpper : ℝ)
    (hsorted : ∀ i j : Fin 15, i.1 < j.1 → theta i ≤ theta j)
    (hthetaLo : ∀ i, 0 ≤ theta i)
    (hthetaHi : ∀ i, theta i ≤ 2 * Real.pi)
    (hsep : ∀ i j : Fin 15, i ≠ j →
      4 ≤ pointNorm
        ((polarPoint (radii i) (theta i)).1 - (polarPoint (radii j) (theta j)).1,
         (polarPoint (radii i) (theta i)).2 - (polarPoint (radii j) (theta j)).2) ^ 2)
    (htau : 2 * Real.pi ≤ tauUpper)
    (i j : Fin 15) (hij : i ≠ j) :
    theta j - theta i ≤ fifteenAngularEdgeUpper tauUpper
      ⟨i, j, ((fifteenStage3OwnerPairTick labels i j : Nat) : ℝ) / 2800⟩ := by
  by_cases hi : labels i < 8
  · by_cases hj : labels j < 8
    · let ticks := (fifteenStage3Q[labels i]!)[labels j]!
      have htick : fifteenStage3OwnerPairTick labels i j = ticks := by
        simp [fifteenStage3OwnerPairTick, hi, hj, ticks]
      have hcontact := fifteenStage3PairTick_lower_bounds_touchAngle
        (labels i) (labels j) hi hj (radii i) (radii j)
        (howners i hi) (howners j hj) (hsum i j hij)
      have hcontact' : (ticks : ℝ) / 2800 ≤ touchAngle (radii i) (radii j) 2 := by
        simpa [ticks] using hcontact
      have hiPos := fifteenStage3OwnerSpec_radius_positive (labels i) (radii i) hi (howners i hi)
      have hjPos := fifteenStage3OwnerSpec_radius_positive (labels j) (radii j) hj (howners j hj)
      let edge : FifteenAngularEdge :=
        ⟨i, j, ((fifteenStage3OwnerPairTick labels i j : Nat) : ℝ) / 2800⟩
      have hlower : edge.lower ≤ touchAngle (radii i) (radii j) 2 := by
        simpa [edge, htick] using hcontact'
      have hpi : edge.lower ≤ Real.pi := le_trans hlower (Real.arccos_le_pi _)
      have hsep' : (2 : ℝ) ^ 2 ≤ pointNorm
          ((polarPoint (radii i) (theta edge.src)).1 -
              (polarPoint (radii j) (theta edge.dst)).1,
           (polarPoint (radii i) (theta edge.src)).2 -
              (polarPoint (radii j) (theta edge.dst)).2) ^ 2 := by
        have h := hsep i j hij
        norm_num at h ⊢
        exact h
      have hbound := fifteen_polar_edge_respects_angular_bound theta tauUpper edge
        (radii i) (radii j) 2 hiPos hjPos hpi hij hsorted hthetaLo hthetaHi
        hsep' hlower htau
      simpa [edge] using hbound
    · have hzero : fifteenStage3OwnerPairTick labels i j = 0 := by
        simp [fifteenStage3OwnerPairTick, hi, hj]
      by_cases hforward : i.1 < j.1
      · have hdelta : theta j - theta i ≤ 2 * Real.pi := by
          have hhi := hthetaHi j
          have hlo := hthetaLo i
          linarith
        have hangular := calc
            theta j - theta i ≤ 2 * Real.pi := hdelta
            _ ≤ tauUpper := htau
        simpa [fifteenAngularEdgeUpper, hforward, hzero] using hangular
      · have hback : j.1 < i.1 := by omega
        have hdelta : theta j - theta i ≤ 0 := by
          have horder := hsorted j i hback
          linarith
        simpa [fifteenAngularEdgeUpper, hforward, hzero] using hdelta
  · have hzero : fifteenStage3OwnerPairTick labels i j = 0 := by
      simp [fifteenStage3OwnerPairTick, hi]
    by_cases hforward : i.1 < j.1
    · have hdelta : theta j - theta i ≤ 2 * Real.pi := by
        have hhi := hthetaHi j
        have hlo := hthetaLo i
        linarith
      have hangular := calc
          theta j - theta i ≤ 2 * Real.pi := hdelta
          _ ≤ tauUpper := htau
      simpa [fifteenAngularEdgeUpper, hforward, hzero] using hangular
    · have hback : j.1 < i.1 := by omega
      have hdelta : theta j - theta i ≤ 0 := by
        have horder := hsorted j i hback
        linarith
      simpa [fifteenAngularEdgeUpper, hforward, hzero] using hdelta

end CirclePacking
