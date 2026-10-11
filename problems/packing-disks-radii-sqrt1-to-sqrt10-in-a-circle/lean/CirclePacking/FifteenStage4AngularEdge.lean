import CirclePacking.FifteenStage4TickSoundness
import CirclePacking.FifteenPackingCycleBridge

/-! Convert Stage 4 owner-pair ticks into the angular upper bounds consumed
by the negative-cycle argument. The origin and unassigned sentinel carry
tick zero; the wall is represented by the twelfth radial table bin. -/

namespace CirclePacking

def fifteenStage4OwnerPairTick
    (labels : Fin 15 → Nat) (i j : Fin 15) : Nat :=
  if labels i ≥ 12 || labels j ≥ 12 then 0
  else (fifteenStage4Q[labels i]!)[labels j]!

/-- The checked Stage 4 table is symmetric, so reversing an owner pair
preserves its tick. The certificate uses the reversed lookup on lower edges. -/
theorem fifteenStage4Q_entry_symmetric (i j : Nat) (hi : i < 12) (hj : j < 12) :
    (fifteenStage4Q[i]!)[j]! = (fifteenStage4Q[j]!)[i]! := by
  interval_cases i <;> interval_cases j <;> decide

theorem fifteenStage4OwnerPairTick_comm
    (labels : Fin 15 → Nat) (i j : Fin 15) :
    fifteenStage4OwnerPairTick labels i j =
      fifteenStage4OwnerPairTick labels j i := by
  by_cases hi : 12 ≤ labels i
  · simp [fifteenStage4OwnerPairTick, hi]
  · by_cases hj : 12 ≤ labels j
    · simp [fifteenStage4OwnerPairTick, hj]
    · have hi' : labels i < 12 := by omega
      have hj' : labels j < 12 := by omega
      simp [fifteenStage4OwnerPairTick, hi, hj,
        fifteenStage4Q_entry_symmetric (labels i) (labels j) hi' hj']

private theorem fifteenStage4OwnerSpec_radius_positive
    (label : Nat) (r : ℝ) (hlabel : label < 12)
    (howner : fifteenStage4OwnerSpec label r) : 0 < r := by
  have hwall := fifteenCandidateOuterRadius_gt_one
  unfold fifteenStage4OwnerSpec at howner
  split at howner <;> simp_all <;> linarith

/-- For any actual owner pair, the Stage 4 table tick gives the angular
upper bound associated with a directed edge. This is the local analytic
bridge needed to interpret a verified cycle's edge weights. -/
theorem fifteenStage4OwnerPair_angular_bound
    (radii : Fin 15 → ℝ) (labels : Fin 15 → Nat)
    (howners : ∀ i, labels i < 12 →
      fifteenStage4OwnerSpec (labels i) (radii i))
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
      ⟨i, j, ((fifteenStage4OwnerPairTick labels i j : Nat) : ℝ) / 2800⟩ := by
  by_cases hi : labels i < 12
  · by_cases hj : labels j < 12
    · let ticks := (fifteenStage4Q[labels i]!)[labels j]!
      have htick : fifteenStage4OwnerPairTick labels i j = ticks := by
        simp [fifteenStage4OwnerPairTick, hi, hj, ticks]
      have hcontact := fifteenStage4PairTick_lower_bounds_touchAngle
        (labels i) (labels j) hi hj (radii i) (radii j)
        (howners i hi) (howners j hj) (hsum i j hij)
      have hcontact' : (ticks : ℝ) / 2800 ≤ touchAngle (radii i) (radii j) 2 := by
        simpa [ticks] using hcontact
      have hiPos := fifteenStage4OwnerSpec_radius_positive (labels i) (radii i) hi (howners i hi)
      have hjPos := fifteenStage4OwnerSpec_radius_positive (labels j) (radii j) hj (howners j hj)
      let edge : FifteenAngularEdge :=
        ⟨i, j, ((fifteenStage4OwnerPairTick labels i j : Nat) : ℝ) / 2800⟩
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
    · have hzero : fifteenStage4OwnerPairTick labels i j = 0 := by
        simp [fifteenStage4OwnerPairTick, hi, hj]
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
  · have hzero : fifteenStage4OwnerPairTick labels i j = 0 := by
      simp [fifteenStage4OwnerPairTick, hi]
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
