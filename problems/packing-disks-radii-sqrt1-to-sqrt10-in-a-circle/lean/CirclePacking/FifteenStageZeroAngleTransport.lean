import CirclePacking.FifteenStageZeroProfileTransport
import CirclePacking.FifteenPackingPolarCoordinates

/-! Lift a rotated or reflected cyclic angle profile back into a monotone
single-turn interval. Radius profiles use exactly the same permutation, and
all polar pair distances are preserved. -/

namespace CirclePacking

private theorem stage0_rotation_preimage_val (shift i : Fin 15) :
    ((finCycle shift).symm i).val =
      if i.val < shift.val then i.val + 15 - shift.val else i.val - shift.val := by
  change (i - shift).val = _
  have h := Fin.intCast_val_sub_eq_sub_add_ite i shift
  by_cases hi : i.val < shift.val
  · have hnot : ¬ shift ≤ i := by change ¬ shift.val ≤ i.val; omega
    simp only [ite_eq_right hnot] at h
    rw [ite_eq_left hi]
    omega
  · have hle : shift ≤ i := by change shift.val ≤ i.val; omega
    simp only [ite_eq_left hle] at h
    rw [ite_eq_right hi]
    omega

noncomputable def fifteenStage0ReflectedAngles (theta : Fin 15 → ℝ) : Fin 15 → ℝ :=
  fun i => 2 * Real.pi - theta i.rev

private noncomputable def stage0RotatedAngleRaw (theta : Fin 15 → ℝ) (shift i : Fin 15) : ℝ :=
  theta ((finCycle shift).symm i) +
    if i.val < shift.val then 0 else 2 * Real.pi

/-- Choose the new first center as angle zero, adding one turn after the
cyclic cut. This normalizes the reindexed angles without changing distances. -/
noncomputable def fifteenStage0RotatedAngles (theta : Fin 15 → ℝ)
    (shift : Fin 15) : Fin 15 → ℝ :=
  fun i => stage0RotatedAngleRaw theta shift i - stage0RotatedAngleRaw theta shift 0

noncomputable def fifteenStage0DihedralAngles (theta : Fin 15 → ℝ)
    (reflected : Bool) (shift : Fin 15) : Fin 15 → ℝ :=
  fifteenStage0RotatedAngles
    (if reflected then fifteenStage0ReflectedAngles theta else theta) shift

theorem fifteenStage0ReflectedAngles_monotone
    (theta : Fin 15 → ℝ)
    (hsorted : ∀ i j : Fin 15, i.val < j.val → theta i ≤ theta j) :
    ∀ i j : Fin 15, i.val < j.val →
      fifteenStage0ReflectedAngles theta i ≤ fifteenStage0ReflectedAngles theta j := by
  intro i j hij
  have hrev : j.rev.val < i.rev.val := by simp only [Fin.val_rev]; omega
  have h := hsorted j.rev i.rev hrev
  dsimp [fifteenStage0ReflectedAngles]
  linarith

theorem fifteenStage0ReflectedAngles_range
    (theta : Fin 15 → ℝ)
    (hrange : ∀ i, 0 ≤ theta i ∧ theta i ≤ 2 * Real.pi) :
    ∀ i, 0 ≤ fifteenStage0ReflectedAngles theta i ∧
      fifteenStage0ReflectedAngles theta i ≤ 2 * Real.pi := by
  intro i
  have h := hrange i.rev
  dsimp [fifteenStage0ReflectedAngles]
  constructor <;> linarith [h.1, h.2]

private theorem stage0RotatedAngleRaw_monotone
    (theta : Fin 15 → ℝ) (shift : Fin 15)
    (hsorted : ∀ i j : Fin 15, i.val < j.val → theta i ≤ theta j)
    (hrange : ∀ i, 0 ≤ theta i ∧ theta i ≤ 2 * Real.pi) :
    ∀ i j : Fin 15, i.val < j.val →
      stage0RotatedAngleRaw theta shift i ≤ stage0RotatedAngleRaw theta shift j := by
  intro i j hij
  have hi := stage0_rotation_preimage_val shift i
  have hj := stage0_rotation_preimage_val shift j
  by_cases hiCut : i.val < shift.val <;> by_cases hjCut : j.val < shift.val
  · have hpre : ((finCycle shift).symm i).val < ((finCycle shift).symm j).val := by
      simp only [ite_eq_left hiCut, ite_eq_left hjCut] at hi hj
      omega
    simpa [stage0RotatedAngleRaw, hiCut, hjCut] using
      hsorted ((finCycle shift).symm i) ((finCycle shift).symm j) hpre
  · have hiRange := hrange ((finCycle shift).symm i)
    have hjRange := hrange ((finCycle shift).symm j)
    dsimp [stage0RotatedAngleRaw]
    rw [ite_eq_left hiCut, ite_eq_right hjCut]
    linarith [hiRange.2, hjRange.1]
  · omega
  · have hpre : ((finCycle shift).symm i).val < ((finCycle shift).symm j).val := by
      simp only [ite_eq_right hiCut, ite_eq_right hjCut] at hi hj
      omega
    have h := hsorted ((finCycle shift).symm i) ((finCycle shift).symm j) hpre
    simpa [stage0RotatedAngleRaw, hiCut, hjCut] using
      add_le_add_right h (2 * Real.pi)

theorem fifteenStage0RotatedAngles_monotone
    (theta : Fin 15 → ℝ) (shift : Fin 15)
    (hsorted : ∀ i j : Fin 15, i.val < j.val → theta i ≤ theta j)
    (hrange : ∀ i, 0 ≤ theta i ∧ theta i ≤ 2 * Real.pi) :
    ∀ i j : Fin 15, i.val < j.val →
      fifteenStage0RotatedAngles theta shift i ≤ fifteenStage0RotatedAngles theta shift j := by
  intro i j hij
  exact sub_le_sub_right (stage0RotatedAngleRaw_monotone theta shift hsorted hrange i j hij) _

theorem fifteenStage0RotatedAngles_range
    (theta : Fin 15 → ℝ) (shift : Fin 15)
    (hsorted : ∀ i j : Fin 15, i.val < j.val → theta i ≤ theta j)
    (hrange : ∀ i, 0 ≤ theta i ∧ theta i ≤ 2 * Real.pi) :
    ∀ i, 0 ≤ fifteenStage0RotatedAngles theta shift i ∧
      fifteenStage0RotatedAngles theta shift i ≤ 2 * Real.pi := by
  intro i
  constructor
  · by_cases hi : i = 0
    · simp [hi, fifteenStage0RotatedAngles]
    · have hpos : (0 : Fin 15).val < i.val := by
        have hne : i.val ≠ 0 := by intro h; apply hi; exact Fin.ext h
        simpa using Nat.pos_of_ne_zero hne
      have h := stage0RotatedAngleRaw_monotone theta shift hsorted hrange 0 i hpos
      exact sub_nonneg.mpr h
  · by_cases hs : shift.val = 0
    · have hshift : shift = 0 := Fin.ext hs
      subst shift
      simpa [fifteenStage0RotatedAngles, stage0RotatedAngleRaw] using
        (show theta i - theta 0 ≤ 2 * Real.pi by
          linarith [(hrange i).2, (hrange 0).1])
    · have hzeroCut : (0 : Fin 15).val < shift.val := by simp; omega
      by_cases hiCut : i.val < shift.val
      · dsimp [fifteenStage0RotatedAngles, stage0RotatedAngleRaw]
        rw [ite_eq_left hiCut, ite_eq_left (show 0 < shift.val by simpa using hzeroCut)]
        linarith [(hrange ((finCycle shift).symm i)).2,
          (hrange ((finCycle shift).symm 0)).1]
      · have hi := stage0_rotation_preimage_val shift i
        have hz := stage0_rotation_preimage_val shift 0
        have hpre : ((finCycle shift).symm i).val < ((finCycle shift).symm 0).val := by
          simp only [ite_eq_right hiCut, ite_eq_left hzeroCut] at hi hz
          have := i.isLt
          omega
        have h := hsorted ((finCycle shift).symm i) ((finCycle shift).symm 0) hpre
        dsimp [fifteenStage0RotatedAngles, stage0RotatedAngleRaw]
        rw [ite_eq_right hiCut, ite_eq_left (show 0 < shift.val by simpa using hzeroCut)]
        linarith

theorem fifteenStage0DihedralAngles_ordered
    (theta : Fin 15 → ℝ) (reflected : Bool) (shift : Fin 15)
    (hsorted : ∀ i j : Fin 15, i.val < j.val → theta i ≤ theta j)
    (hrange : ∀ i, 0 ≤ theta i ∧ theta i ≤ 2 * Real.pi) :
    (∀ i j : Fin 15, i.val < j.val →
      fifteenStage0DihedralAngles theta reflected shift i ≤
        fifteenStage0DihedralAngles theta reflected shift j) ∧
    (∀ i, 0 ≤ fifteenStage0DihedralAngles theta reflected shift i ∧
      fifteenStage0DihedralAngles theta reflected shift i ≤ 2 * Real.pi) := by
  cases reflected
  · exact ⟨fifteenStage0RotatedAngles_monotone theta shift hsorted hrange,
      fifteenStage0RotatedAngles_range theta shift hsorted hrange⟩
  · have hs := fifteenStage0ReflectedAngles_monotone theta hsorted
    have hr := fifteenStage0ReflectedAngles_range theta hrange
    exact ⟨fifteenStage0RotatedAngles_monotone _ shift hs hr,
      fifteenStage0RotatedAngles_range _ shift hs hr⟩

private theorem stage0RotatedAngles_cos_sub
    (theta : Fin 15 → ℝ) (shift i j : Fin 15) :
    Real.cos (fifteenStage0RotatedAngles theta shift i -
        fifteenStage0RotatedAngles theta shift j) =
      Real.cos (theta ((finCycle shift).symm i) - theta ((finCycle shift).symm j)) := by
  have hcancel : fifteenStage0RotatedAngles theta shift i -
      fifteenStage0RotatedAngles theta shift j =
      stage0RotatedAngleRaw theta shift i - stage0RotatedAngleRaw theta shift j := by
    dsimp [fifteenStage0RotatedAngles]
    ring
  rw [hcancel]
  dsimp [stage0RotatedAngleRaw]
  by_cases hi : i.val < shift.val <;> by_cases hj : j.val < shift.val
  · simp [hi, hj]
  · simp only [ite_eq_left hi, ite_eq_right hj, add_zero]
    rw [show theta ((finCycle shift).symm i) -
        (theta ((finCycle shift).symm j) + 2 * Real.pi) =
        (theta ((finCycle shift).symm i) - theta ((finCycle shift).symm j)) -
          2 * Real.pi by ring, Real.cos_sub_two_pi]
  · simp only [ite_eq_right hi, ite_eq_left hj, add_zero]
    rw [show theta ((finCycle shift).symm i) + 2 * Real.pi -
        theta ((finCycle shift).symm j) =
        (theta ((finCycle shift).symm i) - theta ((finCycle shift).symm j)) +
          2 * Real.pi by ring, Real.cos_add_two_pi]
  · simp only [ite_eq_right hi, ite_eq_right hj]
    congr 1
    ring

theorem fifteenStage0DihedralAngles_cos_sub
    (theta : Fin 15 → ℝ) (reflected : Bool) (shift i j : Fin 15) :
    Real.cos (fifteenStage0DihedralAngles theta reflected shift i -
        fifteenStage0DihedralAngles theta reflected shift j) =
      Real.cos (fifteenStage0TransformProfile theta reflected shift i -
        fifteenStage0TransformProfile theta reflected shift j) := by
  unfold fifteenStage0DihedralAngles
  rw [stage0RotatedAngles_cos_sub]
  cases reflected
  · rfl
  · change Real.cos
      ((2 * Real.pi - theta (((finCycle shift).symm i).rev)) -
        (2 * Real.pi - theta (((finCycle shift).symm j).rev))) = _
    rw [show (2 * Real.pi - theta (((finCycle shift).symm i).rev)) -
        (2 * Real.pi - theta (((finCycle shift).symm j).rev)) =
        -(theta (((finCycle shift).symm i).rev) -
          theta (((finCycle shift).symm j).rev)) by ring, Real.cos_neg]
    rfl

/-- Every squared distance of the normalized polar profile is the original
squared distance at the corresponding pair of old slots. -/
theorem fifteenStage0DihedralAngles_distance_sq
    (radii theta : Fin 15 → ℝ) (reflected : Bool) (shift i j : Fin 15) :
    let r := fifteenStage0TransformProfile radii reflected shift
    let t := fifteenStage0DihedralAngles theta reflected shift
    let old := (fifteenStage0DihedralPermutation reflected shift).symm
    pointNorm
      ((polarPoint (r i) (t i)).1 - (polarPoint (r j) (t j)).1,
       (polarPoint (r i) (t i)).2 - (polarPoint (r j) (t j)).2) ^ 2 =
      pointNorm
      ((polarPoint (radii (old i)) (theta (old i))).1 -
          (polarPoint (radii (old j)) (theta (old j))).1,
       (polarPoint (radii (old i)) (theta (old i))).2 -
          (polarPoint (radii (old j)) (theta (old j))).2) ^ 2 := by
  dsimp only
  rw [fifteenPolarPair_distance_sq, fifteenPolarPair_distance_sq,
    fifteenStage0DihedralAngles_cos_sub]
  rfl

end CirclePacking
