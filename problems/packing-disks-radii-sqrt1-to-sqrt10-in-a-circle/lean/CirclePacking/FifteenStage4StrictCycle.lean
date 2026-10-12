import CirclePacking.FifteenStage4LocalRigidity
import CirclePacking.FifteenStrictWallBarrier

/-! Pure polar-coordinate form of the final strict-wall obstruction. It is
independent of how the `(I,O,O)^5` cycle was rotated or reflected before its
angles were normalized. -/

namespace CirclePacking

private theorem s4PolarVariableSectorBudget
    (radius theta : Fin 15 → ℝ) (i j k l : Fin 15)
    (hij : i.val < j.val) (hjk : j.val < k.val) (hkl : k.val < l.val)
    (horder : ∀ a b : Fin 15, a.val < b.val → theta a ≤ theta b)
    (hrange : ∀ a : Fin 15, 0 ≤ theta a ∧ theta a ≤ 2 * Real.pi)
    (hpositive : ∀ a : Fin 15, 0 < radius a)
    (hseparated : ∀ a b : Fin 15, a ≠ b →
      4 ≤ pointNorm
        ((polarPoint (radius a) (theta a)).1 -
          (polarPoint (radius b) (theta b)).1,
         (polarPoint (radius a) (theta a)).2 -
          (polarPoint (radius b) (theta b)).2) ^ 2) :
    max (fifteenTouchAngle (radius i) (radius l))
        (fifteenVariableDetourAngle (radius i) (radius j)
          (radius k) (radius l)) ≤
      (theta j - theta i) + (theta k - theta j) + (theta l - theta k) := by
  have hangleIJ := horder i j hij
  have hangleJK := horder j k hjk
  have hangleKL := horder k l hkl
  have hgapIJhi : theta j - theta i ≤ 2 * Real.pi := by
    linarith [(hrange j).2, (hrange i).1]
  have hgapJKhi : theta k - theta j ≤ 2 * Real.pi := by
    linarith [(hrange k).2, (hrange j).1]
  have hgapKLhi : theta l - theta k ≤ 2 * Real.pi := by
    linarith [(hrange l).2, (hrange k).1]
  have hgapILhi : theta l - theta i ≤ 2 * Real.pi := by
    linarith [(hrange l).2, (hrange i).1]
  exact fifteenLocalVariableSector_max_le_gap
    (hpositive i) (hpositive j) (hpositive k) (hpositive l)
    (by linarith [hangleIJ]) hgapIJhi
    (by linarith [hangleJK]) hgapJKhi
    (by linarith [hangleKL]) hgapKLhi hgapILhi
    (hseparated i l (by omega))
    (hseparated i j (by omega))
    (hseparated j k (by omega))
    (hseparated k l (by omega))

private theorem s4PolarStrictSectorGap
    (radius theta : Fin 15 → ℝ) (i j k l : Fin 15)
    (hij : i.val < j.val) (hjk : j.val < k.val) (hkl : k.val < l.val)
    (horder : ∀ a b : Fin 15, a.val < b.val → theta a ≤ theta b)
    (hrange : ∀ a : Fin 15, 0 ≤ theta a ∧ theta a ≤ 2 * Real.pi)
    (hpositive : ∀ a : Fin 15, 0 < radius a)
    (hseparated : ∀ a b : Fin 15, a ≠ b →
      4 ≤ pointNorm
        ((polarPoint (radius a) (theta a)).1 -
          (polarPoint (radius b) (theta b)).1,
         (polarPoint (radius a) (theta a)).2 -
          (polarPoint (radius b) (theta b)).2) ^ 2)
    (hinnerI : radius i = fifteenCandidateInnerRadius)
    (hinnerL : radius l = fifteenCandidateInnerRadius)
    (houterJ : fifteenCandidateInnerThreshold ≤ radius j ∧
      radius j < fifteenCandidateOuterRadius)
    (houterK : fifteenCandidateInnerThreshold ≤ radius k ∧
      radius k < fifteenCandidateOuterRadius) :
    2 * fifteenLocalPhi <
      (theta j - theta i) + (theta k - theta j) + (theta l - theta k) := by
  have hdetour := fifteen_candidate_variable_detour_strict houterJ houterK
  have hdetour' : 2 * fifteenLocalPhi < fifteenVariableDetourAngle
      (radius i) (radius j) (radius k) (radius l) := by
    simpa [hinnerI, hinnerL] using hdetour
  have hsector := s4PolarVariableSectorBudget radius theta i j k l
    hij hjk hkl horder hrange hpositive hseparated
  exact lt_of_lt_of_le
    (lt_of_lt_of_le hdetour' (le_max_right _ _)) hsector

/-- The closing sector crosses the chosen angular cut. All three centers
after index 14 are represented by their periodic copies one turn later. -/
private theorem s4PolarStrictWrapSectorGap
    (radius theta : Fin 15 → ℝ)
    (horder : ∀ a b : Fin 15, a.val < b.val → theta a ≤ theta b)
    (hrange : ∀ a : Fin 15, 0 ≤ theta a ∧ theta a ≤ 2 * Real.pi)
    (hpositive : ∀ a : Fin 15, 0 < radius a)
    (hseparated : ∀ a b : Fin 15, a ≠ b →
      4 ≤ pointNorm
        ((polarPoint (radius a) (theta a)).1 -
          (polarPoint (radius b) (theta b)).1,
         (polarPoint (radius a) (theta a)).2 -
          (polarPoint (radius b) (theta b)).2) ^ 2)
    (hinner14 : radius 14 = fifteenCandidateInnerRadius)
    (hinner2 : radius 2 = fifteenCandidateInnerRadius)
    (houter0 : fifteenCandidateInnerThreshold ≤ radius 0 ∧
      radius 0 < fifteenCandidateOuterRadius)
    (houter1 : fifteenCandidateInnerThreshold ≤ radius 1 ∧
      radius 1 < fifteenCandidateOuterRadius) :
    2 * fifteenLocalPhi <
      (theta 0 + 2 * Real.pi - theta 14) +
      (theta 1 - theta 0) + (theta 2 - theta 1) := by
  have hangle01 := horder 0 1 (by decide)
  have hangle12 := horder 1 2 (by decide)
  have hangle214 := horder 2 14 (by decide)
  have hgap140 : 0 ≤ theta 0 + 2 * Real.pi - theta 14 := by
    linarith [(hrange 0).1, (hrange 14).2]
  have hgap140hi : theta 0 + 2 * Real.pi - theta 14 ≤ 2 * Real.pi := by
    linarith [hangle214]
  have hgap011 : 0 ≤ theta 1 - theta 0 := by linarith [hangle01]
  have hgap011hi : theta 1 - theta 0 ≤ 2 * Real.pi := by
    linarith [(hrange 1).2, (hrange 0).1]
  have hgap122 : 0 ≤ theta 2 - theta 1 := by linarith [hangle12]
  have hgap122hi : theta 2 - theta 1 ≤ 2 * Real.pi := by
    linarith [(hrange 2).2, (hrange 1).1]
  have hgap011periodic : 0 ≤
      (theta 1 + 2 * Real.pi) - (theta 0 + 2 * Real.pi) := by
    linarith [hgap011]
  have hgap011periodicHi :
      (theta 1 + 2 * Real.pi) - (theta 0 + 2 * Real.pi) ≤ 2 * Real.pi := by
    linarith [hgap011hi]
  have hgap122periodic : 0 ≤
      (theta 2 + 2 * Real.pi) - (theta 1 + 2 * Real.pi) := by
    linarith [hgap122]
  have hgap122periodicHi :
      (theta 2 + 2 * Real.pi) - (theta 1 + 2 * Real.pi) ≤ 2 * Real.pi := by
    linarith [hgap122hi]
  have hgap142 : theta 2 + 2 * Real.pi - theta 14 ≤ 2 * Real.pi := by
    linarith [hangle214]
  have hsep142 := hseparated 14 2 (by decide)
  have hsep140 := hseparated 14 0 (by decide)
  have hsep001 := hseparated 0 1 (by decide)
  have hsep012 := hseparated 1 2 (by decide)
  have hsep140' : 4 ≤ pointNorm
      ((polarPoint (radius 14) (theta 14)).1 -
        (polarPoint (radius 0) (theta 0 + 2 * Real.pi)).1,
       (polarPoint (radius 14) (theta 14)).2 -
        (polarPoint (radius 0) (theta 0 + 2 * Real.pi)).2) ^ 2 := by
    rw [fifteenPolarPoint_add_two_pi]
    exact hsep140
  have hsep142' : 4 ≤ pointNorm
      ((polarPoint (radius 14) (theta 14)).1 -
        (polarPoint (radius 2) (theta 2 + 2 * Real.pi)).1,
       (polarPoint (radius 14) (theta 14)).2 -
        (polarPoint (radius 2) (theta 2 + 2 * Real.pi)).2) ^ 2 := by
    rw [fifteenPolarPoint_add_two_pi]
    exact hsep142
  have hsep012' : 4 ≤ pointNorm
      ((polarPoint (radius 0) (theta 0 + 2 * Real.pi)).1 -
        (polarPoint (radius 1) (theta 1 + 2 * Real.pi)).1,
       (polarPoint (radius 0) (theta 0 + 2 * Real.pi)).2 -
        (polarPoint (radius 1) (theta 1 + 2 * Real.pi)).2) ^ 2 := by
    rw [fifteenPolarPoint_add_two_pi, fifteenPolarPoint_add_two_pi]
    exact hsep001
  have hsep122' : 4 ≤ pointNorm
      ((polarPoint (radius 1) (theta 1 + 2 * Real.pi)).1 -
        (polarPoint (radius 2) (theta 2 + 2 * Real.pi)).1,
       (polarPoint (radius 1) (theta 1 + 2 * Real.pi)).2 -
        (polarPoint (radius 2) (theta 2 + 2 * Real.pi)).2) ^ 2 := by
    rw [fifteenPolarPoint_add_two_pi, fifteenPolarPoint_add_two_pi]
    exact hsep012
  have hbudget := fifteenLocalVariableSector_max_le_gap
    (a := radius 14) (b := radius 0) (c := radius 1) (d := radius 2)
    (alpha := theta 14) (beta := theta 0 + 2 * Real.pi)
    (gamma := theta 1 + 2 * Real.pi) (delta := theta 2 + 2 * Real.pi)
    (hpositive 14) (hpositive 0) (hpositive 1) (hpositive 2)
    hgap140 hgap140hi hgap011periodic hgap011periodicHi
    hgap122periodic hgap122periodicHi hgap142
    hsep142' hsep140' hsep012' hsep122'
  have hdetour := fifteen_candidate_variable_detour_strict houter0 houter1
  have hdetour' : 2 * fifteenLocalPhi < fifteenVariableDetourAngle
      (radius 14) (radius 0) (radius 1) (radius 2) := by
    simpa [hinner14, hinner2] using hdetour
  have hmax : 2 * fifteenLocalPhi < max
      (fifteenTouchAngle (radius 14) (radius 2))
      (fifteenVariableDetourAngle (radius 14) (radius 0) (radius 1) (radius 2)) :=
    lt_of_lt_of_le hdetour' (le_max_right _ _)
  have hbudget' : max
      (fifteenTouchAngle (radius 14) (radius 2))
      (fifteenVariableDetourAngle (radius 14) (radius 0) (radius 1) (radius 2)) ≤
      (theta 0 + 2 * Real.pi - theta 14) +
        (theta 1 - theta 0) + (theta 2 - theta 1) := by
    convert hbudget using 1 <;> ring
  exact lt_of_lt_of_le hmax hbudget'

/-- A phase-2 `(I,O,O)^5` cycle cannot fit when its five inner radii are the
candidate value and all ten outer radii lie between the threshold and the
candidate wall. -/
theorem fifteenStage4StrictCycle_impossible
    (radius theta : Fin 15 → ℝ)
    (horder : ∀ a b : Fin 15, a.val < b.val → theta a ≤ theta b)
    (hrange : ∀ a : Fin 15, 0 ≤ theta a ∧ theta a ≤ 2 * Real.pi)
    (hpositive : ∀ a : Fin 15, 0 < radius a)
    (hseparated : ∀ a b : Fin 15, a ≠ b →
      4 ≤ pointNorm
        ((polarPoint (radius a) (theta a)).1 -
          (polarPoint (radius b) (theta b)).1,
         (polarPoint (radius a) (theta a)).2 -
          (polarPoint (radius b) (theta b)).2) ^ 2)
    (hinner2 : radius 2 = fifteenCandidateInnerRadius)
    (hinner5 : radius 5 = fifteenCandidateInnerRadius)
    (hinner8 : radius 8 = fifteenCandidateInnerRadius)
    (hinner11 : radius 11 = fifteenCandidateInnerRadius)
    (hinner14 : radius 14 = fifteenCandidateInnerRadius)
    (houter0 : fifteenCandidateInnerThreshold ≤ radius 0 ∧
      radius 0 < fifteenCandidateOuterRadius)
    (houter1 : fifteenCandidateInnerThreshold ≤ radius 1 ∧
      radius 1 < fifteenCandidateOuterRadius)
    (houter3 : fifteenCandidateInnerThreshold ≤ radius 3 ∧
      radius 3 < fifteenCandidateOuterRadius)
    (houter4 : fifteenCandidateInnerThreshold ≤ radius 4 ∧
      radius 4 < fifteenCandidateOuterRadius)
    (houter6 : fifteenCandidateInnerThreshold ≤ radius 6 ∧
      radius 6 < fifteenCandidateOuterRadius)
    (houter7 : fifteenCandidateInnerThreshold ≤ radius 7 ∧
      radius 7 < fifteenCandidateOuterRadius)
    (houter9 : fifteenCandidateInnerThreshold ≤ radius 9 ∧
      radius 9 < fifteenCandidateOuterRadius)
    (houter10 : fifteenCandidateInnerThreshold ≤ radius 10 ∧
      radius 10 < fifteenCandidateOuterRadius)
    (houter12 : fifteenCandidateInnerThreshold ≤ radius 12 ∧
      radius 12 < fifteenCandidateOuterRadius)
    (houter13 : fifteenCandidateInnerThreshold ≤ radius 13 ∧
      radius 13 < fifteenCandidateOuterRadius) : False := by
  have hsector0 := s4PolarStrictSectorGap radius theta 2 3 4 5
    (by decide) (by decide) (by decide) horder hrange hpositive hseparated
    hinner2 hinner5 houter3 houter4
  have hsector1 := s4PolarStrictSectorGap radius theta 5 6 7 8
    (by decide) (by decide) (by decide) horder hrange hpositive hseparated
    hinner5 hinner8 houter6 houter7
  have hsector2 := s4PolarStrictSectorGap radius theta 8 9 10 11
    (by decide) (by decide) (by decide) horder hrange hpositive hseparated
    hinner8 hinner11 houter9 houter10
  have hsector3 := s4PolarStrictSectorGap radius theta 11 12 13 14
    (by decide) (by decide) (by decide) horder hrange hpositive hseparated
    hinner11 hinner14 houter12 houter13
  have hsector4 := s4PolarStrictWrapSectorGap radius theta
    horder hrange hpositive hseparated hinner14 hinner2 houter0 houter1
  have hgapSum :
      (theta 3 - theta 2) + (theta 4 - theta 3) + (theta 5 - theta 4) +
      (theta 6 - theta 5) + (theta 7 - theta 6) + (theta 8 - theta 7) +
      (theta 9 - theta 8) + (theta 10 - theta 9) + (theta 11 - theta 10) +
      (theta 12 - theta 11) + (theta 13 - theta 12) + (theta 14 - theta 13) +
      (theta 0 + 2 * Real.pi - theta 14) +
      (theta 1 - theta 0) + (theta 2 - theta 1) = 2 * Real.pi := by
    ring
  have hstrict : 5 * (2 * fifteenLocalPhi) < 2 * Real.pi := by
    linarith [hsector0, hsector1, hsector2, hsector3, hsector4, hgapSum]
  have hphi : 5 * (2 * fifteenLocalPhi) = 2 * Real.pi := by
    unfold fifteenLocalPhi
    ring
  linarith

private theorem s4WallPush_sorted_radius_eq_of_inner
    {R : ℝ} (P : Packing 15 R)
    (hunit : ∀ i, (P.circles i).radius = 1)
    (hR : R ≤ fifteenCandidateOuterRadius + 1) (k : Fin 15)
    (hinner : fifteenPackingSortedRadius P k <
      fifteenCandidateInnerThreshold) :
    fifteenPackingSortedRadius (fifteen_unit_packing_wall_push P hunit hR) k =
      fifteenPackingSortedRadius P k := by
  rw [fifteenPackingSortedRadius,
    fifteen_unit_packing_wall_push_sorted_index_preserved P hunit hR k]
  change pointNorm (fifteenWallPushedCenter P
      (fifteenPackingSortedIndex P k)) =
    pointNorm ((P.circles (fifteenPackingSortedIndex P k)).center)
  have hcenter : fifteenCenterRadius P (fifteenPackingSortedIndex P k) <
      fifteenCandidateInnerThreshold := by
    simpa [fifteenPackingSortedRadius] using hinner
  rw [fifteenWallPushedCenter, if_neg (not_le_of_gt hcenter)]

/-- The entire arbitrary-packing finite reduction, local rigidity, and strict
wall obstruction now combine to rule out every packing in a subcandidate
container. -/
theorem fifteen_unit_packing_stage4_strict_wall_impossible
    {R : ℝ} (P : Packing 15 R)
    (hunit : ∀ i, (P.circles i).radius = 1)
    (hR : R < fifteenCandidateOuterRadius + 1) : False := by
  have hRle : R ≤ fifteenCandidateOuterRadius + 1 := le_of_lt hR
  obtain ⟨reflected, shift, G, hG, hGtheta, hword,
      hI2, hI5, hI8, hI11, hI14⟩ :=
    fifteen_unit_packing_stage4_local_rigidity P hunit hRle
  let Q := fifteen_unit_packing_wall_push P hunit hRle
  let perm := fifteenStage0DihedralPermutation reflected shift
  let old : Fin 15 → Fin 15 := fun i => perm.symm i
  let radius := fifteenStage0TransformProfile
    (fifteenPackingSortedRadius P) reflected shift
  let theta := fifteenStage0DihedralAngles
    (fifteenPackingSortedAngle P) reflected shift
  have hGQ (i : Fin 15) : G.radii i =
      fifteenPackingSortedRadius Q (old i) := by
    rw [hG]
    rfl
  have hprofile (i : Fin 15) : G.profile i = true ↔ i.val % 3 = 2 :=
    fifteenStage4CanonicalProfile_true_iff G hword i
  have hGinner (i : Fin 15) (hi : i.val % 3 = 2) :
      G.radii i = fifteenCandidateInnerRadius := by
    fin_cases i
    all_goals norm_num at hi
    all_goals simp_all
  have hGouter (i : Fin 15) (hi : i.val % 3 ≠ 2) :
      G.radii i = fifteenCandidateOuterRadius := by
    have hfalse : G.profile i ≠ true := by
      intro htrue
      exact hi ((hprofile i).mp htrue)
    rcases G.hclassification i with hwall | hsmall
    · exact hwall
    · exact False.elim (hfalse ((G.hprofile i).2 hsmall))
  have hcandidateLt : fifteenCandidateInnerRadius <
      fifteenCandidateInnerThreshold :=
    lt_trans (lt_trans fifteenCandidateInnerRadius_lt_851_500
      (by norm_num : (851 : ℝ) / 500 < 2))
      fifteenCandidateInnerThreshold_gt_two
  have hinnerP (i : Fin 15) (hi : i.val % 3 = 2) :
      radius i = fifteenCandidateInnerRadius := by
    have hQsmall : fifteenPackingSortedRadius Q (old i) <
        fifteenCandidateInnerThreshold := by
      rw [← hGQ i, hGinner i hi]
      exact hcandidateLt
    have hPsmall :=
      (fifteen_unit_packing_wall_push_sorted_radius_inner_iff P hunit hRle
        (old i)).1 hQsmall
    have hpushEq := s4WallPush_sorted_radius_eq_of_inner
      P hunit hRle (old i) hPsmall
    calc
      radius i = fifteenPackingSortedRadius P (old i) := by
        rfl
      _ = fifteenPackingSortedRadius Q (old i) := hpushEq.symm
      _ = G.radii i := (hGQ i).symm
      _ = fifteenCandidateInnerRadius := hGinner i hi
  have hrawUpper (i : Fin 15) :
      fifteenPackingSortedRadius P (old i) < fifteenCandidateOuterRadius := by
    have hcontainer := fifteen_unit_packing_center_radius_le_container P hunit
      (fifteenPackingSortedIndex P (old i))
    have hradial : fifteenPackingSortedRadius P (old i) ≤ R - 1 := by
      simpa [fifteenPackingSortedRadius] using hcontainer
    linarith
  have houterP (i : Fin 15) (hi : i.val % 3 ≠ 2) :
      fifteenCandidateInnerThreshold ≤ radius i ∧
        radius i < fifteenCandidateOuterRadius := by
    have hnotSmall : ¬ fifteenPackingSortedRadius P (old i) <
        fifteenCandidateInnerThreshold := by
      intro hsmall
      have hpushSmall :=
        (fifteen_unit_packing_wall_push_sorted_radius_inner_iff P hunit hRle
          (old i)).2 hsmall
      have hpushSmall' : G.radii i < fifteenCandidateInnerThreshold := by
        simpa [hGQ i] using hpushSmall
      rw [hGouter i hi] at hpushSmall'
      exact (not_lt_of_ge
        (le_of_lt fifteenCandidateInnerThreshold_lt_outerRadius)) hpushSmall'
    constructor
    · change fifteenCandidateInnerThreshold ≤
        fifteenPackingSortedRadius P (old i)
      exact le_of_not_gt hnotSmall
    · exact hrawUpper i
  have hsorted : ∀ i j : Fin 15, i.val < j.val →
      fifteenPackingSortedAngle P i ≤ fifteenPackingSortedAngle P j :=
    fun i j hij => fifteenPackingSortedAngle_monotone P hij
  have hangleRange : ∀ i : Fin 15,
      0 ≤ fifteenPackingSortedAngle P i ∧
        fifteenPackingSortedAngle P i ≤ 2 * Real.pi :=
    fifteenPackingSortedAngle_range P
  obtain ⟨horder, hrange⟩ := fifteenStage0DihedralAngles_ordered
    (fifteenPackingSortedAngle P) reflected shift hsorted hangleRange
  have hseparated : ∀ i j : Fin 15, i ≠ j →
      4 ≤ pointNorm
        ((polarPoint (radius i) (theta i)).1 -
          (polarPoint (radius j) (theta j)).1,
         (polarPoint (radius i) (theta i)).2 -
          (polarPoint (radius j) (theta j)).2) ^ 2 := by
    intro i j hij
    have hne : old i ≠ old j := by
      intro heq
      exact hij (perm.symm.injective heq)
    have hdist := fifteenStage0DihedralAngles_distance_sq
      (fifteenPackingSortedRadius P) (fifteenPackingSortedAngle P)
      reflected shift i j
    change 4 ≤ pointNorm
      ((polarPoint (radius i) (theta i)).1 -
        (polarPoint (radius j) (theta j)).1,
       (polarPoint (radius i) (theta i)).2 -
        (polarPoint (radius j) (theta j)).2) ^ 2
    rw [hdist]
    exact fifteen_unit_packing_sorted_pair_separated P hunit hne
  have hpositive : ∀ i : Fin 15, 0 < radius i := by
    intro i
    by_cases hi : i.val % 3 = 2
    · rw [hinnerP i hi]
      exact fifteenCandidateInnerRadius_pos
    · have hthresholdPos : 0 < fifteenCandidateInnerThreshold := by
        linarith [fifteenCandidateInnerThreshold_gt_two]
      exact lt_of_lt_of_le hthresholdPos (houterP i hi).1
  exact fifteenStage4StrictCycle_impossible radius theta horder
    (fun i => ⟨(hrange i).1, (hrange i).2⟩) hpositive hseparated
    (hinnerP 2 (by decide)) (hinnerP 5 (by decide))
    (hinnerP 8 (by decide)) (hinnerP 11 (by decide))
    (hinnerP 14 (by decide))
    (houterP 0 (by decide)) (houterP 1 (by decide))
    (houterP 3 (by decide)) (houterP 4 (by decide))
    (houterP 6 (by decide)) (houterP 7 (by decide))
    (houterP 9 (by decide)) (houterP 10 (by decide))
    (houterP 12 (by decide)) (houterP 13 (by decide))

end CirclePacking
