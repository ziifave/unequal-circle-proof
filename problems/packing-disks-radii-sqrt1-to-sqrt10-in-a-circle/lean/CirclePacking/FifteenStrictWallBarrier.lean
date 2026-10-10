import CirclePacking.FifteenWallPush
import CirclePacking.FifteenLocalAngleGeometry

/-! Strict wall-angle growth for the final five-sector obstruction. -/

namespace CirclePacking

/-- If the two inner endpoints have the candidate radius and both outer
centers lie inside the candidate wall, their three-contact detour is strictly
larger than the symmetric candidate detour. -/
theorem fifteen_candidate_variable_detour_strict
    {x y : ℝ}
    (hx : fifteenCandidateInnerThreshold ≤ x ∧
      x < fifteenCandidateOuterRadius)
    (hy : fifteenCandidateInnerThreshold ≤ y ∧
      y < fifteenCandidateOuterRadius) :
    2 * fifteenLocalPhi < fifteenVariableDetourAngle
      fifteenCandidateInnerRadius x y fifteenCandidateInnerRadius := by
  have ha := fifteenCandidateInnerRadius_pos
  have hb := fifteenCandidateOuterRadius_pos
  have hL := le_of_lt fifteenCandidateInnerThreshold_gt_two
  have hthreshold : fifteenCandidateInnerThreshold =
      fifteenCandidateOuterRadius - 4 / fifteenCandidateOuterRadius := rfl
  have haSq : fifteenCandidateInnerRadius ^ 2 < 4 := by
    nlinarith [fifteenCandidateInnerRadius_lt_851_500]
  have hxpos : 0 < x := by linarith [hL, hx.1]
  have hypos : 0 < y := by linarith [hL, hy.1]
  have hxmargin : fifteenCandidateInnerRadius ^ 2 ≤
      x * fifteenCandidateOuterRadius + 4 := by
    have hprod : 0 ≤ x * fifteenCandidateOuterRadius :=
      mul_nonneg hxpos.le hb.le
    linarith
  have hymargin : fifteenCandidateInnerRadius ^ 2 ≤
      y * fifteenCandidateOuterRadius + 4 := by
    have hprod : 0 ≤ y * fifteenCandidateOuterRadius :=
      mul_nonneg hypos.le hb.le
    linarith
  have hleft := fifteen_touch_angle_antitone_outer_radius
    ha hxpos hb (le_of_lt hx.2) hxmargin
  have hright' := fifteen_touch_angle_antitone_outer_radius
    ha hypos hb (le_of_lt hy.2) hymargin
  have hright : fifteenTouchAngle fifteenCandidateInnerRadius
      fifteenCandidateOuterRadius ≤
      fifteenTouchAngle y fifteenCandidateInnerRadius := by
    calc
      fifteenTouchAngle fifteenCandidateInnerRadius fifteenCandidateOuterRadius ≤
          fifteenTouchAngle fifteenCandidateInnerRadius y := hright'
      _ = fifteenTouchAngle y fifteenCandidateInnerRadius :=
        (fifteenTouchAngle_symm _ _).symm
  have hmiddle := fifteen_wall_touch_angle_strict hb hL hthreshold
    hx hy
  have hdetour : fifteenDetourAngle fifteenCandidateOuterRadius
        fifteenCandidateInnerRadius fifteenCandidateInnerRadius <
      fifteenVariableDetourAngle fifteenCandidateInnerRadius x y
        fifteenCandidateInnerRadius := by
    unfold fifteenDetourAngle fifteenVariableDetourAngle
    linarith
  calc
    2 * fifteenLocalPhi = fifteenDetourAngle fifteenCandidateOuterRadius
        fifteenCandidateInnerRadius fifteenCandidateInnerRadius :=
      fifteenCandidateDetourBase_eq.symm
    _ < fifteenVariableDetourAngle fifteenCandidateInnerRadius x y
        fifteenCandidateInnerRadius := hdetour

/-- The strict comparison applies directly to any two outer-class centers of
a hypothetical packing in a subcandidate container. -/
theorem fifteen_unit_packing_variable_sector_detour_strict
    {R : ℝ} (P : Packing 15 R)
    (hunit : ∀ i, (P.circles i).radius = 1)
    (hR : R < fifteenCandidateOuterRadius + 1)
    (i j k l : Fin 15)
    (hi : fifteenPackingSortedRadius P i = fifteenCandidateInnerRadius)
    (hl : fifteenPackingSortedRadius P l = fifteenCandidateInnerRadius)
    (hj : fifteenCandidateInnerThreshold ≤ fifteenPackingSortedRadius P j)
    (hk : fifteenCandidateInnerThreshold ≤ fifteenPackingSortedRadius P k) :
    2 * fifteenLocalPhi < fifteenVariableDetourAngle
      (fifteenPackingSortedRadius P i) (fifteenPackingSortedRadius P j)
      (fifteenPackingSortedRadius P k) (fifteenPackingSortedRadius P l) := by
  have hjlt : fifteenPackingSortedRadius P j < fifteenCandidateOuterRadius := by
    have hcontainer := fifteen_unit_packing_center_radius_le_container P hunit
      (fifteenPackingSortedIndex P j)
    change fifteenCenterRadius P (fifteenPackingSortedIndex P j) <
      fifteenCandidateOuterRadius
    have hbound : fifteenPackingSortedRadius P j ≤ R - 1 := by
      simpa [fifteenPackingSortedRadius] using hcontainer
    linarith
  have hklt : fifteenPackingSortedRadius P k < fifteenCandidateOuterRadius := by
    have hcontainer := fifteen_unit_packing_center_radius_le_container P hunit
      (fifteenPackingSortedIndex P k)
    have hbound : fifteenPackingSortedRadius P k ≤ R - 1 := by
      simpa [fifteenPackingSortedRadius] using hcontainer
    linarith
  have hstrict := fifteen_candidate_variable_detour_strict
    ⟨hj, hjlt⟩ ⟨hk, hklt⟩
  simpa [hi, hl] using hstrict

/-- Pairwise separation in an actual packing bounds a four-center sector by
the direct and variable-radius detour routes. -/
theorem fifteen_unit_packing_variable_sector_angle_budget
    {R : ℝ} (P : Packing 15 R)
    (hunit : ∀ i, (P.circles i).radius = 1)
    (i j k l : Fin 15)
    (hij : i.1 < j.1) (hjk : j.1 < k.1) (hkl : k.1 < l.1)
    (hi : 0 < fifteenPackingSortedRadius P i)
    (hj : 0 < fifteenPackingSortedRadius P j)
    (hk : 0 < fifteenPackingSortedRadius P k)
    (hl : 0 < fifteenPackingSortedRadius P l) :
    max (fifteenTouchAngle (fifteenPackingSortedRadius P i)
        (fifteenPackingSortedRadius P l))
        (fifteenVariableDetourAngle (fifteenPackingSortedRadius P i)
          (fifteenPackingSortedRadius P j) (fifteenPackingSortedRadius P k)
          (fifteenPackingSortedRadius P l)) ≤
      (fifteenPackingSortedAngle P j - fifteenPackingSortedAngle P i) +
      (fifteenPackingSortedAngle P k - fifteenPackingSortedAngle P j) +
      (fifteenPackingSortedAngle P l - fifteenPackingSortedAngle P k) := by
  have hangle01 := fifteenPackingSortedAngle_monotone P hij
  have hangle12 := fifteenPackingSortedAngle_monotone P hjk
  have hangle23 := fifteenPackingSortedAngle_monotone P hkl
  have hgap01hi : fifteenPackingSortedAngle P j -
      fifteenPackingSortedAngle P i ≤ 2 * Real.pi := by
    have hji := (fifteenPackingSortedAngle_range P j).2
    have hii := (fifteenPackingSortedAngle_range P i).1
    linarith
  have hgap12hi : fifteenPackingSortedAngle P k -
      fifteenPackingSortedAngle P j ≤ 2 * Real.pi := by
    have hki := (fifteenPackingSortedAngle_range P k).2
    have hji := (fifteenPackingSortedAngle_range P j).1
    linarith
  have hgap23hi : fifteenPackingSortedAngle P l -
      fifteenPackingSortedAngle P k ≤ 2 * Real.pi := by
    have hli := (fifteenPackingSortedAngle_range P l).2
    have hki := (fifteenPackingSortedAngle_range P k).1
    linarith
  have hgap03hi : fifteenPackingSortedAngle P l -
      fifteenPackingSortedAngle P i ≤ 2 * Real.pi := by
    have hli := (fifteenPackingSortedAngle_range P l).2
    have hii := (fifteenPackingSortedAngle_range P i).1
    linarith
  have hsepIL := fifteen_unit_packing_sorted_pair_separated P hunit
    (i := i) (j := l) (by omega)
  have hsepIJ := fifteen_unit_packing_sorted_pair_separated P hunit
    (i := i) (j := j) (by omega)
  have hsepJK := fifteen_unit_packing_sorted_pair_separated P hunit
    (i := j) (j := k) (by omega)
  have hsepKL := fifteen_unit_packing_sorted_pair_separated P hunit
    (i := k) (j := l) (by omega)
  exact fifteenLocalVariableSector_max_le_gap hi hj hk hl
    (by linarith) hgap01hi (by linarith) hgap12hi (by linarith) hgap23hi
    hgap03hi hsepIL hsepIJ hsepJK hsepKL

/-- Every sector joining two candidate-radius inner centers through two
outer-class centers consumes strictly more than one fifth of a turn in a
subcandidate container. -/
theorem fifteen_unit_packing_small_container_sector_gap_gt_candidate
    {R : ℝ} (P : Packing 15 R)
    (hunit : ∀ i, (P.circles i).radius = 1)
    (hR : R < fifteenCandidateOuterRadius + 1)
    (i j k l : Fin 15)
    (hij : i.1 < j.1) (hjk : j.1 < k.1) (hkl : k.1 < l.1)
    (hi : fifteenPackingSortedRadius P i = fifteenCandidateInnerRadius)
    (hl : fifteenPackingSortedRadius P l = fifteenCandidateInnerRadius)
    (hj : fifteenCandidateInnerThreshold ≤ fifteenPackingSortedRadius P j)
    (hk : fifteenCandidateInnerThreshold ≤ fifteenPackingSortedRadius P k) :
    2 * fifteenLocalPhi <
      (fifteenPackingSortedAngle P j - fifteenPackingSortedAngle P i) +
      (fifteenPackingSortedAngle P k - fifteenPackingSortedAngle P j) +
      (fifteenPackingSortedAngle P l - fifteenPackingSortedAngle P k) := by
  have hbudget := fifteen_unit_packing_variable_sector_angle_budget P hunit
    i j k l hij hjk hkl
    (by rw [hi]; exact fifteenCandidateInnerRadius_pos)
    (by linarith [fifteenCandidateInnerThreshold_gt_two, hj])
    (by linarith [fifteenCandidateInnerThreshold_gt_two, hk])
    (by rw [hl]; exact fifteenCandidateInnerRadius_pos)
  have hdetour := fifteen_unit_packing_variable_sector_detour_strict
    P hunit hR i j k l hi hl hj hk
  have hmax : 2 * fifteenLocalPhi <
      max (fifteenTouchAngle (fifteenPackingSortedRadius P i)
          (fifteenPackingSortedRadius P l))
        (fifteenVariableDetourAngle (fifteenPackingSortedRadius P i)
          (fifteenPackingSortedRadius P j) (fifteenPackingSortedRadius P k)
          (fifteenPackingSortedRadius P l)) :=
    lt_of_lt_of_le hdetour (le_max_right _ _)
  exact lt_of_lt_of_le hmax hbudget

/-- The closing sector uses the periodic copy of position zero after one full
turn. Its detour still costs strictly more than one fifth of a turn. -/
theorem fifteen_unit_packing_small_container_wrap_sector_gap_gt_candidate
    {R : ℝ} (P : Packing 15 R)
    (hunit : ∀ i, (P.circles i).radius = 1)
    (hR : R < fifteenCandidateOuterRadius + 1)
    (h12 : fifteenPackingSortedRadius P 12 = fifteenCandidateInnerRadius)
    (h0 : fifteenPackingSortedRadius P 0 = fifteenCandidateInnerRadius)
    (h13 : fifteenCandidateInnerThreshold ≤ fifteenPackingSortedRadius P 13)
    (h14 : fifteenCandidateInnerThreshold ≤ fifteenPackingSortedRadius P 14) :
    2 * fifteenLocalPhi <
      (fifteenPackingSortedAngle P 13 - fifteenPackingSortedAngle P 12) +
      (fifteenPackingSortedAngle P 14 - fifteenPackingSortedAngle P 13) +
      (fifteenPackingSortedAngle P 0 + 2 * Real.pi -
        fifteenPackingSortedAngle P 14) := by
  let θ12 := fifteenPackingSortedAngle P (12 : Fin 15)
  let θ13 := fifteenPackingSortedAngle P (13 : Fin 15)
  let θ14 := fifteenPackingSortedAngle P (14 : Fin 15)
  let θ0 := fifteenPackingSortedAngle P (0 : Fin 15)
  let r12 := fifteenPackingSortedRadius P (12 : Fin 15)
  let r13 := fifteenPackingSortedRadius P (13 : Fin 15)
  let r14 := fifteenPackingSortedRadius P (14 : Fin 15)
  let r0 := fifteenPackingSortedRadius P (0 : Fin 15)
  have h1213 : θ12 ≤ θ13 := by
    exact fifteenPackingSortedAngle_monotone P (by decide)
  have h1314 : θ13 ≤ θ14 := by
    exact fifteenPackingSortedAngle_monotone P (by decide)
  have h012 : θ0 ≤ θ12 := by
    exact fifteenPackingSortedAngle_monotone P (by decide)
  have hrange12 := fifteenPackingSortedAngle_range P (12 : Fin 15)
  have hrange13 := fifteenPackingSortedAngle_range P (13 : Fin 15)
  have hrange14 := fifteenPackingSortedAngle_range P (14 : Fin 15)
  have hrange0 := fifteenPackingSortedAngle_range P (0 : Fin 15)
  have hgap1213hi : θ13 - θ12 ≤ 2 * Real.pi := by
    dsimp [θ12, θ13]
    linarith [hrange13.2, hrange12.1]
  have hgap1314hi : θ14 - θ13 ≤ 2 * Real.pi := by
    dsimp [θ13, θ14]
    linarith [hrange14.2, hrange13.1]
  have hgap140lo : 0 ≤ θ0 + 2 * Real.pi - θ14 := by
    dsimp [θ0, θ14]
    linarith [hrange0.1, hrange14.2]
  have hgap140hi : θ0 + 2 * Real.pi - θ14 ≤ 2 * Real.pi := by
    dsimp [θ0, θ14]
    linarith [h012]
  have hgap120hi : θ0 + 2 * Real.pi - θ12 ≤ 2 * Real.pi := by
    dsimp [θ0, θ12]
    linarith [h012]
  have h12pos : 0 < r12 := by simpa [r12, h12] using fifteenCandidateInnerRadius_pos
  have h0pos : 0 < r0 := by simpa [r0, h0] using fifteenCandidateInnerRadius_pos
  have h13pos : 0 < r13 := by
    dsimp [r13]
    linarith [fifteenCandidateInnerThreshold_gt_two, h13]
  have h14pos : 0 < r14 := by
    dsimp [r14]
    linarith [fifteenCandidateInnerThreshold_gt_two, h14]
  have hsep120 := fifteen_unit_packing_sorted_pair_separated P hunit
    (i := (12 : Fin 15)) (j := (0 : Fin 15)) (by decide)
  have hsep1213 := fifteen_unit_packing_sorted_pair_separated P hunit
    (i := (12 : Fin 15)) (j := (13 : Fin 15)) (by decide)
  have hsep1314 := fifteen_unit_packing_sorted_pair_separated P hunit
    (i := (13 : Fin 15)) (j := (14 : Fin 15)) (by decide)
  have hsep140 := fifteen_unit_packing_sorted_pair_separated P hunit
    (i := (14 : Fin 15)) (j := (0 : Fin 15)) (by decide)
  have hsep120periodic : 4 ≤ pointNorm
      ((polarPoint r12 θ12).1 -
        (polarPoint r0 (θ0 + 2 * Real.pi)).1,
       (polarPoint r12 θ12).2 -
        (polarPoint r0 (θ0 + 2 * Real.pi)).2) ^ 2 := by
    rw [fifteenPolarPoint_add_two_pi]
    simpa [r12, r0, θ12, θ0] using hsep120
  have hsep140periodic : 4 ≤ pointNorm
      ((polarPoint r14 θ14).1 -
        (polarPoint r0 (θ0 + 2 * Real.pi)).1,
       (polarPoint r14 θ14).2 -
        (polarPoint r0 (θ0 + 2 * Real.pi)).2) ^ 2 := by
    rw [fifteenPolarPoint_add_two_pi]
    simpa [r14, r0, θ14, θ0] using hsep140
  have hbudget := fifteenLocalVariableSector_max_le_gap
    (by simpa [r12] using h12pos) (by simpa [r13] using h13pos)
    (by simpa [r14] using h14pos) (by simpa [r0] using h0pos)
    (by linarith [h1213]) hgap1213hi (by linarith [h1314]) hgap1314hi
    hgap140lo (by linarith [hgap140hi]) hgap120hi
    hsep120periodic
    (by simpa [r12, r13, θ12, θ13] using hsep1213)
    (by simpa [r13, r14, θ13, θ14] using hsep1314)
    hsep140periodic
  have hdetour := fifteen_unit_packing_variable_sector_detour_strict
    P hunit hR (12 : Fin 15) (13 : Fin 15) (14 : Fin 15) (0 : Fin 15)
    h12 h0 h13 h14
  have hmax : 2 * fifteenLocalPhi <
      max (fifteenTouchAngle r12 r0)
        (fifteenVariableDetourAngle r12 r13 r14 r0) := by
    simpa [r12, r13, r14, r0, h12, h0] using
      (lt_of_lt_of_le hdetour (le_max_right _ _))
  have hbudget' : max (fifteenTouchAngle
        (fifteenPackingSortedRadius P 12) (fifteenPackingSortedRadius P 0))
      (fifteenVariableDetourAngle (fifteenPackingSortedRadius P 12)
        (fifteenPackingSortedRadius P 13) (fifteenPackingSortedRadius P 14)
        (fifteenPackingSortedRadius P 0)) ≤
      (fifteenPackingSortedAngle P 13 - fifteenPackingSortedAngle P 12) +
      (fifteenPackingSortedAngle P 14 - fifteenPackingSortedAngle P 13) +
      (fifteenPackingSortedAngle P 0 + 2 * Real.pi -
        fifteenPackingSortedAngle P 14) := by
    simpa [r12, r13, r14, r0, θ12, θ13, θ14, θ0] using hbudget
  exact lt_of_lt_of_le hmax (by simpa [r12, r13, r14, r0, h12, h0] using hbudget')

/-- The canonical `(I,O,O)^5` pattern cannot occur in a subcandidate
container once its five inner radii are forced to the candidate value. Each
of the five detour sectors would consume strictly more than a fifth turn. -/
theorem fifteen_unit_packing_candidate_cycle_impossible
    {R : ℝ} (P : Packing 15 R)
    (hunit : ∀ i, (P.circles i).radius = 1)
    (hR : R < fifteenCandidateOuterRadius + 1)
    (hI0 : fifteenPackingSortedRadius P 0 = fifteenCandidateInnerRadius)
    (hI3 : fifteenPackingSortedRadius P 3 = fifteenCandidateInnerRadius)
    (hI6 : fifteenPackingSortedRadius P 6 = fifteenCandidateInnerRadius)
    (hI9 : fifteenPackingSortedRadius P 9 = fifteenCandidateInnerRadius)
    (hI12 : fifteenPackingSortedRadius P 12 = fifteenCandidateInnerRadius)
    (hO1 : fifteenCandidateInnerThreshold ≤ fifteenPackingSortedRadius P 1)
    (hO2 : fifteenCandidateInnerThreshold ≤ fifteenPackingSortedRadius P 2)
    (hO4 : fifteenCandidateInnerThreshold ≤ fifteenPackingSortedRadius P 4)
    (hO5 : fifteenCandidateInnerThreshold ≤ fifteenPackingSortedRadius P 5)
    (hO7 : fifteenCandidateInnerThreshold ≤ fifteenPackingSortedRadius P 7)
    (hO8 : fifteenCandidateInnerThreshold ≤ fifteenPackingSortedRadius P 8)
    (hO10 : fifteenCandidateInnerThreshold ≤ fifteenPackingSortedRadius P 10)
    (hO11 : fifteenCandidateInnerThreshold ≤ fifteenPackingSortedRadius P 11)
    (hO13 : fifteenCandidateInnerThreshold ≤ fifteenPackingSortedRadius P 13)
    (hO14 : fifteenCandidateInnerThreshold ≤ fifteenPackingSortedRadius P 14) :
    False := by
  have hsector0 := fifteen_unit_packing_small_container_sector_gap_gt_candidate
    P hunit hR 0 1 2 3 (by decide) (by decide) (by decide)
    hI0 hI3 hO1 hO2
  have hsector1 := fifteen_unit_packing_small_container_sector_gap_gt_candidate
    P hunit hR 3 4 5 6 (by decide) (by decide) (by decide)
    hI3 hI6 hO4 hO5
  have hsector2 := fifteen_unit_packing_small_container_sector_gap_gt_candidate
    P hunit hR 6 7 8 9 (by decide) (by decide) (by decide)
    hI6 hI9 hO7 hO8
  have hsector3 := fifteen_unit_packing_small_container_sector_gap_gt_candidate
    P hunit hR 9 10 11 12 (by decide) (by decide) (by decide)
    hI9 hI12 hO10 hO11
  have hsector4 :=
    fifteen_unit_packing_small_container_wrap_sector_gap_gt_candidate
      P hunit hR hI12 hI0 hO13 hO14
  have hgapSum :
      (fifteenPackingSortedAngle P 1 - fifteenPackingSortedAngle P 0) +
      (fifteenPackingSortedAngle P 2 - fifteenPackingSortedAngle P 1) +
      (fifteenPackingSortedAngle P 3 - fifteenPackingSortedAngle P 2) +
      (fifteenPackingSortedAngle P 4 - fifteenPackingSortedAngle P 3) +
      (fifteenPackingSortedAngle P 5 - fifteenPackingSortedAngle P 4) +
      (fifteenPackingSortedAngle P 6 - fifteenPackingSortedAngle P 5) +
      (fifteenPackingSortedAngle P 7 - fifteenPackingSortedAngle P 6) +
      (fifteenPackingSortedAngle P 8 - fifteenPackingSortedAngle P 7) +
      (fifteenPackingSortedAngle P 9 - fifteenPackingSortedAngle P 8) +
      (fifteenPackingSortedAngle P 10 - fifteenPackingSortedAngle P 9) +
      (fifteenPackingSortedAngle P 11 - fifteenPackingSortedAngle P 10) +
      (fifteenPackingSortedAngle P 12 - fifteenPackingSortedAngle P 11) +
      (fifteenPackingSortedAngle P 13 - fifteenPackingSortedAngle P 12) +
      (fifteenPackingSortedAngle P 14 - fifteenPackingSortedAngle P 13) +
      (fifteenPackingSortedAngle P 0 + 2 * Real.pi -
        fifteenPackingSortedAngle P 14) = 2 * Real.pi := by ring
  have hsectors : 5 * (2 * fifteenLocalPhi) < 2 * Real.pi := by
    linarith [hsector0, hsector1, hsector2, hsector3, hsector4, hgapSum]
  have hphi : 5 * (2 * fifteenLocalPhi) = 2 * Real.pi := by
    unfold fifteenLocalPhi
    ring
  linarith

end CirclePacking
