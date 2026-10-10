import CirclePacking.FifteenPackingLocalRigidity
import CirclePacking.FifteenStrictWallBarrier

/-! Assemble the final analytic exit once the finite reduction has isolated
the canonical five-inner pattern and its certified radial box.  The local
rigidity theorem is applied after wall replacement; its exact inner radii are
then transported back to the original packing, where the strict wall barrier
rules out a container smaller than the candidate. -/

namespace CirclePacking

noncomputable def fifteenStrictWallPush
    {R : ℝ} (P : Packing 15 R)
    (hunit : ∀ i, (P.circles i).radius = 1)
    (hR : R < fifteenCandidateOuterRadius + 1) :
    Packing 15 (fifteenCandidateOuterRadius + 1) :=
  fifteen_unit_packing_wall_push P hunit (le_of_lt hR)

private theorem fifteenStrictWallPush_sorted_radius_eq_of_inner
    {R : ℝ} (P : Packing 15 R)
    (hunit : ∀ i, (P.circles i).radius = 1)
    (hR : R < fifteenCandidateOuterRadius + 1) (k : Fin 15)
    (hinner : fifteenPackingSortedRadius P k <
      fifteenCandidateInnerThreshold) :
    fifteenPackingSortedRadius (fifteenStrictWallPush P hunit hR) k =
      fifteenPackingSortedRadius P k := by
  change pointNorm
      ((fifteenStrictWallPush P hunit hR).circles
        (fifteenPackingSortedIndex (fifteenStrictWallPush P hunit hR) k)).center =
    pointNorm ((P.circles (fifteenPackingSortedIndex P k)).center)
  rw [fifteenStrictWallPush,
    fifteen_unit_packing_wall_push_sorted_index_preserved P hunit
      (le_of_lt hR) k]
  change pointNorm (fifteenWallPushedCenter P
      (fifteenPackingSortedIndex P k)) = _
  have hcenterInner : fifteenCenterRadius P
      (fifteenPackingSortedIndex P k) < fifteenCandidateInnerThreshold := by
    simpa [fifteenPackingSortedRadius] using hinner
  rw [fifteenWallPushedCenter, if_neg (not_le_of_gt hcenterInner)]

/-- If wall replacement leaves the canonical radial word `(I,O,O)^5` and
the five inner radii in the certified local box, then the original packing
cannot fit in a circle strictly smaller than the candidate. -/
theorem fifteen_unit_packing_last_survivor_impossible
    {R : ℝ} (P : Packing 15 R)
    (hunit : ∀ i, (P.circles i).radius = 1)
    (hR : R < fifteenCandidateOuterRadius + 1)
    (r₀ r₁ r₂ r₃ r₄ : ℝ)
    (hQ₀ : fifteenPackingSortedRadius
      (fifteenStrictWallPush P hunit hR) 0 = r₀)
    (hQ₁ : fifteenPackingSortedRadius
      (fifteenStrictWallPush P hunit hR) 1 = fifteenCandidateOuterRadius)
    (hQ₂ : fifteenPackingSortedRadius
      (fifteenStrictWallPush P hunit hR) 2 = fifteenCandidateOuterRadius)
    (hQ₃ : fifteenPackingSortedRadius
      (fifteenStrictWallPush P hunit hR) 3 = r₁)
    (hQ₄ : fifteenPackingSortedRadius
      (fifteenStrictWallPush P hunit hR) 4 = fifteenCandidateOuterRadius)
    (hQ₅ : fifteenPackingSortedRadius
      (fifteenStrictWallPush P hunit hR) 5 = fifteenCandidateOuterRadius)
    (hQ₆ : fifteenPackingSortedRadius
      (fifteenStrictWallPush P hunit hR) 6 = r₂)
    (hQ₇ : fifteenPackingSortedRadius
      (fifteenStrictWallPush P hunit hR) 7 = fifteenCandidateOuterRadius)
    (hQ₈ : fifteenPackingSortedRadius
      (fifteenStrictWallPush P hunit hR) 8 = fifteenCandidateOuterRadius)
    (hQ₉ : fifteenPackingSortedRadius
      (fifteenStrictWallPush P hunit hR) 9 = r₃)
    (hQ₁₀ : fifteenPackingSortedRadius
      (fifteenStrictWallPush P hunit hR) 10 = fifteenCandidateOuterRadius)
    (hQ₁₁ : fifteenPackingSortedRadius
      (fifteenStrictWallPush P hunit hR) 11 = fifteenCandidateOuterRadius)
    (hQ₁₂ : fifteenPackingSortedRadius
      (fifteenStrictWallPush P hunit hR) 12 = r₄)
    (hQ₁₃ : fifteenPackingSortedRadius
      (fifteenStrictWallPush P hunit hR) 13 = fifteenCandidateOuterRadius)
    (hQ₁₄ : fifteenPackingSortedRadius
      (fifteenStrictWallPush P hunit hR) 14 = fifteenCandidateOuterRadius)
    (hr₀ : r₀ ∈ Set.Icc (42 / 25 : ℝ) (43 / 25))
    (hr₁ : r₁ ∈ Set.Icc (42 / 25 : ℝ) (43 / 25))
    (hr₂ : r₂ ∈ Set.Icc (42 / 25 : ℝ) (43 / 25))
    (hr₃ : r₃ ∈ Set.Icc (42 / 25 : ℝ) (43 / 25))
    (hr₄ : r₄ ∈ Set.Icc (42 / 25 : ℝ) (43 / 25)) : False := by
  let Q := fifteenStrictWallPush P hunit hR
  have hQrad₀ : fifteenPackingSortedRadius Q 0 = r₀ := by
    simpa [Q, fifteenStrictWallPush] using hQ₀
  have hQrad₁ : fifteenPackingSortedRadius Q 1 = fifteenCandidateOuterRadius := by
    simpa [Q, fifteenStrictWallPush] using hQ₁
  have hQrad₂ : fifteenPackingSortedRadius Q 2 = fifteenCandidateOuterRadius := by
    simpa [Q, fifteenStrictWallPush] using hQ₂
  have hQrad₃ : fifteenPackingSortedRadius Q 3 = r₁ := by
    simpa [Q, fifteenStrictWallPush] using hQ₃
  have hQrad₄ : fifteenPackingSortedRadius Q 4 = fifteenCandidateOuterRadius := by
    simpa [Q, fifteenStrictWallPush] using hQ₄
  have hQrad₅ : fifteenPackingSortedRadius Q 5 = fifteenCandidateOuterRadius := by
    simpa [Q, fifteenStrictWallPush] using hQ₅
  have hQrad₆ : fifteenPackingSortedRadius Q 6 = r₂ := by
    simpa [Q, fifteenStrictWallPush] using hQ₆
  have hQrad₇ : fifteenPackingSortedRadius Q 7 = fifteenCandidateOuterRadius := by
    simpa [Q, fifteenStrictWallPush] using hQ₇
  have hQrad₈ : fifteenPackingSortedRadius Q 8 = fifteenCandidateOuterRadius := by
    simpa [Q, fifteenStrictWallPush] using hQ₈
  have hQrad₉ : fifteenPackingSortedRadius Q 9 = r₃ := by
    simpa [Q, fifteenStrictWallPush] using hQ₉
  have hQrad₁₀ : fifteenPackingSortedRadius Q 10 = fifteenCandidateOuterRadius := by
    simpa [Q, fifteenStrictWallPush] using hQ₁₀
  have hQrad₁₁ : fifteenPackingSortedRadius Q 11 = fifteenCandidateOuterRadius := by
    simpa [Q, fifteenStrictWallPush] using hQ₁₁
  have hQrad₁₂ : fifteenPackingSortedRadius Q 12 = r₄ := by
    simpa [Q, fifteenStrictWallPush] using hQ₁₂
  have hQrad₁₃ : fifteenPackingSortedRadius Q 13 = fifteenCandidateOuterRadius := by
    simpa [Q, fifteenStrictWallPush] using hQ₁₃
  have hQrad₁₄ : fifteenPackingSortedRadius Q 14 = fifteenCandidateOuterRadius := by
    simpa [Q, fifteenStrictWallPush] using hQ₁₄
  have hQunit : ∀ i, (Q.circles i).radius = 1 := by
    intro i
    exact fifteen_unit_packing_wall_push_preserves_unit_radii P hunit
      (le_of_lt hR) i
  have hrigid := fifteen_unit_packing_local_rigidity_of_survivor_pattern
    Q hQunit r₀ r₁ r₂ r₃ r₄
    hQrad₀ hQrad₁ hQrad₂ hQrad₃ hQrad₄ hQrad₅ hQrad₆ hQrad₇ hQrad₈ hQrad₉ hQrad₁₀ hQrad₁₁ hQrad₁₂ hQrad₁₃ hQrad₁₄
    hr₀ hr₁ hr₂ hr₃ hr₄
  have hinner₀ : r₀ = fifteenCandidateInnerRadius := hrigid.1.1
  have hinner₁ : r₁ = fifteenCandidateInnerRadius := hrigid.1.2.1
  have hinner₂ : r₂ = fifteenCandidateInnerRadius := hrigid.1.2.2.1
  have hinner₃ : r₃ = fifteenCandidateInnerRadius := hrigid.1.2.2.2.1
  have hinner₄ : r₄ = fifteenCandidateInnerRadius := hrigid.1.2.2.2.2
  have hcandidateLt : fifteenCandidateInnerRadius <
      fifteenCandidateInnerThreshold := by
    exact lt_trans (lt_trans fifteenCandidateInnerRadius_lt_851_500
      (by norm_num : (851 : ℝ) / 500 < 2))
      fifteenCandidateInnerThreshold_gt_two
  have hQinner₀ : fifteenPackingSortedRadius Q 0 <
      fifteenCandidateInnerThreshold := by
    rw [hQrad₀, hinner₀]
    exact hcandidateLt
  have hQinner₃ : fifteenPackingSortedRadius Q 3 <
      fifteenCandidateInnerThreshold := by
    rw [hQrad₃, hinner₁]
    exact hcandidateLt
  have hQinner₆ : fifteenPackingSortedRadius Q 6 <
      fifteenCandidateInnerThreshold := by
    rw [hQrad₆, hinner₂]
    exact hcandidateLt
  have hQinner₉ : fifteenPackingSortedRadius Q 9 <
      fifteenCandidateInnerThreshold := by
    rw [hQrad₉, hinner₃]
    exact hcandidateLt
  have hQinner₁₂ : fifteenPackingSortedRadius Q 12 <
      fifteenCandidateInnerThreshold := by
    rw [hQrad₁₂, hinner₄]
    exact hcandidateLt
  have hPinner₀ := (fifteen_unit_packing_wall_push_sorted_radius_inner_iff
    P hunit (le_of_lt hR) 0).1 (by simpa [Q, fifteenStrictWallPush] using hQinner₀)
  have hPinner₃ := (fifteen_unit_packing_wall_push_sorted_radius_inner_iff
    P hunit (le_of_lt hR) 3).1 (by simpa [Q, fifteenStrictWallPush] using hQinner₃)
  have hPinner₆ := (fifteen_unit_packing_wall_push_sorted_radius_inner_iff
    P hunit (le_of_lt hR) 6).1 (by simpa [Q, fifteenStrictWallPush] using hQinner₆)
  have hPinner₉ := (fifteen_unit_packing_wall_push_sorted_radius_inner_iff
    P hunit (le_of_lt hR) 9).1 (by simpa [Q, fifteenStrictWallPush] using hQinner₉)
  have hPinner₁₂ := (fifteen_unit_packing_wall_push_sorted_radius_inner_iff
    P hunit (le_of_lt hR) 12).1 (by simpa [Q, fifteenStrictWallPush] using hQinner₁₂)
  have hI₀ : fifteenPackingSortedRadius P 0 = fifteenCandidateInnerRadius := by
    calc
      fifteenPackingSortedRadius P 0 =
          fifteenPackingSortedRadius Q 0 :=
        (fifteenStrictWallPush_sorted_radius_eq_of_inner P hunit hR 0 hPinner₀).symm
      _ = r₀ := hQrad₀
      _ = fifteenCandidateInnerRadius := hinner₀
  have hI₃ : fifteenPackingSortedRadius P 3 = fifteenCandidateInnerRadius := by
    calc
      fifteenPackingSortedRadius P 3 =
          fifteenPackingSortedRadius Q 3 :=
        (fifteenStrictWallPush_sorted_radius_eq_of_inner P hunit hR 3 hPinner₃).symm
      _ = r₁ := hQrad₃
      _ = fifteenCandidateInnerRadius := hinner₁
  have hI₆ : fifteenPackingSortedRadius P 6 = fifteenCandidateInnerRadius := by
    calc
      fifteenPackingSortedRadius P 6 =
          fifteenPackingSortedRadius Q 6 :=
        (fifteenStrictWallPush_sorted_radius_eq_of_inner P hunit hR 6 hPinner₆).symm
      _ = r₂ := hQrad₆
      _ = fifteenCandidateInnerRadius := hinner₂
  have hI₉ : fifteenPackingSortedRadius P 9 = fifteenCandidateInnerRadius := by
    calc
      fifteenPackingSortedRadius P 9 =
          fifteenPackingSortedRadius Q 9 :=
        (fifteenStrictWallPush_sorted_radius_eq_of_inner P hunit hR 9 hPinner₉).symm
      _ = r₃ := hQrad₉
      _ = fifteenCandidateInnerRadius := hinner₃
  have hI₁₂ : fifteenPackingSortedRadius P 12 = fifteenCandidateInnerRadius := by
    calc
      fifteenPackingSortedRadius P 12 =
          fifteenPackingSortedRadius Q 12 :=
        (fifteenStrictWallPush_sorted_radius_eq_of_inner P hunit hR 12 hPinner₁₂).symm
      _ = r₄ := hQrad₁₂
      _ = fifteenCandidateInnerRadius := hinner₄
  have hOuterRadius : fifteenCandidateInnerThreshold <
      fifteenCandidateOuterRadius := fifteenCandidateInnerThreshold_lt_outerRadius
  have houter_at (k : Fin 15)
      (hQouter : fifteenPackingSortedRadius Q k = fifteenCandidateOuterRadius) :
      fifteenCandidateInnerThreshold ≤ fifteenPackingSortedRadius P k := by
    by_contra hnot
    have hinner : fifteenPackingSortedRadius P k <
        fifteenCandidateInnerThreshold := lt_of_not_ge hnot
    have hpush := (fifteen_unit_packing_wall_push_sorted_radius_inner_iff
      P hunit (le_of_lt hR) k).2 hinner
    have hpushQ : fifteenPackingSortedRadius Q k <
        fifteenCandidateInnerThreshold := by
      simpa [Q, fifteenStrictWallPush] using hpush
    rw [hQouter] at hpushQ
    exact (not_lt_of_ge (le_of_lt hOuterRadius)) hpushQ
  have hO₁ := houter_at 1 hQrad₁
  have hO₂ := houter_at 2 hQrad₂
  have hO₄ := houter_at 4 hQrad₄
  have hO₅ := houter_at 5 hQrad₅
  have hO₇ := houter_at 7 hQrad₇
  have hO₈ := houter_at 8 hQrad₈
  have hO₁₀ := houter_at 10 hQrad₁₀
  have hO₁₁ := houter_at 11 hQrad₁₁
  have hO₁₃ := houter_at 13 hQrad₁₃
  have hO₁₄ := houter_at 14 hQrad₁₄
  exact fifteen_unit_packing_candidate_cycle_impossible P hunit hR
    hI₀ hI₃ hI₆ hI₉ hI₁₂
    hO₁ hO₂ hO₄ hO₅ hO₇ hO₈ hO₁₀ hO₁₁ hO₁₃ hO₁₄

end CirclePacking
