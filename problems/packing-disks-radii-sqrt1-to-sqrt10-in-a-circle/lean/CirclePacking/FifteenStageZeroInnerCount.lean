import CirclePacking.FifteenWallPush

/-! A geometric upper bound for the number of centers below the Stage 0 wall
threshold.  Eight centers with radii at least one would force eight angular
gaps larger than one eighth of a turn; at most one center can have radius
below one. -/

namespace CirclePacking

theorem fifteenCandidateInnerThreshold_lt_twelve_fifths :
    fifteenCandidateInnerThreshold < (12 : ℝ) / 5 := by
  have hb := fifteenCandidateOuterRadius_mem_Ioo_352_353
  have hbpos := fifteenCandidateOuterRadius_pos
  have hquot : (400 : ℝ) / 353 < 4 / fifteenCandidateOuterRadius := by
    apply (lt_div_iff₀ hbpos).2
    nlinarith [hb.2]
  have hrat : (353 : ℝ) / 100 - 400 / 353 < (12 : ℝ) / 5 := by
    norm_num
  rw [show fifteenCandidateInnerThreshold =
      fifteenCandidateOuterRadius - 4 / fifteenCandidateOuterRadius by rfl]
  linarith [hb.2, hquot]

private theorem fifteen_inner_pair_cosine_le_two_thirds
    {a b : ℝ}
    (ha0 : 0 < a) (hb0 : 0 < b)
    (ha1 : 1 ≤ a) (hb1 : 1 ≤ b)
    (haU : a ≤ (12 : ℝ) / 5) (hbU : b ≤ (12 : ℝ) / 5) :
    touchCosine a b 2 ≤ (2 : ℝ) / 3 := by
  have haSq : a ^ 2 ≤ (17 : ℝ) / 5 * a - 12 / 5 := by
    have hprod := mul_nonpos_of_nonneg_of_nonpos
      (show 0 ≤ a - 1 by linarith)
      (show a - (12 : ℝ) / 5 ≤ 0 by linarith)
    nlinarith
  have hbSq : b ^ 2 ≤ (17 : ℝ) / 5 * b - 12 / 5 := by
    have hprod := mul_nonpos_of_nonneg_of_nonpos
      (show 0 ≤ b - 1 by linarith)
      (show b - (12 : ℝ) / 5 ≤ 0 by linarith)
    nlinarith
  let x : ℝ := a - 1
  let y : ℝ := b - 1
  have hx0 : 0 ≤ x := by dsimp [x]; linarith
  have hxU : x ≤ (7 : ℝ) / 5 := by dsimp [x]; linarith
  have hy0 : 0 ≤ y := by dsimp [y]; linarith
  have hyU : y ≤ (7 : ℝ) / 5 := by dsimp [y]; linarith
  have hfactor : 0 ≤ ((7 : ℝ) / 5 - x) * (31 - 20 * y) :=
    mul_nonneg (by linarith) (by nlinarith)
  have hbilinear : 0 ≤ 20 * a * b - 51 * a - 51 * b + 132 := by
    have hid : 20 * a * b - 51 * a - 51 * b + 132 =
        (33 : ℝ) / 5 - 3 * y + ((7 : ℝ) / 5 - x) * (31 - 20 * y) := by
      dsimp [x, y]
      ring
    rw [hid]
    nlinarith [hfactor]
  have hnum : a ^ 2 + b ^ 2 - 4 ≤ (4 : ℝ) / 3 * (a * b) := by
    nlinarith [haSq, hbSq, hbilinear]
  unfold touchCosine
  apply (div_le_iff₀ (by positivity : 0 < 2 * a * b)).2
  nlinarith [hnum]

private theorem fifteen_inner_gap_angle_gt_pi_div_four :
    Real.pi / 4 < Real.arccos ((2 : ℝ) / 3) := by
  have hsqrt : (4 : ℝ) / 3 < Real.sqrt 2 := by
    apply Real.lt_sqrt_of_sq_lt
    norm_num
  have hcos : (2 : ℝ) / 3 < Real.cos (Real.pi / 4) := by
    rw [Real.cos_pi_div_four]
    nlinarith [hsqrt]
  have harccos := Real.arccos_lt_arccos
    (show -1 ≤ (2 : ℝ) / 3 by norm_num)
    hcos (Real.cos_le_one (Real.pi / 4))
  have hangle : Real.arccos (Real.cos (Real.pi / 4)) = Real.pi / 4 := by
    apply Real.arccos_cos
    · positivity
    · nlinarith [Real.pi_pos]
  rw [hangle] at harccos
  exact harccos

private theorem fifteen_inner_eight_large_centers_impossible
    {R : ℝ} (P : Packing 15 R)
    (hunit : ∀ i, (P.circles i).radius = 1)
    (S : Finset (Fin 15)) (hcard : S.card = 8)
    (hinner : ∀ i ∈ S,
      fifteenPackingSortedRadius P i < fifteenCandidateInnerThreshold)
    (hlarge : ∀ i ∈ S, 1 ≤ fifteenPackingSortedRadius P i) : False := by
  classical
  let order : Fin 8 ↪o Fin 15 := S.orderEmbOfFin hcard
  let theta : Fin 8 → ℝ := fun k => fifteenPackingSortedAngle P (order k)
  have hinS (k : Fin 8) : order k ∈ S := by
    simpa [order] using S.orderEmbOfFin_mem hcard k
  have hradLower (k : Fin 8) :
      1 ≤ fifteenPackingSortedRadius P (order k) := hlarge (order k) (hinS k)
  have hradUpper (k : Fin 8) :
      fifteenPackingSortedRadius P (order k) ≤ (12 : ℝ) / 5 := by
    exact le_of_lt (lt_of_lt_of_le
      (hinner (order k) (hinS k)) fifteenCandidateInnerThreshold_lt_twelve_fifths.le)
  have hgap (k : Fin 7) :
      Real.arccos ((2 : ℝ) / 3) ≤ theta k.succ - theta k.castSucc := by
    have hkn : k.castSucc < k.succ := Fin.castSucc_lt_succ_iff.mpr le_rfl
    have hlt : (order k.castSucc).1 < (order k.succ).1 := order.strictMono hkn
    have ha0 : 0 < fifteenPackingSortedRadius P (order k.castSucc) := by
      linarith [hradLower k.castSucc]
    have hb0 : 0 < fifteenPackingSortedRadius P (order k.succ) := by
      linarith [hradLower k.succ]
    have hcap := fifteen_inner_pair_cosine_le_two_thirds
      ha0 hb0 (hradLower k.castSucc) (hradLower k.succ)
      (hradUpper k.castSucc) (hradUpper k.succ)
    have hangle : Real.arccos ((2 : ℝ) / 3) ≤
        touchAngle (fifteenPackingSortedRadius P (order k.castSucc))
          (fifteenPackingSortedRadius P (order k.succ)) 2 := by
      unfold touchAngle
      exact Real.antitone_arccos hcap
    have hsep := fifteen_unit_packing_sorted_pair_separated P hunit
      (ne_of_lt hlt)
    have hdelta0 : 0 ≤ theta k.succ - theta k.castSucc :=
      sub_nonneg.mpr (fifteenPackingSortedAngle_monotone P hlt)
    have hdelta2 : theta k.succ - theta k.castSucc ≤ 2 * Real.pi := by
      have hhi := fifteenPackingSortedAngle_range P (order k.succ)
      have hlo := fifteenPackingSortedAngle_range P (order k.castSucc)
      dsimp [theta] at hhi hlo ⊢
      linarith
    have hsepNorm : 4 ≤ pointNorm
        ((polarPoint (fifteenPackingSortedRadius P (order k.castSucc))
            (theta k.castSucc)).1 -
          (polarPoint (fifteenPackingSortedRadius P (order k.succ))
            (theta k.succ)).1,
         (polarPoint (fifteenPackingSortedRadius P (order k.castSucc))
            (theta k.castSucc)).2 -
          (polarPoint (fifteenPackingSortedRadius P (order k.succ))
            (theta k.succ)).2) ^ 2 := by
      simpa only [theta] using hsep
    have hsep' : (2 : ℝ) ^ 2 ≤ pointNorm
        ((polarPoint (fifteenPackingSortedRadius P (order k.castSucc))
            (theta k.castSucc)).1 -
          (polarPoint (fifteenPackingSortedRadius P (order k.succ))
            (theta k.succ)).1,
         (polarPoint (fifteenPackingSortedRadius P (order k.castSucc))
            (theta k.castSucc)).2 -
          (polarPoint (fifteenPackingSortedRadius P (order k.succ))
            (theta k.succ)).2) ^ 2 := by
      calc
        (2 : ℝ) ^ 2 = 4 := by norm_num
        _ ≤ _ := hsepNorm
    have hgap' := fifteen_polar_touch_angle_ordered_gap
      ha0 hb0 (Real.arccos_le_pi _) hdelta0 hdelta2 hsep' hangle
    simpa [theta] using hgap'.1
  have hspanNat : ∀ (n : Nat) (hn : n ≤ 7),
      (n : ℝ) * Real.arccos ((2 : ℝ) / 3) ≤
        theta ⟨n, by omega⟩ - theta (0 : Fin 8) := by
    intro n
    induction n with
    | zero =>
        intro _
        simp [theta]
    | succ n ih =>
        intro hn
        have hn7 : n ≤ 7 := by omega
        have hprev := ih hn7
        let k : Fin 7 := ⟨n, by omega⟩
        have hstep : Real.arccos ((2 : ℝ) / 3) ≤
            theta ⟨n + 1, by omega⟩ - theta ⟨n, by omega⟩ := by
          simpa [k] using hgap k
        calc
          ((n + 1 : Nat) : ℝ) * Real.arccos ((2 : ℝ) / 3) =
              (n : ℝ) * Real.arccos ((2 : ℝ) / 3) +
                Real.arccos ((2 : ℝ) / 3) := by push_cast; ring
          _ ≤ (theta ⟨n, by omega⟩ - theta (0 : Fin 8)) +
                (theta ⟨n + 1, by omega⟩ - theta ⟨n, by omega⟩) :=
              add_le_add hprev hstep
          _ = theta ⟨n + 1, by omega⟩ - theta (0 : Fin 8) := by ring
  have hspan : (7 : ℝ) * Real.arccos ((2 : ℝ) / 3) ≤
      theta (7 : Fin 8) - theta (0 : Fin 8) := by
    simpa using hspanNat 7 (by omega)
  have hlast : (order (0 : Fin 8)).1 < (order (7 : Fin 8)).1 :=
    order.strictMono (by decide)
  have ha0 : 0 < fifteenPackingSortedRadius P (order 0) :=
    lt_of_lt_of_le (by norm_num) (hradLower 0)
  have hb0 : 0 < fifteenPackingSortedRadius P (order 7) :=
    lt_of_lt_of_le (by norm_num) (hradLower 7)
  have hcap := fifteen_inner_pair_cosine_le_two_thirds
    ha0 hb0 (hradLower 0) (hradLower 7) (hradUpper 0) (hradUpper 7)
  have hangle : Real.arccos ((2 : ℝ) / 3) ≤
      touchAngle (fifteenPackingSortedRadius P (order 0))
        (fifteenPackingSortedRadius P (order 7)) 2 := by
    unfold touchAngle
    exact Real.antitone_arccos hcap
  have hsep := fifteen_unit_packing_sorted_pair_separated P hunit
    (ne_of_lt hlast)
  have hdelta0 : 0 ≤ theta 7 - theta 0 := by
    dsimp [theta]
    exact sub_nonneg.mpr (fifteenPackingSortedAngle_monotone P hlast)
  have hdelta2 : theta 7 - theta 0 ≤ 2 * Real.pi := by
    dsimp [theta]
    have hhi := fifteenPackingSortedAngle_range P (order 7)
    have hlo := fifteenPackingSortedAngle_range P (order 0)
    linarith
  have hsepNorm : 4 ≤ pointNorm
      ((polarPoint (fifteenPackingSortedRadius P (order 0))
          (theta 0)).1 -
        (polarPoint (fifteenPackingSortedRadius P (order 7))
          (theta 7)).1,
       (polarPoint (fifteenPackingSortedRadius P (order 0))
          (theta 0)).2 -
        (polarPoint (fifteenPackingSortedRadius P (order 7))
          (theta 7)).2) ^ 2 := by
    simpa only [theta] using hsep
  have hsep' : (2 : ℝ) ^ 2 ≤ pointNorm
      ((polarPoint (fifteenPackingSortedRadius P (order 0))
          (theta 0)).1 -
        (polarPoint (fifteenPackingSortedRadius P (order 7))
          (theta 7)).1,
       (polarPoint (fifteenPackingSortedRadius P (order 0))
          (theta 0)).2 -
        (polarPoint (fifteenPackingSortedRadius P (order 7))
          (theta 7)).2) ^ 2 := by
    calc
      (2 : ℝ) ^ 2 = 4 := by norm_num
      _ ≤ _ := hsepNorm
  have hwrap := fifteen_polar_touch_angle_ordered_gap
    ha0 hb0 (Real.arccos_le_pi _) hdelta0 hdelta2 hsep' hangle
  have htotal : (8 : ℝ) * Real.arccos ((2 : ℝ) / 3) ≤ 2 * Real.pi := by
    nlinarith [hspan, hwrap.2]
  have hstrict : 2 * Real.pi <
      (8 : ℝ) * Real.arccos ((2 : ℝ) / 3) := by
    nlinarith [fifteen_inner_gap_angle_gt_pi_div_four]
  linarith

/-- The wall-pushed inner class contains at most eight centers.  At most one
center can have radius below one; eight remaining centers would contradict
the uniform angular gap forced by their radii being in `[1, 12/5]`. -/
theorem fifteen_unit_packing_wall_push_inner_count_le_eight
    {R : ℝ} (P : Packing 15 R)
    (hunit : ∀ i, (P.circles i).radius = 1)
    (hR : R ≤ fifteenCandidateOuterRadius + 1) :
    (Finset.univ.filter fun k : Fin 15 =>
      fifteenPackingSortedRadius
        (fifteen_unit_packing_wall_push P hunit hR) k <
          fifteenCandidateInnerThreshold).card ≤ 8 := by
  classical
  let Q := fifteen_unit_packing_wall_push P hunit hR
  let inner : Finset (Fin 15) := Finset.univ.filter fun k =>
    fifteenPackingSortedRadius Q k < fifteenCandidateInnerThreshold
  let low : Finset (Fin 15) := inner.filter fun k =>
    fifteenPackingSortedRadius Q k < 1
  let high : Finset (Fin 15) := inner.filter fun k =>
    1 ≤ fifteenPackingSortedRadius Q k
  have hQunit : ∀ i, (Q.circles i).radius = 1 := by
    intro i
    exact fifteen_unit_packing_wall_push_preserves_unit_radii P hunit hR i
  have hlowGlobal : (Finset.univ.filter fun k : Fin 15 =>
      fifteenPackingSortedRadius Q k < 1).card ≤ 1 :=
    fifteen_unit_packing_subunit_sorted_count_le_one Q hQunit
  have hlow : low.card ≤ 1 := by
    calc
      low.card ≤ (Finset.univ.filter fun k : Fin 15 =>
          fifteenPackingSortedRadius Q k < 1).card :=
        Finset.card_le_card (by
          intro i hi
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
            (Finset.mem_filter.mp hi).2⟩)
      _ ≤ 1 := hlowGlobal
  have hpartition : low.card + high.card = inner.card := by
    have hnot : inner.filter (fun k => ¬
        fifteenPackingSortedRadius Q k < 1) = high := by
      ext k
      simp [high, not_lt]
    have h := Finset.card_filter_add_card_filter_not
      (s := inner) (p := fun k => fifteenPackingSortedRadius Q k < 1)
    rw [hnot] at h
    simpa [low] using h
  have hhigh : high.card ≤ 7 := by
    by_contra hnot
    have hcard : 8 ≤ high.card := by omega
    obtain ⟨S, hSsub, hScard⟩ := Finset.exists_subset_card_eq hcard
    have hinner : ∀ i ∈ S,
        fifteenPackingSortedRadius Q i < fifteenCandidateInnerThreshold := by
      intro i hi
      have hm := hSsub hi
      exact (Finset.mem_filter.mp (Finset.mem_filter.mp hm).1).2
    have hlarge : ∀ i ∈ S, 1 ≤ fifteenPackingSortedRadius Q i := by
      intro i hi
      have hm := hSsub hi
      exact (Finset.mem_filter.mp hm).2
    have hex := fifteen_inner_eight_large_centers_impossible Q hQunit S hScard
      hinner hlarge
    exact hex
  have : inner.card ≤ 8 := by omega
  simpa [Q, inner] using this

/-- The concrete bit string handed to the Stage 0 classifier has weight at
most eight.  Its `1` positions are exactly the inner centers, so this bound is
about the encoded pattern itself rather than a separately chosen subset. -/
theorem fifteen_unit_packing_wall_push_pattern_one_count_le_eight
    {R : ℝ} (P : Packing 15 R)
    (hunit : ∀ i, (P.circles i).radius = 1)
    (hR : R ≤ fifteenCandidateOuterRadius + 1) :
    (Finset.univ.filter fun k : Fin 15 =>
      (fifteen_unit_packing_wall_push_sorted_pattern P hunit hR).toList[k.1]? =
        some '1').card ≤ 8 := by
  rw [fifteen_unit_packing_wall_push_pattern_one_positions_eq_inner P hunit hR]
  exact fifteen_unit_packing_wall_push_inner_count_le_eight P hunit hR

/-- Both endpoints of the Stage 0 pattern-weight range follow from geometry
for the actual wall-pushed packing. -/
theorem fifteen_unit_packing_wall_push_pattern_one_count_range
    {R : ℝ} (P : Packing 15 R)
    (hunit : ∀ i, (P.circles i).radius = 1)
    (hR : R ≤ fifteenCandidateOuterRadius + 1) :
    5 ≤ (Finset.univ.filter fun k : Fin 15 =>
      (fifteen_unit_packing_wall_push_sorted_pattern P hunit hR).toList[k.1]? =
        some '1').card ∧
    (Finset.univ.filter fun k : Fin 15 =>
      (fifteen_unit_packing_wall_push_sorted_pattern P hunit hR).toList[k.1]? =
        some '1').card ≤ 8 := by
  exact ⟨fifteen_unit_packing_wall_push_pattern_one_count_ge_five P hunit hR,
    fifteen_unit_packing_wall_push_pattern_one_count_le_eight P hunit hR⟩

end CirclePacking
