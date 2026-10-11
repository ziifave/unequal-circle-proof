import CirclePacking.FifteenSmallRadiusCount

/-! The sixth-center radial bound used by Stage 3/4.  This proof uses strict
angular gaps and therefore keeps the equality case at radius two: six
separated centers cannot all have radius strictly less than two. -/

namespace CirclePacking

theorem fifteen_radius_two_pair_cosine_lt_half
    {a b : ℝ} (ha0 : 0 < a) (hb0 : 0 < b)
    (ha : a < 2) (hb : b < 2) :
    touchCosine a b 2 < (1 : ℝ) / 2 := by
  have hpoly : a ^ 2 + b ^ 2 - a * b < 4 := by
    rcases le_total a b with hab | hba
    · have hprod := mul_nonpos_of_nonneg_of_nonpos ha0.le (sub_nonpos.mpr hab)
      have hsq : b ^ 2 < (2 : ℝ) ^ 2 :=
        (sq_lt_sq₀ hb0.le (by norm_num)).2 hb
      nlinarith
    · have hprod := mul_nonpos_of_nonneg_of_nonpos hb0.le (sub_nonpos.mpr hba)
      have hsq : a ^ 2 < (2 : ℝ) ^ 2 :=
        (sq_lt_sq₀ ha0.le (by norm_num)).2 ha
      nlinarith
  unfold touchCosine
  apply (div_lt_iff₀ (by positivity : 0 < 2 * a * b)).2
  nlinarith

theorem fifteen_radius_two_pair_touch_angle_gt_pi_div_three
    {a b : ℝ} (ha0 : 0 < a) (hb0 : 0 < b)
    (ha : a < 2) (hb : b < 2) (hsum : 2 ≤ a + b) :
    Real.pi / 3 < touchAngle a b 2 := by
  have hcap := fifteen_radius_two_pair_cosine_lt_half ha0 hb0 ha hb
  have hlow : -1 ≤ touchCosine a b 2 := by
    unfold touchCosine
    apply (le_div_iff₀ (by positivity : 0 < 2 * a * b)).2
    have hsq : (2 : ℝ) ^ 2 ≤ (a + b) ^ 2 :=
      (sq_le_sq₀ (by norm_num) (by positivity)).2 hsum
    nlinarith
  have harccos := Real.arccos_lt_arccos hlow hcap (by norm_num : (1 : ℝ) / 2 ≤ 1)
  have hangle : Real.arccos ((1 : ℝ) / 2) = Real.pi / 3 := by
    rw [← Real.cos_pi_div_three]
    apply Real.arccos_cos
    · positivity
    · nlinarith [Real.pi_pos]
  simpa only [hangle, touchAngle] using harccos

private theorem fifteen_radius_two_ordered_gap
    {R : ℝ} (P : Packing 15 R)
    (hunit : ∀ i, (P.circles i).radius = 1)
    {i j : Fin 15} (hij : i.val < j.val)
    (hi : fifteenPackingSortedRadius P i < 2)
    (hj : fifteenPackingSortedRadius P j < 2) :
    Real.pi / 3 < fifteenPackingSortedAngle P j - fifteenPackingSortedAngle P i ∧
      fifteenPackingSortedAngle P j - fifteenPackingSortedAngle P i <
        2 * Real.pi - Real.pi / 3 := by
  have hne : i ≠ j := fun h => by have := congrArg Fin.val h; omega
  have hindices : fifteenPackingSortedIndex P i ≠ fifteenPackingSortedIndex P j := by
    intro heq
    exact hne ((fifteenPackingSortedIndex_bijective P).1 heq)
  have hsum : 2 ≤ fifteenPackingSortedRadius P i + fifteenPackingSortedRadius P j :=
    fifteen_unit_packing_pair_radial_sum_ge_two P hunit hindices
  have ha0 : 0 < fifteenPackingSortedRadius P i := by linarith
  have hb0 : 0 < fifteenPackingSortedRadius P j := by linarith
  have htouch := fifteen_radius_two_pair_touch_angle_gt_pi_div_three ha0 hb0 hi hj hsum
  have hthetaI := fifteenPackingSortedAngle_range P i
  have hthetaJ := fifteenPackingSortedAngle_range P j
  have hdelta0 : 0 ≤ fifteenPackingSortedAngle P j - fifteenPackingSortedAngle P i :=
    sub_nonneg.mpr (fifteenPackingSortedAngle_monotone P hij)
  have hdelta2 : fifteenPackingSortedAngle P j - fifteenPackingSortedAngle P i ≤
      2 * Real.pi := by linarith
  have hsep := fifteen_unit_packing_sorted_pair_separated P hunit hne
  have hgap := fifteen_polar_touch_angle_ordered_gap ha0 hb0
    (Real.arccos_le_pi _) hdelta0 hdelta2
    (by simpa only [show (2 : ℝ) ^ 2 = 4 by norm_num] using hsep)
    (le_refl (touchAngle (fifteenPackingSortedRadius P i)
      (fifteenPackingSortedRadius P j) 2))
  change Real.pi / 3 < Real.arccos
    (touchCosine (fifteenPackingSortedRadius P i) (fifteenPackingSortedRadius P j) 2) at htouch
  exact ⟨lt_of_lt_of_le htouch hgap.1, by linarith [hgap.2]⟩

theorem fifteen_unit_packing_radius_two_six_centers_impossible
    {R : ℝ} (P : Packing 15 R)
    (hunit : ∀ i, (P.circles i).radius = 1)
    (S : Finset (Fin 15)) (hcard : S.card = 6)
    (hsmall : ∀ i ∈ S, fifteenPackingSortedRadius P i < 2) : False := by
  classical
  let order : Fin 6 ↪o Fin 15 := S.orderEmbOfFin hcard
  let theta : Fin 6 → ℝ := fun k => fifteenPackingSortedAngle P (order k)
  have hinS (k : Fin 6) : order k ∈ S := S.orderEmbOfFin_mem hcard k
  have hrad (k : Fin 6) : fifteenPackingSortedRadius P (order k) < 2 :=
    hsmall (order k) (hinS k)
  have hgap (k : Fin 5) : Real.pi / 3 < theta k.succ - theta k.castSucc := by
    have hkn : k.castSucc < k.succ := Fin.castSucc_lt_succ_iff.mpr le_rfl
    have hlt : (order k.castSucc).val < (order k.succ).val := order.strictMono hkn
    exact (fifteen_radius_two_ordered_gap P hunit hlt
      (hrad k.castSucc) (hrad k.succ)).1
  have hspan_nat : ∀ (n : Nat) (hn : n ≤ 5),
      (n : ℝ) * (Real.pi / 3) ≤ theta ⟨n, by omega⟩ - theta (0 : Fin 6) := by
    intro n
    induction n with
    | zero => intro _; simp
    | succ n ih =>
        intro hn
        have hprev := ih (by omega)
        let k : Fin 5 := ⟨n, by omega⟩
        have hstep : Real.pi / 3 ≤ theta ⟨n + 1, by omega⟩ - theta ⟨n, by omega⟩ :=
          (hgap k).le
        calc
          ((n + 1 : Nat) : ℝ) * (Real.pi / 3) =
              (n : ℝ) * (Real.pi / 3) + Real.pi / 3 := by push_cast; ring
          _ ≤ (theta ⟨n, by omega⟩ - theta (0 : Fin 6)) +
              (theta ⟨n + 1, by omega⟩ - theta ⟨n, by omega⟩) :=
            add_le_add hprev hstep
          _ = theta ⟨n + 1, by omega⟩ - theta (0 : Fin 6) := by ring
  have hspan : (5 : ℝ) * (Real.pi / 3) ≤ theta (5 : Fin 6) - theta (0 : Fin 6) := by
    simpa using hspan_nat 5 (by omega)
  have horder : (order (0 : Fin 6)).val < (order (5 : Fin 6)).val :=
    order.strictMono (by decide)
  have hwrap := (fifteen_radius_two_ordered_gap P hunit horder (hrad 0) (hrad 5)).2
  change theta 5 - theta 0 < 2 * Real.pi - Real.pi / 3 at hwrap
  linarith

/-- This is the exact sixth-radius bound, with no appeal to an external
small-packing theorem and no additional native-evaluation assumption. -/
theorem fifteen_unit_packing_radius_two_count_le_five
    {R : ℝ} (P : Packing 15 R)
    (hunit : ∀ i, (P.circles i).radius = 1) :
    (Finset.univ.filter fun i : Fin 15 => fifteenPackingSortedRadius P i < 2).card ≤ 5 := by
  classical
  let S := Finset.univ.filter fun i : Fin 15 => fifteenPackingSortedRadius P i < 2
  change S.card ≤ 5
  by_contra hnot
  have hcard : 6 ≤ S.card := by omega
  obtain ⟨T, hTsub, hTcard⟩ := Finset.exists_subset_card_eq hcard
  exact fifteen_unit_packing_radius_two_six_centers_impossible P hunit T hTcard
    (fun i hi => (Finset.mem_filter.mp (hTsub hi)).2)

end CirclePacking
