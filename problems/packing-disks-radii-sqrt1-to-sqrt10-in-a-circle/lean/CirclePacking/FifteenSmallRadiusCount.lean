import CirclePacking.FifteenPackingSortedGeometry
import CirclePacking.FifteenTickSoundness
import CirclePacking.Angle
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

/-! A packing-theoretic justification for the Stage 0 radial classification:
five pairwise separated centers cannot all lie in the disk of radius `5/3`.
The proof converts the radial bound into a uniform angular gap strictly
larger than one fifth of a turn. -/

namespace CirclePacking

private theorem fifteen_cos_two_pi_div_five_gt_seven_twentyfive :
    (7 : ℝ) / 25 < Real.cos (2 * Real.pi / 5) := by
  have hroot : (67 : ℝ) / 30 < Real.sqrt 5 := by
    have hsq : ((67 : ℝ) / 30) ^ 2 < (Real.sqrt 5) ^ 2 := by
      rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)]
      norm_num
    have hpos : 0 < Real.sqrt 5 := Real.sqrt_pos.2 (by norm_num)
    nlinarith
  have hcos : Real.cos (Real.pi / 5) = (1 + Real.sqrt 5) / 4 :=
    Real.cos_pi_div_five
  have hdouble := Real.cos_two_mul (Real.pi / 5)
  have hangle : 2 * (Real.pi / 5) = 2 * Real.pi / 5 := by ring
  rw [← hangle, hdouble, hcos]
  have hsquare := Real.sin_sq_add_cos_sq (Real.pi / 5)
  nlinarith

private theorem fifteen_small_radius_pair_cosine_cap
    {a b : ℝ} (ha0 : 0 < a) (hb0 : 0 < b)
    (ha : a ≤ 5 / 3) (hb : b ≤ 5 / 3) :
    touchCosine a b 2 ≤ (7 : ℝ) / 25 := by
  have ha' : a ≤ (5 : ℝ) / 3 := by exact_mod_cast ha
  have hb' : b ≤ (5 : ℝ) / 3 := by exact_mod_cast hb
  have hu : 0 ≤ (3 : ℝ) * a / 5 := by positivity
  have hu1 : (3 : ℝ) * a / 5 ≤ 1 := by nlinarith
  have hv : 0 ≤ (3 : ℝ) * b / 5 := by positivity
  have hv1 : (3 : ℝ) * b / 5 ≤ 1 := by nlinarith
  have hkey :
      25 * ((3 : ℝ) * a / 5) + 25 * ((3 : ℝ) * b / 5) -
        14 * ((3 : ℝ) * a / 5) * ((3 : ℝ) * b / 5) ≤ 36 := by
    have hc : 0 ≤ 25 - 14 * ((3 : ℝ) * b / 5) := by nlinarith
    have hmul := mul_le_mul_of_nonneg_right hu1 hc
    nlinarith
  have haSq : a ^ 2 ≤ (5 : ℝ) / 3 * a := by
    nlinarith [mul_nonneg (sub_nonneg.mpr ha') ha0.le]
  have hbSq : b ^ 2 ≤ (5 : ℝ) / 3 * b := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hb') hb0.le]
  have hpoly : a ^ 2 + b ^ 2 - 4 ≤ (14 : ℝ) / 25 * (a * b) := by
    nlinarith [haSq, hbSq, hkey]
  unfold touchCosine
  apply (div_le_iff₀ (by positivity : 0 < 2 * a * b)).2
  nlinarith

private noncomputable def fifteenSmallRadiusGapAngle : ℝ :=
  Real.arccos ((7 : ℝ) / 25)

private theorem fifteenSmallRadiusGapAngle_spec :
    2 * Real.pi / 5 < fifteenSmallRadiusGapAngle ∧
      fifteenSmallRadiusGapAngle ≤ Real.pi := by
  have hcos := fifteen_cos_two_pi_div_five_gt_seven_twentyfive
  have hlow : -1 ≤ (7 : ℝ) / 25 := by norm_num
  have hhigh : Real.cos (2 * Real.pi / 5) ≤ 1 := Real.cos_le_one _
  have hlt := Real.arccos_lt_arccos hlow hcos hhigh
  have hangle0 : 0 ≤ 2 * Real.pi / 5 := by positivity
  have hanglePi : 2 * Real.pi / 5 ≤ Real.pi := by
    nlinarith [Real.pi_pos]
  rw [Real.arccos_cos hangle0 hanglePi] at hlt
  exact ⟨by simpa [fifteenSmallRadiusGapAngle] using hlt,
    by simpa [fifteenSmallRadiusGapAngle] using Real.arccos_le_pi ((7 : ℝ) / 25)⟩

theorem fifteen_small_radius_pair_touch_angle_lower
    {a b : ℝ} (ha0 : 0 < a) (hb0 : 0 < b)
    (ha : a ≤ 5 / 3) (hb : b ≤ 5 / 3) :
    fifteenSmallRadiusGapAngle ≤ touchAngle a b 2 := by
  have hcap := fifteen_small_radius_pair_cosine_cap ha0 hb0 ha hb
  have harccos := Real.antitone_arccos hcap
  simpa [fifteenSmallRadiusGapAngle, touchAngle] using harccos

private theorem fifteen_small_radius_ordered_gap
    {R : ℝ} (P : Packing 15 R)
    (hunit : ∀ i, (P.circles i).radius = 1)
    {i j : Fin 15} (hij : i.1 < j.1)
    (hi : fifteenPackingSortedRadius P i ≤ 5 / 3)
    (hj : fifteenPackingSortedRadius P j ≤ 5 / 3) :
    fifteenSmallRadiusGapAngle ≤
        fifteenPackingSortedAngle P j - fifteenPackingSortedAngle P i ∧
      fifteenPackingSortedAngle P j - fifteenPackingSortedAngle P i ≤
        2 * Real.pi - fifteenSmallRadiusGapAngle := by
  let a := fifteenPackingSortedRadius P i
  let b := fifteenPackingSortedRadius P j
  have hne : i ≠ j := fun h => by have := congrArg Fin.val h; omega
  have hindices : fifteenPackingSortedIndex P i ≠
      fifteenPackingSortedIndex P j := by
    intro heq
    have hinj := fifteenPackingAngleOrder_injective (fifteenPackingPolarAngle P)
    apply hne
    exact hinj heq
  have hsum := fifteen_unit_packing_pair_radial_sum_ge_two P hunit hindices
  have ha0 : 0 < a := by
    dsimp [a, fifteenPackingSortedRadius] at hi hsum ⊢
    have hb0 : 0 ≤ fifteenCenterRadius P (fifteenPackingSortedIndex P j) :=
      pointNorm_nonneg _
    have hj' : fifteenCenterRadius P (fifteenPackingSortedIndex P j) ≤ 5 / 3 := by
      simpa [fifteenPackingSortedRadius] using hj
    linarith [hsum, hj']
  have hb0 : 0 < b := by
    dsimp [b, fifteenPackingSortedRadius] at hi hsum ⊢
    have ha0' : 0 ≤ fifteenCenterRadius P (fifteenPackingSortedIndex P i) :=
      pointNorm_nonneg _
    have hi' : fifteenCenterRadius P (fifteenPackingSortedIndex P i) ≤ 5 / 3 := by
      simpa [fifteenPackingSortedRadius] using hi
    linarith [hsum, hi']
  have hthetaI := fifteenPackingSortedAngle_range P i
  have hthetaJ := fifteenPackingSortedAngle_range P j
  have hdelta0 : 0 ≤ fifteenPackingSortedAngle P j -
      fifteenPackingSortedAngle P i :=
    sub_nonneg.mpr (fifteenPackingSortedAngle_monotone P hij)
  have hdelta2 : fifteenPackingSortedAngle P j -
      fifteenPackingSortedAngle P i ≤ 2 * Real.pi := by
    linarith
  have hsep := fifteen_unit_packing_sorted_pair_separated P hunit hne
  have hsep' : (2 : ℝ) ^ 2 ≤ pointNorm
      ((polarPoint a (fifteenPackingSortedAngle P i)).1 -
          (polarPoint b (fifteenPackingSortedAngle P j)).1,
       (polarPoint a (fifteenPackingSortedAngle P i)).2 -
          (polarPoint b (fifteenPackingSortedAngle P j)).2) ^ 2 := by
    rw [show (2 : ℝ) ^ 2 = 4 by norm_num]
    simpa [a, b] using hsep
  have htouch := fifteen_small_radius_pair_touch_angle_lower ha0 hb0 hi hj
  have hgapAngle := fifteenSmallRadiusGapAngle_spec
  exact fifteen_polar_touch_angle_ordered_gap
    (a := a) (b := b) (d := 2) (ell := fifteenSmallRadiusGapAngle)
    (alpha := fifteenPackingSortedAngle P i)
    (beta := fifteenPackingSortedAngle P j)
    ha0 hb0 hgapAngle.2 hdelta0 hdelta2 hsep' htouch

theorem fifteen_unit_packing_small_radius_five_centers_impossible
    {R : ℝ} (P : Packing 15 R)
    (hunit : ∀ i, (P.circles i).radius = 1)
    (S : Finset (Fin 15)) (hcard : S.card = 5)
    (hsmall : ∀ i ∈ S, fifteenPackingSortedRadius P i ≤ 5 / 3) : False := by
  classical
  let order : Fin 5 ↪o Fin 15 := S.orderEmbOfFin hcard
  let theta : Fin 5 → ℝ := fun k => fifteenPackingSortedAngle P (order k)
  have hinS (k : Fin 5) : order k ∈ S := by
    simpa [order] using S.orderEmbOfFin_mem hcard k
  have hrad (k : Fin 5) : fifteenPackingSortedRadius P (order k) ≤ 5 / 3 :=
    hsmall (order k) (hinS k)
  have hgap (k : Fin 4) :
      fifteenSmallRadiusGapAngle ≤ theta k.succ - theta k.castSucc := by
    have hkn : k.castSucc < k.succ := Fin.castSucc_lt_succ_iff.mpr le_rfl
    have hlt : (order k.castSucc).1 < (order k.succ).1 := order.strictMono hkn
    have hbound := fifteen_small_radius_ordered_gap P hunit hlt
      (hrad k.castSucc) (hrad k.succ)
    simpa [theta] using hbound.1
  have hspan_nat : ∀ (n : Nat) (hn : n ≤ 4),
      (n : ℝ) * fifteenSmallRadiusGapAngle ≤
        theta ⟨n, by omega⟩ - theta (0 : Fin 5) := by
    intro n
    induction n with
    | zero => intro _; simp [theta]
    | succ n ih =>
        intro hn
        have hn4 : n ≤ 4 := by omega
        have hprev := ih hn4
        let k : Fin 4 := ⟨n, by omega⟩
        have hstep : fifteenSmallRadiusGapAngle ≤
            theta ⟨n + 1, by omega⟩ - theta ⟨n, by omega⟩ := by
          simpa [k] using hgap k
        calc
          ((n + 1 : Nat) : ℝ) * fifteenSmallRadiusGapAngle =
              (n : ℝ) * fifteenSmallRadiusGapAngle +
                fifteenSmallRadiusGapAngle := by push_cast; ring
          _ ≤ (theta ⟨n, by omega⟩ - theta (0 : Fin 5)) +
                (theta ⟨n + 1, by omega⟩ - theta ⟨n, by omega⟩) :=
              add_le_add hprev hstep
          _ = theta ⟨n + 1, by omega⟩ - theta (0 : Fin 5) := by ring
  have hspan : (4 : ℝ) * fifteenSmallRadiusGapAngle ≤
      theta (4 : Fin 5) - theta (0 : Fin 5) := by
    simpa using hspan_nat 4 (by omega)
  have horder : (order (0 : Fin 5)).1 < (order (4 : Fin 5)).1 := by
    exact order.strictMono (by decide)
  have hwrap := fifteen_small_radius_ordered_gap P hunit horder (hrad 0) (hrad 4)
  have hspanUpper : theta (4 : Fin 5) - theta (0 : Fin 5) ≤
      2 * Real.pi - fifteenSmallRadiusGapAngle := by
    simpa [theta] using hwrap.2
  have hangle := fifteenSmallRadiusGapAngle_spec.1
  nlinarith [hspan, hspanUpper]

theorem fifteen_unit_packing_small_radius_count_le_four
    {R : ℝ} (P : Packing 15 R)
    (hunit : ∀ i, (P.circles i).radius = 1) :
    (Finset.univ.filter fun i : Fin 15 =>
      fifteenPackingSortedRadius P i ≤ 5 / 3).card ≤ 4 := by
  classical
  let S := Finset.univ.filter fun i : Fin 15 =>
    fifteenPackingSortedRadius P i ≤ 5 / 3
  change S.card ≤ 4
  by_contra hnot
  have hcard : 5 ≤ S.card := by omega
  obtain ⟨T, hTsub, hTcard⟩ := Finset.exists_subset_card_eq hcard
  exact fifteen_unit_packing_small_radius_five_centers_impossible P hunit T hTcard
    (by
      intro i hi
      have hmem : i ∈ S := hTsub hi
      exact (Finset.mem_filter.mp hmem).2)

end CirclePacking
