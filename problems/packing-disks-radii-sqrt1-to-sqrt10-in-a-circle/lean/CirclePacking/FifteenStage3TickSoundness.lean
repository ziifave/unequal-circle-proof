import CirclePacking.FifteenStage3RadialOwners
import CirclePacking.FifteenTickSoundness

/-! Soundness of one Stage 3 table entry as an actual contact-angle lower
bound. The remaining cycle proof can apply this entrywise after identifying
the labels carried by a certificate leaf with their geometric owners. -/

namespace CirclePacking

private theorem fifteenStage3Bin_lower_positive
    (i : Nat) (hi : i < 8) (hzero : i ≠ 0) :
    0 < (fifteenStage3Bins[i]!).1 := by
  interval_cases i <;>
    norm_num [fifteenStage3Bins, fifteenRational, Rat.normalize_eq_mkRat] at *

private theorem fifteenStage3Bin_zero_upper_le_two
    (i : Nat) (hzero : i = 0) :
    (fifteenStage3Bins[i]!).2 ≤ 2 := by
  subst i
  norm_num [fifteenStage3Bins, fifteenRational, Rat.normalize_eq_mkRat]

private theorem fifteenStage3OwnerSpec_radius_positive
    (i : Nat) (hi : i < 8) (r : ℝ)
    (howner : fifteenStage3OwnerSpec i r) : 0 < r := by
  have hwall := fifteenCandidateOuterRadius_gt_one
  unfold fifteenStage3OwnerSpec at howner
  split at howner <;> simp_all <;> linarith

/-- Each positive Stage 3 pair-table tick is a genuine lower bound for the
contact angle of radii owned by the corresponding half-open bins. Label zero
uses the separate positive-zero Taylor branch; the singleton origin and the
unassigned sentinel are handled elsewhere with the zero tick. -/
theorem fifteenStage3PairTick_lower_bounds_touchAngle
    (i j : Nat) (hi : i < 8) (hj : j < 8)
    (a b : ℝ)
    (haOwner : fifteenStage3OwnerSpec i a)
    (hbOwner : fifteenStage3OwnerSpec j b)
    (hsum : 2 ≤ a + b) :
    ((fifteenStage3Q[i]!)[j]! : ℝ) / 2800 ≤ touchAngle a b 2 := by
  let x := fifteenStage3Bins[i]!
  let y := fifteenStage3Bins[j]!
  let ticks := (fifteenStage3Q[i]!)[j]!
  have htable : fifteenStage3PairTickValid i j = true := by
    have hall := fifteenStage3Table_valid
    unfold fifteenStage3TableValid at hall
    have hrow := (List.all_eq_true.mp hall) i (List.mem_range.mpr hi)
    exact (List.all_eq_true.mp hrow) j (List.mem_range.mpr hj)
  have hxHull := fifteenStage3OwnerSpec_closed_hull haOwner
  have hyHull := fifteenStage3OwnerSpec_closed_hull hbOwner
  have hix9 : i ≠ 9 := by omega
  have hjx9 : j ≠ 9 := by omega
  have hxBounds : (x.1 : ℝ) ≤ a ∧ a ≤ (x.2 : ℝ) := by
    simpa [x, hix9] using hxHull
  have hyBounds : (y.1 : ℝ) ≤ b ∧ b ≤ (y.2 : ℝ) := by
    simpa [y, hjx9] using hyHull
  have hxOrder : x.1 ≤ x.2 := by
    exact_mod_cast hxBounds.1.trans hxBounds.2
  have hyOrder : y.1 ≤ y.2 := by
    exact_mod_cast hyBounds.1.trans hyBounds.2
  have hsumBinReal : 2 ≤ (x.2 : ℝ) + (y.2 : ℝ) := by
    linarith [hxBounds.2, hyBounds.2]
  have hsumBin : 2 ≤ x.2 + y.2 := by exact_mod_cast hsumBinReal
  change (ticks : ℝ) / 2800 ≤ touchAngle a b 2
  by_cases hticks0 : ticks = 0
  · have hnonneg : 0 ≤ touchAngle a b 2 := by
      simpa [touchAngle] using Real.arccos_nonneg (touchCosine a b 2)
    simpa [ticks, hticks0] using hnonneg
  · have hqNonzero : (fifteenStage3Q[i]!)[j]! ≠ 0 := by
      simpa [ticks] using hticks0
    have hvalid :
        fifteenTickCertificateValid x y (i == 0 || j == 0) false ticks = true := by
      have hnotSmall : ¬ x.2 + y.2 < 2 := not_lt_of_ge hsumBin
      simpa [fifteenStage3PairTickValid, x, y, ticks,
        hqNonzero, hnotSmall] using htable
    by_cases hi0 : i = 0
    · have hzero : x.1 = 0 ∨ y.1 = 0 := by
        left
        subst i
        norm_num [x, fifteenStage3Bins, fifteenRational, Rat.normalize_eq_mkRat]
      have hxUpperLeTwo : x.1 = 0 → x.2 ≤ 2 := by
        intro _
        subst i
        norm_num [x, fifteenStage3Bins, fifteenRational, Rat.normalize_eq_mkRat]
      have hyUpperLeTwo : y.1 = 0 → y.2 ≤ 2 := by
        intro hyzero
        have hjzero : j = 0 := by
          by_contra hjne
          have hpos := fifteenStage3Bin_lower_positive j hj hjne
          have hposReal : 0 < (y.1 : ℝ) := by exact_mod_cast hpos
          have hzeroReal : (y.1 : ℝ) = 0 := by exact_mod_cast hyzero
          linarith
        subst j
        norm_num [y, fifteenStage3Bins, fifteenRational, Rat.normalize_eq_mkRat]
      have haPos := fifteenStage3OwnerSpec_radius_positive i hi a haOwner
      have hbPos := fifteenStage3OwnerSpec_radius_positive j hj b hbOwner
      have hflag : (i == 0 || j == 0) = true := by simp [hi0]
      have hvalidZero : fifteenTickCertificateValid x y true false ticks = true := by
        simpa [hflag] using hvalid
      have htick := fifteenPositiveZeroTick_lower_bounds_touch_angle_of_box
        x y ticks a b hsumBin hvalidZero hzero ⟨hxUpperLeTwo, hyUpperLeTwo⟩
        haPos hbPos hxBounds.2 hyBounds.2
      simpa [ticks] using htick
    · by_cases hj0 : j = 0
      · have hzero : x.1 = 0 ∨ y.1 = 0 := by
          right
          subst j
          norm_num [y, fifteenStage3Bins, fifteenRational, Rat.normalize_eq_mkRat]
        have hxUpperLeTwo : x.1 = 0 → x.2 ≤ 2 := by
          intro hxzero
          have hizero : i = 0 := by
            by_contra hine
            have hpos := fifteenStage3Bin_lower_positive i hi hine
            have hposReal : 0 < (x.1 : ℝ) := by exact_mod_cast hpos
            have hzeroReal : (x.1 : ℝ) = 0 := by exact_mod_cast hxzero
            linarith
          subst i
          norm_num [x, fifteenStage3Bins, fifteenRational, Rat.normalize_eq_mkRat]
        have hyUpperLeTwo : y.1 = 0 → y.2 ≤ 2 := by
          intro _
          subst j
          norm_num [y, fifteenStage3Bins, fifteenRational, Rat.normalize_eq_mkRat]
        have haPos := fifteenStage3OwnerSpec_radius_positive i hi a haOwner
        have hbPos := fifteenStage3OwnerSpec_radius_positive j hj b hbOwner
        have hflag : (i == 0 || j == 0) = true := by simp [hi0, hj0]
        have hvalidZero : fifteenTickCertificateValid x y true false ticks = true := by
          simpa [hflag] using hvalid
        have htick := fifteenPositiveZeroTick_lower_bounds_touch_angle_of_box
          x y ticks a b hsumBin hvalidZero hzero ⟨hxUpperLeTwo, hyUpperLeTwo⟩
          haPos hbPos hxBounds.2 hyBounds.2
        simpa [ticks] using htick
      · have hxLowerPos : 0 < (x.1 : ℝ) := by
          exact_mod_cast fifteenStage3Bin_lower_positive i hi hi0
        have hyLowerPos : 0 < (y.1 : ℝ) := by
          exact_mod_cast fifteenStage3Bin_lower_positive j hj hj0
        have hflag : (i == 0 || j == 0) = false := by simp [hi0, hj0]
        have hvalidRegular : fifteenTickCertificateValid x y false false ticks = true := by
          simpa [hflag] using hvalid
        have htick := fifteenRegularTick_lower_bounds_touch_angle_all_caps
          x y ticks a b hsumBin hvalidRegular hxOrder hyOrder hxLowerPos hyLowerPos
          hxBounds.1 hxBounds.2 hyBounds.1 hyBounds.2
        simpa [ticks] using htick

end CirclePacking
