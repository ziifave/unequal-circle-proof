import CirclePacking.CosineTaylor
import CirclePacking.GlobalRadialBox
import CirclePacking.NineCircleGeometry
import CirclePacking.NineCirclePackingSoundness
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Data.List.Permutation
import Mathlib.Data.List.Sort

namespace CirclePacking

open scoped BigOperators

/-!
# Four-large-circle half-plane obstruction

The exact certificate proposes rational radial and angle bounds for the four
largest disks. This file verifies those bounds by rational corner checks and
a cosine Taylor remainder estimate, derives the radial boxes and angle gaps
from any packing below the rational radius ceiling, and proves that these four
centers cannot lie in a common closed half-plane through the origin. The
result is a geometric obstruction available to the global proof; the concrete
global certificate tree and its terminal cases still need to be connected to
it.
-/

abbrev LargeFourLabel := Fin 4

/-- The four labels 0 through 3 stand for the disks of radii
`sqrt 7`, `sqrt 8`, `sqrt 9`, and `sqrt 10` in a ten-disk packing. -/
def largeFourPackingIndex (i : LargeFourLabel) : Fin 10 :=
  ⟨i.val + 6, by omega⟩

def largeFourRootLower (i : LargeFourLabel) : ℚ :=
  tenRootLower (largeFourPackingIndex i)

theorem largeFourRootLower_pos (i : LargeFourLabel) :
    0 < (largeFourRootLower i : ℝ) := by
  fin_cases i <;>
    norm_num [largeFourRootLower, largeFourPackingIndex, tenRootLower]

theorem largeFour_packing_root_radius_lower {R : ℝ} (P : Packing 10 R)
    (hRadius : ∀ i : LargeFourLabel,
      (P.circles (largeFourPackingIndex i)).radius =
        Real.sqrt ((i.val + 7 : ℕ) : ℝ)) (i : LargeFourLabel) :
    (largeFourRootLower i : ℝ) ≤
      (P.circles (largeFourPackingIndex i)).radius := by
  rw [hRadius i]
  have h := tenRootLower_le_sqrt (largeFourPackingIndex i)
  have hidx : (largeFourPackingIndex i).val + 1 = i.val + 7 := by
    simp [largeFourPackingIndex]
  rw [hidx] at h
  simpa [largeFourRootLower] using h

/-- Companion used to certify a positive lower radius for each of the four
large disks. -/
def largeFourRadialPartner (i : LargeFourLabel) : LargeFourLabel :=
  if i.val = 3 then 2 else 3

/-- Radial bounds obtained from containment and separation from the largest
available companion disk. -/
def largeFourRadialLower (i : LargeFourLabel) : ℚ :=
  largeFourRootLower i + 2 * largeFourRootLower (largeFourRadialPartner i) -
    tenCircleGlobalRadiusUpper

def largeFourRadialUpper (i : LargeFourLabel) : ℚ :=
  tenCircleGlobalRadiusUpper - largeFourRootLower i

/-- A rational upper bound for the cosine of the touch angle, checked at the
four corners of the certified radial rectangle. -/
def largeFourCosineCap (i j : LargeFourLabel) : ℚ :=
  if (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) then
    160096019448775304252377891201 / 309762314919689491812172771201 else
  if (i = 0 ∧ j = 2) ∨ (i = 2 ∧ j = 0) then
    141310128849406394903774646601 / 300055207513246394903774646601 else
  if (i = 0 ∧ j = 3) ∨ (i = 3 ∧ j = 0) then
    123541991746589257390505823401 / 290873997053346942400480863401 else
  if (i = 1 ∧ j = 2) ∨ (i = 2 ∧ j = 1) then
    120661426483053745187060584801 / 290367053967813745187060584801 else
  if (i = 1 ∧ j = 3) ∨ (i = 3 ∧ j = 1) then
    102596847344100602865606001601 / 281482285544050297491952561601 else
  if (i = 2 ∧ j = 3) ∨ (i = 3 ∧ j = 2) then
    82924737636129447050278597001 / 272661397246209447050278597001 else 0

def largeFourTaylorPoly (x : ℚ) : ℚ :=
  1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720 + x ^ 8 / 40320 -
    x ^ 10 / 3628800 + x ^ 12 / 479001600 - x ^ 14 / 87178291200

def largeFourLabels : List LargeFourLabel := [0, 1, 2, 3]

def largeFourOrders : List (List LargeFourLabel) := largeFourLabels.permutations

/-- Downward rational angle bounds for pairs among disks 7, 8, 9, 10.
Indices 0 through 3 correspond respectively to disk labels 7 through 10. -/
def largeFourPairAngleLower (i j : LargeFourLabel) : ℚ :=
  if (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) then 2569 / 2500 else
  if (i = 0 ∧ j = 2) ∨ (i = 2 ∧ j = 0) then 2701 / 2500 else
  if (i = 0 ∧ j = 3) ∨ (i = 3 ∧ j = 0) then 11321 / 10000 else
  if (i = 1 ∧ j = 2) ∨ (i = 2 ∧ j = 1) then 5711 / 5000 else
  if (i = 1 ∧ j = 3) ∨ (i = 3 ∧ j = 1) then 11977 / 10000 else
  if (i = 2 ∧ j = 3) ∨ (i = 3 ∧ j = 2) then 12617 / 10000 else 0

def largeFourPiUpper : ℚ := 31416 / 10000

theorem largeFourPairAngleLower_bounds (i j : LargeFourLabel) :
    0 ≤ largeFourPairAngleLower i j ∧
      largeFourPairAngleLower i j ≤ 13 / 10 := by
  fin_cases i <;> fin_cases j <;> norm_num [largeFourPairAngleLower]

theorem largeFourPairAngleLower_real_bounds (i j : LargeFourLabel) :
    0 ≤ (largeFourPairAngleLower i j : ℝ) ∧
      (largeFourPairAngleLower i j : ℝ) ≤ 13 / 10 := by
  fin_cases i <;> fin_cases j <;> norm_num [largeFourPairAngleLower]

theorem largeFourRadialLower_pos (i : LargeFourLabel) :
    0 < (largeFourRadialLower i : ℝ) := by
  fin_cases i <;>
    norm_num [largeFourRadialLower, largeFourRadialPartner, largeFourRootLower,
      largeFourPackingIndex, tenRootLower, tenCircleGlobalRadiusUpper]

theorem largeFourRadialPartner_ne (i : LargeFourLabel) :
    i ≠ largeFourRadialPartner i := by
  fin_cases i <;> norm_num [largeFourRadialPartner]

theorem largeFourPackingIndex_injective :
    Function.Injective largeFourPackingIndex := by
  intro i j hij
  apply Fin.ext
  have hval := congrArg Fin.val hij
  dsimp [largeFourPackingIndex] at hval
  omega

/-- Exact rational check that the cosine cap lies below the degree-14 Taylor
polynomial after reserving the order-15 Taylor remainder. -/
theorem cosine_taylor_fifteen_remainder
    {a b x : ℝ} (hab : a < b) (hx : x ∈ Set.Icc a b) :
    ‖Real.cos x - taylorWithinEval Real.cos 15 (Set.Icc a b) a x‖ ≤
      (x - a) ^ 16 / ((Nat.factorial 15 : ℕ) : ℝ) := by
  have h := taylor_mean_remainder_bound (n := 15) (C := (1 : ℝ)) hab.le
      Real.contDiff_cos.contDiffOn hx (by
        intro y hy
        rw [show 15 + 1 = 16 by norm_num,
          Real.iteratedDerivWithin_cos_Icc 16 hab hy]
        simpa [Real.norm_eq_abs] using Real.abs_iteratedDeriv_cos_le_one 16 y)
  simpa using h

theorem cosine_taylor_fifteen_at_zero
    {b x : ℝ} (hb : 0 < b) :
    taylorWithinEval Real.cos 15 (Set.Icc 0 b) 0 x =
      1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720 +
        x ^ 8 / 40320 - x ^ 10 / 3628800 +
        x ^ 12 / 479001600 - x ^ 14 / 87178291200 := by
  rw [taylor_within_apply]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial_zero,
    Nat.factorial_one, Nat.cast_one, inv_one]
  have hzero : (0 : ℝ) ∈ Set.Icc 0 b := ⟨le_rfl, hb.le⟩
  rw [Real.iteratedDerivWithin_cos_Icc 0 hb hzero,
    Real.iteratedDerivWithin_cos_Icc 1 hb hzero,
    Real.iteratedDerivWithin_cos_Icc 2 hb hzero,
    Real.iteratedDerivWithin_cos_Icc 3 hb hzero,
    Real.iteratedDerivWithin_cos_Icc 4 hb hzero,
    Real.iteratedDerivWithin_cos_Icc 5 hb hzero,
    Real.iteratedDerivWithin_cos_Icc 6 hb hzero,
    Real.iteratedDerivWithin_cos_Icc 7 hb hzero,
    Real.iteratedDerivWithin_cos_Icc 8 hb hzero,
    Real.iteratedDerivWithin_cos_Icc 9 hb hzero,
    Real.iteratedDerivWithin_cos_Icc 10 hb hzero,
    Real.iteratedDerivWithin_cos_Icc 11 hb hzero,
    Real.iteratedDerivWithin_cos_Icc 12 hb hzero,
    Real.iteratedDerivWithin_cos_Icc 13 hb hzero,
    Real.iteratedDerivWithin_cos_Icc 14 hb hzero,
    Real.iteratedDerivWithin_cos_Icc 15 hb hzero]
  norm_num [Real.iteratedDeriv_even_cos, Real.iteratedDeriv_odd_cos]
  ring

/-- Exact rational check that each cosine cap lies below the degree-14 Taylor
polynomial after reserving the order-15 Taylor remainder. -/
theorem largeFour_cosine_taylor_data_check {i j : LargeFourLabel}
    (hij : i.val < j.val) :
    largeFourCosineCap i j + largeFourPairAngleLower i j ^ 16 / 1307674368000 ≤
      largeFourTaylorPoly (largeFourPairAngleLower i j) := by
  fin_cases i <;> fin_cases j <;>
    simp_all [largeFourCosineCap, largeFourPairAngleLower] <;>
    norm_num [largeFourTaylorPoly]

theorem largeFour_pair_cosine_cap_le_cos {i j : LargeFourLabel}
    (hij : i.val < j.val) :
    (largeFourCosineCap i j : ℝ) ≤
      Real.cos (largeFourPairAngleLower i j) := by
  have hcheck := largeFour_cosine_taylor_data_check hij
  have hell0 : 0 ≤ (largeFourPairAngleLower i j : ℝ) := by
    fin_cases i <;> fin_cases j <;>
      norm_num [largeFourPairAngleLower] at *
  have hellb : (largeFourPairAngleLower i j : ℝ) ≤ 13 / 10 := by
    fin_cases i <;> fin_cases j <;>
      norm_num [largeFourPairAngleLower] at *
  have hb : (0 : ℝ) < 13 / 10 := by norm_num
  have hx : (largeFourPairAngleLower i j : ℝ) ∈ Set.Icc 0 (13 / 10) :=
    ⟨hell0, hellb⟩
  have htaylor := cosine_taylor_fifteen_at_zero
    (b := (13 / 10 : ℝ)) (x := (largeFourPairAngleLower i j : ℝ)) hb
  have herror := cosine_taylor_fifteen_remainder
    (a := (0 : ℝ)) (b := (13 / 10 : ℝ))
    (x := (largeFourPairAngleLower i j : ℝ)) (by norm_num) hx
  have hpolyCast :
      (largeFourTaylorPoly (largeFourPairAngleLower i j) : ℝ) =
        1 - (largeFourPairAngleLower i j : ℝ) ^ 2 / 2 +
          (largeFourPairAngleLower i j : ℝ) ^ 4 / 24 -
          (largeFourPairAngleLower i j : ℝ) ^ 6 / 720 +
          (largeFourPairAngleLower i j : ℝ) ^ 8 / 40320 -
          (largeFourPairAngleLower i j : ℝ) ^ 10 / 3628800 +
          (largeFourPairAngleLower i j : ℝ) ^ 12 / 479001600 -
          (largeFourPairAngleLower i j : ℝ) ^ 14 / 87178291200 := by
    norm_num [largeFourTaylorPoly]
  have hcheckR :
      (largeFourCosineCap i j : ℝ) +
          (largeFourPairAngleLower i j : ℝ) ^ 16 / 1307674368000 ≤
        (largeFourTaylorPoly (largeFourPairAngleLower i j) : ℝ) := by
    exact_mod_cast hcheck
  have hfac : (Nat.factorial 15 : ℝ) = 1307674368000 := by norm_num
  apply lower_bound_of_taylor_error herror
  rw [htaylor, ← hpolyCast, hfac]
  simpa only [sub_zero] using hcheckR

theorem largeFourPairAngleLower_symm (i j : LargeFourLabel) :
    largeFourPairAngleLower i j = largeFourPairAngleLower j i := by
  fin_cases i <;> fin_cases j <;> norm_num [largeFourPairAngleLower]

theorem largeFourCosineCap_symm (i j : LargeFourLabel) :
    largeFourCosineCap i j = largeFourCosineCap j i := by
  fin_cases i <;> fin_cases j <;> norm_num [largeFourCosineCap]

theorem largeFour_pair_cosine_cap_le_cos_of_ne {i j : LargeFourLabel}
    (hne : i ≠ j) :
    (largeFourCosineCap i j : ℝ) ≤
      Real.cos (largeFourPairAngleLower i j) := by
  by_cases hlt : i.val < j.val
  · exact largeFour_pair_cosine_cap_le_cos hlt
  · have hneval : i.val ≠ j.val := fun h => hne (Fin.ext h)
    have hgt : j.val < i.val :=
      lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm hneval)
    have h := largeFour_pair_cosine_cap_le_cos (i := j) (j := i) hgt
    simpa only [largeFourCosineCap_symm, largeFourPairAngleLower_symm] using h

/-- Four exact rational corner inequalities for each of the six disk pairs.
The lemma is the finite-arithmetic part of the rectangle maximization. -/
theorem largeFour_pair_radial_corner_check {i j : LargeFourLabel}
    (hij : i ≠ j) :
    (largeFourRadialLower i) ^ 2 + (largeFourRadialLower j) ^ 2 -
        (largeFourRootLower i + largeFourRootLower j) ^ 2 ≤
      largeFourCosineCap i j *
        (2 * largeFourRadialLower i * largeFourRadialLower j) ∧
    (largeFourRadialLower i) ^ 2 + (largeFourRadialUpper j) ^ 2 -
        (largeFourRootLower i + largeFourRootLower j) ^ 2 ≤
      largeFourCosineCap i j *
        (2 * largeFourRadialLower i * largeFourRadialUpper j) ∧
    (largeFourRadialUpper i) ^ 2 + (largeFourRadialLower j) ^ 2 -
        (largeFourRootLower i + largeFourRootLower j) ^ 2 ≤
      largeFourCosineCap i j *
        (2 * largeFourRadialUpper i * largeFourRadialLower j) ∧
    (largeFourRadialUpper i) ^ 2 + (largeFourRadialUpper j) ^ 2 -
        (largeFourRootLower i + largeFourRootLower j) ^ 2 ≤
      largeFourCosineCap i j *
        (2 * largeFourRadialUpper i * largeFourRadialUpper j) := by
  fin_cases i <;> fin_cases j <;>
    norm_num [largeFourRadialLower, largeFourRadialUpper, largeFourRootLower,
      largeFourPackingIndex, largeFourRadialPartner, tenRootLower, tenCircleGlobalRadiusUpper,
      largeFourCosineCap] at *

/-- The rational radial rectangle and the four checked corners imply the
certified lower bound for each pair's actual contact angle. -/
theorem largeFour_pair_touch_angle_lower {i j : LargeFourLabel}
    {a b : ℝ} (hne : i ≠ j)
    (haL : (largeFourRadialLower i : ℝ) ≤ a)
    (haU : a ≤ (largeFourRadialUpper i : ℝ))
    (hbL : (largeFourRadialLower j : ℝ) ≤ b)
    (hbU : b ≤ (largeFourRadialUpper j : ℝ)) :
    (largeFourPairAngleLower i j : ℝ) ≤
      touchAngle a b ((largeFourRootLower i : ℝ) +
        (largeFourRootLower j : ℝ)) := by
  have hcorners := largeFour_pair_radial_corner_check hne
  have h00 :
      (largeFourRadialLower i : ℝ) ^ 2 +
          (largeFourRadialLower j : ℝ) ^ 2 -
          ((largeFourRootLower i : ℝ) + (largeFourRootLower j : ℝ)) ^ 2 ≤
        (largeFourCosineCap i j : ℝ) *
          (2 * (largeFourRadialLower i : ℝ) *
            (largeFourRadialLower j : ℝ)) := by
    exact_mod_cast hcorners.1
  have h01 :
      (largeFourRadialLower i : ℝ) ^ 2 +
          (largeFourRadialUpper j : ℝ) ^ 2 -
          ((largeFourRootLower i : ℝ) + (largeFourRootLower j : ℝ)) ^ 2 ≤
        (largeFourCosineCap i j : ℝ) *
          (2 * (largeFourRadialLower i : ℝ) *
            (largeFourRadialUpper j : ℝ)) := by
    exact_mod_cast hcorners.2.1
  have h10 :
      (largeFourRadialUpper i : ℝ) ^ 2 +
          (largeFourRadialLower j : ℝ) ^ 2 -
          ((largeFourRootLower i : ℝ) + (largeFourRootLower j : ℝ)) ^ 2 ≤
        (largeFourCosineCap i j : ℝ) *
          (2 * (largeFourRadialUpper i : ℝ) *
            (largeFourRadialLower j : ℝ)) := by
    exact_mod_cast hcorners.2.2.1
  have h11 :
      (largeFourRadialUpper i : ℝ) ^ 2 +
          (largeFourRadialUpper j : ℝ) ^ 2 -
          ((largeFourRootLower i : ℝ) + (largeFourRootLower j : ℝ)) ^ 2 ≤
        (largeFourCosineCap i j : ℝ) *
          (2 * (largeFourRadialUpper i : ℝ) *
            (largeFourRadialUpper j : ℝ)) := by
    exact_mod_cast hcorners.2.2.2
  have hangle := largeFourPairAngleLower_real_bounds i j
  have hellpi : (largeFourPairAngleLower i j : ℝ) ≤ Real.pi := by
    linarith [Real.pi_gt_three]
  exact box_corners_certify_touch_angle haL haU hbL hbU
    (largeFourRadialLower_pos i) (largeFourRadialLower_pos j)
    h00 h01 h10 h11 hangle.1 hellpi
    (largeFour_pair_cosine_cap_le_cos_of_ne hne)

/-- Every packing below the rational radius ceiling puts each of the four
large-circle center radii inside the rectangle certified above. -/
theorem largeFour_packing_radial_bounds {R : ℝ} (P : Packing 10 R)
    (hRU : R ≤ (tenCircleGlobalRadiusUpper : ℝ))
    (hRadius : ∀ i : LargeFourLabel,
      (P.circles (largeFourPackingIndex i)).radius =
        Real.sqrt ((i.val + 7 : ℕ) : ℝ)) :
    ∀ i : LargeFourLabel,
      (largeFourRadialLower i : ℝ) ≤
          globalPointNorm (P.circles (largeFourPackingIndex i)).center ∧
        globalPointNorm (P.circles (largeFourPackingIndex i)).center ≤
          (largeFourRadialUpper i : ℝ) := by
  intro i
  let s (k : LargeFourLabel) :=
    globalPointNorm (P.circles (largeFourPackingIndex k)).center
  have hroot (k : LargeFourLabel) :
      (largeFourRootLower k : ℝ) ≤
        (P.circles (largeFourPackingIndex k)).radius :=
    largeFour_packing_root_radius_lower P hRadius k
  have hcontained (k : LargeFourLabel) :
      Contained (tenCircleGlobalRadiusUpper : ℝ)
        (P.circles (largeFourPackingIndex k)) :=
    contained_mono hRU (P.contained (largeFourPackingIndex k))
  have hupper (k : LargeFourLabel) :
      s k ≤ (tenCircleGlobalRadiusUpper : ℝ) - largeFourRootLower k := by
    have h := contained_radial_upper (hcontained k)
    dsimp [s]
    linarith [hroot k]
  have hupperQ (k : LargeFourLabel) :
      s k ≤ (largeFourRadialUpper k : ℝ) := by
    dsimp [largeFourRadialUpper]
    simpa only [Rat.cast_sub] using hupper k
  have hindexNe :
      largeFourPackingIndex i ≠
        largeFourPackingIndex (largeFourRadialPartner i) := by
    intro h
    exact largeFourRadialPartner_ne i
      (largeFourPackingIndex_injective h)
  have hradialSum := separated_implies_radial_sum_lower
    (P.separated hindexNe) rfl rfl
  have hpartnerUpper :
      s (largeFourRadialPartner i) ≤
        (tenCircleGlobalRadiusUpper : ℝ) -
          largeFourRootLower (largeFourRadialPartner i) := by
    have h := contained_radial_upper (hcontained (largeFourRadialPartner i))
    dsimp [s]
    linarith [hroot (largeFourRadialPartner i)]
  have hlowerRaw :
      (largeFourRootLower i : ℝ) +
          2 * (largeFourRootLower (largeFourRadialPartner i) : ℝ) -
          (tenCircleGlobalRadiusUpper : ℝ) ≤ s i := by
    dsimp [s] at hradialSum ⊢
    linarith [hroot i, hroot (largeFourRadialPartner i), hpartnerUpper]
  have hlower : (largeFourRadialLower i : ℝ) ≤ s i := by
    have hformula : (largeFourRadialLower i : ℝ) =
        (largeFourRootLower i : ℝ) +
          2 * (largeFourRootLower (largeFourRadialPartner i) : ℝ) -
          (tenCircleGlobalRadiusUpper : ℝ) := by
      exact_mod_cast (rfl : largeFourRadialLower i =
        largeFourRootLower i +
          2 * largeFourRootLower (largeFourRadialPartner i) -
          tenCircleGlobalRadiusUpper)
    rw [hformula]
    exact hlowerRaw
  exact ⟨by simpa [s] using hlower, by simpa [s] using hupperQ i⟩

/-- Pairwise non-overlap also gives a lower bound on the distance between
the centers, using only the rational lower bounds for the two radii. -/
theorem largeFour_packing_pair_distance_lower {R : ℝ} (P : Packing 10 R)
    (hRadius : ∀ i : LargeFourLabel,
      (P.circles (largeFourPackingIndex i)).radius =
        Real.sqrt ((i.val + 7 : ℕ) : ℝ))
    {i j : LargeFourLabel} (hij : i ≠ j) :
    ((largeFourRootLower i : ℝ) + (largeFourRootLower j : ℝ)) ^ 2 ≤
      pointNorm
        ((P.circles (largeFourPackingIndex i)).center.1 -
            (P.circles (largeFourPackingIndex j)).center.1,
         (P.circles (largeFourPackingIndex i)).center.2 -
            (P.circles (largeFourPackingIndex j)).center.2) ^ 2 := by
  have hidx : largeFourPackingIndex i ≠ largeFourPackingIndex j := by
    intro h
    exact hij (largeFourPackingIndex_injective h)
  have hsep := P.separated hidx
  change ((P.circles (largeFourPackingIndex i)).radius +
      (P.circles (largeFourPackingIndex j)).radius) ^ 2 ≤
    distSq (P.circles (largeFourPackingIndex i)).center
      (P.circles (largeFourPackingIndex j)).center at hsep
  have hsepNorm :
      ((P.circles (largeFourPackingIndex i)).radius +
        (P.circles (largeFourPackingIndex j)).radius) ^ 2 ≤
      pointNorm
        ((P.circles (largeFourPackingIndex i)).center.1 -
            (P.circles (largeFourPackingIndex j)).center.1,
         (P.circles (largeFourPackingIndex i)).center.2 -
            (P.circles (largeFourPackingIndex j)).center.2) ^ 2 := by
    simpa [distSq, pointNorm_sq] using hsep
  exact separated_lower_contact_distance
    (le_of_lt (largeFourRootLower_pos i))
    (le_of_lt (largeFourRootLower_pos j))
    (largeFour_packing_root_radius_lower P hRadius i)
    (largeFour_packing_root_radius_lower P hRadius j)
    hsepNorm

private theorem list_exists_eq_four_of_length {α : Type*} {l : List α}
    (hlen : l.length = 4) : ∃ a b c d, l = [a, b, c, d] := by
  cases l with
  | nil => simp at hlen
  | cons a l =>
    cases l with
    | nil => simp at hlen
    | cons b l =>
      cases l with
      | nil => simp at hlen
      | cons c l =>
        cases l with
        | nil => simp at hlen
        | cons d rest =>
          have hrest : rest.length = 0 := by
            simp only [List.length_cons] at hlen
            omega
          have hrest' : rest = [] := List.length_eq_zero_iff.mp hrest
          subst rest
          exact ⟨a, b, c, d, rfl⟩

private noncomputable def largeFourSorted (theta : LargeFourLabel → ℝ) :
    List LargeFourLabel :=
  List.mergeSort largeFourLabels (fun a b => decide (theta a ≤ theta b))

/-- Any four real angles admit a label order that is nondecreasing. -/
theorem largeFour_exists_sorted_four (theta : LargeFourLabel → ℝ) :
    ∃ i0 i1 i2 i3 : LargeFourLabel,
      [i0, i1, i2, i3].Perm largeFourLabels ∧
      theta i0 ≤ theta i1 ∧ theta i1 ≤ theta i2 ∧ theta i2 ≤ theta i3 := by
  let sorted := largeFourSorted theta
  have hpair : sorted.Pairwise (fun a b => theta a ≤ theta b) := by
    simpa [sorted, largeFourSorted] using
      (List.pairwise_mergeSort
        (le := fun a b : LargeFourLabel => theta a ≤ theta b)
        (fun _ _ _ hab hbc => by
          simpa using le_trans (of_decide_eq_true hab) (of_decide_eq_true hbc))
        (fun a b => by
          rcases le_total (theta a) (theta b) with hab | hab <;> simp [hab])
        largeFourLabels)
  have hperm : sorted.Perm largeFourLabels := by
    simpa [sorted, largeFourSorted] using
      (List.mergeSort_perm largeFourLabels
        (fun a b => decide (theta a ≤ theta b)))
  have hlen : sorted.length = 4 := by
    calc
      sorted.length = largeFourLabels.length := hperm.length_eq
      _ = 4 := by simp [largeFourLabels]
  obtain ⟨i0, i1, i2, i3, hsorted⟩ :=
    list_exists_eq_four_of_length hlen
  have hperm' : [i0, i1, i2, i3].Perm largeFourLabels := by
    rw [← hsorted]
    exact hperm
  have hpair' := hpair
  rw [hsorted] at hpair'
  have h01idx : (⟨0, by simp⟩ : Fin ([i0, i1, i2, i3].length)) < ⟨1, by simp⟩ := by
    apply Fin.lt_def.mpr
    norm_num
  have h12idx : (⟨1, by simp⟩ : Fin ([i0, i1, i2, i3].length)) < ⟨2, by simp⟩ := by
    apply Fin.lt_def.mpr
    norm_num
  have h23idx : (⟨2, by simp⟩ : Fin ([i0, i1, i2, i3].length)) < ⟨3, by simp⟩ := by
    apply Fin.lt_def.mpr
    norm_num
  have h01 := hpair'.rel_get_of_lt h01idx
  have h12 := hpair'.rel_get_of_lt h12idx
  have h23 := hpair'.rel_get_of_lt h23idx
  have h01' : theta i0 ≤ theta i1 := by simpa using h01
  have h12' : theta i1 ≤ theta i2 := by simpa using h12
  have h23' : theta i2 ≤ theta i3 := by simpa using h23
  exact ⟨i0, i1, i2, i3, hperm', h01', h12', h23'⟩

/-- Sum of the certified lower bounds along a list's consecutive path. -/
def largeFourPathAngleLower : List LargeFourLabel → ℚ
  | [] => 0
  | [_] => 0
  | i :: j :: rest =>
      largeFourPairAngleLower i j + largeFourPathAngleLower (j :: rest)

def largeFourAllPathChecks : Bool :=
  largeFourOrders.all fun order =>
    decide (largeFourPiUpper < largeFourPathAngleLower order)

theorem largeFour_all_path_checks_pass : largeFourAllPathChecks = true := by
  native_decide

theorem largeFour_path_lower_gt_pi_upper {order : List LargeFourLabel}
    (horder : order.Perm largeFourLabels) :
    largeFourPiUpper < largeFourPathAngleLower order := by
  have hmem : order ∈ largeFourOrders := List.mem_permutations.mpr horder
  have hcheck := (List.all_eq_true.mp largeFour_all_path_checks_pass) order hmem
  exact of_decide_eq_true hcheck

theorem largeFour_angle_path_excludes_semicircle
    (theta : LargeFourLabel → ℝ) (origin : ℝ)
    (i0 i1 i2 i3 : LargeFourLabel)
    (horder : [i0, i1, i2, i3].Perm largeFourLabels)
    (hsemicircle : ∀ i, origin ≤ theta i ∧ theta i ≤ origin + Real.pi)
    (hgap01 : (largeFourPairAngleLower i0 i1 : ℝ) ≤ theta i1 - theta i0)
    (hgap12 : (largeFourPairAngleLower i1 i2 : ℝ) ≤ theta i2 - theta i1)
    (hgap23 : (largeFourPairAngleLower i2 i3 : ℝ) ≤ theta i3 - theta i2) :
    False := by
  have hfiniteQ := largeFour_path_lower_gt_pi_upper horder
  have hfiniteQ' : largeFourPiUpper <
      largeFourPairAngleLower i0 i1 +
        (largeFourPairAngleLower i1 i2 +
          largeFourPairAngleLower i2 i3) := by
    simpa [largeFourPathAngleLower] using hfiniteQ
  have hfinite : (largeFourPiUpper : ℝ) <
      (largeFourPairAngleLower i0 i1 : ℝ) +
        ((largeFourPairAngleLower i1 i2 : ℝ) +
          (largeFourPairAngleLower i2 i3 : ℝ)) := by
    exact_mod_cast hfiniteQ'
  have hpi : Real.pi < (largeFourPiUpper : ℝ) := by
    rw [show (largeFourPiUpper : ℝ) = 3.1416 by norm_num [largeFourPiUpper]]
    exact Real.pi_lt_d4
  have hgapSum :
      (largeFourPairAngleLower i0 i1 : ℝ) +
        (largeFourPairAngleLower i1 i2 : ℝ) +
        (largeFourPairAngleLower i2 i3 : ℝ) ≤ theta i3 - theta i0 := by
    linarith
  have hspan : theta i3 - theta i0 ≤ Real.pi := by
    have hlast := (hsemicircle i3).2
    have hfirst := (hsemicircle i0).1
    linarith
  linarith


theorem pointPolarAngle_lt_two_pi (p : Point) :
    pointPolarAngle p < 2 * Real.pi := by
  unfold pointPolarAngle
  dsimp
  split_ifs with h
  · linarith [Complex.arg_le_pi ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I),
      Real.pi_pos]
  · have hargLo := Complex.neg_pi_lt_arg
      ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I)
    have hargNeg : Complex.arg ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I) < 0 :=
      lt_of_not_ge h
    linarith

/-- In any packing below the certified ceiling, the centers of the four
largest disks cannot be contained in a closed half-plane through the origin.
The half-plane may be rotated arbitrarily; the proof derives the six angle
bounds from the packing's own radial boxes and pairwise non-overlap. -/
theorem largeFour_packing_not_in_closed_halfplane {R : ℝ}
    (P : Packing 10 R) (hRU : R ≤ (tenCircleGlobalRadiusUpper : ℝ))
    (hRadius : ∀ i : LargeFourLabel,
      (P.circles (largeFourPackingIndex i)).radius =
        Real.sqrt ((i.val + 7 : ℕ) : ℝ)) :
    ¬ ∃ φ : ℝ, ∀ i : LargeFourLabel,
      0 ≤ (rotatePoint φ
        (P.circles (largeFourPackingIndex i)).center).2 := by
  rintro ⟨φ, hhalf⟩
  let Q : Packing 10 R := P.rotate φ
  have hRadiusQ : ∀ i : LargeFourLabel,
      (Q.circles (largeFourPackingIndex i)).radius =
        Real.sqrt ((i.val + 7 : ℕ) : ℝ) := by
    intro i
    simpa [Q, Packing.rotate] using hRadius i
  have hrad := largeFour_packing_radial_bounds Q hRU hRadiusQ
  let radial (i : LargeFourLabel) : ℝ :=
    globalPointNorm (Q.circles (largeFourPackingIndex i)).center
  let theta (i : LargeFourLabel) : ℝ :=
    pointPolarAngle (Q.circles (largeFourPackingIndex i)).center
  have hpolar (i : LargeFourLabel) :
      (Q.circles (largeFourPackingIndex i)).center =
        polarPoint (radial i) (theta i) := by
    have h := pointPolarAngle_representation
      (Q.circles (largeFourPackingIndex i)).center
    simpa [radial, theta, pointNorm, globalPointNorm] using h.2.2.symm
  have hhalfQ (i : LargeFourLabel) :
      0 ≤ (Q.circles (largeFourPackingIndex i)).center.2 := by
    simpa [Q, Packing.rotate] using hhalf i
  have hthetaLo (i : LargeFourLabel) : 0 ≤ theta i := by
    exact (pointPolarAngle_representation
      (Q.circles (largeFourPackingIndex i)).center).1
  have hthetaHi (i : LargeFourLabel) : theta i ≤ Real.pi := by
    have hradPos : 0 < radial i :=
      lt_of_lt_of_le (largeFourRadialLower_pos i) (hrad i).1
    have hy : (Q.circles (largeFourPackingIndex i)).center.2 =
        radial i * Real.sin (theta i) := by
      have h := congrArg Prod.snd (hpolar i)
      simpa [polarPoint] using h
    have hsinNonneg : 0 ≤ Real.sin (theta i) := by
      by_contra hneg
      have hneg' : Real.sin (theta i) < 0 := lt_of_not_ge hneg
      have hprod : radial i * Real.sin (theta i) < 0 :=
        mul_neg_of_pos_of_neg hradPos hneg'
      linarith [hhalfQ i, hy]
    by_contra hnot
    have hpiLt : Real.pi < theta i := lt_of_not_ge hnot
    have hthetaLt : theta i < 2 * Real.pi := by
      exact pointPolarAngle_lt_two_pi _
    have hshiftLo : -Real.pi < theta i - 2 * Real.pi := by
      linarith
    have hshiftHi : theta i - 2 * Real.pi < 0 := by
      linarith
    have hsinShift : Real.sin (theta i - 2 * Real.pi) < 0 :=
      Real.sin_neg_of_neg_of_neg_pi_lt hshiftHi hshiftLo
    have hperiod : Real.sin (theta i - 2 * Real.pi) = Real.sin (theta i) := by
      calc
        Real.sin (theta i - 2 * Real.pi) =
            Real.sin ((theta i - 2 * Real.pi) + 2 * Real.pi) :=
          (Real.sin_add_two_pi _).symm
        _ = Real.sin (theta i) := by congr 1; ring
    rw [hperiod] at hsinShift
    exact (not_lt_of_ge hsinNonneg) hsinShift
  have hthetaSemicircle (i : LargeFourLabel) :
      0 ≤ theta i ∧ theta i ≤ (0 : ℝ) + Real.pi := by
    exact ⟨hthetaLo i, by simpa using hthetaHi i⟩
  have hgap {i j : LargeFourLabel} (hne : i ≠ j)
      (hmon : theta i ≤ theta j) :
      (largeFourPairAngleLower i j : ℝ) ≤ theta j - theta i := by
    have hri : 0 < radial i :=
      lt_of_lt_of_le (largeFourRadialLower_pos i) (hrad i).1
    have hrj : 0 < radial j :=
      lt_of_lt_of_le (largeFourRadialLower_pos j) (hrad j).1
    have hdist := largeFour_packing_pair_distance_lower Q hRadiusQ hne
    have hdistPolar := hdist
    rw [hpolar i, hpolar j] at hdistPolar
    have hangle := largeFour_pair_touch_angle_lower hne
      (hrad i).1 (hrad i).2 (hrad j).1 (hrad j).2
    have hdelta0 : 0 ≤ theta j - theta i := sub_nonneg.mpr hmon
    have hdelta2 : theta j - theta i ≤ 2 * Real.pi := by
      have hJ := hthetaHi j
      have hI := hthetaLo i
      nlinarith [Real.pi_pos]
    have hgapBounds := polar_touch_angle_ordered_gap
      hri hrj
      ((largeFourPairAngleLower_real_bounds i j).2.trans (by
        nlinarith [Real.pi_gt_three]))
      hdelta0 hdelta2 hdistPolar hangle
    exact hgapBounds.1
  rcases largeFour_exists_sorted_four theta with
    ⟨i0, i1, i2, i3, horder, h01, h12, h23⟩
  have hnodup : [i0, i1, i2, i3].Nodup :=
    horder.nodup_iff.2 (by decide : largeFourLabels.Nodup)
  have hne01 : i0 ≠ i1 := by
    intro heq
    have hnot := (List.nodup_cons.mp hnodup).1
    apply hnot
    simp [heq]
  have hne12 : i1 ≠ i2 := by
    intro heq
    have htail := (List.nodup_cons.mp hnodup).2
    have hnot := (List.nodup_cons.mp htail).1
    apply hnot
    simp [heq]
  have hne23 : i2 ≠ i3 := by
    intro heq
    have htail := (List.nodup_cons.mp hnodup).2
    have htail := (List.nodup_cons.mp htail).2
    have hnot := (List.nodup_cons.mp htail).1
    apply hnot
    simp [heq]
  exact largeFour_angle_path_excludes_semicircle theta 0 i0 i1 i2 i3
    horder hthetaSemicircle
    (hgap hne01 h01) (hgap hne12 h12) (hgap hne23 h23)


end CirclePacking
