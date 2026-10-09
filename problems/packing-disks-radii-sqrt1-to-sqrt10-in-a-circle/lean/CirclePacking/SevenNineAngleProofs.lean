import CirclePacking.CornerBound
import CirclePacking.CosineTaylor
import CirclePacking.SevenNineAngleData
import CirclePacking.SevenNineAngles
import Mathlib.Analysis.Real.Pi.Bounds

namespace CirclePacking

set_option maxRecDepth 100000

def sevenNineRadial (i state side : Nat) : Rat :=
  let p := sevenNineRadialBounds[i * 2 + state]!
  if side == 0 then p.1 else p.2

lemma rat_le_sqrt {q : Rat} {n : ℕ} (hq : (0 : ℝ) ≤ q) (hsq : (q : ℝ)^2 ≤ n) : (q : ℝ) ≤ Real.sqrt n := by
  have hn := Real.sq_sqrt (show (0 : ℝ) ≤ n by positivity)
  have hs := Real.sqrt_nonneg (n : ℝ)
  by_contra h
  have hlt : Real.sqrt (n : ℝ) < q := lt_of_not_ge h
  have hh := (sq_lt_sq₀ hs hq).mpr hlt
  nlinarith

lemma rat_sum_sqrt_lower {q qi qj : Rat} {ni nj : ℕ}
    (hqi : (qi : ℝ) ≤ Real.sqrt ni) (hqj : (qj : ℝ) ≤ Real.sqrt nj)
    (hq : q ≤ qi + qj) :
    (q : ℝ) ≤ Real.sqrt ni + Real.sqrt nj := by
  have hqR : (q : ℝ) ≤ (qi : ℝ) + (qj : ℝ) := by exact_mod_cast hq
  linarith

lemma rat_le_real {x y : Rat} (h : x ≤ y) : (x : ℝ) ≤ (y : ℝ) := by
  exact_mod_cast h

lemma zero_angle_lower {x : ℝ} : (0 : ℝ) ≤ Real.arccos x := by
  exact Real.arccos_nonneg x

lemma sqrt_lower_4 : ((2 : ℝ) / 1) ≤ Real.sqrt 4 := by
  convert (rat_le_sqrt (q := ((2 : Rat) / 1)) (n := 4) (by norm_num) (by norm_num)) using 1 ; norm_num

lemma sqrt_lower_5 : ((2236067977499789696409173668731276235440618359611525724270897245410520925637804899414414408378782274969508176150773783504 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) ≤ Real.sqrt 5 := by
  convert (rat_le_sqrt (q := ((2236067977499789696409173668731276235440618359611525724270897245410520925637804899414414408378782274969508176150773783504 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (n := 5) (by norm_num) (by norm_num)) using 1 ; norm_num

lemma sqrt_lower_6 : ((2449489742783178098197284074705891391965947480656670128432692567250960377457315026539859433104640234818594601226614189124 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) ≤ Real.sqrt 6 := by
  convert (rat_le_sqrt (q := ((2449489742783178098197284074705891391965947480656670128432692567250960377457315026539859433104640234818594601226614189124 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (n := 6) (by norm_num) (by norm_num)) using 1 ; norm_num

lemma sqrt_lower_7 : ((2645751311064590590501615753639260425710259183082450180368334459201068823230283627760392886474543610615064578338497463095 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) ≤ Real.sqrt 7 := by
  convert (rat_le_sqrt (q := ((2645751311064590590501615753639260425710259183082450180368334459201068823230283627760392886474543610615064578338497463095 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (n := 7) (by norm_num) (by norm_num)) using 1 ; norm_num

lemma sqrt_lower_8 : ((2828427124746190097603377448419396157139343750753896146353359475981464956924214077700775068655283145470027692461824594049 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) ≤ Real.sqrt 8 := by
  convert (rat_le_sqrt (q := ((2828427124746190097603377448419396157139343750753896146353359475981464956924214077700775068655283145470027692461824594049 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (n := 8) (by norm_num) (by norm_num)) using 1 ; norm_num

lemma sqrt_lower_9 : ((3 : ℝ) / 1) ≤ Real.sqrt 9 := by
  convert (rat_le_sqrt (q := ((3 : Rat) / 1)) (n := 9) (by norm_num) (by norm_num)) using 1 ; norm_num

lemma sqrt_lower_10 : ((3162277660168379331998893544432718533719555139325216826857504852792594438639238221344248108379300295187347284152840055148 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) ≤ Real.sqrt 10 := by
  convert (rat_le_sqrt (q := ((3162277660168379331998893544432718533719555139325216826857504852792594438639238221344248108379300295187347284152840055148 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (n := 10) (by norm_num) (by norm_num)) using 1 ; norm_num

theorem sevenNineAngle_0_1_0_0 {a b : ℝ}
    (haL : (sevenNineRadial 0 0 0 : ℝ) ≤ a) (haU : a ≤ (sevenNineRadial 0 0 1 : ℝ))
    (hbL : (sevenNineRadial 1 0 0 : ℝ) ≤ b) (hbU : b ≤ (sevenNineRadial 1 0 1 : ℝ)) :
    (sevenNineAngleLower[0]! : ℝ) ≤ Real.arccos (touchCosine a b (Real.sqrt 4 + Real.sqrt 5)) := by
  let d : ℝ := Real.sqrt 4 + Real.sqrt 5
  have hd' : (((4236067977499789696409173668731276235440618359611525724270897245410520925637804899414414408 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) : ℝ) ≤ d := by
    dsimp [d]
    have h := rat_sum_sqrt_lower (q := ((4236067977499789696409173668731276235440618359611525724270897245410520925637804899414414408 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (qi := ((2 : Rat) / 1)) (qj := ((2236067977499789696409173668731276235440618359611525724270897245410520925637804899414414408378782274969508176150773783504 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))
      (ni := 4) (nj := 5)
      (by convert sqrt_lower_4 using 1 ; norm_num)
      (by convert sqrt_lower_5 using 1 ; norm_num)
      (by native_decide)
    convert h using 1 ; norm_num
  have hd : (((4236067977499789696409173668731276235440618359611525724270897245410520925637804899414414408 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) ≤ d := by exact hd'
  have hd2 : (((4236067977499789696409173668731276235440618359611525724270897245410520925637804899414414408 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))^2 ≤ d^2 := by
    have hq : (0 : ℝ) ≤ ((4236067977499789696409173668731276235440618359611525724270897245410520925637804899414414408 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) := by norm_num
    have hdn : 0 ≤ d := by positivity
    exact (sq_le_sq₀ hq hdn).mpr hd
  have hd2' : (sevenNineDistanceLower[0]! : ℝ)^2 ≤ d^2 := by
    convert hd2 using 1 ; norm_num [sevenNineDistanceLower]
  have h00 : (sevenNineRadial 0 0 0 : ℝ)^2 + (sevenNineRadial 1 0 0 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[0]! : ℝ) * (2 * (sevenNineRadial 0 0 0 : ℝ) * (sevenNineRadial 1 0 0 : ℝ)) := by
    have hq : (sevenNineRadial 0 0 0)^2 + (sevenNineRadial 1 0 0)^2 - sevenNineDistanceLower[0]!^2 ≤
        sevenNineCosUpper[0]! * (2 * sevenNineRadial 0 0 0 * sevenNineRadial 1 0 0) := by native_decide
    have hqR :
        (sevenNineRadial 0 0 0 : ℝ)^2 + (sevenNineRadial 1 0 0 : ℝ)^2 - (sevenNineDistanceLower[0]! : ℝ)^2 ≤
          (sevenNineCosUpper[0]! : ℝ) * (2 * (sevenNineRadial 0 0 0 : ℝ) * (sevenNineRadial 1 0 0 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 0 0 0 : ℝ)^2 + (sevenNineRadial 1 0 0 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 0 0 0 : ℝ)^2 + (sevenNineRadial 1 0 0 : ℝ)^2 - (sevenNineDistanceLower[0]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h01 : (sevenNineRadial 0 0 0 : ℝ)^2 + (sevenNineRadial 1 0 1 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[0]! : ℝ) * (2 * (sevenNineRadial 0 0 0 : ℝ) * (sevenNineRadial 1 0 1 : ℝ)) := by
    have hq : (sevenNineRadial 0 0 0)^2 + (sevenNineRadial 1 0 1)^2 - sevenNineDistanceLower[0]!^2 ≤
        sevenNineCosUpper[0]! * (2 * sevenNineRadial 0 0 0 * sevenNineRadial 1 0 1) := by native_decide
    have hqR :
        (sevenNineRadial 0 0 0 : ℝ)^2 + (sevenNineRadial 1 0 1 : ℝ)^2 - (sevenNineDistanceLower[0]! : ℝ)^2 ≤
          (sevenNineCosUpper[0]! : ℝ) * (2 * (sevenNineRadial 0 0 0 : ℝ) * (sevenNineRadial 1 0 1 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 0 0 0 : ℝ)^2 + (sevenNineRadial 1 0 1 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 0 0 0 : ℝ)^2 + (sevenNineRadial 1 0 1 : ℝ)^2 - (sevenNineDistanceLower[0]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h10 : (sevenNineRadial 0 0 1 : ℝ)^2 + (sevenNineRadial 1 0 0 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[0]! : ℝ) * (2 * (sevenNineRadial 0 0 1 : ℝ) * (sevenNineRadial 1 0 0 : ℝ)) := by
    have hq : (sevenNineRadial 0 0 1)^2 + (sevenNineRadial 1 0 0)^2 - sevenNineDistanceLower[0]!^2 ≤
        sevenNineCosUpper[0]! * (2 * sevenNineRadial 0 0 1 * sevenNineRadial 1 0 0) := by native_decide
    have hqR :
        (sevenNineRadial 0 0 1 : ℝ)^2 + (sevenNineRadial 1 0 0 : ℝ)^2 - (sevenNineDistanceLower[0]! : ℝ)^2 ≤
          (sevenNineCosUpper[0]! : ℝ) * (2 * (sevenNineRadial 0 0 1 : ℝ) * (sevenNineRadial 1 0 0 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 0 0 1 : ℝ)^2 + (sevenNineRadial 1 0 0 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 0 0 1 : ℝ)^2 + (sevenNineRadial 1 0 0 : ℝ)^2 - (sevenNineDistanceLower[0]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h11 : (sevenNineRadial 0 0 1 : ℝ)^2 + (sevenNineRadial 1 0 1 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[0]! : ℝ) * (2 * (sevenNineRadial 0 0 1 : ℝ) * (sevenNineRadial 1 0 1 : ℝ)) := by
    have hq : (sevenNineRadial 0 0 1)^2 + (sevenNineRadial 1 0 1)^2 - sevenNineDistanceLower[0]!^2 ≤
        sevenNineCosUpper[0]! * (2 * sevenNineRadial 0 0 1 * sevenNineRadial 1 0 1) := by native_decide
    have hqR :
        (sevenNineRadial 0 0 1 : ℝ)^2 + (sevenNineRadial 1 0 1 : ℝ)^2 - (sevenNineDistanceLower[0]! : ℝ)^2 ≤
          (sevenNineCosUpper[0]! : ℝ) * (2 * (sevenNineRadial 0 0 1 : ℝ) * (sevenNineRadial 1 0 1 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 0 0 1 : ℝ)^2 + (sevenNineRadial 1 0 1 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 0 0 1 : ℝ)^2 + (sevenNineRadial 1 0 1 : ℝ)^2 - (sevenNineDistanceLower[0]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have htouch := corner_touch_cosine_bound haL haU hbL hbU
    (by norm_num [sevenNineRadial, sevenNineRadialBounds])
    (by norm_num [sevenNineRadial, sevenNineRadialBounds]) h00 h01 h10 h11
  have hcos : (sevenNineCosUpper[0]! : ℝ) ≤ Real.cos ((146782806586930821740 : ℝ) / 100000000000000000000) := by
    apply lower_bound_of_taylor_error
      (cosine_taylor_ninety_six_remainder (a := 0) (b := 4) (x := ((146782806586930821740 : ℝ) / 100000000000000000000) )
        (by norm_num) (by constructor <;> norm_num [Real.pi_gt_d20, Real.pi_lt_four]))
    rw [cosine_taylor_ninety_six_at_zero (b := 4) (x := ((146782806586930821740 : ℝ) / 100000000000000000000)) (by norm_num)]
    have hp : (sevenNineCosUpper[0]! : Rat) + (((146782806586930821740 : Rat) / 100000000000000000000) : Rat)^97 / (Nat.factorial 96) ≤
        Finset.sum (Finset.range 49) (fun k => (-1 : Rat)^k * (((146782806586930821740 : Rat) / 100000000000000000000) : Rat)^(2*k) / Nat.factorial (2*k)) := by native_decide
    have hpR : (sevenNineCosUpper[0]! : ℝ) + ((146782806586930821740 : ℝ) / 100000000000000000000)^97 / (Nat.factorial 96) ≤
        Finset.sum (Finset.range 49) (fun k => (-1 : ℝ)^k * ((146782806586930821740 : ℝ) / 100000000000000000000)^(2*k) / Nat.factorial (2*k)) := by
      norm_num [sevenNineCosUpper, Finset.sum_range_succ]
    simpa [sub_zero] using hpR
  have hangle : ((146782806586930821740 : ℝ) / 100000000000000000000) ≤ Real.arccos (touchCosine a b (Real.sqrt 4 + Real.sqrt 5)) := by
    exact angle_lower_bound_of_cosine (by norm_num)
      (by
        calc
          ((146782806586930821740 : ℝ) / 100000000000000000000) ≤ (314159265358979323846 : ℝ) / 100000000000000000000 := by norm_num
          _ ≤ Real.pi := by
            have hpi := Real.pi_gt_d20.le
            norm_num at hpi ⊢
            exact hpi) (le_trans htouch hcos)
  have hdata : sevenNineAngleLower[0]! = ((146782806586930821740 : Rat) / 100000000000000000000) := by native_decide
  have hdataR : (sevenNineAngleLower[0]! : ℝ) = ((146782806586930821740 : ℝ) / 100000000000000000000) := by
    have h := congrArg (fun q : Rat => (q : ℝ)) hdata
    convert h using 1 ; norm_num
  rw [hdataR]
  exact hangle

theorem sevenNineAngle_0_1_1_1 {a b : ℝ}
    (haL : (sevenNineRadial 0 1 0 : ℝ) ≤ a) (haU : a ≤ (sevenNineRadial 0 1 1 : ℝ))
    (hbL : (sevenNineRadial 1 1 0 : ℝ) ≤ b) (hbU : b ≤ (sevenNineRadial 1 1 1 : ℝ)) :
    (sevenNineAngleLower[3]! : ℝ) ≤ Real.arccos (touchCosine a b (Real.sqrt 4 + Real.sqrt 5)) := by
  let d : ℝ := Real.sqrt 4 + Real.sqrt 5
  have hd' : (((4236067977499789696409173668731276235440618359611525724270897245410520925637804899414414408 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) : ℝ) ≤ d := by
    dsimp [d]
    have h := rat_sum_sqrt_lower (q := ((4236067977499789696409173668731276235440618359611525724270897245410520925637804899414414408 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (qi := ((2 : Rat) / 1)) (qj := ((2236067977499789696409173668731276235440618359611525724270897245410520925637804899414414408378782274969508176150773783504 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))
      (ni := 4) (nj := 5)
      (by convert sqrt_lower_4 using 1 ; norm_num)
      (by convert sqrt_lower_5 using 1 ; norm_num)
      (by native_decide)
    convert h using 1 ; norm_num
  have hd : (((4236067977499789696409173668731276235440618359611525724270897245410520925637804899414414408 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) ≤ d := by exact hd'
  have hd2 : (((4236067977499789696409173668731276235440618359611525724270897245410520925637804899414414408 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))^2 ≤ d^2 := by
    have hq : (0 : ℝ) ≤ ((4236067977499789696409173668731276235440618359611525724270897245410520925637804899414414408 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) := by norm_num
    have hdn : 0 ≤ d := by positivity
    exact (sq_le_sq₀ hq hdn).mpr hd
  have hd2' : (sevenNineDistanceLower[0]! : ℝ)^2 ≤ d^2 := by
    convert hd2 using 1 ; norm_num [sevenNineDistanceLower]
  have h00 : (sevenNineRadial 0 1 0 : ℝ)^2 + (sevenNineRadial 1 1 0 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[3]! : ℝ) * (2 * (sevenNineRadial 0 1 0 : ℝ) * (sevenNineRadial 1 1 0 : ℝ)) := by
    have hq : (sevenNineRadial 0 1 0)^2 + (sevenNineRadial 1 1 0)^2 - sevenNineDistanceLower[0]!^2 ≤
        sevenNineCosUpper[3]! * (2 * sevenNineRadial 0 1 0 * sevenNineRadial 1 1 0) := by native_decide
    have hqR :
        (sevenNineRadial 0 1 0 : ℝ)^2 + (sevenNineRadial 1 1 0 : ℝ)^2 - (sevenNineDistanceLower[0]! : ℝ)^2 ≤
          (sevenNineCosUpper[3]! : ℝ) * (2 * (sevenNineRadial 0 1 0 : ℝ) * (sevenNineRadial 1 1 0 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 0 1 0 : ℝ)^2 + (sevenNineRadial 1 1 0 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 0 1 0 : ℝ)^2 + (sevenNineRadial 1 1 0 : ℝ)^2 - (sevenNineDistanceLower[0]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h01 : (sevenNineRadial 0 1 0 : ℝ)^2 + (sevenNineRadial 1 1 1 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[3]! : ℝ) * (2 * (sevenNineRadial 0 1 0 : ℝ) * (sevenNineRadial 1 1 1 : ℝ)) := by
    have hq : (sevenNineRadial 0 1 0)^2 + (sevenNineRadial 1 1 1)^2 - sevenNineDistanceLower[0]!^2 ≤
        sevenNineCosUpper[3]! * (2 * sevenNineRadial 0 1 0 * sevenNineRadial 1 1 1) := by native_decide
    have hqR :
        (sevenNineRadial 0 1 0 : ℝ)^2 + (sevenNineRadial 1 1 1 : ℝ)^2 - (sevenNineDistanceLower[0]! : ℝ)^2 ≤
          (sevenNineCosUpper[3]! : ℝ) * (2 * (sevenNineRadial 0 1 0 : ℝ) * (sevenNineRadial 1 1 1 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 0 1 0 : ℝ)^2 + (sevenNineRadial 1 1 1 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 0 1 0 : ℝ)^2 + (sevenNineRadial 1 1 1 : ℝ)^2 - (sevenNineDistanceLower[0]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h10 : (sevenNineRadial 0 1 1 : ℝ)^2 + (sevenNineRadial 1 1 0 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[3]! : ℝ) * (2 * (sevenNineRadial 0 1 1 : ℝ) * (sevenNineRadial 1 1 0 : ℝ)) := by
    have hq : (sevenNineRadial 0 1 1)^2 + (sevenNineRadial 1 1 0)^2 - sevenNineDistanceLower[0]!^2 ≤
        sevenNineCosUpper[3]! * (2 * sevenNineRadial 0 1 1 * sevenNineRadial 1 1 0) := by native_decide
    have hqR :
        (sevenNineRadial 0 1 1 : ℝ)^2 + (sevenNineRadial 1 1 0 : ℝ)^2 - (sevenNineDistanceLower[0]! : ℝ)^2 ≤
          (sevenNineCosUpper[3]! : ℝ) * (2 * (sevenNineRadial 0 1 1 : ℝ) * (sevenNineRadial 1 1 0 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 0 1 1 : ℝ)^2 + (sevenNineRadial 1 1 0 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 0 1 1 : ℝ)^2 + (sevenNineRadial 1 1 0 : ℝ)^2 - (sevenNineDistanceLower[0]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h11 : (sevenNineRadial 0 1 1 : ℝ)^2 + (sevenNineRadial 1 1 1 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[3]! : ℝ) * (2 * (sevenNineRadial 0 1 1 : ℝ) * (sevenNineRadial 1 1 1 : ℝ)) := by
    have hq : (sevenNineRadial 0 1 1)^2 + (sevenNineRadial 1 1 1)^2 - sevenNineDistanceLower[0]!^2 ≤
        sevenNineCosUpper[3]! * (2 * sevenNineRadial 0 1 1 * sevenNineRadial 1 1 1) := by native_decide
    have hqR :
        (sevenNineRadial 0 1 1 : ℝ)^2 + (sevenNineRadial 1 1 1 : ℝ)^2 - (sevenNineDistanceLower[0]! : ℝ)^2 ≤
          (sevenNineCosUpper[3]! : ℝ) * (2 * (sevenNineRadial 0 1 1 : ℝ) * (sevenNineRadial 1 1 1 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 0 1 1 : ℝ)^2 + (sevenNineRadial 1 1 1 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 0 1 1 : ℝ)^2 + (sevenNineRadial 1 1 1 : ℝ)^2 - (sevenNineDistanceLower[0]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have htouch := corner_touch_cosine_bound haL haU hbL hbU
    (by norm_num [sevenNineRadial, sevenNineRadialBounds])
    (by norm_num [sevenNineRadial, sevenNineRadialBounds]) h00 h01 h10 h11
  have hcos : (sevenNineCosUpper[3]! : ℝ) ≤ Real.cos ((74903655084147933254 : ℝ) / 100000000000000000000) := by
    apply lower_bound_of_taylor_error
      (cosine_taylor_ninety_six_remainder (a := 0) (b := 4) (x := ((74903655084147933254 : ℝ) / 100000000000000000000) )
        (by norm_num) (by constructor <;> norm_num [Real.pi_gt_d20, Real.pi_lt_four]))
    rw [cosine_taylor_ninety_six_at_zero (b := 4) (x := ((74903655084147933254 : ℝ) / 100000000000000000000)) (by norm_num)]
    have hp : (sevenNineCosUpper[3]! : Rat) + (((74903655084147933254 : Rat) / 100000000000000000000) : Rat)^97 / (Nat.factorial 96) ≤
        Finset.sum (Finset.range 49) (fun k => (-1 : Rat)^k * (((74903655084147933254 : Rat) / 100000000000000000000) : Rat)^(2*k) / Nat.factorial (2*k)) := by native_decide
    have hpR : (sevenNineCosUpper[3]! : ℝ) + ((74903655084147933254 : ℝ) / 100000000000000000000)^97 / (Nat.factorial 96) ≤
        Finset.sum (Finset.range 49) (fun k => (-1 : ℝ)^k * ((74903655084147933254 : ℝ) / 100000000000000000000)^(2*k) / Nat.factorial (2*k)) := by
      norm_num [sevenNineCosUpper, Finset.sum_range_succ]
    simpa [sub_zero] using hpR
  have hangle : ((74903655084147933254 : ℝ) / 100000000000000000000) ≤ Real.arccos (touchCosine a b (Real.sqrt 4 + Real.sqrt 5)) := by
    exact angle_lower_bound_of_cosine (by norm_num)
      (by
        calc
          ((74903655084147933254 : ℝ) / 100000000000000000000) ≤ (314159265358979323846 : ℝ) / 100000000000000000000 := by norm_num
          _ ≤ Real.pi := by
            have hpi := Real.pi_gt_d20.le
            norm_num at hpi ⊢
            exact hpi) (le_trans htouch hcos)
  have hdata : sevenNineAngleLower[3]! = ((74903655084147933254 : Rat) / 100000000000000000000) := by native_decide
  have hdataR : (sevenNineAngleLower[3]! : ℝ) = ((74903655084147933254 : ℝ) / 100000000000000000000) := by
    have h := congrArg (fun q : Rat => (q : ℝ)) hdata
    convert h using 1 ; norm_num
  rw [hdataR]
  exact hangle

theorem sevenNineAngle_0_2_0_0 {a b : ℝ}
    (haL : (sevenNineRadial 0 0 0 : ℝ) ≤ a) (haU : a ≤ (sevenNineRadial 0 0 1 : ℝ))
    (hbL : (sevenNineRadial 2 0 0 : ℝ) ≤ b) (hbU : b ≤ (sevenNineRadial 2 0 1 : ℝ)) :
    (sevenNineAngleLower[4]! : ℝ) ≤ Real.arccos (touchCosine a b (Real.sqrt 4 + Real.sqrt 6)) := by
  let d : ℝ := Real.sqrt 4 + Real.sqrt 6
  have hd' : (((4449489742783178098197284074705891391965947480656670128432692567250960377457315026539859433 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) : ℝ) ≤ d := by
    dsimp [d]
    have h := rat_sum_sqrt_lower (q := ((4449489742783178098197284074705891391965947480656670128432692567250960377457315026539859433 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (qi := ((2 : Rat) / 1)) (qj := ((2449489742783178098197284074705891391965947480656670128432692567250960377457315026539859433104640234818594601226614189124 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))
      (ni := 4) (nj := 6)
      (by convert sqrt_lower_4 using 1 ; norm_num)
      (by convert sqrt_lower_6 using 1 ; norm_num)
      (by native_decide)
    convert h using 1 ; norm_num
  have hd : (((4449489742783178098197284074705891391965947480656670128432692567250960377457315026539859433 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) ≤ d := by exact hd'
  have hd2 : (((4449489742783178098197284074705891391965947480656670128432692567250960377457315026539859433 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))^2 ≤ d^2 := by
    have hq : (0 : ℝ) ≤ ((4449489742783178098197284074705891391965947480656670128432692567250960377457315026539859433 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) := by norm_num
    have hdn : 0 ≤ d := by positivity
    exact (sq_le_sq₀ hq hdn).mpr hd
  have hd2' : (sevenNineDistanceLower[1]! : ℝ)^2 ≤ d^2 := by
    convert hd2 using 1 ; norm_num [sevenNineDistanceLower]
  have h00 : (sevenNineRadial 0 0 0 : ℝ)^2 + (sevenNineRadial 2 0 0 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[4]! : ℝ) * (2 * (sevenNineRadial 0 0 0 : ℝ) * (sevenNineRadial 2 0 0 : ℝ)) := by
    have hq : (sevenNineRadial 0 0 0)^2 + (sevenNineRadial 2 0 0)^2 - sevenNineDistanceLower[1]!^2 ≤
        sevenNineCosUpper[4]! * (2 * sevenNineRadial 0 0 0 * sevenNineRadial 2 0 0) := by native_decide
    have hqR :
        (sevenNineRadial 0 0 0 : ℝ)^2 + (sevenNineRadial 2 0 0 : ℝ)^2 - (sevenNineDistanceLower[1]! : ℝ)^2 ≤
          (sevenNineCosUpper[4]! : ℝ) * (2 * (sevenNineRadial 0 0 0 : ℝ) * (sevenNineRadial 2 0 0 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 0 0 0 : ℝ)^2 + (sevenNineRadial 2 0 0 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 0 0 0 : ℝ)^2 + (sevenNineRadial 2 0 0 : ℝ)^2 - (sevenNineDistanceLower[1]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h01 : (sevenNineRadial 0 0 0 : ℝ)^2 + (sevenNineRadial 2 0 1 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[4]! : ℝ) * (2 * (sevenNineRadial 0 0 0 : ℝ) * (sevenNineRadial 2 0 1 : ℝ)) := by
    have hq : (sevenNineRadial 0 0 0)^2 + (sevenNineRadial 2 0 1)^2 - sevenNineDistanceLower[1]!^2 ≤
        sevenNineCosUpper[4]! * (2 * sevenNineRadial 0 0 0 * sevenNineRadial 2 0 1) := by native_decide
    have hqR :
        (sevenNineRadial 0 0 0 : ℝ)^2 + (sevenNineRadial 2 0 1 : ℝ)^2 - (sevenNineDistanceLower[1]! : ℝ)^2 ≤
          (sevenNineCosUpper[4]! : ℝ) * (2 * (sevenNineRadial 0 0 0 : ℝ) * (sevenNineRadial 2 0 1 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 0 0 0 : ℝ)^2 + (sevenNineRadial 2 0 1 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 0 0 0 : ℝ)^2 + (sevenNineRadial 2 0 1 : ℝ)^2 - (sevenNineDistanceLower[1]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h10 : (sevenNineRadial 0 0 1 : ℝ)^2 + (sevenNineRadial 2 0 0 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[4]! : ℝ) * (2 * (sevenNineRadial 0 0 1 : ℝ) * (sevenNineRadial 2 0 0 : ℝ)) := by
    have hq : (sevenNineRadial 0 0 1)^2 + (sevenNineRadial 2 0 0)^2 - sevenNineDistanceLower[1]!^2 ≤
        sevenNineCosUpper[4]! * (2 * sevenNineRadial 0 0 1 * sevenNineRadial 2 0 0) := by native_decide
    have hqR :
        (sevenNineRadial 0 0 1 : ℝ)^2 + (sevenNineRadial 2 0 0 : ℝ)^2 - (sevenNineDistanceLower[1]! : ℝ)^2 ≤
          (sevenNineCosUpper[4]! : ℝ) * (2 * (sevenNineRadial 0 0 1 : ℝ) * (sevenNineRadial 2 0 0 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 0 0 1 : ℝ)^2 + (sevenNineRadial 2 0 0 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 0 0 1 : ℝ)^2 + (sevenNineRadial 2 0 0 : ℝ)^2 - (sevenNineDistanceLower[1]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h11 : (sevenNineRadial 0 0 1 : ℝ)^2 + (sevenNineRadial 2 0 1 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[4]! : ℝ) * (2 * (sevenNineRadial 0 0 1 : ℝ) * (sevenNineRadial 2 0 1 : ℝ)) := by
    have hq : (sevenNineRadial 0 0 1)^2 + (sevenNineRadial 2 0 1)^2 - sevenNineDistanceLower[1]!^2 ≤
        sevenNineCosUpper[4]! * (2 * sevenNineRadial 0 0 1 * sevenNineRadial 2 0 1) := by native_decide
    have hqR :
        (sevenNineRadial 0 0 1 : ℝ)^2 + (sevenNineRadial 2 0 1 : ℝ)^2 - (sevenNineDistanceLower[1]! : ℝ)^2 ≤
          (sevenNineCosUpper[4]! : ℝ) * (2 * (sevenNineRadial 0 0 1 : ℝ) * (sevenNineRadial 2 0 1 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 0 0 1 : ℝ)^2 + (sevenNineRadial 2 0 1 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 0 0 1 : ℝ)^2 + (sevenNineRadial 2 0 1 : ℝ)^2 - (sevenNineDistanceLower[1]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have htouch := corner_touch_cosine_bound haL haU hbL hbU
    (by norm_num [sevenNineRadial, sevenNineRadialBounds])
    (by norm_num [sevenNineRadial, sevenNineRadialBounds]) h00 h01 h10 h11
  have hcos : (sevenNineCosUpper[4]! : ℝ) ≤ Real.cos ((156069410352215271952 : ℝ) / 100000000000000000000) := by
    apply lower_bound_of_taylor_error
      (cosine_taylor_ninety_six_remainder (a := 0) (b := 4) (x := ((156069410352215271952 : ℝ) / 100000000000000000000) )
        (by norm_num) (by constructor <;> norm_num [Real.pi_gt_d20, Real.pi_lt_four]))
    rw [cosine_taylor_ninety_six_at_zero (b := 4) (x := ((156069410352215271952 : ℝ) / 100000000000000000000)) (by norm_num)]
    have hp : (sevenNineCosUpper[4]! : Rat) + (((156069410352215271952 : Rat) / 100000000000000000000) : Rat)^97 / (Nat.factorial 96) ≤
        Finset.sum (Finset.range 49) (fun k => (-1 : Rat)^k * (((156069410352215271952 : Rat) / 100000000000000000000) : Rat)^(2*k) / Nat.factorial (2*k)) := by native_decide
    have hpR : (sevenNineCosUpper[4]! : ℝ) + ((156069410352215271952 : ℝ) / 100000000000000000000)^97 / (Nat.factorial 96) ≤
        Finset.sum (Finset.range 49) (fun k => (-1 : ℝ)^k * ((156069410352215271952 : ℝ) / 100000000000000000000)^(2*k) / Nat.factorial (2*k)) := by
      norm_num [sevenNineCosUpper, Finset.sum_range_succ]
    simpa [sub_zero] using hpR
  have hangle : ((156069410352215271952 : ℝ) / 100000000000000000000) ≤ Real.arccos (touchCosine a b (Real.sqrt 4 + Real.sqrt 6)) := by
    exact angle_lower_bound_of_cosine (by norm_num)
      (by
        calc
          ((156069410352215271952 : ℝ) / 100000000000000000000) ≤ (314159265358979323846 : ℝ) / 100000000000000000000 := by norm_num
          _ ≤ Real.pi := by
            have hpi := Real.pi_gt_d20.le
            norm_num at hpi ⊢
            exact hpi) (le_trans htouch hcos)
  have hdata : sevenNineAngleLower[4]! = ((156069410352215271952 : Rat) / 100000000000000000000) := by native_decide
  have hdataR : (sevenNineAngleLower[4]! : ℝ) = ((156069410352215271952 : ℝ) / 100000000000000000000) := by
    have h := congrArg (fun q : Rat => (q : ℝ)) hdata
    convert h using 1 ; norm_num
  rw [hdataR]
  exact hangle

theorem sevenNineAngle_0_2_1_1 {a b : ℝ}
    (haL : (sevenNineRadial 0 1 0 : ℝ) ≤ a) (haU : a ≤ (sevenNineRadial 0 1 1 : ℝ))
    (hbL : (sevenNineRadial 2 1 0 : ℝ) ≤ b) (hbU : b ≤ (sevenNineRadial 2 1 1 : ℝ)) :
    (sevenNineAngleLower[7]! : ℝ) ≤ Real.arccos (touchCosine a b (Real.sqrt 4 + Real.sqrt 6)) := by
  let d : ℝ := Real.sqrt 4 + Real.sqrt 6
  have hd' : (((4449489742783178098197284074705891391965947480656670128432692567250960377457315026539859433 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) : ℝ) ≤ d := by
    dsimp [d]
    have h := rat_sum_sqrt_lower (q := ((4449489742783178098197284074705891391965947480656670128432692567250960377457315026539859433 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (qi := ((2 : Rat) / 1)) (qj := ((2449489742783178098197284074705891391965947480656670128432692567250960377457315026539859433104640234818594601226614189124 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))
      (ni := 4) (nj := 6)
      (by convert sqrt_lower_4 using 1 ; norm_num)
      (by convert sqrt_lower_6 using 1 ; norm_num)
      (by native_decide)
    convert h using 1 ; norm_num
  have hd : (((4449489742783178098197284074705891391965947480656670128432692567250960377457315026539859433 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) ≤ d := by exact hd'
  have hd2 : (((4449489742783178098197284074705891391965947480656670128432692567250960377457315026539859433 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))^2 ≤ d^2 := by
    have hq : (0 : ℝ) ≤ ((4449489742783178098197284074705891391965947480656670128432692567250960377457315026539859433 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) := by norm_num
    have hdn : 0 ≤ d := by positivity
    exact (sq_le_sq₀ hq hdn).mpr hd
  have hd2' : (sevenNineDistanceLower[1]! : ℝ)^2 ≤ d^2 := by
    convert hd2 using 1 ; norm_num [sevenNineDistanceLower]
  have h00 : (sevenNineRadial 0 1 0 : ℝ)^2 + (sevenNineRadial 2 1 0 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[7]! : ℝ) * (2 * (sevenNineRadial 0 1 0 : ℝ) * (sevenNineRadial 2 1 0 : ℝ)) := by
    have hq : (sevenNineRadial 0 1 0)^2 + (sevenNineRadial 2 1 0)^2 - sevenNineDistanceLower[1]!^2 ≤
        sevenNineCosUpper[7]! * (2 * sevenNineRadial 0 1 0 * sevenNineRadial 2 1 0) := by native_decide
    have hqR :
        (sevenNineRadial 0 1 0 : ℝ)^2 + (sevenNineRadial 2 1 0 : ℝ)^2 - (sevenNineDistanceLower[1]! : ℝ)^2 ≤
          (sevenNineCosUpper[7]! : ℝ) * (2 * (sevenNineRadial 0 1 0 : ℝ) * (sevenNineRadial 2 1 0 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 0 1 0 : ℝ)^2 + (sevenNineRadial 2 1 0 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 0 1 0 : ℝ)^2 + (sevenNineRadial 2 1 0 : ℝ)^2 - (sevenNineDistanceLower[1]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h01 : (sevenNineRadial 0 1 0 : ℝ)^2 + (sevenNineRadial 2 1 1 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[7]! : ℝ) * (2 * (sevenNineRadial 0 1 0 : ℝ) * (sevenNineRadial 2 1 1 : ℝ)) := by
    have hq : (sevenNineRadial 0 1 0)^2 + (sevenNineRadial 2 1 1)^2 - sevenNineDistanceLower[1]!^2 ≤
        sevenNineCosUpper[7]! * (2 * sevenNineRadial 0 1 0 * sevenNineRadial 2 1 1) := by native_decide
    have hqR :
        (sevenNineRadial 0 1 0 : ℝ)^2 + (sevenNineRadial 2 1 1 : ℝ)^2 - (sevenNineDistanceLower[1]! : ℝ)^2 ≤
          (sevenNineCosUpper[7]! : ℝ) * (2 * (sevenNineRadial 0 1 0 : ℝ) * (sevenNineRadial 2 1 1 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 0 1 0 : ℝ)^2 + (sevenNineRadial 2 1 1 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 0 1 0 : ℝ)^2 + (sevenNineRadial 2 1 1 : ℝ)^2 - (sevenNineDistanceLower[1]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h10 : (sevenNineRadial 0 1 1 : ℝ)^2 + (sevenNineRadial 2 1 0 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[7]! : ℝ) * (2 * (sevenNineRadial 0 1 1 : ℝ) * (sevenNineRadial 2 1 0 : ℝ)) := by
    have hq : (sevenNineRadial 0 1 1)^2 + (sevenNineRadial 2 1 0)^2 - sevenNineDistanceLower[1]!^2 ≤
        sevenNineCosUpper[7]! * (2 * sevenNineRadial 0 1 1 * sevenNineRadial 2 1 0) := by native_decide
    have hqR :
        (sevenNineRadial 0 1 1 : ℝ)^2 + (sevenNineRadial 2 1 0 : ℝ)^2 - (sevenNineDistanceLower[1]! : ℝ)^2 ≤
          (sevenNineCosUpper[7]! : ℝ) * (2 * (sevenNineRadial 0 1 1 : ℝ) * (sevenNineRadial 2 1 0 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 0 1 1 : ℝ)^2 + (sevenNineRadial 2 1 0 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 0 1 1 : ℝ)^2 + (sevenNineRadial 2 1 0 : ℝ)^2 - (sevenNineDistanceLower[1]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h11 : (sevenNineRadial 0 1 1 : ℝ)^2 + (sevenNineRadial 2 1 1 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[7]! : ℝ) * (2 * (sevenNineRadial 0 1 1 : ℝ) * (sevenNineRadial 2 1 1 : ℝ)) := by
    have hq : (sevenNineRadial 0 1 1)^2 + (sevenNineRadial 2 1 1)^2 - sevenNineDistanceLower[1]!^2 ≤
        sevenNineCosUpper[7]! * (2 * sevenNineRadial 0 1 1 * sevenNineRadial 2 1 1) := by native_decide
    have hqR :
        (sevenNineRadial 0 1 1 : ℝ)^2 + (sevenNineRadial 2 1 1 : ℝ)^2 - (sevenNineDistanceLower[1]! : ℝ)^2 ≤
          (sevenNineCosUpper[7]! : ℝ) * (2 * (sevenNineRadial 0 1 1 : ℝ) * (sevenNineRadial 2 1 1 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 0 1 1 : ℝ)^2 + (sevenNineRadial 2 1 1 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 0 1 1 : ℝ)^2 + (sevenNineRadial 2 1 1 : ℝ)^2 - (sevenNineDistanceLower[1]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have htouch := corner_touch_cosine_bound haL haU hbL hbU
    (by norm_num [sevenNineRadial, sevenNineRadialBounds])
    (by norm_num [sevenNineRadial, sevenNineRadialBounds]) h00 h01 h10 h11
  have hcos : (sevenNineCosUpper[7]! : ℝ) ≤ Real.cos ((80193371076413932841 : ℝ) / 100000000000000000000) := by
    apply lower_bound_of_taylor_error
      (cosine_taylor_ninety_six_remainder (a := 0) (b := 4) (x := ((80193371076413932841 : ℝ) / 100000000000000000000) )
        (by norm_num) (by constructor <;> norm_num [Real.pi_gt_d20, Real.pi_lt_four]))
    rw [cosine_taylor_ninety_six_at_zero (b := 4) (x := ((80193371076413932841 : ℝ) / 100000000000000000000)) (by norm_num)]
    have hp : (sevenNineCosUpper[7]! : Rat) + (((80193371076413932841 : Rat) / 100000000000000000000) : Rat)^97 / (Nat.factorial 96) ≤
        Finset.sum (Finset.range 49) (fun k => (-1 : Rat)^k * (((80193371076413932841 : Rat) / 100000000000000000000) : Rat)^(2*k) / Nat.factorial (2*k)) := by native_decide
    have hpR : (sevenNineCosUpper[7]! : ℝ) + ((80193371076413932841 : ℝ) / 100000000000000000000)^97 / (Nat.factorial 96) ≤
        Finset.sum (Finset.range 49) (fun k => (-1 : ℝ)^k * ((80193371076413932841 : ℝ) / 100000000000000000000)^(2*k) / Nat.factorial (2*k)) := by
      norm_num [sevenNineCosUpper, Finset.sum_range_succ]
    simpa [sub_zero] using hpR
  have hangle : ((80193371076413932841 : ℝ) / 100000000000000000000) ≤ Real.arccos (touchCosine a b (Real.sqrt 4 + Real.sqrt 6)) := by
    exact angle_lower_bound_of_cosine (by norm_num)
      (by
        calc
          ((80193371076413932841 : ℝ) / 100000000000000000000) ≤ (314159265358979323846 : ℝ) / 100000000000000000000 := by norm_num
          _ ≤ Real.pi := by
            have hpi := Real.pi_gt_d20.le
            norm_num at hpi ⊢
            exact hpi) (le_trans htouch hcos)
  have hdata : sevenNineAngleLower[7]! = ((80193371076413932841 : Rat) / 100000000000000000000) := by native_decide
  have hdataR : (sevenNineAngleLower[7]! : ℝ) = ((80193371076413932841 : ℝ) / 100000000000000000000) := by
    have h := congrArg (fun q : Rat => (q : ℝ)) hdata
    convert h using 1 ; norm_num
  rw [hdataR]
  exact hangle

theorem sevenNineAngle_0_3_0_0 {a b : ℝ}
    (haL : (sevenNineRadial 0 0 0 : ℝ) ≤ a) (haU : a ≤ (sevenNineRadial 0 0 1 : ℝ))
    (hbL : (sevenNineRadial 3 0 0 : ℝ) ≤ b) (hbU : b ≤ (sevenNineRadial 3 0 1 : ℝ)) :
    (sevenNineAngleLower[8]! : ℝ) ≤ Real.arccos (touchCosine a b (Real.sqrt 4 + Real.sqrt 7)) := by
  let d : ℝ := Real.sqrt 4 + Real.sqrt 7
  have hd' : (((4645751311064590590501615753639260425710259183082450180368334459201068823230283627760392886 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) : ℝ) ≤ d := by
    dsimp [d]
    have h := rat_sum_sqrt_lower (q := ((4645751311064590590501615753639260425710259183082450180368334459201068823230283627760392886 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (qi := ((2 : Rat) / 1)) (qj := ((2645751311064590590501615753639260425710259183082450180368334459201068823230283627760392886474543610615064578338497463095 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))
      (ni := 4) (nj := 7)
      (by convert sqrt_lower_4 using 1 ; norm_num)
      (by convert sqrt_lower_7 using 1 ; norm_num)
      (by native_decide)
    convert h using 1 ; norm_num
  have hd : (((4645751311064590590501615753639260425710259183082450180368334459201068823230283627760392886 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) ≤ d := by exact hd'
  have hd2 : (((4645751311064590590501615753639260425710259183082450180368334459201068823230283627760392886 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))^2 ≤ d^2 := by
    have hq : (0 : ℝ) ≤ ((4645751311064590590501615753639260425710259183082450180368334459201068823230283627760392886 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) := by norm_num
    have hdn : 0 ≤ d := by positivity
    exact (sq_le_sq₀ hq hdn).mpr hd
  have hd2' : (sevenNineDistanceLower[2]! : ℝ)^2 ≤ d^2 := by
    convert hd2 using 1 ; norm_num [sevenNineDistanceLower]
  have h00 : (sevenNineRadial 0 0 0 : ℝ)^2 + (sevenNineRadial 3 0 0 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[8]! : ℝ) * (2 * (sevenNineRadial 0 0 0 : ℝ) * (sevenNineRadial 3 0 0 : ℝ)) := by
    have hq : (sevenNineRadial 0 0 0)^2 + (sevenNineRadial 3 0 0)^2 - sevenNineDistanceLower[2]!^2 ≤
        sevenNineCosUpper[8]! * (2 * sevenNineRadial 0 0 0 * sevenNineRadial 3 0 0) := by native_decide
    have hqR :
        (sevenNineRadial 0 0 0 : ℝ)^2 + (sevenNineRadial 3 0 0 : ℝ)^2 - (sevenNineDistanceLower[2]! : ℝ)^2 ≤
          (sevenNineCosUpper[8]! : ℝ) * (2 * (sevenNineRadial 0 0 0 : ℝ) * (sevenNineRadial 3 0 0 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 0 0 0 : ℝ)^2 + (sevenNineRadial 3 0 0 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 0 0 0 : ℝ)^2 + (sevenNineRadial 3 0 0 : ℝ)^2 - (sevenNineDistanceLower[2]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h01 : (sevenNineRadial 0 0 0 : ℝ)^2 + (sevenNineRadial 3 0 1 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[8]! : ℝ) * (2 * (sevenNineRadial 0 0 0 : ℝ) * (sevenNineRadial 3 0 1 : ℝ)) := by
    have hq : (sevenNineRadial 0 0 0)^2 + (sevenNineRadial 3 0 1)^2 - sevenNineDistanceLower[2]!^2 ≤
        sevenNineCosUpper[8]! * (2 * sevenNineRadial 0 0 0 * sevenNineRadial 3 0 1) := by native_decide
    have hqR :
        (sevenNineRadial 0 0 0 : ℝ)^2 + (sevenNineRadial 3 0 1 : ℝ)^2 - (sevenNineDistanceLower[2]! : ℝ)^2 ≤
          (sevenNineCosUpper[8]! : ℝ) * (2 * (sevenNineRadial 0 0 0 : ℝ) * (sevenNineRadial 3 0 1 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 0 0 0 : ℝ)^2 + (sevenNineRadial 3 0 1 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 0 0 0 : ℝ)^2 + (sevenNineRadial 3 0 1 : ℝ)^2 - (sevenNineDistanceLower[2]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h10 : (sevenNineRadial 0 0 1 : ℝ)^2 + (sevenNineRadial 3 0 0 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[8]! : ℝ) * (2 * (sevenNineRadial 0 0 1 : ℝ) * (sevenNineRadial 3 0 0 : ℝ)) := by
    have hq : (sevenNineRadial 0 0 1)^2 + (sevenNineRadial 3 0 0)^2 - sevenNineDistanceLower[2]!^2 ≤
        sevenNineCosUpper[8]! * (2 * sevenNineRadial 0 0 1 * sevenNineRadial 3 0 0) := by native_decide
    have hqR :
        (sevenNineRadial 0 0 1 : ℝ)^2 + (sevenNineRadial 3 0 0 : ℝ)^2 - (sevenNineDistanceLower[2]! : ℝ)^2 ≤
          (sevenNineCosUpper[8]! : ℝ) * (2 * (sevenNineRadial 0 0 1 : ℝ) * (sevenNineRadial 3 0 0 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 0 0 1 : ℝ)^2 + (sevenNineRadial 3 0 0 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 0 0 1 : ℝ)^2 + (sevenNineRadial 3 0 0 : ℝ)^2 - (sevenNineDistanceLower[2]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h11 : (sevenNineRadial 0 0 1 : ℝ)^2 + (sevenNineRadial 3 0 1 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[8]! : ℝ) * (2 * (sevenNineRadial 0 0 1 : ℝ) * (sevenNineRadial 3 0 1 : ℝ)) := by
    have hq : (sevenNineRadial 0 0 1)^2 + (sevenNineRadial 3 0 1)^2 - sevenNineDistanceLower[2]!^2 ≤
        sevenNineCosUpper[8]! * (2 * sevenNineRadial 0 0 1 * sevenNineRadial 3 0 1) := by native_decide
    have hqR :
        (sevenNineRadial 0 0 1 : ℝ)^2 + (sevenNineRadial 3 0 1 : ℝ)^2 - (sevenNineDistanceLower[2]! : ℝ)^2 ≤
          (sevenNineCosUpper[8]! : ℝ) * (2 * (sevenNineRadial 0 0 1 : ℝ) * (sevenNineRadial 3 0 1 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 0 0 1 : ℝ)^2 + (sevenNineRadial 3 0 1 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 0 0 1 : ℝ)^2 + (sevenNineRadial 3 0 1 : ℝ)^2 - (sevenNineDistanceLower[2]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have htouch := corner_touch_cosine_bound haL haU hbL hbU
    (by norm_num [sevenNineRadial, sevenNineRadialBounds])
    (by norm_num [sevenNineRadial, sevenNineRadialBounds]) h00 h01 h10 h11
  have hcos : (sevenNineCosUpper[8]! : ℝ) ≤ Real.cos ((165002946581502784360 : ℝ) / 100000000000000000000) := by
    apply lower_bound_of_taylor_error
      (cosine_taylor_ninety_six_remainder (a := 0) (b := 4) (x := ((165002946581502784360 : ℝ) / 100000000000000000000) )
        (by norm_num) (by constructor <;> norm_num [Real.pi_gt_d20, Real.pi_lt_four]))
    rw [cosine_taylor_ninety_six_at_zero (b := 4) (x := ((165002946581502784360 : ℝ) / 100000000000000000000)) (by norm_num)]
    have hp : (sevenNineCosUpper[8]! : Rat) + (((165002946581502784360 : Rat) / 100000000000000000000) : Rat)^97 / (Nat.factorial 96) ≤
        Finset.sum (Finset.range 49) (fun k => (-1 : Rat)^k * (((165002946581502784360 : Rat) / 100000000000000000000) : Rat)^(2*k) / Nat.factorial (2*k)) := by native_decide
    have hpR : (sevenNineCosUpper[8]! : ℝ) + ((165002946581502784360 : ℝ) / 100000000000000000000)^97 / (Nat.factorial 96) ≤
        Finset.sum (Finset.range 49) (fun k => (-1 : ℝ)^k * ((165002946581502784360 : ℝ) / 100000000000000000000)^(2*k) / Nat.factorial (2*k)) := by
      norm_num [sevenNineCosUpper, Finset.sum_range_succ]
    simpa [sub_zero] using hpR
  have hangle : ((165002946581502784360 : ℝ) / 100000000000000000000) ≤ Real.arccos (touchCosine a b (Real.sqrt 4 + Real.sqrt 7)) := by
    exact angle_lower_bound_of_cosine (by norm_num)
      (by
        calc
          ((165002946581502784360 : ℝ) / 100000000000000000000) ≤ (314159265358979323846 : ℝ) / 100000000000000000000 := by norm_num
          _ ≤ Real.pi := by
            have hpi := Real.pi_gt_d20.le
            norm_num at hpi ⊢
            exact hpi) (le_trans htouch hcos)
  have hdata : sevenNineAngleLower[8]! = ((165002946581502784360 : Rat) / 100000000000000000000) := by native_decide
  have hdataR : (sevenNineAngleLower[8]! : ℝ) = ((165002946581502784360 : ℝ) / 100000000000000000000) := by
    have h := congrArg (fun q : Rat => (q : ℝ)) hdata
    convert h using 1 ; norm_num
  rw [hdataR]
  exact hangle

theorem sevenNineAngle_0_3_1_1 {a b : ℝ}
    (haL : (sevenNineRadial 0 1 0 : ℝ) ≤ a) (haU : a ≤ (sevenNineRadial 0 1 1 : ℝ))
    (hbL : (sevenNineRadial 3 1 0 : ℝ) ≤ b) (hbU : b ≤ (sevenNineRadial 3 1 1 : ℝ)) :
    (sevenNineAngleLower[11]! : ℝ) ≤ Real.arccos (touchCosine a b (Real.sqrt 4 + Real.sqrt 7)) := by
  let d : ℝ := Real.sqrt 4 + Real.sqrt 7
  have hd' : (((4645751311064590590501615753639260425710259183082450180368334459201068823230283627760392886 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) : ℝ) ≤ d := by
    dsimp [d]
    have h := rat_sum_sqrt_lower (q := ((4645751311064590590501615753639260425710259183082450180368334459201068823230283627760392886 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (qi := ((2 : Rat) / 1)) (qj := ((2645751311064590590501615753639260425710259183082450180368334459201068823230283627760392886474543610615064578338497463095 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))
      (ni := 4) (nj := 7)
      (by convert sqrt_lower_4 using 1 ; norm_num)
      (by convert sqrt_lower_7 using 1 ; norm_num)
      (by native_decide)
    convert h using 1 ; norm_num
  have hd : (((4645751311064590590501615753639260425710259183082450180368334459201068823230283627760392886 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) ≤ d := by exact hd'
  have hd2 : (((4645751311064590590501615753639260425710259183082450180368334459201068823230283627760392886 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))^2 ≤ d^2 := by
    have hq : (0 : ℝ) ≤ ((4645751311064590590501615753639260425710259183082450180368334459201068823230283627760392886 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) := by norm_num
    have hdn : 0 ≤ d := by positivity
    exact (sq_le_sq₀ hq hdn).mpr hd
  have hd2' : (sevenNineDistanceLower[2]! : ℝ)^2 ≤ d^2 := by
    convert hd2 using 1 ; norm_num [sevenNineDistanceLower]
  have h00 : (sevenNineRadial 0 1 0 : ℝ)^2 + (sevenNineRadial 3 1 0 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[11]! : ℝ) * (2 * (sevenNineRadial 0 1 0 : ℝ) * (sevenNineRadial 3 1 0 : ℝ)) := by
    have hq : (sevenNineRadial 0 1 0)^2 + (sevenNineRadial 3 1 0)^2 - sevenNineDistanceLower[2]!^2 ≤
        sevenNineCosUpper[11]! * (2 * sevenNineRadial 0 1 0 * sevenNineRadial 3 1 0) := by native_decide
    have hqR :
        (sevenNineRadial 0 1 0 : ℝ)^2 + (sevenNineRadial 3 1 0 : ℝ)^2 - (sevenNineDistanceLower[2]! : ℝ)^2 ≤
          (sevenNineCosUpper[11]! : ℝ) * (2 * (sevenNineRadial 0 1 0 : ℝ) * (sevenNineRadial 3 1 0 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 0 1 0 : ℝ)^2 + (sevenNineRadial 3 1 0 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 0 1 0 : ℝ)^2 + (sevenNineRadial 3 1 0 : ℝ)^2 - (sevenNineDistanceLower[2]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h01 : (sevenNineRadial 0 1 0 : ℝ)^2 + (sevenNineRadial 3 1 1 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[11]! : ℝ) * (2 * (sevenNineRadial 0 1 0 : ℝ) * (sevenNineRadial 3 1 1 : ℝ)) := by
    have hq : (sevenNineRadial 0 1 0)^2 + (sevenNineRadial 3 1 1)^2 - sevenNineDistanceLower[2]!^2 ≤
        sevenNineCosUpper[11]! * (2 * sevenNineRadial 0 1 0 * sevenNineRadial 3 1 1) := by native_decide
    have hqR :
        (sevenNineRadial 0 1 0 : ℝ)^2 + (sevenNineRadial 3 1 1 : ℝ)^2 - (sevenNineDistanceLower[2]! : ℝ)^2 ≤
          (sevenNineCosUpper[11]! : ℝ) * (2 * (sevenNineRadial 0 1 0 : ℝ) * (sevenNineRadial 3 1 1 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 0 1 0 : ℝ)^2 + (sevenNineRadial 3 1 1 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 0 1 0 : ℝ)^2 + (sevenNineRadial 3 1 1 : ℝ)^2 - (sevenNineDistanceLower[2]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h10 : (sevenNineRadial 0 1 1 : ℝ)^2 + (sevenNineRadial 3 1 0 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[11]! : ℝ) * (2 * (sevenNineRadial 0 1 1 : ℝ) * (sevenNineRadial 3 1 0 : ℝ)) := by
    have hq : (sevenNineRadial 0 1 1)^2 + (sevenNineRadial 3 1 0)^2 - sevenNineDistanceLower[2]!^2 ≤
        sevenNineCosUpper[11]! * (2 * sevenNineRadial 0 1 1 * sevenNineRadial 3 1 0) := by native_decide
    have hqR :
        (sevenNineRadial 0 1 1 : ℝ)^2 + (sevenNineRadial 3 1 0 : ℝ)^2 - (sevenNineDistanceLower[2]! : ℝ)^2 ≤
          (sevenNineCosUpper[11]! : ℝ) * (2 * (sevenNineRadial 0 1 1 : ℝ) * (sevenNineRadial 3 1 0 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 0 1 1 : ℝ)^2 + (sevenNineRadial 3 1 0 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 0 1 1 : ℝ)^2 + (sevenNineRadial 3 1 0 : ℝ)^2 - (sevenNineDistanceLower[2]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h11 : (sevenNineRadial 0 1 1 : ℝ)^2 + (sevenNineRadial 3 1 1 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[11]! : ℝ) * (2 * (sevenNineRadial 0 1 1 : ℝ) * (sevenNineRadial 3 1 1 : ℝ)) := by
    have hq : (sevenNineRadial 0 1 1)^2 + (sevenNineRadial 3 1 1)^2 - sevenNineDistanceLower[2]!^2 ≤
        sevenNineCosUpper[11]! * (2 * sevenNineRadial 0 1 1 * sevenNineRadial 3 1 1) := by native_decide
    have hqR :
        (sevenNineRadial 0 1 1 : ℝ)^2 + (sevenNineRadial 3 1 1 : ℝ)^2 - (sevenNineDistanceLower[2]! : ℝ)^2 ≤
          (sevenNineCosUpper[11]! : ℝ) * (2 * (sevenNineRadial 0 1 1 : ℝ) * (sevenNineRadial 3 1 1 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 0 1 1 : ℝ)^2 + (sevenNineRadial 3 1 1 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 0 1 1 : ℝ)^2 + (sevenNineRadial 3 1 1 : ℝ)^2 - (sevenNineDistanceLower[2]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have htouch := corner_touch_cosine_bound haL haU hbL hbU
    (by norm_num [sevenNineRadial, sevenNineRadialBounds])
    (by norm_num [sevenNineRadial, sevenNineRadialBounds]) h00 h01 h10 h11
  have hcos : (sevenNineCosUpper[11]! : ℝ) ≤ Real.cos ((85182165908789975115 : ℝ) / 100000000000000000000) := by
    apply lower_bound_of_taylor_error
      (cosine_taylor_ninety_six_remainder (a := 0) (b := 4) (x := ((85182165908789975115 : ℝ) / 100000000000000000000) )
        (by norm_num) (by constructor <;> norm_num [Real.pi_gt_d20, Real.pi_lt_four]))
    rw [cosine_taylor_ninety_six_at_zero (b := 4) (x := ((85182165908789975115 : ℝ) / 100000000000000000000)) (by norm_num)]
    have hp : (sevenNineCosUpper[11]! : Rat) + (((85182165908789975115 : Rat) / 100000000000000000000) : Rat)^97 / (Nat.factorial 96) ≤
        Finset.sum (Finset.range 49) (fun k => (-1 : Rat)^k * (((85182165908789975115 : Rat) / 100000000000000000000) : Rat)^(2*k) / Nat.factorial (2*k)) := by native_decide
    have hpR : (sevenNineCosUpper[11]! : ℝ) + ((85182165908789975115 : ℝ) / 100000000000000000000)^97 / (Nat.factorial 96) ≤
        Finset.sum (Finset.range 49) (fun k => (-1 : ℝ)^k * ((85182165908789975115 : ℝ) / 100000000000000000000)^(2*k) / Nat.factorial (2*k)) := by
      norm_num [sevenNineCosUpper, Finset.sum_range_succ]
    simpa [sub_zero] using hpR
  have hangle : ((85182165908789975115 : ℝ) / 100000000000000000000) ≤ Real.arccos (touchCosine a b (Real.sqrt 4 + Real.sqrt 7)) := by
    exact angle_lower_bound_of_cosine (by norm_num)
      (by
        calc
          ((85182165908789975115 : ℝ) / 100000000000000000000) ≤ (314159265358979323846 : ℝ) / 100000000000000000000 := by norm_num
          _ ≤ Real.pi := by
            have hpi := Real.pi_gt_d20.le
            norm_num at hpi ⊢
            exact hpi) (le_trans htouch hcos)
  have hdata : sevenNineAngleLower[11]! = ((85182165908789975115 : Rat) / 100000000000000000000) := by native_decide
  have hdataR : (sevenNineAngleLower[11]! : ℝ) = ((85182165908789975115 : ℝ) / 100000000000000000000) := by
    have h := congrArg (fun q : Rat => (q : ℝ)) hdata
    convert h using 1 ; norm_num
  rw [hdataR]
  exact hangle

theorem sevenNineAngle_0_4_0_0 {a b : ℝ}
    (haL : (sevenNineRadial 0 0 0 : ℝ) ≤ a) (haU : a ≤ (sevenNineRadial 0 0 1 : ℝ))
    (hbL : (sevenNineRadial 4 0 0 : ℝ) ≤ b) (hbU : b ≤ (sevenNineRadial 4 0 1 : ℝ)) :
    (sevenNineAngleLower[12]! : ℝ) ≤ Real.arccos (touchCosine a b (Real.sqrt 4 + Real.sqrt 8)) := by
  let d : ℝ := Real.sqrt 4 + Real.sqrt 8
  have hd' : (((4828427124746190097603377448419396157139343750753896146353359475981464956924214077700775068 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) : ℝ) ≤ d := by
    dsimp [d]
    have h := rat_sum_sqrt_lower (q := ((4828427124746190097603377448419396157139343750753896146353359475981464956924214077700775068 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (qi := ((2 : Rat) / 1)) (qj := ((2828427124746190097603377448419396157139343750753896146353359475981464956924214077700775068655283145470027692461824594049 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))
      (ni := 4) (nj := 8)
      (by convert sqrt_lower_4 using 1 ; norm_num)
      (by convert sqrt_lower_8 using 1 ; norm_num)
      (by native_decide)
    convert h using 1 ; norm_num
  have hd : (((4828427124746190097603377448419396157139343750753896146353359475981464956924214077700775068 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) ≤ d := by exact hd'
  have hd2 : (((4828427124746190097603377448419396157139343750753896146353359475981464956924214077700775068 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))^2 ≤ d^2 := by
    have hq : (0 : ℝ) ≤ ((4828427124746190097603377448419396157139343750753896146353359475981464956924214077700775068 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) := by norm_num
    have hdn : 0 ≤ d := by positivity
    exact (sq_le_sq₀ hq hdn).mpr hd
  have hd2' : (sevenNineDistanceLower[3]! : ℝ)^2 ≤ d^2 := by
    convert hd2 using 1 ; norm_num [sevenNineDistanceLower]
  have h00 : (sevenNineRadial 0 0 0 : ℝ)^2 + (sevenNineRadial 4 0 0 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[12]! : ℝ) * (2 * (sevenNineRadial 0 0 0 : ℝ) * (sevenNineRadial 4 0 0 : ℝ)) := by
    have hq : (sevenNineRadial 0 0 0)^2 + (sevenNineRadial 4 0 0)^2 - sevenNineDistanceLower[3]!^2 ≤
        sevenNineCosUpper[12]! * (2 * sevenNineRadial 0 0 0 * sevenNineRadial 4 0 0) := by native_decide
    have hqR :
        (sevenNineRadial 0 0 0 : ℝ)^2 + (sevenNineRadial 4 0 0 : ℝ)^2 - (sevenNineDistanceLower[3]! : ℝ)^2 ≤
          (sevenNineCosUpper[12]! : ℝ) * (2 * (sevenNineRadial 0 0 0 : ℝ) * (sevenNineRadial 4 0 0 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 0 0 0 : ℝ)^2 + (sevenNineRadial 4 0 0 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 0 0 0 : ℝ)^2 + (sevenNineRadial 4 0 0 : ℝ)^2 - (sevenNineDistanceLower[3]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h01 : (sevenNineRadial 0 0 0 : ℝ)^2 + (sevenNineRadial 4 0 1 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[12]! : ℝ) * (2 * (sevenNineRadial 0 0 0 : ℝ) * (sevenNineRadial 4 0 1 : ℝ)) := by
    have hq : (sevenNineRadial 0 0 0)^2 + (sevenNineRadial 4 0 1)^2 - sevenNineDistanceLower[3]!^2 ≤
        sevenNineCosUpper[12]! * (2 * sevenNineRadial 0 0 0 * sevenNineRadial 4 0 1) := by native_decide
    have hqR :
        (sevenNineRadial 0 0 0 : ℝ)^2 + (sevenNineRadial 4 0 1 : ℝ)^2 - (sevenNineDistanceLower[3]! : ℝ)^2 ≤
          (sevenNineCosUpper[12]! : ℝ) * (2 * (sevenNineRadial 0 0 0 : ℝ) * (sevenNineRadial 4 0 1 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 0 0 0 : ℝ)^2 + (sevenNineRadial 4 0 1 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 0 0 0 : ℝ)^2 + (sevenNineRadial 4 0 1 : ℝ)^2 - (sevenNineDistanceLower[3]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h10 : (sevenNineRadial 0 0 1 : ℝ)^2 + (sevenNineRadial 4 0 0 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[12]! : ℝ) * (2 * (sevenNineRadial 0 0 1 : ℝ) * (sevenNineRadial 4 0 0 : ℝ)) := by
    have hq : (sevenNineRadial 0 0 1)^2 + (sevenNineRadial 4 0 0)^2 - sevenNineDistanceLower[3]!^2 ≤
        sevenNineCosUpper[12]! * (2 * sevenNineRadial 0 0 1 * sevenNineRadial 4 0 0) := by native_decide
    have hqR :
        (sevenNineRadial 0 0 1 : ℝ)^2 + (sevenNineRadial 4 0 0 : ℝ)^2 - (sevenNineDistanceLower[3]! : ℝ)^2 ≤
          (sevenNineCosUpper[12]! : ℝ) * (2 * (sevenNineRadial 0 0 1 : ℝ) * (sevenNineRadial 4 0 0 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 0 0 1 : ℝ)^2 + (sevenNineRadial 4 0 0 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 0 0 1 : ℝ)^2 + (sevenNineRadial 4 0 0 : ℝ)^2 - (sevenNineDistanceLower[3]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h11 : (sevenNineRadial 0 0 1 : ℝ)^2 + (sevenNineRadial 4 0 1 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[12]! : ℝ) * (2 * (sevenNineRadial 0 0 1 : ℝ) * (sevenNineRadial 4 0 1 : ℝ)) := by
    have hq : (sevenNineRadial 0 0 1)^2 + (sevenNineRadial 4 0 1)^2 - sevenNineDistanceLower[3]!^2 ≤
        sevenNineCosUpper[12]! * (2 * sevenNineRadial 0 0 1 * sevenNineRadial 4 0 1) := by native_decide
    have hqR :
        (sevenNineRadial 0 0 1 : ℝ)^2 + (sevenNineRadial 4 0 1 : ℝ)^2 - (sevenNineDistanceLower[3]! : ℝ)^2 ≤
          (sevenNineCosUpper[12]! : ℝ) * (2 * (sevenNineRadial 0 0 1 : ℝ) * (sevenNineRadial 4 0 1 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 0 0 1 : ℝ)^2 + (sevenNineRadial 4 0 1 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 0 0 1 : ℝ)^2 + (sevenNineRadial 4 0 1 : ℝ)^2 - (sevenNineDistanceLower[3]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have htouch := corner_touch_cosine_bound haL haU hbL hbU
    (by norm_num [sevenNineRadial, sevenNineRadialBounds])
    (by norm_num [sevenNineRadial, sevenNineRadialBounds]) h00 h01 h10 h11
  have hcos : (sevenNineCosUpper[12]! : ℝ) ≤ Real.cos ((173724932880085021011 : ℝ) / 100000000000000000000) := by
    apply lower_bound_of_taylor_error
      (cosine_taylor_ninety_six_remainder (a := 0) (b := 4) (x := ((173724932880085021011 : ℝ) / 100000000000000000000) )
        (by norm_num) (by constructor <;> norm_num [Real.pi_gt_d20, Real.pi_lt_four]))
    rw [cosine_taylor_ninety_six_at_zero (b := 4) (x := ((173724932880085021011 : ℝ) / 100000000000000000000)) (by norm_num)]
    have hp : (sevenNineCosUpper[12]! : Rat) + (((173724932880085021011 : Rat) / 100000000000000000000) : Rat)^97 / (Nat.factorial 96) ≤
        Finset.sum (Finset.range 49) (fun k => (-1 : Rat)^k * (((173724932880085021011 : Rat) / 100000000000000000000) : Rat)^(2*k) / Nat.factorial (2*k)) := by native_decide
    have hpR : (sevenNineCosUpper[12]! : ℝ) + ((173724932880085021011 : ℝ) / 100000000000000000000)^97 / (Nat.factorial 96) ≤
        Finset.sum (Finset.range 49) (fun k => (-1 : ℝ)^k * ((173724932880085021011 : ℝ) / 100000000000000000000)^(2*k) / Nat.factorial (2*k)) := by
      norm_num [sevenNineCosUpper, Finset.sum_range_succ]
    simpa [sub_zero] using hpR
  have hangle : ((173724932880085021011 : ℝ) / 100000000000000000000) ≤ Real.arccos (touchCosine a b (Real.sqrt 4 + Real.sqrt 8)) := by
    exact angle_lower_bound_of_cosine (by norm_num)
      (by
        calc
          ((173724932880085021011 : ℝ) / 100000000000000000000) ≤ (314159265358979323846 : ℝ) / 100000000000000000000 := by norm_num
          _ ≤ Real.pi := by
            have hpi := Real.pi_gt_d20.le
            norm_num at hpi ⊢
            exact hpi) (le_trans htouch hcos)
  have hdata : sevenNineAngleLower[12]! = ((173724932880085021011 : Rat) / 100000000000000000000) := by native_decide
  have hdataR : (sevenNineAngleLower[12]! : ℝ) = ((173724932880085021011 : ℝ) / 100000000000000000000) := by
    have h := congrArg (fun q : Rat => (q : ℝ)) hdata
    convert h using 1 ; norm_num
  rw [hdataR]
  exact hangle

theorem sevenNineAngle_0_4_0_1 {a b : ℝ}
    (haL : (sevenNineRadial 0 0 0 : ℝ) ≤ a) (haU : a ≤ (sevenNineRadial 0 0 1 : ℝ))
    (hbL : (sevenNineRadial 4 1 0 : ℝ) ≤ b) (hbU : b ≤ (sevenNineRadial 4 1 1 : ℝ)) :
    (sevenNineAngleLower[13]! : ℝ) ≤ Real.arccos (touchCosine a b (Real.sqrt 4 + Real.sqrt 8)) := by
  let d : ℝ := Real.sqrt 4 + Real.sqrt 8
  have hd' : (((4828427124746190097603377448419396157139343750753896146353359475981464956924214077700775068 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) : ℝ) ≤ d := by
    dsimp [d]
    have h := rat_sum_sqrt_lower (q := ((4828427124746190097603377448419396157139343750753896146353359475981464956924214077700775068 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (qi := ((2 : Rat) / 1)) (qj := ((2828427124746190097603377448419396157139343750753896146353359475981464956924214077700775068655283145470027692461824594049 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))
      (ni := 4) (nj := 8)
      (by convert sqrt_lower_4 using 1 ; norm_num)
      (by convert sqrt_lower_8 using 1 ; norm_num)
      (by native_decide)
    convert h using 1 ; norm_num
  have hd : (((4828427124746190097603377448419396157139343750753896146353359475981464956924214077700775068 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) ≤ d := by exact hd'
  have hd2 : (((4828427124746190097603377448419396157139343750753896146353359475981464956924214077700775068 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))^2 ≤ d^2 := by
    have hq : (0 : ℝ) ≤ ((4828427124746190097603377448419396157139343750753896146353359475981464956924214077700775068 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) := by norm_num
    have hdn : 0 ≤ d := by positivity
    exact (sq_le_sq₀ hq hdn).mpr hd
  have hd2' : (sevenNineDistanceLower[3]! : ℝ)^2 ≤ d^2 := by
    convert hd2 using 1 ; norm_num [sevenNineDistanceLower]
  have h00 : (sevenNineRadial 0 0 0 : ℝ)^2 + (sevenNineRadial 4 1 0 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[13]! : ℝ) * (2 * (sevenNineRadial 0 0 0 : ℝ) * (sevenNineRadial 4 1 0 : ℝ)) := by
    have hq : (sevenNineRadial 0 0 0)^2 + (sevenNineRadial 4 1 0)^2 - sevenNineDistanceLower[3]!^2 ≤
        sevenNineCosUpper[13]! * (2 * sevenNineRadial 0 0 0 * sevenNineRadial 4 1 0) := by native_decide
    have hqR :
        (sevenNineRadial 0 0 0 : ℝ)^2 + (sevenNineRadial 4 1 0 : ℝ)^2 - (sevenNineDistanceLower[3]! : ℝ)^2 ≤
          (sevenNineCosUpper[13]! : ℝ) * (2 * (sevenNineRadial 0 0 0 : ℝ) * (sevenNineRadial 4 1 0 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 0 0 0 : ℝ)^2 + (sevenNineRadial 4 1 0 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 0 0 0 : ℝ)^2 + (sevenNineRadial 4 1 0 : ℝ)^2 - (sevenNineDistanceLower[3]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h01 : (sevenNineRadial 0 0 0 : ℝ)^2 + (sevenNineRadial 4 1 1 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[13]! : ℝ) * (2 * (sevenNineRadial 0 0 0 : ℝ) * (sevenNineRadial 4 1 1 : ℝ)) := by
    have hq : (sevenNineRadial 0 0 0)^2 + (sevenNineRadial 4 1 1)^2 - sevenNineDistanceLower[3]!^2 ≤
        sevenNineCosUpper[13]! * (2 * sevenNineRadial 0 0 0 * sevenNineRadial 4 1 1) := by native_decide
    have hqR :
        (sevenNineRadial 0 0 0 : ℝ)^2 + (sevenNineRadial 4 1 1 : ℝ)^2 - (sevenNineDistanceLower[3]! : ℝ)^2 ≤
          (sevenNineCosUpper[13]! : ℝ) * (2 * (sevenNineRadial 0 0 0 : ℝ) * (sevenNineRadial 4 1 1 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 0 0 0 : ℝ)^2 + (sevenNineRadial 4 1 1 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 0 0 0 : ℝ)^2 + (sevenNineRadial 4 1 1 : ℝ)^2 - (sevenNineDistanceLower[3]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h10 : (sevenNineRadial 0 0 1 : ℝ)^2 + (sevenNineRadial 4 1 0 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[13]! : ℝ) * (2 * (sevenNineRadial 0 0 1 : ℝ) * (sevenNineRadial 4 1 0 : ℝ)) := by
    have hq : (sevenNineRadial 0 0 1)^2 + (sevenNineRadial 4 1 0)^2 - sevenNineDistanceLower[3]!^2 ≤
        sevenNineCosUpper[13]! * (2 * sevenNineRadial 0 0 1 * sevenNineRadial 4 1 0) := by native_decide
    have hqR :
        (sevenNineRadial 0 0 1 : ℝ)^2 + (sevenNineRadial 4 1 0 : ℝ)^2 - (sevenNineDistanceLower[3]! : ℝ)^2 ≤
          (sevenNineCosUpper[13]! : ℝ) * (2 * (sevenNineRadial 0 0 1 : ℝ) * (sevenNineRadial 4 1 0 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 0 0 1 : ℝ)^2 + (sevenNineRadial 4 1 0 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 0 0 1 : ℝ)^2 + (sevenNineRadial 4 1 0 : ℝ)^2 - (sevenNineDistanceLower[3]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h11 : (sevenNineRadial 0 0 1 : ℝ)^2 + (sevenNineRadial 4 1 1 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[13]! : ℝ) * (2 * (sevenNineRadial 0 0 1 : ℝ) * (sevenNineRadial 4 1 1 : ℝ)) := by
    have hq : (sevenNineRadial 0 0 1)^2 + (sevenNineRadial 4 1 1)^2 - sevenNineDistanceLower[3]!^2 ≤
        sevenNineCosUpper[13]! * (2 * sevenNineRadial 0 0 1 * sevenNineRadial 4 1 1) := by native_decide
    have hqR :
        (sevenNineRadial 0 0 1 : ℝ)^2 + (sevenNineRadial 4 1 1 : ℝ)^2 - (sevenNineDistanceLower[3]! : ℝ)^2 ≤
          (sevenNineCosUpper[13]! : ℝ) * (2 * (sevenNineRadial 0 0 1 : ℝ) * (sevenNineRadial 4 1 1 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 0 0 1 : ℝ)^2 + (sevenNineRadial 4 1 1 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 0 0 1 : ℝ)^2 + (sevenNineRadial 4 1 1 : ℝ)^2 - (sevenNineDistanceLower[3]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have htouch := corner_touch_cosine_bound haL haU hbL hbU
    (by norm_num [sevenNineRadial, sevenNineRadialBounds])
    (by norm_num [sevenNineRadial, sevenNineRadialBounds]) h00 h01 h10 h11
  have hcos : (sevenNineCosUpper[13]! : ℝ) ≤ Real.cos ((92625150300757551863 : ℝ) / 100000000000000000000) := by
    apply lower_bound_of_taylor_error
      (cosine_taylor_ninety_six_remainder (a := 0) (b := 4) (x := ((92625150300757551863 : ℝ) / 100000000000000000000) )
        (by norm_num) (by constructor <;> norm_num [Real.pi_gt_d20, Real.pi_lt_four]))
    rw [cosine_taylor_ninety_six_at_zero (b := 4) (x := ((92625150300757551863 : ℝ) / 100000000000000000000)) (by norm_num)]
    have hp : (sevenNineCosUpper[13]! : Rat) + (((92625150300757551863 : Rat) / 100000000000000000000) : Rat)^97 / (Nat.factorial 96) ≤
        Finset.sum (Finset.range 49) (fun k => (-1 : Rat)^k * (((92625150300757551863 : Rat) / 100000000000000000000) : Rat)^(2*k) / Nat.factorial (2*k)) := by native_decide
    have hpR : (sevenNineCosUpper[13]! : ℝ) + ((92625150300757551863 : ℝ) / 100000000000000000000)^97 / (Nat.factorial 96) ≤
        Finset.sum (Finset.range 49) (fun k => (-1 : ℝ)^k * ((92625150300757551863 : ℝ) / 100000000000000000000)^(2*k) / Nat.factorial (2*k)) := by
      norm_num [sevenNineCosUpper, Finset.sum_range_succ]
    simpa [sub_zero] using hpR
  have hangle : ((92625150300757551863 : ℝ) / 100000000000000000000) ≤ Real.arccos (touchCosine a b (Real.sqrt 4 + Real.sqrt 8)) := by
    exact angle_lower_bound_of_cosine (by norm_num)
      (by
        calc
          ((92625150300757551863 : ℝ) / 100000000000000000000) ≤ (314159265358979323846 : ℝ) / 100000000000000000000 := by norm_num
          _ ≤ Real.pi := by
            have hpi := Real.pi_gt_d20.le
            norm_num at hpi ⊢
            exact hpi) (le_trans htouch hcos)
  have hdata : sevenNineAngleLower[13]! = ((92625150300757551863 : Rat) / 100000000000000000000) := by native_decide
  have hdataR : (sevenNineAngleLower[13]! : ℝ) = ((92625150300757551863 : ℝ) / 100000000000000000000) := by
    have h := congrArg (fun q : Rat => (q : ℝ)) hdata
    convert h using 1 ; norm_num
  rw [hdataR]
  exact hangle

theorem sevenNineAngle_0_4_1_0 {a b : ℝ}
    (haL : (sevenNineRadial 0 1 0 : ℝ) ≤ a) (haU : a ≤ (sevenNineRadial 0 1 1 : ℝ))
    (hbL : (sevenNineRadial 4 0 0 : ℝ) ≤ b) (hbU : b ≤ (sevenNineRadial 4 0 1 : ℝ)) :
    (sevenNineAngleLower[14]! : ℝ) ≤ Real.arccos (touchCosine a b (Real.sqrt 4 + Real.sqrt 8)) := by
  let d : ℝ := Real.sqrt 4 + Real.sqrt 8
  have hd' : (((4828427124746190097603377448419396157139343750753896146353359475981464956924214077700775068 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) : ℝ) ≤ d := by
    dsimp [d]
    have h := rat_sum_sqrt_lower (q := ((4828427124746190097603377448419396157139343750753896146353359475981464956924214077700775068 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (qi := ((2 : Rat) / 1)) (qj := ((2828427124746190097603377448419396157139343750753896146353359475981464956924214077700775068655283145470027692461824594049 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))
      (ni := 4) (nj := 8)
      (by convert sqrt_lower_4 using 1 ; norm_num)
      (by convert sqrt_lower_8 using 1 ; norm_num)
      (by native_decide)
    convert h using 1 ; norm_num
  have hd : (((4828427124746190097603377448419396157139343750753896146353359475981464956924214077700775068 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) ≤ d := by exact hd'
  have hd2 : (((4828427124746190097603377448419396157139343750753896146353359475981464956924214077700775068 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))^2 ≤ d^2 := by
    have hq : (0 : ℝ) ≤ ((4828427124746190097603377448419396157139343750753896146353359475981464956924214077700775068 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) := by norm_num
    have hdn : 0 ≤ d := by positivity
    exact (sq_le_sq₀ hq hdn).mpr hd
  have hd2' : (sevenNineDistanceLower[3]! : ℝ)^2 ≤ d^2 := by
    convert hd2 using 1 ; norm_num [sevenNineDistanceLower]
  have h00 : (sevenNineRadial 0 1 0 : ℝ)^2 + (sevenNineRadial 4 0 0 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[14]! : ℝ) * (2 * (sevenNineRadial 0 1 0 : ℝ) * (sevenNineRadial 4 0 0 : ℝ)) := by
    have hq : (sevenNineRadial 0 1 0)^2 + (sevenNineRadial 4 0 0)^2 - sevenNineDistanceLower[3]!^2 ≤
        sevenNineCosUpper[14]! * (2 * sevenNineRadial 0 1 0 * sevenNineRadial 4 0 0) := by native_decide
    have hqR :
        (sevenNineRadial 0 1 0 : ℝ)^2 + (sevenNineRadial 4 0 0 : ℝ)^2 - (sevenNineDistanceLower[3]! : ℝ)^2 ≤
          (sevenNineCosUpper[14]! : ℝ) * (2 * (sevenNineRadial 0 1 0 : ℝ) * (sevenNineRadial 4 0 0 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 0 1 0 : ℝ)^2 + (sevenNineRadial 4 0 0 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 0 1 0 : ℝ)^2 + (sevenNineRadial 4 0 0 : ℝ)^2 - (sevenNineDistanceLower[3]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h01 : (sevenNineRadial 0 1 0 : ℝ)^2 + (sevenNineRadial 4 0 1 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[14]! : ℝ) * (2 * (sevenNineRadial 0 1 0 : ℝ) * (sevenNineRadial 4 0 1 : ℝ)) := by
    have hq : (sevenNineRadial 0 1 0)^2 + (sevenNineRadial 4 0 1)^2 - sevenNineDistanceLower[3]!^2 ≤
        sevenNineCosUpper[14]! * (2 * sevenNineRadial 0 1 0 * sevenNineRadial 4 0 1) := by native_decide
    have hqR :
        (sevenNineRadial 0 1 0 : ℝ)^2 + (sevenNineRadial 4 0 1 : ℝ)^2 - (sevenNineDistanceLower[3]! : ℝ)^2 ≤
          (sevenNineCosUpper[14]! : ℝ) * (2 * (sevenNineRadial 0 1 0 : ℝ) * (sevenNineRadial 4 0 1 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 0 1 0 : ℝ)^2 + (sevenNineRadial 4 0 1 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 0 1 0 : ℝ)^2 + (sevenNineRadial 4 0 1 : ℝ)^2 - (sevenNineDistanceLower[3]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h10 : (sevenNineRadial 0 1 1 : ℝ)^2 + (sevenNineRadial 4 0 0 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[14]! : ℝ) * (2 * (sevenNineRadial 0 1 1 : ℝ) * (sevenNineRadial 4 0 0 : ℝ)) := by
    have hq : (sevenNineRadial 0 1 1)^2 + (sevenNineRadial 4 0 0)^2 - sevenNineDistanceLower[3]!^2 ≤
        sevenNineCosUpper[14]! * (2 * sevenNineRadial 0 1 1 * sevenNineRadial 4 0 0) := by native_decide
    have hqR :
        (sevenNineRadial 0 1 1 : ℝ)^2 + (sevenNineRadial 4 0 0 : ℝ)^2 - (sevenNineDistanceLower[3]! : ℝ)^2 ≤
          (sevenNineCosUpper[14]! : ℝ) * (2 * (sevenNineRadial 0 1 1 : ℝ) * (sevenNineRadial 4 0 0 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 0 1 1 : ℝ)^2 + (sevenNineRadial 4 0 0 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 0 1 1 : ℝ)^2 + (sevenNineRadial 4 0 0 : ℝ)^2 - (sevenNineDistanceLower[3]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h11 : (sevenNineRadial 0 1 1 : ℝ)^2 + (sevenNineRadial 4 0 1 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[14]! : ℝ) * (2 * (sevenNineRadial 0 1 1 : ℝ) * (sevenNineRadial 4 0 1 : ℝ)) := by
    have hq : (sevenNineRadial 0 1 1)^2 + (sevenNineRadial 4 0 1)^2 - sevenNineDistanceLower[3]!^2 ≤
        sevenNineCosUpper[14]! * (2 * sevenNineRadial 0 1 1 * sevenNineRadial 4 0 1) := by native_decide
    have hqR :
        (sevenNineRadial 0 1 1 : ℝ)^2 + (sevenNineRadial 4 0 1 : ℝ)^2 - (sevenNineDistanceLower[3]! : ℝ)^2 ≤
          (sevenNineCosUpper[14]! : ℝ) * (2 * (sevenNineRadial 0 1 1 : ℝ) * (sevenNineRadial 4 0 1 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 0 1 1 : ℝ)^2 + (sevenNineRadial 4 0 1 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 0 1 1 : ℝ)^2 + (sevenNineRadial 4 0 1 : ℝ)^2 - (sevenNineDistanceLower[3]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have htouch := corner_touch_cosine_bound haL haU hbL hbU
    (by norm_num [sevenNineRadial, sevenNineRadialBounds])
    (by norm_num [sevenNineRadial, sevenNineRadialBounds]) h00 h01 h10 h11
  have hcos : (sevenNineCosUpper[14]! : ℝ) ≤ Real.cos ((48700305141601732239 : ℝ) / 100000000000000000000) := by
    apply lower_bound_of_taylor_error
      (cosine_taylor_ninety_six_remainder (a := 0) (b := 4) (x := ((48700305141601732239 : ℝ) / 100000000000000000000) )
        (by norm_num) (by constructor <;> norm_num [Real.pi_gt_d20, Real.pi_lt_four]))
    rw [cosine_taylor_ninety_six_at_zero (b := 4) (x := ((48700305141601732239 : ℝ) / 100000000000000000000)) (by norm_num)]
    have hp : (sevenNineCosUpper[14]! : Rat) + (((48700305141601732239 : Rat) / 100000000000000000000) : Rat)^97 / (Nat.factorial 96) ≤
        Finset.sum (Finset.range 49) (fun k => (-1 : Rat)^k * (((48700305141601732239 : Rat) / 100000000000000000000) : Rat)^(2*k) / Nat.factorial (2*k)) := by native_decide
    have hpR : (sevenNineCosUpper[14]! : ℝ) + ((48700305141601732239 : ℝ) / 100000000000000000000)^97 / (Nat.factorial 96) ≤
        Finset.sum (Finset.range 49) (fun k => (-1 : ℝ)^k * ((48700305141601732239 : ℝ) / 100000000000000000000)^(2*k) / Nat.factorial (2*k)) := by
      norm_num [sevenNineCosUpper, Finset.sum_range_succ]
    simpa [sub_zero] using hpR
  have hangle : ((48700305141601732239 : ℝ) / 100000000000000000000) ≤ Real.arccos (touchCosine a b (Real.sqrt 4 + Real.sqrt 8)) := by
    exact angle_lower_bound_of_cosine (by norm_num)
      (by
        calc
          ((48700305141601732239 : ℝ) / 100000000000000000000) ≤ (314159265358979323846 : ℝ) / 100000000000000000000 := by norm_num
          _ ≤ Real.pi := by
            have hpi := Real.pi_gt_d20.le
            norm_num at hpi ⊢
            exact hpi) (le_trans htouch hcos)
  have hdata : sevenNineAngleLower[14]! = ((48700305141601732239 : Rat) / 100000000000000000000) := by native_decide
  have hdataR : (sevenNineAngleLower[14]! : ℝ) = ((48700305141601732239 : ℝ) / 100000000000000000000) := by
    have h := congrArg (fun q : Rat => (q : ℝ)) hdata
    convert h using 1 ; norm_num
  rw [hdataR]
  exact hangle

theorem sevenNineAngle_0_4_1_1 {a b : ℝ}
    (haL : (sevenNineRadial 0 1 0 : ℝ) ≤ a) (haU : a ≤ (sevenNineRadial 0 1 1 : ℝ))
    (hbL : (sevenNineRadial 4 1 0 : ℝ) ≤ b) (hbU : b ≤ (sevenNineRadial 4 1 1 : ℝ)) :
    (sevenNineAngleLower[15]! : ℝ) ≤ Real.arccos (touchCosine a b (Real.sqrt 4 + Real.sqrt 8)) := by
  let d : ℝ := Real.sqrt 4 + Real.sqrt 8
  have hd' : (((4828427124746190097603377448419396157139343750753896146353359475981464956924214077700775068 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) : ℝ) ≤ d := by
    dsimp [d]
    have h := rat_sum_sqrt_lower (q := ((4828427124746190097603377448419396157139343750753896146353359475981464956924214077700775068 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (qi := ((2 : Rat) / 1)) (qj := ((2828427124746190097603377448419396157139343750753896146353359475981464956924214077700775068655283145470027692461824594049 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))
      (ni := 4) (nj := 8)
      (by convert sqrt_lower_4 using 1 ; norm_num)
      (by convert sqrt_lower_8 using 1 ; norm_num)
      (by native_decide)
    convert h using 1 ; norm_num
  have hd : (((4828427124746190097603377448419396157139343750753896146353359475981464956924214077700775068 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) ≤ d := by exact hd'
  have hd2 : (((4828427124746190097603377448419396157139343750753896146353359475981464956924214077700775068 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))^2 ≤ d^2 := by
    have hq : (0 : ℝ) ≤ ((4828427124746190097603377448419396157139343750753896146353359475981464956924214077700775068 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) := by norm_num
    have hdn : 0 ≤ d := by positivity
    exact (sq_le_sq₀ hq hdn).mpr hd
  have hd2' : (sevenNineDistanceLower[3]! : ℝ)^2 ≤ d^2 := by
    convert hd2 using 1 ; norm_num [sevenNineDistanceLower]
  have h00 : (sevenNineRadial 0 1 0 : ℝ)^2 + (sevenNineRadial 4 1 0 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[15]! : ℝ) * (2 * (sevenNineRadial 0 1 0 : ℝ) * (sevenNineRadial 4 1 0 : ℝ)) := by
    have hq : (sevenNineRadial 0 1 0)^2 + (sevenNineRadial 4 1 0)^2 - sevenNineDistanceLower[3]!^2 ≤
        sevenNineCosUpper[15]! * (2 * sevenNineRadial 0 1 0 * sevenNineRadial 4 1 0) := by native_decide
    have hqR :
        (sevenNineRadial 0 1 0 : ℝ)^2 + (sevenNineRadial 4 1 0 : ℝ)^2 - (sevenNineDistanceLower[3]! : ℝ)^2 ≤
          (sevenNineCosUpper[15]! : ℝ) * (2 * (sevenNineRadial 0 1 0 : ℝ) * (sevenNineRadial 4 1 0 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 0 1 0 : ℝ)^2 + (sevenNineRadial 4 1 0 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 0 1 0 : ℝ)^2 + (sevenNineRadial 4 1 0 : ℝ)^2 - (sevenNineDistanceLower[3]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h01 : (sevenNineRadial 0 1 0 : ℝ)^2 + (sevenNineRadial 4 1 1 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[15]! : ℝ) * (2 * (sevenNineRadial 0 1 0 : ℝ) * (sevenNineRadial 4 1 1 : ℝ)) := by
    have hq : (sevenNineRadial 0 1 0)^2 + (sevenNineRadial 4 1 1)^2 - sevenNineDistanceLower[3]!^2 ≤
        sevenNineCosUpper[15]! * (2 * sevenNineRadial 0 1 0 * sevenNineRadial 4 1 1) := by native_decide
    have hqR :
        (sevenNineRadial 0 1 0 : ℝ)^2 + (sevenNineRadial 4 1 1 : ℝ)^2 - (sevenNineDistanceLower[3]! : ℝ)^2 ≤
          (sevenNineCosUpper[15]! : ℝ) * (2 * (sevenNineRadial 0 1 0 : ℝ) * (sevenNineRadial 4 1 1 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 0 1 0 : ℝ)^2 + (sevenNineRadial 4 1 1 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 0 1 0 : ℝ)^2 + (sevenNineRadial 4 1 1 : ℝ)^2 - (sevenNineDistanceLower[3]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h10 : (sevenNineRadial 0 1 1 : ℝ)^2 + (sevenNineRadial 4 1 0 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[15]! : ℝ) * (2 * (sevenNineRadial 0 1 1 : ℝ) * (sevenNineRadial 4 1 0 : ℝ)) := by
    have hq : (sevenNineRadial 0 1 1)^2 + (sevenNineRadial 4 1 0)^2 - sevenNineDistanceLower[3]!^2 ≤
        sevenNineCosUpper[15]! * (2 * sevenNineRadial 0 1 1 * sevenNineRadial 4 1 0) := by native_decide
    have hqR :
        (sevenNineRadial 0 1 1 : ℝ)^2 + (sevenNineRadial 4 1 0 : ℝ)^2 - (sevenNineDistanceLower[3]! : ℝ)^2 ≤
          (sevenNineCosUpper[15]! : ℝ) * (2 * (sevenNineRadial 0 1 1 : ℝ) * (sevenNineRadial 4 1 0 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 0 1 1 : ℝ)^2 + (sevenNineRadial 4 1 0 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 0 1 1 : ℝ)^2 + (sevenNineRadial 4 1 0 : ℝ)^2 - (sevenNineDistanceLower[3]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h11 : (sevenNineRadial 0 1 1 : ℝ)^2 + (sevenNineRadial 4 1 1 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[15]! : ℝ) * (2 * (sevenNineRadial 0 1 1 : ℝ) * (sevenNineRadial 4 1 1 : ℝ)) := by
    have hq : (sevenNineRadial 0 1 1)^2 + (sevenNineRadial 4 1 1)^2 - sevenNineDistanceLower[3]!^2 ≤
        sevenNineCosUpper[15]! * (2 * sevenNineRadial 0 1 1 * sevenNineRadial 4 1 1) := by native_decide
    have hqR :
        (sevenNineRadial 0 1 1 : ℝ)^2 + (sevenNineRadial 4 1 1 : ℝ)^2 - (sevenNineDistanceLower[3]! : ℝ)^2 ≤
          (sevenNineCosUpper[15]! : ℝ) * (2 * (sevenNineRadial 0 1 1 : ℝ) * (sevenNineRadial 4 1 1 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 0 1 1 : ℝ)^2 + (sevenNineRadial 4 1 1 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 0 1 1 : ℝ)^2 + (sevenNineRadial 4 1 1 : ℝ)^2 - (sevenNineDistanceLower[3]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have htouch := corner_touch_cosine_bound haL haU hbL hbU
    (by norm_num [sevenNineRadial, sevenNineRadialBounds])
    (by norm_num [sevenNineRadial, sevenNineRadialBounds]) h00 h01 h10 h11
  have hcos : (sevenNineCosUpper[15]! : ℝ) ≤ Real.cos ((89963371984297709635 : ℝ) / 100000000000000000000) := by
    apply lower_bound_of_taylor_error
      (cosine_taylor_ninety_six_remainder (a := 0) (b := 4) (x := ((89963371984297709635 : ℝ) / 100000000000000000000) )
        (by norm_num) (by constructor <;> norm_num [Real.pi_gt_d20, Real.pi_lt_four]))
    rw [cosine_taylor_ninety_six_at_zero (b := 4) (x := ((89963371984297709635 : ℝ) / 100000000000000000000)) (by norm_num)]
    have hp : (sevenNineCosUpper[15]! : Rat) + (((89963371984297709635 : Rat) / 100000000000000000000) : Rat)^97 / (Nat.factorial 96) ≤
        Finset.sum (Finset.range 49) (fun k => (-1 : Rat)^k * (((89963371984297709635 : Rat) / 100000000000000000000) : Rat)^(2*k) / Nat.factorial (2*k)) := by native_decide
    have hpR : (sevenNineCosUpper[15]! : ℝ) + ((89963371984297709635 : ℝ) / 100000000000000000000)^97 / (Nat.factorial 96) ≤
        Finset.sum (Finset.range 49) (fun k => (-1 : ℝ)^k * ((89963371984297709635 : ℝ) / 100000000000000000000)^(2*k) / Nat.factorial (2*k)) := by
      norm_num [sevenNineCosUpper, Finset.sum_range_succ]
    simpa [sub_zero] using hpR
  have hangle : ((89963371984297709635 : ℝ) / 100000000000000000000) ≤ Real.arccos (touchCosine a b (Real.sqrt 4 + Real.sqrt 8)) := by
    exact angle_lower_bound_of_cosine (by norm_num)
      (by
        calc
          ((89963371984297709635 : ℝ) / 100000000000000000000) ≤ (314159265358979323846 : ℝ) / 100000000000000000000 := by norm_num
          _ ≤ Real.pi := by
            have hpi := Real.pi_gt_d20.le
            norm_num at hpi ⊢
            exact hpi) (le_trans htouch hcos)
  have hdata : sevenNineAngleLower[15]! = ((89963371984297709635 : Rat) / 100000000000000000000) := by native_decide
  have hdataR : (sevenNineAngleLower[15]! : ℝ) = ((89963371984297709635 : ℝ) / 100000000000000000000) := by
    have h := congrArg (fun q : Rat => (q : ℝ)) hdata
    convert h using 1 ; norm_num
  rw [hdataR]
  exact hangle

theorem sevenNineAngle_0_5_0_0 {a b : ℝ}
    (haL : (sevenNineRadial 0 0 0 : ℝ) ≤ a) (haU : a ≤ (sevenNineRadial 0 0 1 : ℝ))
    (hbL : (sevenNineRadial 5 0 0 : ℝ) ≤ b) (hbU : b ≤ (sevenNineRadial 5 0 1 : ℝ)) :
    (sevenNineAngleLower[16]! : ℝ) ≤ Real.arccos (touchCosine a b (Real.sqrt 4 + Real.sqrt 9)) := by
  let d : ℝ := Real.sqrt 4 + Real.sqrt 9
  have hd' : (((5 : Rat) / 1) : ℝ) ≤ d := by
    dsimp [d]
    have h := rat_sum_sqrt_lower (q := ((5 : Rat) / 1)) (qi := ((2 : Rat) / 1)) (qj := ((3 : Rat) / 1))
      (ni := 4) (nj := 9)
      (by convert sqrt_lower_4 using 1 ; norm_num)
      (by convert sqrt_lower_9 using 1 ; norm_num)
      (by native_decide)
    convert h using 1 ; norm_num
  have hd : (((5 : ℝ) / 1)) ≤ d := by exact hd'
  have hd2 : (((5 : ℝ) / 1))^2 ≤ d^2 := by
    have hq : (0 : ℝ) ≤ ((5 : ℝ) / 1) := by norm_num
    have hdn : 0 ≤ d := by positivity
    exact (sq_le_sq₀ hq hdn).mpr hd
  have hd2' : (sevenNineDistanceLower[4]! : ℝ)^2 ≤ d^2 := by
    convert hd2 using 1 ; norm_num [sevenNineDistanceLower]
  have h00 : (sevenNineRadial 0 0 0 : ℝ)^2 + (sevenNineRadial 5 0 0 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[16]! : ℝ) * (2 * (sevenNineRadial 0 0 0 : ℝ) * (sevenNineRadial 5 0 0 : ℝ)) := by
    have hq : (sevenNineRadial 0 0 0)^2 + (sevenNineRadial 5 0 0)^2 - sevenNineDistanceLower[4]!^2 ≤
        sevenNineCosUpper[16]! * (2 * sevenNineRadial 0 0 0 * sevenNineRadial 5 0 0) := by native_decide
    have hqR :
        (sevenNineRadial 0 0 0 : ℝ)^2 + (sevenNineRadial 5 0 0 : ℝ)^2 - (sevenNineDistanceLower[4]! : ℝ)^2 ≤
          (sevenNineCosUpper[16]! : ℝ) * (2 * (sevenNineRadial 0 0 0 : ℝ) * (sevenNineRadial 5 0 0 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 0 0 0 : ℝ)^2 + (sevenNineRadial 5 0 0 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 0 0 0 : ℝ)^2 + (sevenNineRadial 5 0 0 : ℝ)^2 - (sevenNineDistanceLower[4]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h01 : (sevenNineRadial 0 0 0 : ℝ)^2 + (sevenNineRadial 5 0 1 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[16]! : ℝ) * (2 * (sevenNineRadial 0 0 0 : ℝ) * (sevenNineRadial 5 0 1 : ℝ)) := by
    have hq : (sevenNineRadial 0 0 0)^2 + (sevenNineRadial 5 0 1)^2 - sevenNineDistanceLower[4]!^2 ≤
        sevenNineCosUpper[16]! * (2 * sevenNineRadial 0 0 0 * sevenNineRadial 5 0 1) := by native_decide
    have hqR :
        (sevenNineRadial 0 0 0 : ℝ)^2 + (sevenNineRadial 5 0 1 : ℝ)^2 - (sevenNineDistanceLower[4]! : ℝ)^2 ≤
          (sevenNineCosUpper[16]! : ℝ) * (2 * (sevenNineRadial 0 0 0 : ℝ) * (sevenNineRadial 5 0 1 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 0 0 0 : ℝ)^2 + (sevenNineRadial 5 0 1 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 0 0 0 : ℝ)^2 + (sevenNineRadial 5 0 1 : ℝ)^2 - (sevenNineDistanceLower[4]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h10 : (sevenNineRadial 0 0 1 : ℝ)^2 + (sevenNineRadial 5 0 0 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[16]! : ℝ) * (2 * (sevenNineRadial 0 0 1 : ℝ) * (sevenNineRadial 5 0 0 : ℝ)) := by
    have hq : (sevenNineRadial 0 0 1)^2 + (sevenNineRadial 5 0 0)^2 - sevenNineDistanceLower[4]!^2 ≤
        sevenNineCosUpper[16]! * (2 * sevenNineRadial 0 0 1 * sevenNineRadial 5 0 0) := by native_decide
    have hqR :
        (sevenNineRadial 0 0 1 : ℝ)^2 + (sevenNineRadial 5 0 0 : ℝ)^2 - (sevenNineDistanceLower[4]! : ℝ)^2 ≤
          (sevenNineCosUpper[16]! : ℝ) * (2 * (sevenNineRadial 0 0 1 : ℝ) * (sevenNineRadial 5 0 0 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 0 0 1 : ℝ)^2 + (sevenNineRadial 5 0 0 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 0 0 1 : ℝ)^2 + (sevenNineRadial 5 0 0 : ℝ)^2 - (sevenNineDistanceLower[4]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h11 : (sevenNineRadial 0 0 1 : ℝ)^2 + (sevenNineRadial 5 0 1 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[16]! : ℝ) * (2 * (sevenNineRadial 0 0 1 : ℝ) * (sevenNineRadial 5 0 1 : ℝ)) := by
    have hq : (sevenNineRadial 0 0 1)^2 + (sevenNineRadial 5 0 1)^2 - sevenNineDistanceLower[4]!^2 ≤
        sevenNineCosUpper[16]! * (2 * sevenNineRadial 0 0 1 * sevenNineRadial 5 0 1) := by native_decide
    have hqR :
        (sevenNineRadial 0 0 1 : ℝ)^2 + (sevenNineRadial 5 0 1 : ℝ)^2 - (sevenNineDistanceLower[4]! : ℝ)^2 ≤
          (sevenNineCosUpper[16]! : ℝ) * (2 * (sevenNineRadial 0 0 1 : ℝ) * (sevenNineRadial 5 0 1 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 0 0 1 : ℝ)^2 + (sevenNineRadial 5 0 1 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 0 0 1 : ℝ)^2 + (sevenNineRadial 5 0 1 : ℝ)^2 - (sevenNineDistanceLower[4]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have htouch := corner_touch_cosine_bound haL haU hbL hbU
    (by norm_num [sevenNineRadial, sevenNineRadialBounds])
    (by norm_num [sevenNineRadial, sevenNineRadialBounds]) h00 h01 h10 h11
  have hcos : (sevenNineCosUpper[16]! : ℝ) ≤ Real.cos ((182347658193697527271 : ℝ) / 100000000000000000000) := by
    apply lower_bound_of_taylor_error
      (cosine_taylor_ninety_six_remainder (a := 0) (b := 4) (x := ((182347658193697527271 : ℝ) / 100000000000000000000) )
        (by norm_num) (by constructor <;> norm_num [Real.pi_gt_d20, Real.pi_lt_four]))
    rw [cosine_taylor_ninety_six_at_zero (b := 4) (x := ((182347658193697527271 : ℝ) / 100000000000000000000)) (by norm_num)]
    have hp : (sevenNineCosUpper[16]! : Rat) + (((182347658193697527271 : Rat) / 100000000000000000000) : Rat)^97 / (Nat.factorial 96) ≤
        Finset.sum (Finset.range 49) (fun k => (-1 : Rat)^k * (((182347658193697527271 : Rat) / 100000000000000000000) : Rat)^(2*k) / Nat.factorial (2*k)) := by native_decide
    have hpR : (sevenNineCosUpper[16]! : ℝ) + ((182347658193697527271 : ℝ) / 100000000000000000000)^97 / (Nat.factorial 96) ≤
        Finset.sum (Finset.range 49) (fun k => (-1 : ℝ)^k * ((182347658193697527271 : ℝ) / 100000000000000000000)^(2*k) / Nat.factorial (2*k)) := by
      norm_num [sevenNineCosUpper, Finset.sum_range_succ]
    simpa [sub_zero] using hpR
  have hangle : ((182347658193697527271 : ℝ) / 100000000000000000000) ≤ Real.arccos (touchCosine a b (Real.sqrt 4 + Real.sqrt 9)) := by
    exact angle_lower_bound_of_cosine (by norm_num)
      (by
        calc
          ((182347658193697527271 : ℝ) / 100000000000000000000) ≤ (314159265358979323846 : ℝ) / 100000000000000000000 := by norm_num
          _ ≤ Real.pi := by
            have hpi := Real.pi_gt_d20.le
            norm_num at hpi ⊢
            exact hpi) (le_trans htouch hcos)
  have hdata : sevenNineAngleLower[16]! = ((182347658193697527271 : Rat) / 100000000000000000000) := by native_decide
  have hdataR : (sevenNineAngleLower[16]! : ℝ) = ((182347658193697527271 : ℝ) / 100000000000000000000) := by
    have h := congrArg (fun q : Rat => (q : ℝ)) hdata
    convert h using 1 ; norm_num
  rw [hdataR]
  exact hangle

theorem sevenNineAngle_0_5_0_1 {a b : ℝ}
    (haL : (sevenNineRadial 0 0 0 : ℝ) ≤ a) (haU : a ≤ (sevenNineRadial 0 0 1 : ℝ))
    (hbL : (sevenNineRadial 5 1 0 : ℝ) ≤ b) (hbU : b ≤ (sevenNineRadial 5 1 1 : ℝ)) :
    (sevenNineAngleLower[17]! : ℝ) ≤ Real.arccos (touchCosine a b (Real.sqrt 4 + Real.sqrt 9)) := by
  let d : ℝ := Real.sqrt 4 + Real.sqrt 9
  have hd' : (((5 : Rat) / 1) : ℝ) ≤ d := by
    dsimp [d]
    have h := rat_sum_sqrt_lower (q := ((5 : Rat) / 1)) (qi := ((2 : Rat) / 1)) (qj := ((3 : Rat) / 1))
      (ni := 4) (nj := 9)
      (by convert sqrt_lower_4 using 1 ; norm_num)
      (by convert sqrt_lower_9 using 1 ; norm_num)
      (by native_decide)
    convert h using 1 ; norm_num
  have hd : (((5 : ℝ) / 1)) ≤ d := by exact hd'
  have hd2 : (((5 : ℝ) / 1))^2 ≤ d^2 := by
    have hq : (0 : ℝ) ≤ ((5 : ℝ) / 1) := by norm_num
    have hdn : 0 ≤ d := by positivity
    exact (sq_le_sq₀ hq hdn).mpr hd
  have hd2' : (sevenNineDistanceLower[4]! : ℝ)^2 ≤ d^2 := by
    convert hd2 using 1 ; norm_num [sevenNineDistanceLower]
  have h00 : (sevenNineRadial 0 0 0 : ℝ)^2 + (sevenNineRadial 5 1 0 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[17]! : ℝ) * (2 * (sevenNineRadial 0 0 0 : ℝ) * (sevenNineRadial 5 1 0 : ℝ)) := by
    have hq : (sevenNineRadial 0 0 0)^2 + (sevenNineRadial 5 1 0)^2 - sevenNineDistanceLower[4]!^2 ≤
        sevenNineCosUpper[17]! * (2 * sevenNineRadial 0 0 0 * sevenNineRadial 5 1 0) := by native_decide
    have hqR :
        (sevenNineRadial 0 0 0 : ℝ)^2 + (sevenNineRadial 5 1 0 : ℝ)^2 - (sevenNineDistanceLower[4]! : ℝ)^2 ≤
          (sevenNineCosUpper[17]! : ℝ) * (2 * (sevenNineRadial 0 0 0 : ℝ) * (sevenNineRadial 5 1 0 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 0 0 0 : ℝ)^2 + (sevenNineRadial 5 1 0 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 0 0 0 : ℝ)^2 + (sevenNineRadial 5 1 0 : ℝ)^2 - (sevenNineDistanceLower[4]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h01 : (sevenNineRadial 0 0 0 : ℝ)^2 + (sevenNineRadial 5 1 1 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[17]! : ℝ) * (2 * (sevenNineRadial 0 0 0 : ℝ) * (sevenNineRadial 5 1 1 : ℝ)) := by
    have hq : (sevenNineRadial 0 0 0)^2 + (sevenNineRadial 5 1 1)^2 - sevenNineDistanceLower[4]!^2 ≤
        sevenNineCosUpper[17]! * (2 * sevenNineRadial 0 0 0 * sevenNineRadial 5 1 1) := by native_decide
    have hqR :
        (sevenNineRadial 0 0 0 : ℝ)^2 + (sevenNineRadial 5 1 1 : ℝ)^2 - (sevenNineDistanceLower[4]! : ℝ)^2 ≤
          (sevenNineCosUpper[17]! : ℝ) * (2 * (sevenNineRadial 0 0 0 : ℝ) * (sevenNineRadial 5 1 1 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 0 0 0 : ℝ)^2 + (sevenNineRadial 5 1 1 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 0 0 0 : ℝ)^2 + (sevenNineRadial 5 1 1 : ℝ)^2 - (sevenNineDistanceLower[4]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h10 : (sevenNineRadial 0 0 1 : ℝ)^2 + (sevenNineRadial 5 1 0 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[17]! : ℝ) * (2 * (sevenNineRadial 0 0 1 : ℝ) * (sevenNineRadial 5 1 0 : ℝ)) := by
    have hq : (sevenNineRadial 0 0 1)^2 + (sevenNineRadial 5 1 0)^2 - sevenNineDistanceLower[4]!^2 ≤
        sevenNineCosUpper[17]! * (2 * sevenNineRadial 0 0 1 * sevenNineRadial 5 1 0) := by native_decide
    have hqR :
        (sevenNineRadial 0 0 1 : ℝ)^2 + (sevenNineRadial 5 1 0 : ℝ)^2 - (sevenNineDistanceLower[4]! : ℝ)^2 ≤
          (sevenNineCosUpper[17]! : ℝ) * (2 * (sevenNineRadial 0 0 1 : ℝ) * (sevenNineRadial 5 1 0 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 0 0 1 : ℝ)^2 + (sevenNineRadial 5 1 0 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 0 0 1 : ℝ)^2 + (sevenNineRadial 5 1 0 : ℝ)^2 - (sevenNineDistanceLower[4]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h11 : (sevenNineRadial 0 0 1 : ℝ)^2 + (sevenNineRadial 5 1 1 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[17]! : ℝ) * (2 * (sevenNineRadial 0 0 1 : ℝ) * (sevenNineRadial 5 1 1 : ℝ)) := by
    have hq : (sevenNineRadial 0 0 1)^2 + (sevenNineRadial 5 1 1)^2 - sevenNineDistanceLower[4]!^2 ≤
        sevenNineCosUpper[17]! * (2 * sevenNineRadial 0 0 1 * sevenNineRadial 5 1 1) := by native_decide
    have hqR :
        (sevenNineRadial 0 0 1 : ℝ)^2 + (sevenNineRadial 5 1 1 : ℝ)^2 - (sevenNineDistanceLower[4]! : ℝ)^2 ≤
          (sevenNineCosUpper[17]! : ℝ) * (2 * (sevenNineRadial 0 0 1 : ℝ) * (sevenNineRadial 5 1 1 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 0 0 1 : ℝ)^2 + (sevenNineRadial 5 1 1 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 0 0 1 : ℝ)^2 + (sevenNineRadial 5 1 1 : ℝ)^2 - (sevenNineDistanceLower[4]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have htouch := corner_touch_cosine_bound haL haU hbL hbU
    (by norm_num [sevenNineRadial, sevenNineRadialBounds])
    (by norm_num [sevenNineRadial, sevenNineRadialBounds]) h00 h01 h10 h11
  have hcos : (sevenNineCosUpper[17]! : ℝ) ≤ Real.cos ((127580041773688210575 : ℝ) / 100000000000000000000) := by
    apply lower_bound_of_taylor_error
      (cosine_taylor_ninety_six_remainder (a := 0) (b := 4) (x := ((127580041773688210575 : ℝ) / 100000000000000000000) )
        (by norm_num) (by constructor <;> norm_num [Real.pi_gt_d20, Real.pi_lt_four]))
    rw [cosine_taylor_ninety_six_at_zero (b := 4) (x := ((127580041773688210575 : ℝ) / 100000000000000000000)) (by norm_num)]
    have hp : (sevenNineCosUpper[17]! : Rat) + (((127580041773688210575 : Rat) / 100000000000000000000) : Rat)^97 / (Nat.factorial 96) ≤
        Finset.sum (Finset.range 49) (fun k => (-1 : Rat)^k * (((127580041773688210575 : Rat) / 100000000000000000000) : Rat)^(2*k) / Nat.factorial (2*k)) := by native_decide
    have hpR : (sevenNineCosUpper[17]! : ℝ) + ((127580041773688210575 : ℝ) / 100000000000000000000)^97 / (Nat.factorial 96) ≤
        Finset.sum (Finset.range 49) (fun k => (-1 : ℝ)^k * ((127580041773688210575 : ℝ) / 100000000000000000000)^(2*k) / Nat.factorial (2*k)) := by
      norm_num [sevenNineCosUpper, Finset.sum_range_succ]
    simpa [sub_zero] using hpR
  have hangle : ((127580041773688210575 : ℝ) / 100000000000000000000) ≤ Real.arccos (touchCosine a b (Real.sqrt 4 + Real.sqrt 9)) := by
    exact angle_lower_bound_of_cosine (by norm_num)
      (by
        calc
          ((127580041773688210575 : ℝ) / 100000000000000000000) ≤ (314159265358979323846 : ℝ) / 100000000000000000000 := by norm_num
          _ ≤ Real.pi := by
            have hpi := Real.pi_gt_d20.le
            norm_num at hpi ⊢
            exact hpi) (le_trans htouch hcos)
  have hdata : sevenNineAngleLower[17]! = ((127580041773688210575 : Rat) / 100000000000000000000) := by native_decide
  have hdataR : (sevenNineAngleLower[17]! : ℝ) = ((127580041773688210575 : ℝ) / 100000000000000000000) := by
    have h := congrArg (fun q : Rat => (q : ℝ)) hdata
    convert h using 1 ; norm_num
  rw [hdataR]
  exact hangle

theorem sevenNineAngle_0_5_1_0 {a b : ℝ}
    (haL : (sevenNineRadial 0 1 0 : ℝ) ≤ a) (haU : a ≤ (sevenNineRadial 0 1 1 : ℝ))
    (hbL : (sevenNineRadial 5 0 0 : ℝ) ≤ b) (hbU : b ≤ (sevenNineRadial 5 0 1 : ℝ)) :
    (sevenNineAngleLower[18]! : ℝ) ≤ Real.arccos (touchCosine a b (Real.sqrt 4 + Real.sqrt 9)) := by
  let d : ℝ := Real.sqrt 4 + Real.sqrt 9
  have hd' : (((5 : Rat) / 1) : ℝ) ≤ d := by
    dsimp [d]
    have h := rat_sum_sqrt_lower (q := ((5 : Rat) / 1)) (qi := ((2 : Rat) / 1)) (qj := ((3 : Rat) / 1))
      (ni := 4) (nj := 9)
      (by convert sqrt_lower_4 using 1 ; norm_num)
      (by convert sqrt_lower_9 using 1 ; norm_num)
      (by native_decide)
    convert h using 1 ; norm_num
  have hd : (((5 : ℝ) / 1)) ≤ d := by exact hd'
  have hd2 : (((5 : ℝ) / 1))^2 ≤ d^2 := by
    have hq : (0 : ℝ) ≤ ((5 : ℝ) / 1) := by norm_num
    have hdn : 0 ≤ d := by positivity
    exact (sq_le_sq₀ hq hdn).mpr hd
  have hd2' : (sevenNineDistanceLower[4]! : ℝ)^2 ≤ d^2 := by
    convert hd2 using 1 ; norm_num [sevenNineDistanceLower]
  have h00 : (sevenNineRadial 0 1 0 : ℝ)^2 + (sevenNineRadial 5 0 0 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[18]! : ℝ) * (2 * (sevenNineRadial 0 1 0 : ℝ) * (sevenNineRadial 5 0 0 : ℝ)) := by
    have hq : (sevenNineRadial 0 1 0)^2 + (sevenNineRadial 5 0 0)^2 - sevenNineDistanceLower[4]!^2 ≤
        sevenNineCosUpper[18]! * (2 * sevenNineRadial 0 1 0 * sevenNineRadial 5 0 0) := by native_decide
    have hqR :
        (sevenNineRadial 0 1 0 : ℝ)^2 + (sevenNineRadial 5 0 0 : ℝ)^2 - (sevenNineDistanceLower[4]! : ℝ)^2 ≤
          (sevenNineCosUpper[18]! : ℝ) * (2 * (sevenNineRadial 0 1 0 : ℝ) * (sevenNineRadial 5 0 0 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 0 1 0 : ℝ)^2 + (sevenNineRadial 5 0 0 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 0 1 0 : ℝ)^2 + (sevenNineRadial 5 0 0 : ℝ)^2 - (sevenNineDistanceLower[4]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h01 : (sevenNineRadial 0 1 0 : ℝ)^2 + (sevenNineRadial 5 0 1 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[18]! : ℝ) * (2 * (sevenNineRadial 0 1 0 : ℝ) * (sevenNineRadial 5 0 1 : ℝ)) := by
    have hq : (sevenNineRadial 0 1 0)^2 + (sevenNineRadial 5 0 1)^2 - sevenNineDistanceLower[4]!^2 ≤
        sevenNineCosUpper[18]! * (2 * sevenNineRadial 0 1 0 * sevenNineRadial 5 0 1) := by native_decide
    have hqR :
        (sevenNineRadial 0 1 0 : ℝ)^2 + (sevenNineRadial 5 0 1 : ℝ)^2 - (sevenNineDistanceLower[4]! : ℝ)^2 ≤
          (sevenNineCosUpper[18]! : ℝ) * (2 * (sevenNineRadial 0 1 0 : ℝ) * (sevenNineRadial 5 0 1 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 0 1 0 : ℝ)^2 + (sevenNineRadial 5 0 1 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 0 1 0 : ℝ)^2 + (sevenNineRadial 5 0 1 : ℝ)^2 - (sevenNineDistanceLower[4]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h10 : (sevenNineRadial 0 1 1 : ℝ)^2 + (sevenNineRadial 5 0 0 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[18]! : ℝ) * (2 * (sevenNineRadial 0 1 1 : ℝ) * (sevenNineRadial 5 0 0 : ℝ)) := by
    have hq : (sevenNineRadial 0 1 1)^2 + (sevenNineRadial 5 0 0)^2 - sevenNineDistanceLower[4]!^2 ≤
        sevenNineCosUpper[18]! * (2 * sevenNineRadial 0 1 1 * sevenNineRadial 5 0 0) := by native_decide
    have hqR :
        (sevenNineRadial 0 1 1 : ℝ)^2 + (sevenNineRadial 5 0 0 : ℝ)^2 - (sevenNineDistanceLower[4]! : ℝ)^2 ≤
          (sevenNineCosUpper[18]! : ℝ) * (2 * (sevenNineRadial 0 1 1 : ℝ) * (sevenNineRadial 5 0 0 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 0 1 1 : ℝ)^2 + (sevenNineRadial 5 0 0 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 0 1 1 : ℝ)^2 + (sevenNineRadial 5 0 0 : ℝ)^2 - (sevenNineDistanceLower[4]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h11 : (sevenNineRadial 0 1 1 : ℝ)^2 + (sevenNineRadial 5 0 1 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[18]! : ℝ) * (2 * (sevenNineRadial 0 1 1 : ℝ) * (sevenNineRadial 5 0 1 : ℝ)) := by
    have hq : (sevenNineRadial 0 1 1)^2 + (sevenNineRadial 5 0 1)^2 - sevenNineDistanceLower[4]!^2 ≤
        sevenNineCosUpper[18]! * (2 * sevenNineRadial 0 1 1 * sevenNineRadial 5 0 1) := by native_decide
    have hqR :
        (sevenNineRadial 0 1 1 : ℝ)^2 + (sevenNineRadial 5 0 1 : ℝ)^2 - (sevenNineDistanceLower[4]! : ℝ)^2 ≤
          (sevenNineCosUpper[18]! : ℝ) * (2 * (sevenNineRadial 0 1 1 : ℝ) * (sevenNineRadial 5 0 1 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 0 1 1 : ℝ)^2 + (sevenNineRadial 5 0 1 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 0 1 1 : ℝ)^2 + (sevenNineRadial 5 0 1 : ℝ)^2 - (sevenNineDistanceLower[4]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have htouch := corner_touch_cosine_bound haL haU hbL hbU
    (by norm_num [sevenNineRadial, sevenNineRadialBounds])
    (by norm_num [sevenNineRadial, sevenNineRadialBounds]) h00 h01 h10 h11
  have hcos : (sevenNineCosUpper[18]! : ℝ) ≤ Real.cos ((78933885048640215079 : ℝ) / 100000000000000000000) := by
    apply lower_bound_of_taylor_error
      (cosine_taylor_ninety_six_remainder (a := 0) (b := 4) (x := ((78933885048640215079 : ℝ) / 100000000000000000000) )
        (by norm_num) (by constructor <;> norm_num [Real.pi_gt_d20, Real.pi_lt_four]))
    rw [cosine_taylor_ninety_six_at_zero (b := 4) (x := ((78933885048640215079 : ℝ) / 100000000000000000000)) (by norm_num)]
    have hp : (sevenNineCosUpper[18]! : Rat) + (((78933885048640215079 : Rat) / 100000000000000000000) : Rat)^97 / (Nat.factorial 96) ≤
        Finset.sum (Finset.range 49) (fun k => (-1 : Rat)^k * (((78933885048640215079 : Rat) / 100000000000000000000) : Rat)^(2*k) / Nat.factorial (2*k)) := by native_decide
    have hpR : (sevenNineCosUpper[18]! : ℝ) + ((78933885048640215079 : ℝ) / 100000000000000000000)^97 / (Nat.factorial 96) ≤
        Finset.sum (Finset.range 49) (fun k => (-1 : ℝ)^k * ((78933885048640215079 : ℝ) / 100000000000000000000)^(2*k) / Nat.factorial (2*k)) := by
      norm_num [sevenNineCosUpper, Finset.sum_range_succ]
    simpa [sub_zero] using hpR
  have hangle : ((78933885048640215079 : ℝ) / 100000000000000000000) ≤ Real.arccos (touchCosine a b (Real.sqrt 4 + Real.sqrt 9)) := by
    exact angle_lower_bound_of_cosine (by norm_num)
      (by
        calc
          ((78933885048640215079 : ℝ) / 100000000000000000000) ≤ (314159265358979323846 : ℝ) / 100000000000000000000 := by norm_num
          _ ≤ Real.pi := by
            have hpi := Real.pi_gt_d20.le
            norm_num at hpi ⊢
            exact hpi) (le_trans htouch hcos)
  have hdata : sevenNineAngleLower[18]! = ((78933885048640215079 : Rat) / 100000000000000000000) := by native_decide
  have hdataR : (sevenNineAngleLower[18]! : ℝ) = ((78933885048640215079 : ℝ) / 100000000000000000000) := by
    have h := congrArg (fun q : Rat => (q : ℝ)) hdata
    convert h using 1 ; norm_num
  rw [hdataR]
  exact hangle

theorem sevenNineAngle_0_5_1_1 {a b : ℝ}
    (haL : (sevenNineRadial 0 1 0 : ℝ) ≤ a) (haU : a ≤ (sevenNineRadial 0 1 1 : ℝ))
    (hbL : (sevenNineRadial 5 1 0 : ℝ) ≤ b) (hbU : b ≤ (sevenNineRadial 5 1 1 : ℝ)) :
    (sevenNineAngleLower[19]! : ℝ) ≤ Real.arccos (touchCosine a b (Real.sqrt 4 + Real.sqrt 9)) := by
  let d : ℝ := Real.sqrt 4 + Real.sqrt 9
  have hd' : (((5 : Rat) / 1) : ℝ) ≤ d := by
    dsimp [d]
    have h := rat_sum_sqrt_lower (q := ((5 : Rat) / 1)) (qi := ((2 : Rat) / 1)) (qj := ((3 : Rat) / 1))
      (ni := 4) (nj := 9)
      (by convert sqrt_lower_4 using 1 ; norm_num)
      (by convert sqrt_lower_9 using 1 ; norm_num)
      (by native_decide)
    convert h using 1 ; norm_num
  have hd : (((5 : ℝ) / 1)) ≤ d := by exact hd'
  have hd2 : (((5 : ℝ) / 1))^2 ≤ d^2 := by
    have hq : (0 : ℝ) ≤ ((5 : ℝ) / 1) := by norm_num
    have hdn : 0 ≤ d := by positivity
    exact (sq_le_sq₀ hq hdn).mpr hd
  have hd2' : (sevenNineDistanceLower[4]! : ℝ)^2 ≤ d^2 := by
    convert hd2 using 1 ; norm_num [sevenNineDistanceLower]
  have h00 : (sevenNineRadial 0 1 0 : ℝ)^2 + (sevenNineRadial 5 1 0 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[19]! : ℝ) * (2 * (sevenNineRadial 0 1 0 : ℝ) * (sevenNineRadial 5 1 0 : ℝ)) := by
    have hq : (sevenNineRadial 0 1 0)^2 + (sevenNineRadial 5 1 0)^2 - sevenNineDistanceLower[4]!^2 ≤
        sevenNineCosUpper[19]! * (2 * sevenNineRadial 0 1 0 * sevenNineRadial 5 1 0) := by native_decide
    have hqR :
        (sevenNineRadial 0 1 0 : ℝ)^2 + (sevenNineRadial 5 1 0 : ℝ)^2 - (sevenNineDistanceLower[4]! : ℝ)^2 ≤
          (sevenNineCosUpper[19]! : ℝ) * (2 * (sevenNineRadial 0 1 0 : ℝ) * (sevenNineRadial 5 1 0 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 0 1 0 : ℝ)^2 + (sevenNineRadial 5 1 0 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 0 1 0 : ℝ)^2 + (sevenNineRadial 5 1 0 : ℝ)^2 - (sevenNineDistanceLower[4]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h01 : (sevenNineRadial 0 1 0 : ℝ)^2 + (sevenNineRadial 5 1 1 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[19]! : ℝ) * (2 * (sevenNineRadial 0 1 0 : ℝ) * (sevenNineRadial 5 1 1 : ℝ)) := by
    have hq : (sevenNineRadial 0 1 0)^2 + (sevenNineRadial 5 1 1)^2 - sevenNineDistanceLower[4]!^2 ≤
        sevenNineCosUpper[19]! * (2 * sevenNineRadial 0 1 0 * sevenNineRadial 5 1 1) := by native_decide
    have hqR :
        (sevenNineRadial 0 1 0 : ℝ)^2 + (sevenNineRadial 5 1 1 : ℝ)^2 - (sevenNineDistanceLower[4]! : ℝ)^2 ≤
          (sevenNineCosUpper[19]! : ℝ) * (2 * (sevenNineRadial 0 1 0 : ℝ) * (sevenNineRadial 5 1 1 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 0 1 0 : ℝ)^2 + (sevenNineRadial 5 1 1 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 0 1 0 : ℝ)^2 + (sevenNineRadial 5 1 1 : ℝ)^2 - (sevenNineDistanceLower[4]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h10 : (sevenNineRadial 0 1 1 : ℝ)^2 + (sevenNineRadial 5 1 0 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[19]! : ℝ) * (2 * (sevenNineRadial 0 1 1 : ℝ) * (sevenNineRadial 5 1 0 : ℝ)) := by
    have hq : (sevenNineRadial 0 1 1)^2 + (sevenNineRadial 5 1 0)^2 - sevenNineDistanceLower[4]!^2 ≤
        sevenNineCosUpper[19]! * (2 * sevenNineRadial 0 1 1 * sevenNineRadial 5 1 0) := by native_decide
    have hqR :
        (sevenNineRadial 0 1 1 : ℝ)^2 + (sevenNineRadial 5 1 0 : ℝ)^2 - (sevenNineDistanceLower[4]! : ℝ)^2 ≤
          (sevenNineCosUpper[19]! : ℝ) * (2 * (sevenNineRadial 0 1 1 : ℝ) * (sevenNineRadial 5 1 0 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 0 1 1 : ℝ)^2 + (sevenNineRadial 5 1 0 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 0 1 1 : ℝ)^2 + (sevenNineRadial 5 1 0 : ℝ)^2 - (sevenNineDistanceLower[4]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h11 : (sevenNineRadial 0 1 1 : ℝ)^2 + (sevenNineRadial 5 1 1 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[19]! : ℝ) * (2 * (sevenNineRadial 0 1 1 : ℝ) * (sevenNineRadial 5 1 1 : ℝ)) := by
    have hq : (sevenNineRadial 0 1 1)^2 + (sevenNineRadial 5 1 1)^2 - sevenNineDistanceLower[4]!^2 ≤
        sevenNineCosUpper[19]! * (2 * sevenNineRadial 0 1 1 * sevenNineRadial 5 1 1) := by native_decide
    have hqR :
        (sevenNineRadial 0 1 1 : ℝ)^2 + (sevenNineRadial 5 1 1 : ℝ)^2 - (sevenNineDistanceLower[4]! : ℝ)^2 ≤
          (sevenNineCosUpper[19]! : ℝ) * (2 * (sevenNineRadial 0 1 1 : ℝ) * (sevenNineRadial 5 1 1 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 0 1 1 : ℝ)^2 + (sevenNineRadial 5 1 1 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 0 1 1 : ℝ)^2 + (sevenNineRadial 5 1 1 : ℝ)^2 - (sevenNineDistanceLower[4]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have htouch := corner_touch_cosine_bound haL haU hbL hbU
    (by norm_num [sevenNineRadial, sevenNineRadialBounds])
    (by norm_num [sevenNineRadial, sevenNineRadialBounds]) h00 h01 h10 h11
  have hcos : (sevenNineCosUpper[19]! : ℝ) ≤ Real.cos ((94601649157061464815 : ℝ) / 100000000000000000000) := by
    apply lower_bound_of_taylor_error
      (cosine_taylor_ninety_six_remainder (a := 0) (b := 4) (x := ((94601649157061464815 : ℝ) / 100000000000000000000) )
        (by norm_num) (by constructor <;> norm_num [Real.pi_gt_d20, Real.pi_lt_four]))
    rw [cosine_taylor_ninety_six_at_zero (b := 4) (x := ((94601649157061464815 : ℝ) / 100000000000000000000)) (by norm_num)]
    have hp : (sevenNineCosUpper[19]! : Rat) + (((94601649157061464815 : Rat) / 100000000000000000000) : Rat)^97 / (Nat.factorial 96) ≤
        Finset.sum (Finset.range 49) (fun k => (-1 : Rat)^k * (((94601649157061464815 : Rat) / 100000000000000000000) : Rat)^(2*k) / Nat.factorial (2*k)) := by native_decide
    have hpR : (sevenNineCosUpper[19]! : ℝ) + ((94601649157061464815 : ℝ) / 100000000000000000000)^97 / (Nat.factorial 96) ≤
        Finset.sum (Finset.range 49) (fun k => (-1 : ℝ)^k * ((94601649157061464815 : ℝ) / 100000000000000000000)^(2*k) / Nat.factorial (2*k)) := by
      norm_num [sevenNineCosUpper, Finset.sum_range_succ]
    simpa [sub_zero] using hpR
  have hangle : ((94601649157061464815 : ℝ) / 100000000000000000000) ≤ Real.arccos (touchCosine a b (Real.sqrt 4 + Real.sqrt 9)) := by
    exact angle_lower_bound_of_cosine (by norm_num)
      (by
        calc
          ((94601649157061464815 : ℝ) / 100000000000000000000) ≤ (314159265358979323846 : ℝ) / 100000000000000000000 := by norm_num
          _ ≤ Real.pi := by
            have hpi := Real.pi_gt_d20.le
            norm_num at hpi ⊢
            exact hpi) (le_trans htouch hcos)
  have hdata : sevenNineAngleLower[19]! = ((94601649157061464815 : Rat) / 100000000000000000000) := by native_decide
  have hdataR : (sevenNineAngleLower[19]! : ℝ) = ((94601649157061464815 : ℝ) / 100000000000000000000) := by
    have h := congrArg (fun q : Rat => (q : ℝ)) hdata
    convert h using 1 ; norm_num
  rw [hdataR]
  exact hangle

theorem sevenNineAngle_0_6_0_0 {a b : ℝ}
    (haL : (sevenNineRadial 0 0 0 : ℝ) ≤ a) (haU : a ≤ (sevenNineRadial 0 0 1 : ℝ))
    (hbL : (sevenNineRadial 6 0 0 : ℝ) ≤ b) (hbU : b ≤ (sevenNineRadial 6 0 1 : ℝ)) :
    (sevenNineAngleLower[20]! : ℝ) ≤ Real.arccos (touchCosine a b (Real.sqrt 4 + Real.sqrt 10)) := by
  let d : ℝ := Real.sqrt 4 + Real.sqrt 10
  have hd' : (((5162277660168379331998893544432718533719555139325216826857504852792594438639238221344248108 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) : ℝ) ≤ d := by
    dsimp [d]
    have h := rat_sum_sqrt_lower (q := ((5162277660168379331998893544432718533719555139325216826857504852792594438639238221344248108 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (qi := ((2 : Rat) / 1)) (qj := ((3162277660168379331998893544432718533719555139325216826857504852792594438639238221344248108379300295187347284152840055148 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))
      (ni := 4) (nj := 10)
      (by convert sqrt_lower_4 using 1 ; norm_num)
      (by convert sqrt_lower_10 using 1 ; norm_num)
      (by native_decide)
    convert h using 1 ; norm_num
  have hd : (((5162277660168379331998893544432718533719555139325216826857504852792594438639238221344248108 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) ≤ d := by exact hd'
  have hd2 : (((5162277660168379331998893544432718533719555139325216826857504852792594438639238221344248108 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))^2 ≤ d^2 := by
    have hq : (0 : ℝ) ≤ ((5162277660168379331998893544432718533719555139325216826857504852792594438639238221344248108 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) := by norm_num
    have hdn : 0 ≤ d := by positivity
    exact (sq_le_sq₀ hq hdn).mpr hd
  have hd2' : (sevenNineDistanceLower[5]! : ℝ)^2 ≤ d^2 := by
    convert hd2 using 1 ; norm_num [sevenNineDistanceLower]
  have h00 : (sevenNineRadial 0 0 0 : ℝ)^2 + (sevenNineRadial 6 0 0 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[20]! : ℝ) * (2 * (sevenNineRadial 0 0 0 : ℝ) * (sevenNineRadial 6 0 0 : ℝ)) := by
    have hq : (sevenNineRadial 0 0 0)^2 + (sevenNineRadial 6 0 0)^2 - sevenNineDistanceLower[5]!^2 ≤
        sevenNineCosUpper[20]! * (2 * sevenNineRadial 0 0 0 * sevenNineRadial 6 0 0) := by native_decide
    have hqR :
        (sevenNineRadial 0 0 0 : ℝ)^2 + (sevenNineRadial 6 0 0 : ℝ)^2 - (sevenNineDistanceLower[5]! : ℝ)^2 ≤
          (sevenNineCosUpper[20]! : ℝ) * (2 * (sevenNineRadial 0 0 0 : ℝ) * (sevenNineRadial 6 0 0 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 0 0 0 : ℝ)^2 + (sevenNineRadial 6 0 0 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 0 0 0 : ℝ)^2 + (sevenNineRadial 6 0 0 : ℝ)^2 - (sevenNineDistanceLower[5]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h01 : (sevenNineRadial 0 0 0 : ℝ)^2 + (sevenNineRadial 6 0 1 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[20]! : ℝ) * (2 * (sevenNineRadial 0 0 0 : ℝ) * (sevenNineRadial 6 0 1 : ℝ)) := by
    have hq : (sevenNineRadial 0 0 0)^2 + (sevenNineRadial 6 0 1)^2 - sevenNineDistanceLower[5]!^2 ≤
        sevenNineCosUpper[20]! * (2 * sevenNineRadial 0 0 0 * sevenNineRadial 6 0 1) := by native_decide
    have hqR :
        (sevenNineRadial 0 0 0 : ℝ)^2 + (sevenNineRadial 6 0 1 : ℝ)^2 - (sevenNineDistanceLower[5]! : ℝ)^2 ≤
          (sevenNineCosUpper[20]! : ℝ) * (2 * (sevenNineRadial 0 0 0 : ℝ) * (sevenNineRadial 6 0 1 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 0 0 0 : ℝ)^2 + (sevenNineRadial 6 0 1 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 0 0 0 : ℝ)^2 + (sevenNineRadial 6 0 1 : ℝ)^2 - (sevenNineDistanceLower[5]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h10 : (sevenNineRadial 0 0 1 : ℝ)^2 + (sevenNineRadial 6 0 0 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[20]! : ℝ) * (2 * (sevenNineRadial 0 0 1 : ℝ) * (sevenNineRadial 6 0 0 : ℝ)) := by
    have hq : (sevenNineRadial 0 0 1)^2 + (sevenNineRadial 6 0 0)^2 - sevenNineDistanceLower[5]!^2 ≤
        sevenNineCosUpper[20]! * (2 * sevenNineRadial 0 0 1 * sevenNineRadial 6 0 0) := by native_decide
    have hqR :
        (sevenNineRadial 0 0 1 : ℝ)^2 + (sevenNineRadial 6 0 0 : ℝ)^2 - (sevenNineDistanceLower[5]! : ℝ)^2 ≤
          (sevenNineCosUpper[20]! : ℝ) * (2 * (sevenNineRadial 0 0 1 : ℝ) * (sevenNineRadial 6 0 0 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 0 0 1 : ℝ)^2 + (sevenNineRadial 6 0 0 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 0 0 1 : ℝ)^2 + (sevenNineRadial 6 0 0 : ℝ)^2 - (sevenNineDistanceLower[5]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h11 : (sevenNineRadial 0 0 1 : ℝ)^2 + (sevenNineRadial 6 0 1 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[20]! : ℝ) * (2 * (sevenNineRadial 0 0 1 : ℝ) * (sevenNineRadial 6 0 1 : ℝ)) := by
    have hq : (sevenNineRadial 0 0 1)^2 + (sevenNineRadial 6 0 1)^2 - sevenNineDistanceLower[5]!^2 ≤
        sevenNineCosUpper[20]! * (2 * sevenNineRadial 0 0 1 * sevenNineRadial 6 0 1) := by native_decide
    have hqR :
        (sevenNineRadial 0 0 1 : ℝ)^2 + (sevenNineRadial 6 0 1 : ℝ)^2 - (sevenNineDistanceLower[5]! : ℝ)^2 ≤
          (sevenNineCosUpper[20]! : ℝ) * (2 * (sevenNineRadial 0 0 1 : ℝ) * (sevenNineRadial 6 0 1 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 0 0 1 : ℝ)^2 + (sevenNineRadial 6 0 1 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 0 0 1 : ℝ)^2 + (sevenNineRadial 6 0 1 : ℝ)^2 - (sevenNineDistanceLower[5]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have htouch := corner_touch_cosine_bound haL haU hbL hbU
    (by norm_num [sevenNineRadial, sevenNineRadialBounds])
    (by norm_num [sevenNineRadial, sevenNineRadialBounds]) h00 h01 h10 h11
  have hcos : (sevenNineCosUpper[20]! : ℝ) ≤ Real.cos ((198574562116655987359 : ℝ) / 100000000000000000000) := by
    apply lower_bound_of_taylor_error
      (cosine_taylor_ninety_six_remainder (a := 0) (b := 4) (x := ((198574562116655987359 : ℝ) / 100000000000000000000) )
        (by norm_num) (by constructor <;> norm_num [Real.pi_gt_d20, Real.pi_lt_four]))
    rw [cosine_taylor_ninety_six_at_zero (b := 4) (x := ((198574562116655987359 : ℝ) / 100000000000000000000)) (by norm_num)]
    have hp : (sevenNineCosUpper[20]! : Rat) + (((198574562116655987359 : Rat) / 100000000000000000000) : Rat)^97 / (Nat.factorial 96) ≤
        Finset.sum (Finset.range 49) (fun k => (-1 : Rat)^k * (((198574562116655987359 : Rat) / 100000000000000000000) : Rat)^(2*k) / Nat.factorial (2*k)) := by native_decide
    have hpR : (sevenNineCosUpper[20]! : ℝ) + ((198574562116655987359 : ℝ) / 100000000000000000000)^97 / (Nat.factorial 96) ≤
        Finset.sum (Finset.range 49) (fun k => (-1 : ℝ)^k * ((198574562116655987359 : ℝ) / 100000000000000000000)^(2*k) / Nat.factorial (2*k)) := by
      norm_num [sevenNineCosUpper, Finset.sum_range_succ]
    simpa [sub_zero] using hpR
  have hangle : ((198574562116655987359 : ℝ) / 100000000000000000000) ≤ Real.arccos (touchCosine a b (Real.sqrt 4 + Real.sqrt 10)) := by
    exact angle_lower_bound_of_cosine (by norm_num)
      (by
        calc
          ((198574562116655987359 : ℝ) / 100000000000000000000) ≤ (314159265358979323846 : ℝ) / 100000000000000000000 := by norm_num
          _ ≤ Real.pi := by
            have hpi := Real.pi_gt_d20.le
            norm_num at hpi ⊢
            exact hpi) (le_trans htouch hcos)
  have hdata : sevenNineAngleLower[20]! = ((198574562116655987359 : Rat) / 100000000000000000000) := by native_decide
  have hdataR : (sevenNineAngleLower[20]! : ℝ) = ((198574562116655987359 : ℝ) / 100000000000000000000) := by
    have h := congrArg (fun q : Rat => (q : ℝ)) hdata
    convert h using 1 ; norm_num
  rw [hdataR]
  exact hangle

theorem sevenNineAngle_0_6_0_1 {a b : ℝ}
    (haL : (sevenNineRadial 0 0 0 : ℝ) ≤ a) (haU : a ≤ (sevenNineRadial 0 0 1 : ℝ))
    (hbL : (sevenNineRadial 6 1 0 : ℝ) ≤ b) (hbU : b ≤ (sevenNineRadial 6 1 1 : ℝ)) :
    (sevenNineAngleLower[21]! : ℝ) ≤ Real.arccos (touchCosine a b (Real.sqrt 4 + Real.sqrt 10)) := by
  let d : ℝ := Real.sqrt 4 + Real.sqrt 10
  have hd' : (((5162277660168379331998893544432718533719555139325216826857504852792594438639238221344248108 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) : ℝ) ≤ d := by
    dsimp [d]
    have h := rat_sum_sqrt_lower (q := ((5162277660168379331998893544432718533719555139325216826857504852792594438639238221344248108 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (qi := ((2 : Rat) / 1)) (qj := ((3162277660168379331998893544432718533719555139325216826857504852792594438639238221344248108379300295187347284152840055148 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))
      (ni := 4) (nj := 10)
      (by convert sqrt_lower_4 using 1 ; norm_num)
      (by convert sqrt_lower_10 using 1 ; norm_num)
      (by native_decide)
    convert h using 1 ; norm_num
  have hd : (((5162277660168379331998893544432718533719555139325216826857504852792594438639238221344248108 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) ≤ d := by exact hd'
  have hd2 : (((5162277660168379331998893544432718533719555139325216826857504852792594438639238221344248108 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))^2 ≤ d^2 := by
    have hq : (0 : ℝ) ≤ ((5162277660168379331998893544432718533719555139325216826857504852792594438639238221344248108 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) := by norm_num
    have hdn : 0 ≤ d := by positivity
    exact (sq_le_sq₀ hq hdn).mpr hd
  have hd2' : (sevenNineDistanceLower[5]! : ℝ)^2 ≤ d^2 := by
    convert hd2 using 1 ; norm_num [sevenNineDistanceLower]
  have h00 : (sevenNineRadial 0 0 0 : ℝ)^2 + (sevenNineRadial 6 1 0 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[21]! : ℝ) * (2 * (sevenNineRadial 0 0 0 : ℝ) * (sevenNineRadial 6 1 0 : ℝ)) := by
    have hq : (sevenNineRadial 0 0 0)^2 + (sevenNineRadial 6 1 0)^2 - sevenNineDistanceLower[5]!^2 ≤
        sevenNineCosUpper[21]! * (2 * sevenNineRadial 0 0 0 * sevenNineRadial 6 1 0) := by native_decide
    have hqR :
        (sevenNineRadial 0 0 0 : ℝ)^2 + (sevenNineRadial 6 1 0 : ℝ)^2 - (sevenNineDistanceLower[5]! : ℝ)^2 ≤
          (sevenNineCosUpper[21]! : ℝ) * (2 * (sevenNineRadial 0 0 0 : ℝ) * (sevenNineRadial 6 1 0 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 0 0 0 : ℝ)^2 + (sevenNineRadial 6 1 0 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 0 0 0 : ℝ)^2 + (sevenNineRadial 6 1 0 : ℝ)^2 - (sevenNineDistanceLower[5]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h01 : (sevenNineRadial 0 0 0 : ℝ)^2 + (sevenNineRadial 6 1 1 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[21]! : ℝ) * (2 * (sevenNineRadial 0 0 0 : ℝ) * (sevenNineRadial 6 1 1 : ℝ)) := by
    have hq : (sevenNineRadial 0 0 0)^2 + (sevenNineRadial 6 1 1)^2 - sevenNineDistanceLower[5]!^2 ≤
        sevenNineCosUpper[21]! * (2 * sevenNineRadial 0 0 0 * sevenNineRadial 6 1 1) := by native_decide
    have hqR :
        (sevenNineRadial 0 0 0 : ℝ)^2 + (sevenNineRadial 6 1 1 : ℝ)^2 - (sevenNineDistanceLower[5]! : ℝ)^2 ≤
          (sevenNineCosUpper[21]! : ℝ) * (2 * (sevenNineRadial 0 0 0 : ℝ) * (sevenNineRadial 6 1 1 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 0 0 0 : ℝ)^2 + (sevenNineRadial 6 1 1 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 0 0 0 : ℝ)^2 + (sevenNineRadial 6 1 1 : ℝ)^2 - (sevenNineDistanceLower[5]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h10 : (sevenNineRadial 0 0 1 : ℝ)^2 + (sevenNineRadial 6 1 0 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[21]! : ℝ) * (2 * (sevenNineRadial 0 0 1 : ℝ) * (sevenNineRadial 6 1 0 : ℝ)) := by
    have hq : (sevenNineRadial 0 0 1)^2 + (sevenNineRadial 6 1 0)^2 - sevenNineDistanceLower[5]!^2 ≤
        sevenNineCosUpper[21]! * (2 * sevenNineRadial 0 0 1 * sevenNineRadial 6 1 0) := by native_decide
    have hqR :
        (sevenNineRadial 0 0 1 : ℝ)^2 + (sevenNineRadial 6 1 0 : ℝ)^2 - (sevenNineDistanceLower[5]! : ℝ)^2 ≤
          (sevenNineCosUpper[21]! : ℝ) * (2 * (sevenNineRadial 0 0 1 : ℝ) * (sevenNineRadial 6 1 0 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 0 0 1 : ℝ)^2 + (sevenNineRadial 6 1 0 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 0 0 1 : ℝ)^2 + (sevenNineRadial 6 1 0 : ℝ)^2 - (sevenNineDistanceLower[5]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h11 : (sevenNineRadial 0 0 1 : ℝ)^2 + (sevenNineRadial 6 1 1 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[21]! : ℝ) * (2 * (sevenNineRadial 0 0 1 : ℝ) * (sevenNineRadial 6 1 1 : ℝ)) := by
    have hq : (sevenNineRadial 0 0 1)^2 + (sevenNineRadial 6 1 1)^2 - sevenNineDistanceLower[5]!^2 ≤
        sevenNineCosUpper[21]! * (2 * sevenNineRadial 0 0 1 * sevenNineRadial 6 1 1) := by native_decide
    have hqR :
        (sevenNineRadial 0 0 1 : ℝ)^2 + (sevenNineRadial 6 1 1 : ℝ)^2 - (sevenNineDistanceLower[5]! : ℝ)^2 ≤
          (sevenNineCosUpper[21]! : ℝ) * (2 * (sevenNineRadial 0 0 1 : ℝ) * (sevenNineRadial 6 1 1 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 0 0 1 : ℝ)^2 + (sevenNineRadial 6 1 1 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 0 0 1 : ℝ)^2 + (sevenNineRadial 6 1 1 : ℝ)^2 - (sevenNineDistanceLower[5]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have htouch := corner_touch_cosine_bound haL haU hbL hbU
    (by norm_num [sevenNineRadial, sevenNineRadialBounds])
    (by norm_num [sevenNineRadial, sevenNineRadialBounds]) h00 h01 h10 h11
  have hcos : (sevenNineCosUpper[21]! : ℝ) ≤ Real.cos ((137610641327047287093 : ℝ) / 100000000000000000000) := by
    apply lower_bound_of_taylor_error
      (cosine_taylor_ninety_six_remainder (a := 0) (b := 4) (x := ((137610641327047287093 : ℝ) / 100000000000000000000) )
        (by norm_num) (by constructor <;> norm_num [Real.pi_gt_d20, Real.pi_lt_four]))
    rw [cosine_taylor_ninety_six_at_zero (b := 4) (x := ((137610641327047287093 : ℝ) / 100000000000000000000)) (by norm_num)]
    have hp : (sevenNineCosUpper[21]! : Rat) + (((137610641327047287093 : Rat) / 100000000000000000000) : Rat)^97 / (Nat.factorial 96) ≤
        Finset.sum (Finset.range 49) (fun k => (-1 : Rat)^k * (((137610641327047287093 : Rat) / 100000000000000000000) : Rat)^(2*k) / Nat.factorial (2*k)) := by native_decide
    have hpR : (sevenNineCosUpper[21]! : ℝ) + ((137610641327047287093 : ℝ) / 100000000000000000000)^97 / (Nat.factorial 96) ≤
        Finset.sum (Finset.range 49) (fun k => (-1 : ℝ)^k * ((137610641327047287093 : ℝ) / 100000000000000000000)^(2*k) / Nat.factorial (2*k)) := by
      norm_num [sevenNineCosUpper, Finset.sum_range_succ]
    simpa [sub_zero] using hpR
  have hangle : ((137610641327047287093 : ℝ) / 100000000000000000000) ≤ Real.arccos (touchCosine a b (Real.sqrt 4 + Real.sqrt 10)) := by
    exact angle_lower_bound_of_cosine (by norm_num)
      (by
        calc
          ((137610641327047287093 : ℝ) / 100000000000000000000) ≤ (314159265358979323846 : ℝ) / 100000000000000000000 := by norm_num
          _ ≤ Real.pi := by
            have hpi := Real.pi_gt_d20.le
            norm_num at hpi ⊢
            exact hpi) (le_trans htouch hcos)
  have hdata : sevenNineAngleLower[21]! = ((137610641327047287093 : Rat) / 100000000000000000000) := by native_decide
  have hdataR : (sevenNineAngleLower[21]! : ℝ) = ((137610641327047287093 : ℝ) / 100000000000000000000) := by
    have h := congrArg (fun q : Rat => (q : ℝ)) hdata
    convert h using 1 ; norm_num
  rw [hdataR]
  exact hangle

theorem sevenNineAngle_0_6_1_0 {a b : ℝ}
    (haL : (sevenNineRadial 0 1 0 : ℝ) ≤ a) (haU : a ≤ (sevenNineRadial 0 1 1 : ℝ))
    (hbL : (sevenNineRadial 6 0 0 : ℝ) ≤ b) (hbU : b ≤ (sevenNineRadial 6 0 1 : ℝ)) :
    (sevenNineAngleLower[22]! : ℝ) ≤ Real.arccos (touchCosine a b (Real.sqrt 4 + Real.sqrt 10)) := by
  let d : ℝ := Real.sqrt 4 + Real.sqrt 10
  have hd' : (((5162277660168379331998893544432718533719555139325216826857504852792594438639238221344248108 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) : ℝ) ≤ d := by
    dsimp [d]
    have h := rat_sum_sqrt_lower (q := ((5162277660168379331998893544432718533719555139325216826857504852792594438639238221344248108 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (qi := ((2 : Rat) / 1)) (qj := ((3162277660168379331998893544432718533719555139325216826857504852792594438639238221344248108379300295187347284152840055148 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))
      (ni := 4) (nj := 10)
      (by convert sqrt_lower_4 using 1 ; norm_num)
      (by convert sqrt_lower_10 using 1 ; norm_num)
      (by native_decide)
    convert h using 1 ; norm_num
  have hd : (((5162277660168379331998893544432718533719555139325216826857504852792594438639238221344248108 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) ≤ d := by exact hd'
  have hd2 : (((5162277660168379331998893544432718533719555139325216826857504852792594438639238221344248108 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))^2 ≤ d^2 := by
    have hq : (0 : ℝ) ≤ ((5162277660168379331998893544432718533719555139325216826857504852792594438639238221344248108 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) := by norm_num
    have hdn : 0 ≤ d := by positivity
    exact (sq_le_sq₀ hq hdn).mpr hd
  have hd2' : (sevenNineDistanceLower[5]! : ℝ)^2 ≤ d^2 := by
    convert hd2 using 1 ; norm_num [sevenNineDistanceLower]
  have h00 : (sevenNineRadial 0 1 0 : ℝ)^2 + (sevenNineRadial 6 0 0 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[22]! : ℝ) * (2 * (sevenNineRadial 0 1 0 : ℝ) * (sevenNineRadial 6 0 0 : ℝ)) := by
    have hq : (sevenNineRadial 0 1 0)^2 + (sevenNineRadial 6 0 0)^2 - sevenNineDistanceLower[5]!^2 ≤
        sevenNineCosUpper[22]! * (2 * sevenNineRadial 0 1 0 * sevenNineRadial 6 0 0) := by native_decide
    have hqR :
        (sevenNineRadial 0 1 0 : ℝ)^2 + (sevenNineRadial 6 0 0 : ℝ)^2 - (sevenNineDistanceLower[5]! : ℝ)^2 ≤
          (sevenNineCosUpper[22]! : ℝ) * (2 * (sevenNineRadial 0 1 0 : ℝ) * (sevenNineRadial 6 0 0 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 0 1 0 : ℝ)^2 + (sevenNineRadial 6 0 0 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 0 1 0 : ℝ)^2 + (sevenNineRadial 6 0 0 : ℝ)^2 - (sevenNineDistanceLower[5]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h01 : (sevenNineRadial 0 1 0 : ℝ)^2 + (sevenNineRadial 6 0 1 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[22]! : ℝ) * (2 * (sevenNineRadial 0 1 0 : ℝ) * (sevenNineRadial 6 0 1 : ℝ)) := by
    have hq : (sevenNineRadial 0 1 0)^2 + (sevenNineRadial 6 0 1)^2 - sevenNineDistanceLower[5]!^2 ≤
        sevenNineCosUpper[22]! * (2 * sevenNineRadial 0 1 0 * sevenNineRadial 6 0 1) := by native_decide
    have hqR :
        (sevenNineRadial 0 1 0 : ℝ)^2 + (sevenNineRadial 6 0 1 : ℝ)^2 - (sevenNineDistanceLower[5]! : ℝ)^2 ≤
          (sevenNineCosUpper[22]! : ℝ) * (2 * (sevenNineRadial 0 1 0 : ℝ) * (sevenNineRadial 6 0 1 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 0 1 0 : ℝ)^2 + (sevenNineRadial 6 0 1 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 0 1 0 : ℝ)^2 + (sevenNineRadial 6 0 1 : ℝ)^2 - (sevenNineDistanceLower[5]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h10 : (sevenNineRadial 0 1 1 : ℝ)^2 + (sevenNineRadial 6 0 0 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[22]! : ℝ) * (2 * (sevenNineRadial 0 1 1 : ℝ) * (sevenNineRadial 6 0 0 : ℝ)) := by
    have hq : (sevenNineRadial 0 1 1)^2 + (sevenNineRadial 6 0 0)^2 - sevenNineDistanceLower[5]!^2 ≤
        sevenNineCosUpper[22]! * (2 * sevenNineRadial 0 1 1 * sevenNineRadial 6 0 0) := by native_decide
    have hqR :
        (sevenNineRadial 0 1 1 : ℝ)^2 + (sevenNineRadial 6 0 0 : ℝ)^2 - (sevenNineDistanceLower[5]! : ℝ)^2 ≤
          (sevenNineCosUpper[22]! : ℝ) * (2 * (sevenNineRadial 0 1 1 : ℝ) * (sevenNineRadial 6 0 0 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 0 1 1 : ℝ)^2 + (sevenNineRadial 6 0 0 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 0 1 1 : ℝ)^2 + (sevenNineRadial 6 0 0 : ℝ)^2 - (sevenNineDistanceLower[5]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h11 : (sevenNineRadial 0 1 1 : ℝ)^2 + (sevenNineRadial 6 0 1 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[22]! : ℝ) * (2 * (sevenNineRadial 0 1 1 : ℝ) * (sevenNineRadial 6 0 1 : ℝ)) := by
    have hq : (sevenNineRadial 0 1 1)^2 + (sevenNineRadial 6 0 1)^2 - sevenNineDistanceLower[5]!^2 ≤
        sevenNineCosUpper[22]! * (2 * sevenNineRadial 0 1 1 * sevenNineRadial 6 0 1) := by native_decide
    have hqR :
        (sevenNineRadial 0 1 1 : ℝ)^2 + (sevenNineRadial 6 0 1 : ℝ)^2 - (sevenNineDistanceLower[5]! : ℝ)^2 ≤
          (sevenNineCosUpper[22]! : ℝ) * (2 * (sevenNineRadial 0 1 1 : ℝ) * (sevenNineRadial 6 0 1 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 0 1 1 : ℝ)^2 + (sevenNineRadial 6 0 1 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 0 1 1 : ℝ)^2 + (sevenNineRadial 6 0 1 : ℝ)^2 - (sevenNineDistanceLower[5]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have htouch := corner_touch_cosine_bound haL haU hbL hbU
    (by norm_num [sevenNineRadial, sevenNineRadialBounds])
    (by norm_num [sevenNineRadial, sevenNineRadialBounds]) h00 h01 h10 h11
  have hcos : (sevenNineCosUpper[22]! : ℝ) ≤ Real.cos ((85678337709156660566 : ℝ) / 100000000000000000000) := by
    apply lower_bound_of_taylor_error
      (cosine_taylor_ninety_six_remainder (a := 0) (b := 4) (x := ((85678337709156660566 : ℝ) / 100000000000000000000) )
        (by norm_num) (by constructor <;> norm_num [Real.pi_gt_d20, Real.pi_lt_four]))
    rw [cosine_taylor_ninety_six_at_zero (b := 4) (x := ((85678337709156660566 : ℝ) / 100000000000000000000)) (by norm_num)]
    have hp : (sevenNineCosUpper[22]! : Rat) + (((85678337709156660566 : Rat) / 100000000000000000000) : Rat)^97 / (Nat.factorial 96) ≤
        Finset.sum (Finset.range 49) (fun k => (-1 : Rat)^k * (((85678337709156660566 : Rat) / 100000000000000000000) : Rat)^(2*k) / Nat.factorial (2*k)) := by native_decide
    have hpR : (sevenNineCosUpper[22]! : ℝ) + ((85678337709156660566 : ℝ) / 100000000000000000000)^97 / (Nat.factorial 96) ≤
        Finset.sum (Finset.range 49) (fun k => (-1 : ℝ)^k * ((85678337709156660566 : ℝ) / 100000000000000000000)^(2*k) / Nat.factorial (2*k)) := by
      norm_num [sevenNineCosUpper, Finset.sum_range_succ]
    simpa [sub_zero] using hpR
  have hangle : ((85678337709156660566 : ℝ) / 100000000000000000000) ≤ Real.arccos (touchCosine a b (Real.sqrt 4 + Real.sqrt 10)) := by
    exact angle_lower_bound_of_cosine (by norm_num)
      (by
        calc
          ((85678337709156660566 : ℝ) / 100000000000000000000) ≤ (314159265358979323846 : ℝ) / 100000000000000000000 := by norm_num
          _ ≤ Real.pi := by
            have hpi := Real.pi_gt_d20.le
            norm_num at hpi ⊢
            exact hpi) (le_trans htouch hcos)
  have hdata : sevenNineAngleLower[22]! = ((85678337709156660566 : Rat) / 100000000000000000000) := by native_decide
  have hdataR : (sevenNineAngleLower[22]! : ℝ) = ((85678337709156660566 : ℝ) / 100000000000000000000) := by
    have h := congrArg (fun q : Rat => (q : ℝ)) hdata
    convert h using 1 ; norm_num
  rw [hdataR]
  exact hangle

theorem sevenNineAngle_0_6_1_1 {a b : ℝ}
    (haL : (sevenNineRadial 0 1 0 : ℝ) ≤ a) (haU : a ≤ (sevenNineRadial 0 1 1 : ℝ))
    (hbL : (sevenNineRadial 6 1 0 : ℝ) ≤ b) (hbU : b ≤ (sevenNineRadial 6 1 1 : ℝ)) :
    (sevenNineAngleLower[23]! : ℝ) ≤ Real.arccos (touchCosine a b (Real.sqrt 4 + Real.sqrt 10)) := by
  let d : ℝ := Real.sqrt 4 + Real.sqrt 10
  have hd' : (((5162277660168379331998893544432718533719555139325216826857504852792594438639238221344248108 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) : ℝ) ≤ d := by
    dsimp [d]
    have h := rat_sum_sqrt_lower (q := ((5162277660168379331998893544432718533719555139325216826857504852792594438639238221344248108 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (qi := ((2 : Rat) / 1)) (qj := ((3162277660168379331998893544432718533719555139325216826857504852792594438639238221344248108379300295187347284152840055148 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))
      (ni := 4) (nj := 10)
      (by convert sqrt_lower_4 using 1 ; norm_num)
      (by convert sqrt_lower_10 using 1 ; norm_num)
      (by native_decide)
    convert h using 1 ; norm_num
  have hd : (((5162277660168379331998893544432718533719555139325216826857504852792594438639238221344248108 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) ≤ d := by exact hd'
  have hd2 : (((5162277660168379331998893544432718533719555139325216826857504852792594438639238221344248108 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))^2 ≤ d^2 := by
    have hq : (0 : ℝ) ≤ ((5162277660168379331998893544432718533719555139325216826857504852792594438639238221344248108 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) := by norm_num
    have hdn : 0 ≤ d := by positivity
    exact (sq_le_sq₀ hq hdn).mpr hd
  have hd2' : (sevenNineDistanceLower[5]! : ℝ)^2 ≤ d^2 := by
    convert hd2 using 1 ; norm_num [sevenNineDistanceLower]
  have h00 : (sevenNineRadial 0 1 0 : ℝ)^2 + (sevenNineRadial 6 1 0 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[23]! : ℝ) * (2 * (sevenNineRadial 0 1 0 : ℝ) * (sevenNineRadial 6 1 0 : ℝ)) := by
    have hq : (sevenNineRadial 0 1 0)^2 + (sevenNineRadial 6 1 0)^2 - sevenNineDistanceLower[5]!^2 ≤
        sevenNineCosUpper[23]! * (2 * sevenNineRadial 0 1 0 * sevenNineRadial 6 1 0) := by native_decide
    have hqR :
        (sevenNineRadial 0 1 0 : ℝ)^2 + (sevenNineRadial 6 1 0 : ℝ)^2 - (sevenNineDistanceLower[5]! : ℝ)^2 ≤
          (sevenNineCosUpper[23]! : ℝ) * (2 * (sevenNineRadial 0 1 0 : ℝ) * (sevenNineRadial 6 1 0 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 0 1 0 : ℝ)^2 + (sevenNineRadial 6 1 0 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 0 1 0 : ℝ)^2 + (sevenNineRadial 6 1 0 : ℝ)^2 - (sevenNineDistanceLower[5]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h01 : (sevenNineRadial 0 1 0 : ℝ)^2 + (sevenNineRadial 6 1 1 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[23]! : ℝ) * (2 * (sevenNineRadial 0 1 0 : ℝ) * (sevenNineRadial 6 1 1 : ℝ)) := by
    have hq : (sevenNineRadial 0 1 0)^2 + (sevenNineRadial 6 1 1)^2 - sevenNineDistanceLower[5]!^2 ≤
        sevenNineCosUpper[23]! * (2 * sevenNineRadial 0 1 0 * sevenNineRadial 6 1 1) := by native_decide
    have hqR :
        (sevenNineRadial 0 1 0 : ℝ)^2 + (sevenNineRadial 6 1 1 : ℝ)^2 - (sevenNineDistanceLower[5]! : ℝ)^2 ≤
          (sevenNineCosUpper[23]! : ℝ) * (2 * (sevenNineRadial 0 1 0 : ℝ) * (sevenNineRadial 6 1 1 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 0 1 0 : ℝ)^2 + (sevenNineRadial 6 1 1 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 0 1 0 : ℝ)^2 + (sevenNineRadial 6 1 1 : ℝ)^2 - (sevenNineDistanceLower[5]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h10 : (sevenNineRadial 0 1 1 : ℝ)^2 + (sevenNineRadial 6 1 0 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[23]! : ℝ) * (2 * (sevenNineRadial 0 1 1 : ℝ) * (sevenNineRadial 6 1 0 : ℝ)) := by
    have hq : (sevenNineRadial 0 1 1)^2 + (sevenNineRadial 6 1 0)^2 - sevenNineDistanceLower[5]!^2 ≤
        sevenNineCosUpper[23]! * (2 * sevenNineRadial 0 1 1 * sevenNineRadial 6 1 0) := by native_decide
    have hqR :
        (sevenNineRadial 0 1 1 : ℝ)^2 + (sevenNineRadial 6 1 0 : ℝ)^2 - (sevenNineDistanceLower[5]! : ℝ)^2 ≤
          (sevenNineCosUpper[23]! : ℝ) * (2 * (sevenNineRadial 0 1 1 : ℝ) * (sevenNineRadial 6 1 0 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 0 1 1 : ℝ)^2 + (sevenNineRadial 6 1 0 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 0 1 1 : ℝ)^2 + (sevenNineRadial 6 1 0 : ℝ)^2 - (sevenNineDistanceLower[5]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h11 : (sevenNineRadial 0 1 1 : ℝ)^2 + (sevenNineRadial 6 1 1 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[23]! : ℝ) * (2 * (sevenNineRadial 0 1 1 : ℝ) * (sevenNineRadial 6 1 1 : ℝ)) := by
    have hq : (sevenNineRadial 0 1 1)^2 + (sevenNineRadial 6 1 1)^2 - sevenNineDistanceLower[5]!^2 ≤
        sevenNineCosUpper[23]! * (2 * sevenNineRadial 0 1 1 * sevenNineRadial 6 1 1) := by native_decide
    have hqR :
        (sevenNineRadial 0 1 1 : ℝ)^2 + (sevenNineRadial 6 1 1 : ℝ)^2 - (sevenNineDistanceLower[5]! : ℝ)^2 ≤
          (sevenNineCosUpper[23]! : ℝ) * (2 * (sevenNineRadial 0 1 1 : ℝ) * (sevenNineRadial 6 1 1 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 0 1 1 : ℝ)^2 + (sevenNineRadial 6 1 1 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 0 1 1 : ℝ)^2 + (sevenNineRadial 6 1 1 : ℝ)^2 - (sevenNineDistanceLower[5]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have htouch := corner_touch_cosine_bound haL haU hbL hbU
    (by norm_num [sevenNineRadial, sevenNineRadialBounds])
    (by norm_num [sevenNineRadial, sevenNineRadialBounds]) h00 h01 h10 h11
  have hcos : (sevenNineCosUpper[23]! : ℝ) ≤ Real.cos ((99144721329874029450 : ℝ) / 100000000000000000000) := by
    apply lower_bound_of_taylor_error
      (cosine_taylor_ninety_six_remainder (a := 0) (b := 4) (x := ((99144721329874029450 : ℝ) / 100000000000000000000) )
        (by norm_num) (by constructor <;> norm_num [Real.pi_gt_d20, Real.pi_lt_four]))
    rw [cosine_taylor_ninety_six_at_zero (b := 4) (x := ((99144721329874029450 : ℝ) / 100000000000000000000)) (by norm_num)]
    have hp : (sevenNineCosUpper[23]! : Rat) + (((99144721329874029450 : Rat) / 100000000000000000000) : Rat)^97 / (Nat.factorial 96) ≤
        Finset.sum (Finset.range 49) (fun k => (-1 : Rat)^k * (((99144721329874029450 : Rat) / 100000000000000000000) : Rat)^(2*k) / Nat.factorial (2*k)) := by native_decide
    have hpR : (sevenNineCosUpper[23]! : ℝ) + ((99144721329874029450 : ℝ) / 100000000000000000000)^97 / (Nat.factorial 96) ≤
        Finset.sum (Finset.range 49) (fun k => (-1 : ℝ)^k * ((99144721329874029450 : ℝ) / 100000000000000000000)^(2*k) / Nat.factorial (2*k)) := by
      norm_num [sevenNineCosUpper, Finset.sum_range_succ]
    simpa [sub_zero] using hpR
  have hangle : ((99144721329874029450 : ℝ) / 100000000000000000000) ≤ Real.arccos (touchCosine a b (Real.sqrt 4 + Real.sqrt 10)) := by
    exact angle_lower_bound_of_cosine (by norm_num)
      (by
        calc
          ((99144721329874029450 : ℝ) / 100000000000000000000) ≤ (314159265358979323846 : ℝ) / 100000000000000000000 := by norm_num
          _ ≤ Real.pi := by
            have hpi := Real.pi_gt_d20.le
            norm_num at hpi ⊢
            exact hpi) (le_trans htouch hcos)
  have hdata : sevenNineAngleLower[23]! = ((99144721329874029450 : Rat) / 100000000000000000000) := by native_decide
  have hdataR : (sevenNineAngleLower[23]! : ℝ) = ((99144721329874029450 : ℝ) / 100000000000000000000) := by
    have h := congrArg (fun q : Rat => (q : ℝ)) hdata
    convert h using 1 ; norm_num
  rw [hdataR]
  exact hangle

theorem sevenNineAngle_1_2_0_0 {a b : ℝ}
    (haL : (sevenNineRadial 1 0 0 : ℝ) ≤ a) (haU : a ≤ (sevenNineRadial 1 0 1 : ℝ))
    (hbL : (sevenNineRadial 2 0 0 : ℝ) ≤ b) (hbU : b ≤ (sevenNineRadial 2 0 1 : ℝ)) :
    (sevenNineAngleLower[24]! : ℝ) ≤ Real.arccos (touchCosine a b (Real.sqrt 5 + Real.sqrt 6)) := by
  let d : ℝ := Real.sqrt 5 + Real.sqrt 6
  have hd' : (((4685557720282967794606457743437167627406565840268195852703589812661481303095119925954273841 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) : ℝ) ≤ d := by
    dsimp [d]
    have h := rat_sum_sqrt_lower (q := ((4685557720282967794606457743437167627406565840268195852703589812661481303095119925954273841 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (qi := ((2236067977499789696409173668731276235440618359611525724270897245410520925637804899414414408378782274969508176150773783504 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (qj := ((2449489742783178098197284074705891391965947480656670128432692567250960377457315026539859433104640234818594601226614189124 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))
      (ni := 5) (nj := 6)
      (by convert sqrt_lower_5 using 1 ; norm_num)
      (by convert sqrt_lower_6 using 1 ; norm_num)
      (by native_decide)
    convert h using 1 ; norm_num
  have hd : (((4685557720282967794606457743437167627406565840268195852703589812661481303095119925954273841 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) ≤ d := by exact hd'
  have hd2 : (((4685557720282967794606457743437167627406565840268195852703589812661481303095119925954273841 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))^2 ≤ d^2 := by
    have hq : (0 : ℝ) ≤ ((4685557720282967794606457743437167627406565840268195852703589812661481303095119925954273841 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) := by norm_num
    have hdn : 0 ≤ d := by positivity
    exact (sq_le_sq₀ hq hdn).mpr hd
  have hd2' : (sevenNineDistanceLower[6]! : ℝ)^2 ≤ d^2 := by
    convert hd2 using 1 ; norm_num [sevenNineDistanceLower]
  have h00 : (sevenNineRadial 1 0 0 : ℝ)^2 + (sevenNineRadial 2 0 0 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[24]! : ℝ) * (2 * (sevenNineRadial 1 0 0 : ℝ) * (sevenNineRadial 2 0 0 : ℝ)) := by
    have hq : (sevenNineRadial 1 0 0)^2 + (sevenNineRadial 2 0 0)^2 - sevenNineDistanceLower[6]!^2 ≤
        sevenNineCosUpper[24]! * (2 * sevenNineRadial 1 0 0 * sevenNineRadial 2 0 0) := by native_decide
    have hqR :
        (sevenNineRadial 1 0 0 : ℝ)^2 + (sevenNineRadial 2 0 0 : ℝ)^2 - (sevenNineDistanceLower[6]! : ℝ)^2 ≤
          (sevenNineCosUpper[24]! : ℝ) * (2 * (sevenNineRadial 1 0 0 : ℝ) * (sevenNineRadial 2 0 0 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 1 0 0 : ℝ)^2 + (sevenNineRadial 2 0 0 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 1 0 0 : ℝ)^2 + (sevenNineRadial 2 0 0 : ℝ)^2 - (sevenNineDistanceLower[6]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h01 : (sevenNineRadial 1 0 0 : ℝ)^2 + (sevenNineRadial 2 0 1 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[24]! : ℝ) * (2 * (sevenNineRadial 1 0 0 : ℝ) * (sevenNineRadial 2 0 1 : ℝ)) := by
    have hq : (sevenNineRadial 1 0 0)^2 + (sevenNineRadial 2 0 1)^2 - sevenNineDistanceLower[6]!^2 ≤
        sevenNineCosUpper[24]! * (2 * sevenNineRadial 1 0 0 * sevenNineRadial 2 0 1) := by native_decide
    have hqR :
        (sevenNineRadial 1 0 0 : ℝ)^2 + (sevenNineRadial 2 0 1 : ℝ)^2 - (sevenNineDistanceLower[6]! : ℝ)^2 ≤
          (sevenNineCosUpper[24]! : ℝ) * (2 * (sevenNineRadial 1 0 0 : ℝ) * (sevenNineRadial 2 0 1 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 1 0 0 : ℝ)^2 + (sevenNineRadial 2 0 1 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 1 0 0 : ℝ)^2 + (sevenNineRadial 2 0 1 : ℝ)^2 - (sevenNineDistanceLower[6]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h10 : (sevenNineRadial 1 0 1 : ℝ)^2 + (sevenNineRadial 2 0 0 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[24]! : ℝ) * (2 * (sevenNineRadial 1 0 1 : ℝ) * (sevenNineRadial 2 0 0 : ℝ)) := by
    have hq : (sevenNineRadial 1 0 1)^2 + (sevenNineRadial 2 0 0)^2 - sevenNineDistanceLower[6]!^2 ≤
        sevenNineCosUpper[24]! * (2 * sevenNineRadial 1 0 1 * sevenNineRadial 2 0 0) := by native_decide
    have hqR :
        (sevenNineRadial 1 0 1 : ℝ)^2 + (sevenNineRadial 2 0 0 : ℝ)^2 - (sevenNineDistanceLower[6]! : ℝ)^2 ≤
          (sevenNineCosUpper[24]! : ℝ) * (2 * (sevenNineRadial 1 0 1 : ℝ) * (sevenNineRadial 2 0 0 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 1 0 1 : ℝ)^2 + (sevenNineRadial 2 0 0 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 1 0 1 : ℝ)^2 + (sevenNineRadial 2 0 0 : ℝ)^2 - (sevenNineDistanceLower[6]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h11 : (sevenNineRadial 1 0 1 : ℝ)^2 + (sevenNineRadial 2 0 1 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[24]! : ℝ) * (2 * (sevenNineRadial 1 0 1 : ℝ) * (sevenNineRadial 2 0 1 : ℝ)) := by
    have hq : (sevenNineRadial 1 0 1)^2 + (sevenNineRadial 2 0 1)^2 - sevenNineDistanceLower[6]!^2 ≤
        sevenNineCosUpper[24]! * (2 * sevenNineRadial 1 0 1 * sevenNineRadial 2 0 1) := by native_decide
    have hqR :
        (sevenNineRadial 1 0 1 : ℝ)^2 + (sevenNineRadial 2 0 1 : ℝ)^2 - (sevenNineDistanceLower[6]! : ℝ)^2 ≤
          (sevenNineCosUpper[24]! : ℝ) * (2 * (sevenNineRadial 1 0 1 : ℝ) * (sevenNineRadial 2 0 1 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 1 0 1 : ℝ)^2 + (sevenNineRadial 2 0 1 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 1 0 1 : ℝ)^2 + (sevenNineRadial 2 0 1 : ℝ)^2 - (sevenNineDistanceLower[6]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have htouch := corner_touch_cosine_bound haL haU hbL hbU
    (by norm_num [sevenNineRadial, sevenNineRadialBounds])
    (by norm_num [sevenNineRadial, sevenNineRadialBounds]) h00 h01 h10 h11
  have hcos : (sevenNineCosUpper[24]! : ℝ) ≤ Real.cos ((166867509334536827348 : ℝ) / 100000000000000000000) := by
    apply lower_bound_of_taylor_error
      (cosine_taylor_ninety_six_remainder (a := 0) (b := 4) (x := ((166867509334536827348 : ℝ) / 100000000000000000000) )
        (by norm_num) (by constructor <;> norm_num [Real.pi_gt_d20, Real.pi_lt_four]))
    rw [cosine_taylor_ninety_six_at_zero (b := 4) (x := ((166867509334536827348 : ℝ) / 100000000000000000000)) (by norm_num)]
    have hp : (sevenNineCosUpper[24]! : Rat) + (((166867509334536827348 : Rat) / 100000000000000000000) : Rat)^97 / (Nat.factorial 96) ≤
        Finset.sum (Finset.range 49) (fun k => (-1 : Rat)^k * (((166867509334536827348 : Rat) / 100000000000000000000) : Rat)^(2*k) / Nat.factorial (2*k)) := by native_decide
    have hpR : (sevenNineCosUpper[24]! : ℝ) + ((166867509334536827348 : ℝ) / 100000000000000000000)^97 / (Nat.factorial 96) ≤
        Finset.sum (Finset.range 49) (fun k => (-1 : ℝ)^k * ((166867509334536827348 : ℝ) / 100000000000000000000)^(2*k) / Nat.factorial (2*k)) := by
      norm_num [sevenNineCosUpper, Finset.sum_range_succ]
    simpa [sub_zero] using hpR
  have hangle : ((166867509334536827348 : ℝ) / 100000000000000000000) ≤ Real.arccos (touchCosine a b (Real.sqrt 5 + Real.sqrt 6)) := by
    exact angle_lower_bound_of_cosine (by norm_num)
      (by
        calc
          ((166867509334536827348 : ℝ) / 100000000000000000000) ≤ (314159265358979323846 : ℝ) / 100000000000000000000 := by norm_num
          _ ≤ Real.pi := by
            have hpi := Real.pi_gt_d20.le
            norm_num at hpi ⊢
            exact hpi) (le_trans htouch hcos)
  have hdata : sevenNineAngleLower[24]! = ((166867509334536827348 : Rat) / 100000000000000000000) := by native_decide
  have hdataR : (sevenNineAngleLower[24]! : ℝ) = ((166867509334536827348 : ℝ) / 100000000000000000000) := by
    have h := congrArg (fun q : Rat => (q : ℝ)) hdata
    convert h using 1 ; norm_num
  rw [hdataR]
  exact hangle

theorem sevenNineAngle_1_2_1_1 {a b : ℝ}
    (haL : (sevenNineRadial 1 1 0 : ℝ) ≤ a) (haU : a ≤ (sevenNineRadial 1 1 1 : ℝ))
    (hbL : (sevenNineRadial 2 1 0 : ℝ) ≤ b) (hbU : b ≤ (sevenNineRadial 2 1 1 : ℝ)) :
    (sevenNineAngleLower[27]! : ℝ) ≤ Real.arccos (touchCosine a b (Real.sqrt 5 + Real.sqrt 6)) := by
  let d : ℝ := Real.sqrt 5 + Real.sqrt 6
  have hd' : (((4685557720282967794606457743437167627406565840268195852703589812661481303095119925954273841 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) : ℝ) ≤ d := by
    dsimp [d]
    have h := rat_sum_sqrt_lower (q := ((4685557720282967794606457743437167627406565840268195852703589812661481303095119925954273841 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (qi := ((2236067977499789696409173668731276235440618359611525724270897245410520925637804899414414408378782274969508176150773783504 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (qj := ((2449489742783178098197284074705891391965947480656670128432692567250960377457315026539859433104640234818594601226614189124 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))
      (ni := 5) (nj := 6)
      (by convert sqrt_lower_5 using 1 ; norm_num)
      (by convert sqrt_lower_6 using 1 ; norm_num)
      (by native_decide)
    convert h using 1 ; norm_num
  have hd : (((4685557720282967794606457743437167627406565840268195852703589812661481303095119925954273841 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) ≤ d := by exact hd'
  have hd2 : (((4685557720282967794606457743437167627406565840268195852703589812661481303095119925954273841 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))^2 ≤ d^2 := by
    have hq : (0 : ℝ) ≤ ((4685557720282967794606457743437167627406565840268195852703589812661481303095119925954273841 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) := by norm_num
    have hdn : 0 ≤ d := by positivity
    exact (sq_le_sq₀ hq hdn).mpr hd
  have hd2' : (sevenNineDistanceLower[6]! : ℝ)^2 ≤ d^2 := by
    convert hd2 using 1 ; norm_num [sevenNineDistanceLower]
  have h00 : (sevenNineRadial 1 1 0 : ℝ)^2 + (sevenNineRadial 2 1 0 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[27]! : ℝ) * (2 * (sevenNineRadial 1 1 0 : ℝ) * (sevenNineRadial 2 1 0 : ℝ)) := by
    have hq : (sevenNineRadial 1 1 0)^2 + (sevenNineRadial 2 1 0)^2 - sevenNineDistanceLower[6]!^2 ≤
        sevenNineCosUpper[27]! * (2 * sevenNineRadial 1 1 0 * sevenNineRadial 2 1 0) := by native_decide
    have hqR :
        (sevenNineRadial 1 1 0 : ℝ)^2 + (sevenNineRadial 2 1 0 : ℝ)^2 - (sevenNineDistanceLower[6]! : ℝ)^2 ≤
          (sevenNineCosUpper[27]! : ℝ) * (2 * (sevenNineRadial 1 1 0 : ℝ) * (sevenNineRadial 2 1 0 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 1 1 0 : ℝ)^2 + (sevenNineRadial 2 1 0 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 1 1 0 : ℝ)^2 + (sevenNineRadial 2 1 0 : ℝ)^2 - (sevenNineDistanceLower[6]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h01 : (sevenNineRadial 1 1 0 : ℝ)^2 + (sevenNineRadial 2 1 1 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[27]! : ℝ) * (2 * (sevenNineRadial 1 1 0 : ℝ) * (sevenNineRadial 2 1 1 : ℝ)) := by
    have hq : (sevenNineRadial 1 1 0)^2 + (sevenNineRadial 2 1 1)^2 - sevenNineDistanceLower[6]!^2 ≤
        sevenNineCosUpper[27]! * (2 * sevenNineRadial 1 1 0 * sevenNineRadial 2 1 1) := by native_decide
    have hqR :
        (sevenNineRadial 1 1 0 : ℝ)^2 + (sevenNineRadial 2 1 1 : ℝ)^2 - (sevenNineDistanceLower[6]! : ℝ)^2 ≤
          (sevenNineCosUpper[27]! : ℝ) * (2 * (sevenNineRadial 1 1 0 : ℝ) * (sevenNineRadial 2 1 1 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 1 1 0 : ℝ)^2 + (sevenNineRadial 2 1 1 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 1 1 0 : ℝ)^2 + (sevenNineRadial 2 1 1 : ℝ)^2 - (sevenNineDistanceLower[6]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h10 : (sevenNineRadial 1 1 1 : ℝ)^2 + (sevenNineRadial 2 1 0 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[27]! : ℝ) * (2 * (sevenNineRadial 1 1 1 : ℝ) * (sevenNineRadial 2 1 0 : ℝ)) := by
    have hq : (sevenNineRadial 1 1 1)^2 + (sevenNineRadial 2 1 0)^2 - sevenNineDistanceLower[6]!^2 ≤
        sevenNineCosUpper[27]! * (2 * sevenNineRadial 1 1 1 * sevenNineRadial 2 1 0) := by native_decide
    have hqR :
        (sevenNineRadial 1 1 1 : ℝ)^2 + (sevenNineRadial 2 1 0 : ℝ)^2 - (sevenNineDistanceLower[6]! : ℝ)^2 ≤
          (sevenNineCosUpper[27]! : ℝ) * (2 * (sevenNineRadial 1 1 1 : ℝ) * (sevenNineRadial 2 1 0 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 1 1 1 : ℝ)^2 + (sevenNineRadial 2 1 0 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 1 1 1 : ℝ)^2 + (sevenNineRadial 2 1 0 : ℝ)^2 - (sevenNineDistanceLower[6]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h11 : (sevenNineRadial 1 1 1 : ℝ)^2 + (sevenNineRadial 2 1 1 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[27]! : ℝ) * (2 * (sevenNineRadial 1 1 1 : ℝ) * (sevenNineRadial 2 1 1 : ℝ)) := by
    have hq : (sevenNineRadial 1 1 1)^2 + (sevenNineRadial 2 1 1)^2 - sevenNineDistanceLower[6]!^2 ≤
        sevenNineCosUpper[27]! * (2 * sevenNineRadial 1 1 1 * sevenNineRadial 2 1 1) := by native_decide
    have hqR :
        (sevenNineRadial 1 1 1 : ℝ)^2 + (sevenNineRadial 2 1 1 : ℝ)^2 - (sevenNineDistanceLower[6]! : ℝ)^2 ≤
          (sevenNineCosUpper[27]! : ℝ) * (2 * (sevenNineRadial 1 1 1 : ℝ) * (sevenNineRadial 2 1 1 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 1 1 1 : ℝ)^2 + (sevenNineRadial 2 1 1 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 1 1 1 : ℝ)^2 + (sevenNineRadial 2 1 1 : ℝ)^2 - (sevenNineDistanceLower[6]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have htouch := corner_touch_cosine_bound haL haU hbL hbU
    (by norm_num [sevenNineRadial, sevenNineRadialBounds])
    (by norm_num [sevenNineRadial, sevenNineRadialBounds]) h00 h01 h10 h11
  have hcos : (sevenNineCosUpper[27]! : ℝ) ≤ Real.cos ((86956670812230797312 : ℝ) / 100000000000000000000) := by
    apply lower_bound_of_taylor_error
      (cosine_taylor_ninety_six_remainder (a := 0) (b := 4) (x := ((86956670812230797312 : ℝ) / 100000000000000000000) )
        (by norm_num) (by constructor <;> norm_num [Real.pi_gt_d20, Real.pi_lt_four]))
    rw [cosine_taylor_ninety_six_at_zero (b := 4) (x := ((86956670812230797312 : ℝ) / 100000000000000000000)) (by norm_num)]
    have hp : (sevenNineCosUpper[27]! : Rat) + (((86956670812230797312 : Rat) / 100000000000000000000) : Rat)^97 / (Nat.factorial 96) ≤
        Finset.sum (Finset.range 49) (fun k => (-1 : Rat)^k * (((86956670812230797312 : Rat) / 100000000000000000000) : Rat)^(2*k) / Nat.factorial (2*k)) := by native_decide
    have hpR : (sevenNineCosUpper[27]! : ℝ) + ((86956670812230797312 : ℝ) / 100000000000000000000)^97 / (Nat.factorial 96) ≤
        Finset.sum (Finset.range 49) (fun k => (-1 : ℝ)^k * ((86956670812230797312 : ℝ) / 100000000000000000000)^(2*k) / Nat.factorial (2*k)) := by
      norm_num [sevenNineCosUpper, Finset.sum_range_succ]
    simpa [sub_zero] using hpR
  have hangle : ((86956670812230797312 : ℝ) / 100000000000000000000) ≤ Real.arccos (touchCosine a b (Real.sqrt 5 + Real.sqrt 6)) := by
    exact angle_lower_bound_of_cosine (by norm_num)
      (by
        calc
          ((86956670812230797312 : ℝ) / 100000000000000000000) ≤ (314159265358979323846 : ℝ) / 100000000000000000000 := by norm_num
          _ ≤ Real.pi := by
            have hpi := Real.pi_gt_d20.le
            norm_num at hpi ⊢
            exact hpi) (le_trans htouch hcos)
  have hdata : sevenNineAngleLower[27]! = ((86956670812230797312 : Rat) / 100000000000000000000) := by native_decide
  have hdataR : (sevenNineAngleLower[27]! : ℝ) = ((86956670812230797312 : ℝ) / 100000000000000000000) := by
    have h := congrArg (fun q : Rat => (q : ℝ)) hdata
    convert h using 1 ; norm_num
  rw [hdataR]
  exact hangle

theorem sevenNineAngle_1_3_0_0 {a b : ℝ}
    (haL : (sevenNineRadial 1 0 0 : ℝ) ≤ a) (haU : a ≤ (sevenNineRadial 1 0 1 : ℝ))
    (hbL : (sevenNineRadial 3 0 0 : ℝ) ≤ b) (hbU : b ≤ (sevenNineRadial 3 0 1 : ℝ)) :
    (sevenNineAngleLower[28]! : ℝ) ≤ Real.arccos (touchCosine a b (Real.sqrt 5 + Real.sqrt 7)) := by
  let d : ℝ := Real.sqrt 5 + Real.sqrt 7
  have hd' : (((4881819288564380286910789422370536661150877542693975904639231704611589748868088527174807294 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) : ℝ) ≤ d := by
    dsimp [d]
    have h := rat_sum_sqrt_lower (q := ((4881819288564380286910789422370536661150877542693975904639231704611589748868088527174807294 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (qi := ((2236067977499789696409173668731276235440618359611525724270897245410520925637804899414414408378782274969508176150773783504 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (qj := ((2645751311064590590501615753639260425710259183082450180368334459201068823230283627760392886474543610615064578338497463095 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))
      (ni := 5) (nj := 7)
      (by convert sqrt_lower_5 using 1 ; norm_num)
      (by convert sqrt_lower_7 using 1 ; norm_num)
      (by native_decide)
    convert h using 1 ; norm_num
  have hd : (((4881819288564380286910789422370536661150877542693975904639231704611589748868088527174807294 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) ≤ d := by exact hd'
  have hd2 : (((4881819288564380286910789422370536661150877542693975904639231704611589748868088527174807294 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))^2 ≤ d^2 := by
    have hq : (0 : ℝ) ≤ ((4881819288564380286910789422370536661150877542693975904639231704611589748868088527174807294 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) := by norm_num
    have hdn : 0 ≤ d := by positivity
    exact (sq_le_sq₀ hq hdn).mpr hd
  have hd2' : (sevenNineDistanceLower[7]! : ℝ)^2 ≤ d^2 := by
    convert hd2 using 1 ; norm_num [sevenNineDistanceLower]
  have h00 : (sevenNineRadial 1 0 0 : ℝ)^2 + (sevenNineRadial 3 0 0 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[28]! : ℝ) * (2 * (sevenNineRadial 1 0 0 : ℝ) * (sevenNineRadial 3 0 0 : ℝ)) := by
    have hq : (sevenNineRadial 1 0 0)^2 + (sevenNineRadial 3 0 0)^2 - sevenNineDistanceLower[7]!^2 ≤
        sevenNineCosUpper[28]! * (2 * sevenNineRadial 1 0 0 * sevenNineRadial 3 0 0) := by native_decide
    have hqR :
        (sevenNineRadial 1 0 0 : ℝ)^2 + (sevenNineRadial 3 0 0 : ℝ)^2 - (sevenNineDistanceLower[7]! : ℝ)^2 ≤
          (sevenNineCosUpper[28]! : ℝ) * (2 * (sevenNineRadial 1 0 0 : ℝ) * (sevenNineRadial 3 0 0 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 1 0 0 : ℝ)^2 + (sevenNineRadial 3 0 0 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 1 0 0 : ℝ)^2 + (sevenNineRadial 3 0 0 : ℝ)^2 - (sevenNineDistanceLower[7]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h01 : (sevenNineRadial 1 0 0 : ℝ)^2 + (sevenNineRadial 3 0 1 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[28]! : ℝ) * (2 * (sevenNineRadial 1 0 0 : ℝ) * (sevenNineRadial 3 0 1 : ℝ)) := by
    have hq : (sevenNineRadial 1 0 0)^2 + (sevenNineRadial 3 0 1)^2 - sevenNineDistanceLower[7]!^2 ≤
        sevenNineCosUpper[28]! * (2 * sevenNineRadial 1 0 0 * sevenNineRadial 3 0 1) := by native_decide
    have hqR :
        (sevenNineRadial 1 0 0 : ℝ)^2 + (sevenNineRadial 3 0 1 : ℝ)^2 - (sevenNineDistanceLower[7]! : ℝ)^2 ≤
          (sevenNineCosUpper[28]! : ℝ) * (2 * (sevenNineRadial 1 0 0 : ℝ) * (sevenNineRadial 3 0 1 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 1 0 0 : ℝ)^2 + (sevenNineRadial 3 0 1 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 1 0 0 : ℝ)^2 + (sevenNineRadial 3 0 1 : ℝ)^2 - (sevenNineDistanceLower[7]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h10 : (sevenNineRadial 1 0 1 : ℝ)^2 + (sevenNineRadial 3 0 0 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[28]! : ℝ) * (2 * (sevenNineRadial 1 0 1 : ℝ) * (sevenNineRadial 3 0 0 : ℝ)) := by
    have hq : (sevenNineRadial 1 0 1)^2 + (sevenNineRadial 3 0 0)^2 - sevenNineDistanceLower[7]!^2 ≤
        sevenNineCosUpper[28]! * (2 * sevenNineRadial 1 0 1 * sevenNineRadial 3 0 0) := by native_decide
    have hqR :
        (sevenNineRadial 1 0 1 : ℝ)^2 + (sevenNineRadial 3 0 0 : ℝ)^2 - (sevenNineDistanceLower[7]! : ℝ)^2 ≤
          (sevenNineCosUpper[28]! : ℝ) * (2 * (sevenNineRadial 1 0 1 : ℝ) * (sevenNineRadial 3 0 0 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 1 0 1 : ℝ)^2 + (sevenNineRadial 3 0 0 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 1 0 1 : ℝ)^2 + (sevenNineRadial 3 0 0 : ℝ)^2 - (sevenNineDistanceLower[7]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h11 : (sevenNineRadial 1 0 1 : ℝ)^2 + (sevenNineRadial 3 0 1 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[28]! : ℝ) * (2 * (sevenNineRadial 1 0 1 : ℝ) * (sevenNineRadial 3 0 1 : ℝ)) := by
    have hq : (sevenNineRadial 1 0 1)^2 + (sevenNineRadial 3 0 1)^2 - sevenNineDistanceLower[7]!^2 ≤
        sevenNineCosUpper[28]! * (2 * sevenNineRadial 1 0 1 * sevenNineRadial 3 0 1) := by native_decide
    have hqR :
        (sevenNineRadial 1 0 1 : ℝ)^2 + (sevenNineRadial 3 0 1 : ℝ)^2 - (sevenNineDistanceLower[7]! : ℝ)^2 ≤
          (sevenNineCosUpper[28]! : ℝ) * (2 * (sevenNineRadial 1 0 1 : ℝ) * (sevenNineRadial 3 0 1 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 1 0 1 : ℝ)^2 + (sevenNineRadial 3 0 1 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 1 0 1 : ℝ)^2 + (sevenNineRadial 3 0 1 : ℝ)^2 - (sevenNineDistanceLower[7]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have htouch := corner_touch_cosine_bound haL haU hbL hbU
    (by norm_num [sevenNineRadial, sevenNineRadialBounds])
    (by norm_num [sevenNineRadial, sevenNineRadialBounds]) h00 h01 h10 h11
  have hcos : (sevenNineCosUpper[28]! : ℝ) ≤ Real.cos ((176359654625550122144 : ℝ) / 100000000000000000000) := by
    apply lower_bound_of_taylor_error
      (cosine_taylor_ninety_six_remainder (a := 0) (b := 4) (x := ((176359654625550122144 : ℝ) / 100000000000000000000) )
        (by norm_num) (by constructor <;> norm_num [Real.pi_gt_d20, Real.pi_lt_four]))
    rw [cosine_taylor_ninety_six_at_zero (b := 4) (x := ((176359654625550122144 : ℝ) / 100000000000000000000)) (by norm_num)]
    have hp : (sevenNineCosUpper[28]! : Rat) + (((176359654625550122144 : Rat) / 100000000000000000000) : Rat)^97 / (Nat.factorial 96) ≤
        Finset.sum (Finset.range 49) (fun k => (-1 : Rat)^k * (((176359654625550122144 : Rat) / 100000000000000000000) : Rat)^(2*k) / Nat.factorial (2*k)) := by native_decide
    have hpR : (sevenNineCosUpper[28]! : ℝ) + ((176359654625550122144 : ℝ) / 100000000000000000000)^97 / (Nat.factorial 96) ≤
        Finset.sum (Finset.range 49) (fun k => (-1 : ℝ)^k * ((176359654625550122144 : ℝ) / 100000000000000000000)^(2*k) / Nat.factorial (2*k)) := by
      norm_num [sevenNineCosUpper, Finset.sum_range_succ]
    simpa [sub_zero] using hpR
  have hangle : ((176359654625550122144 : ℝ) / 100000000000000000000) ≤ Real.arccos (touchCosine a b (Real.sqrt 5 + Real.sqrt 7)) := by
    exact angle_lower_bound_of_cosine (by norm_num)
      (by
        calc
          ((176359654625550122144 : ℝ) / 100000000000000000000) ≤ (314159265358979323846 : ℝ) / 100000000000000000000 := by norm_num
          _ ≤ Real.pi := by
            have hpi := Real.pi_gt_d20.le
            norm_num at hpi ⊢
            exact hpi) (le_trans htouch hcos)
  have hdata : sevenNineAngleLower[28]! = ((176359654625550122144 : Rat) / 100000000000000000000) := by native_decide
  have hdataR : (sevenNineAngleLower[28]! : ℝ) = ((176359654625550122144 : ℝ) / 100000000000000000000) := by
    have h := congrArg (fun q : Rat => (q : ℝ)) hdata
    convert h using 1 ; norm_num
  rw [hdataR]
  exact hangle

theorem sevenNineAngle_1_3_0_1 {a b : ℝ}
    (haL : (sevenNineRadial 1 0 0 : ℝ) ≤ a) (haU : a ≤ (sevenNineRadial 1 0 1 : ℝ))
    (hbL : (sevenNineRadial 3 1 0 : ℝ) ≤ b) (hbU : b ≤ (sevenNineRadial 3 1 1 : ℝ)) :
    (sevenNineAngleLower[29]! : ℝ) ≤ Real.arccos (touchCosine a b (Real.sqrt 5 + Real.sqrt 7)) := by
  let d : ℝ := Real.sqrt 5 + Real.sqrt 7
  have hd' : (((4881819288564380286910789422370536661150877542693975904639231704611589748868088527174807294 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) : ℝ) ≤ d := by
    dsimp [d]
    have h := rat_sum_sqrt_lower (q := ((4881819288564380286910789422370536661150877542693975904639231704611589748868088527174807294 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (qi := ((2236067977499789696409173668731276235440618359611525724270897245410520925637804899414414408378782274969508176150773783504 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (qj := ((2645751311064590590501615753639260425710259183082450180368334459201068823230283627760392886474543610615064578338497463095 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))
      (ni := 5) (nj := 7)
      (by convert sqrt_lower_5 using 1 ; norm_num)
      (by convert sqrt_lower_7 using 1 ; norm_num)
      (by native_decide)
    convert h using 1 ; norm_num
  have hd : (((4881819288564380286910789422370536661150877542693975904639231704611589748868088527174807294 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) ≤ d := by exact hd'
  have hd2 : (((4881819288564380286910789422370536661150877542693975904639231704611589748868088527174807294 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))^2 ≤ d^2 := by
    have hq : (0 : ℝ) ≤ ((4881819288564380286910789422370536661150877542693975904639231704611589748868088527174807294 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) := by norm_num
    have hdn : 0 ≤ d := by positivity
    exact (sq_le_sq₀ hq hdn).mpr hd
  have hd2' : (sevenNineDistanceLower[7]! : ℝ)^2 ≤ d^2 := by
    convert hd2 using 1 ; norm_num [sevenNineDistanceLower]
  have h00 : (sevenNineRadial 1 0 0 : ℝ)^2 + (sevenNineRadial 3 1 0 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[29]! : ℝ) * (2 * (sevenNineRadial 1 0 0 : ℝ) * (sevenNineRadial 3 1 0 : ℝ)) := by
    have hq : (sevenNineRadial 1 0 0)^2 + (sevenNineRadial 3 1 0)^2 - sevenNineDistanceLower[7]!^2 ≤
        sevenNineCosUpper[29]! * (2 * sevenNineRadial 1 0 0 * sevenNineRadial 3 1 0) := by native_decide
    have hqR :
        (sevenNineRadial 1 0 0 : ℝ)^2 + (sevenNineRadial 3 1 0 : ℝ)^2 - (sevenNineDistanceLower[7]! : ℝ)^2 ≤
          (sevenNineCosUpper[29]! : ℝ) * (2 * (sevenNineRadial 1 0 0 : ℝ) * (sevenNineRadial 3 1 0 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 1 0 0 : ℝ)^2 + (sevenNineRadial 3 1 0 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 1 0 0 : ℝ)^2 + (sevenNineRadial 3 1 0 : ℝ)^2 - (sevenNineDistanceLower[7]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h01 : (sevenNineRadial 1 0 0 : ℝ)^2 + (sevenNineRadial 3 1 1 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[29]! : ℝ) * (2 * (sevenNineRadial 1 0 0 : ℝ) * (sevenNineRadial 3 1 1 : ℝ)) := by
    have hq : (sevenNineRadial 1 0 0)^2 + (sevenNineRadial 3 1 1)^2 - sevenNineDistanceLower[7]!^2 ≤
        sevenNineCosUpper[29]! * (2 * sevenNineRadial 1 0 0 * sevenNineRadial 3 1 1) := by native_decide
    have hqR :
        (sevenNineRadial 1 0 0 : ℝ)^2 + (sevenNineRadial 3 1 1 : ℝ)^2 - (sevenNineDistanceLower[7]! : ℝ)^2 ≤
          (sevenNineCosUpper[29]! : ℝ) * (2 * (sevenNineRadial 1 0 0 : ℝ) * (sevenNineRadial 3 1 1 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 1 0 0 : ℝ)^2 + (sevenNineRadial 3 1 1 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 1 0 0 : ℝ)^2 + (sevenNineRadial 3 1 1 : ℝ)^2 - (sevenNineDistanceLower[7]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h10 : (sevenNineRadial 1 0 1 : ℝ)^2 + (sevenNineRadial 3 1 0 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[29]! : ℝ) * (2 * (sevenNineRadial 1 0 1 : ℝ) * (sevenNineRadial 3 1 0 : ℝ)) := by
    have hq : (sevenNineRadial 1 0 1)^2 + (sevenNineRadial 3 1 0)^2 - sevenNineDistanceLower[7]!^2 ≤
        sevenNineCosUpper[29]! * (2 * sevenNineRadial 1 0 1 * sevenNineRadial 3 1 0) := by native_decide
    have hqR :
        (sevenNineRadial 1 0 1 : ℝ)^2 + (sevenNineRadial 3 1 0 : ℝ)^2 - (sevenNineDistanceLower[7]! : ℝ)^2 ≤
          (sevenNineCosUpper[29]! : ℝ) * (2 * (sevenNineRadial 1 0 1 : ℝ) * (sevenNineRadial 3 1 0 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 1 0 1 : ℝ)^2 + (sevenNineRadial 3 1 0 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 1 0 1 : ℝ)^2 + (sevenNineRadial 3 1 0 : ℝ)^2 - (sevenNineDistanceLower[7]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h11 : (sevenNineRadial 1 0 1 : ℝ)^2 + (sevenNineRadial 3 1 1 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[29]! : ℝ) * (2 * (sevenNineRadial 1 0 1 : ℝ) * (sevenNineRadial 3 1 1 : ℝ)) := by
    have hq : (sevenNineRadial 1 0 1)^2 + (sevenNineRadial 3 1 1)^2 - sevenNineDistanceLower[7]!^2 ≤
        sevenNineCosUpper[29]! * (2 * sevenNineRadial 1 0 1 * sevenNineRadial 3 1 1) := by native_decide
    have hqR :
        (sevenNineRadial 1 0 1 : ℝ)^2 + (sevenNineRadial 3 1 1 : ℝ)^2 - (sevenNineDistanceLower[7]! : ℝ)^2 ≤
          (sevenNineCosUpper[29]! : ℝ) * (2 * (sevenNineRadial 1 0 1 : ℝ) * (sevenNineRadial 3 1 1 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 1 0 1 : ℝ)^2 + (sevenNineRadial 3 1 1 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 1 0 1 : ℝ)^2 + (sevenNineRadial 3 1 1 : ℝ)^2 - (sevenNineDistanceLower[7]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have htouch := corner_touch_cosine_bound haL haU hbL hbU
    (by norm_num [sevenNineRadial, sevenNineRadialBounds])
    (by norm_num [sevenNineRadial, sevenNineRadialBounds]) h00 h01 h10 h11
  have hcos : (sevenNineCosUpper[29]! : ℝ) ≤ Real.cos ((91896876052246885190 : ℝ) / 100000000000000000000) := by
    apply lower_bound_of_taylor_error
      (cosine_taylor_ninety_six_remainder (a := 0) (b := 4) (x := ((91896876052246885190 : ℝ) / 100000000000000000000) )
        (by norm_num) (by constructor <;> norm_num [Real.pi_gt_d20, Real.pi_lt_four]))
    rw [cosine_taylor_ninety_six_at_zero (b := 4) (x := ((91896876052246885190 : ℝ) / 100000000000000000000)) (by norm_num)]
    have hp : (sevenNineCosUpper[29]! : Rat) + (((91896876052246885190 : Rat) / 100000000000000000000) : Rat)^97 / (Nat.factorial 96) ≤
        Finset.sum (Finset.range 49) (fun k => (-1 : Rat)^k * (((91896876052246885190 : Rat) / 100000000000000000000) : Rat)^(2*k) / Nat.factorial (2*k)) := by native_decide
    have hpR : (sevenNineCosUpper[29]! : ℝ) + ((91896876052246885190 : ℝ) / 100000000000000000000)^97 / (Nat.factorial 96) ≤
        Finset.sum (Finset.range 49) (fun k => (-1 : ℝ)^k * ((91896876052246885190 : ℝ) / 100000000000000000000)^(2*k) / Nat.factorial (2*k)) := by
      norm_num [sevenNineCosUpper, Finset.sum_range_succ]
    simpa [sub_zero] using hpR
  have hangle : ((91896876052246885190 : ℝ) / 100000000000000000000) ≤ Real.arccos (touchCosine a b (Real.sqrt 5 + Real.sqrt 7)) := by
    exact angle_lower_bound_of_cosine (by norm_num)
      (by
        calc
          ((91896876052246885190 : ℝ) / 100000000000000000000) ≤ (314159265358979323846 : ℝ) / 100000000000000000000 := by norm_num
          _ ≤ Real.pi := by
            have hpi := Real.pi_gt_d20.le
            norm_num at hpi ⊢
            exact hpi) (le_trans htouch hcos)
  have hdata : sevenNineAngleLower[29]! = ((91896876052246885190 : Rat) / 100000000000000000000) := by native_decide
  have hdataR : (sevenNineAngleLower[29]! : ℝ) = ((91896876052246885190 : ℝ) / 100000000000000000000) := by
    have h := congrArg (fun q : Rat => (q : ℝ)) hdata
    convert h using 1 ; norm_num
  rw [hdataR]
  exact hangle

theorem sevenNineAngle_1_3_1_0 {a b : ℝ}
    (haL : (sevenNineRadial 1 1 0 : ℝ) ≤ a) (haU : a ≤ (sevenNineRadial 1 1 1 : ℝ))
    (hbL : (sevenNineRadial 3 0 0 : ℝ) ≤ b) (hbU : b ≤ (sevenNineRadial 3 0 1 : ℝ)) :
    (sevenNineAngleLower[30]! : ℝ) ≤ Real.arccos (touchCosine a b (Real.sqrt 5 + Real.sqrt 7)) := by
  let d : ℝ := Real.sqrt 5 + Real.sqrt 7
  have hd' : (((4881819288564380286910789422370536661150877542693975904639231704611589748868088527174807294 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) : ℝ) ≤ d := by
    dsimp [d]
    have h := rat_sum_sqrt_lower (q := ((4881819288564380286910789422370536661150877542693975904639231704611589748868088527174807294 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (qi := ((2236067977499789696409173668731276235440618359611525724270897245410520925637804899414414408378782274969508176150773783504 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (qj := ((2645751311064590590501615753639260425710259183082450180368334459201068823230283627760392886474543610615064578338497463095 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))
      (ni := 5) (nj := 7)
      (by convert sqrt_lower_5 using 1 ; norm_num)
      (by convert sqrt_lower_7 using 1 ; norm_num)
      (by native_decide)
    convert h using 1 ; norm_num
  have hd : (((4881819288564380286910789422370536661150877542693975904639231704611589748868088527174807294 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) ≤ d := by exact hd'
  have hd2 : (((4881819288564380286910789422370536661150877542693975904639231704611589748868088527174807294 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))^2 ≤ d^2 := by
    have hq : (0 : ℝ) ≤ ((4881819288564380286910789422370536661150877542693975904639231704611589748868088527174807294 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) := by norm_num
    have hdn : 0 ≤ d := by positivity
    exact (sq_le_sq₀ hq hdn).mpr hd
  have hd2' : (sevenNineDistanceLower[7]! : ℝ)^2 ≤ d^2 := by
    convert hd2 using 1 ; norm_num [sevenNineDistanceLower]
  have h00 : (sevenNineRadial 1 1 0 : ℝ)^2 + (sevenNineRadial 3 0 0 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[30]! : ℝ) * (2 * (sevenNineRadial 1 1 0 : ℝ) * (sevenNineRadial 3 0 0 : ℝ)) := by
    have hq : (sevenNineRadial 1 1 0)^2 + (sevenNineRadial 3 0 0)^2 - sevenNineDistanceLower[7]!^2 ≤
        sevenNineCosUpper[30]! * (2 * sevenNineRadial 1 1 0 * sevenNineRadial 3 0 0) := by native_decide
    have hqR :
        (sevenNineRadial 1 1 0 : ℝ)^2 + (sevenNineRadial 3 0 0 : ℝ)^2 - (sevenNineDistanceLower[7]! : ℝ)^2 ≤
          (sevenNineCosUpper[30]! : ℝ) * (2 * (sevenNineRadial 1 1 0 : ℝ) * (sevenNineRadial 3 0 0 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 1 1 0 : ℝ)^2 + (sevenNineRadial 3 0 0 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 1 1 0 : ℝ)^2 + (sevenNineRadial 3 0 0 : ℝ)^2 - (sevenNineDistanceLower[7]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h01 : (sevenNineRadial 1 1 0 : ℝ)^2 + (sevenNineRadial 3 0 1 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[30]! : ℝ) * (2 * (sevenNineRadial 1 1 0 : ℝ) * (sevenNineRadial 3 0 1 : ℝ)) := by
    have hq : (sevenNineRadial 1 1 0)^2 + (sevenNineRadial 3 0 1)^2 - sevenNineDistanceLower[7]!^2 ≤
        sevenNineCosUpper[30]! * (2 * sevenNineRadial 1 1 0 * sevenNineRadial 3 0 1) := by native_decide
    have hqR :
        (sevenNineRadial 1 1 0 : ℝ)^2 + (sevenNineRadial 3 0 1 : ℝ)^2 - (sevenNineDistanceLower[7]! : ℝ)^2 ≤
          (sevenNineCosUpper[30]! : ℝ) * (2 * (sevenNineRadial 1 1 0 : ℝ) * (sevenNineRadial 3 0 1 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 1 1 0 : ℝ)^2 + (sevenNineRadial 3 0 1 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 1 1 0 : ℝ)^2 + (sevenNineRadial 3 0 1 : ℝ)^2 - (sevenNineDistanceLower[7]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h10 : (sevenNineRadial 1 1 1 : ℝ)^2 + (sevenNineRadial 3 0 0 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[30]! : ℝ) * (2 * (sevenNineRadial 1 1 1 : ℝ) * (sevenNineRadial 3 0 0 : ℝ)) := by
    have hq : (sevenNineRadial 1 1 1)^2 + (sevenNineRadial 3 0 0)^2 - sevenNineDistanceLower[7]!^2 ≤
        sevenNineCosUpper[30]! * (2 * sevenNineRadial 1 1 1 * sevenNineRadial 3 0 0) := by native_decide
    have hqR :
        (sevenNineRadial 1 1 1 : ℝ)^2 + (sevenNineRadial 3 0 0 : ℝ)^2 - (sevenNineDistanceLower[7]! : ℝ)^2 ≤
          (sevenNineCosUpper[30]! : ℝ) * (2 * (sevenNineRadial 1 1 1 : ℝ) * (sevenNineRadial 3 0 0 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 1 1 1 : ℝ)^2 + (sevenNineRadial 3 0 0 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 1 1 1 : ℝ)^2 + (sevenNineRadial 3 0 0 : ℝ)^2 - (sevenNineDistanceLower[7]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h11 : (sevenNineRadial 1 1 1 : ℝ)^2 + (sevenNineRadial 3 0 1 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[30]! : ℝ) * (2 * (sevenNineRadial 1 1 1 : ℝ) * (sevenNineRadial 3 0 1 : ℝ)) := by
    have hq : (sevenNineRadial 1 1 1)^2 + (sevenNineRadial 3 0 1)^2 - sevenNineDistanceLower[7]!^2 ≤
        sevenNineCosUpper[30]! * (2 * sevenNineRadial 1 1 1 * sevenNineRadial 3 0 1) := by native_decide
    have hqR :
        (sevenNineRadial 1 1 1 : ℝ)^2 + (sevenNineRadial 3 0 1 : ℝ)^2 - (sevenNineDistanceLower[7]! : ℝ)^2 ≤
          (sevenNineCosUpper[30]! : ℝ) * (2 * (sevenNineRadial 1 1 1 : ℝ) * (sevenNineRadial 3 0 1 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 1 1 1 : ℝ)^2 + (sevenNineRadial 3 0 1 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 1 1 1 : ℝ)^2 + (sevenNineRadial 3 0 1 : ℝ)^2 - (sevenNineDistanceLower[7]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have htouch := corner_touch_cosine_bound haL haU hbL hbU
    (by norm_num [sevenNineRadial, sevenNineRadialBounds])
    (by norm_num [sevenNineRadial, sevenNineRadialBounds]) h00 h01 h10 h11
  have hcos : (sevenNineCosUpper[30]! : ℝ) ≤ Real.cos ((68444665522847992508 : ℝ) / 100000000000000000000) := by
    apply lower_bound_of_taylor_error
      (cosine_taylor_ninety_six_remainder (a := 0) (b := 4) (x := ((68444665522847992508 : ℝ) / 100000000000000000000) )
        (by norm_num) (by constructor <;> norm_num [Real.pi_gt_d20, Real.pi_lt_four]))
    rw [cosine_taylor_ninety_six_at_zero (b := 4) (x := ((68444665522847992508 : ℝ) / 100000000000000000000)) (by norm_num)]
    have hp : (sevenNineCosUpper[30]! : Rat) + (((68444665522847992508 : Rat) / 100000000000000000000) : Rat)^97 / (Nat.factorial 96) ≤
        Finset.sum (Finset.range 49) (fun k => (-1 : Rat)^k * (((68444665522847992508 : Rat) / 100000000000000000000) : Rat)^(2*k) / Nat.factorial (2*k)) := by native_decide
    have hpR : (sevenNineCosUpper[30]! : ℝ) + ((68444665522847992508 : ℝ) / 100000000000000000000)^97 / (Nat.factorial 96) ≤
        Finset.sum (Finset.range 49) (fun k => (-1 : ℝ)^k * ((68444665522847992508 : ℝ) / 100000000000000000000)^(2*k) / Nat.factorial (2*k)) := by
      norm_num [sevenNineCosUpper, Finset.sum_range_succ]
    simpa [sub_zero] using hpR
  have hangle : ((68444665522847992508 : ℝ) / 100000000000000000000) ≤ Real.arccos (touchCosine a b (Real.sqrt 5 + Real.sqrt 7)) := by
    exact angle_lower_bound_of_cosine (by norm_num)
      (by
        calc
          ((68444665522847992508 : ℝ) / 100000000000000000000) ≤ (314159265358979323846 : ℝ) / 100000000000000000000 := by norm_num
          _ ≤ Real.pi := by
            have hpi := Real.pi_gt_d20.le
            norm_num at hpi ⊢
            exact hpi) (le_trans htouch hcos)
  have hdata : sevenNineAngleLower[30]! = ((68444665522847992508 : Rat) / 100000000000000000000) := by native_decide
  have hdataR : (sevenNineAngleLower[30]! : ℝ) = ((68444665522847992508 : ℝ) / 100000000000000000000) := by
    have h := congrArg (fun q : Rat => (q : ℝ)) hdata
    convert h using 1 ; norm_num
  rw [hdataR]
  exact hangle

theorem sevenNineAngle_1_3_1_1 {a b : ℝ}
    (haL : (sevenNineRadial 1 1 0 : ℝ) ≤ a) (haU : a ≤ (sevenNineRadial 1 1 1 : ℝ))
    (hbL : (sevenNineRadial 3 1 0 : ℝ) ≤ b) (hbU : b ≤ (sevenNineRadial 3 1 1 : ℝ)) :
    (sevenNineAngleLower[31]! : ℝ) ≤ Real.arccos (touchCosine a b (Real.sqrt 5 + Real.sqrt 7)) := by
  let d : ℝ := Real.sqrt 5 + Real.sqrt 7
  have hd' : (((4881819288564380286910789422370536661150877542693975904639231704611589748868088527174807294 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) : ℝ) ≤ d := by
    dsimp [d]
    have h := rat_sum_sqrt_lower (q := ((4881819288564380286910789422370536661150877542693975904639231704611589748868088527174807294 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (qi := ((2236067977499789696409173668731276235440618359611525724270897245410520925637804899414414408378782274969508176150773783504 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (qj := ((2645751311064590590501615753639260425710259183082450180368334459201068823230283627760392886474543610615064578338497463095 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))
      (ni := 5) (nj := 7)
      (by convert sqrt_lower_5 using 1 ; norm_num)
      (by convert sqrt_lower_7 using 1 ; norm_num)
      (by native_decide)
    convert h using 1 ; norm_num
  have hd : (((4881819288564380286910789422370536661150877542693975904639231704611589748868088527174807294 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) ≤ d := by exact hd'
  have hd2 : (((4881819288564380286910789422370536661150877542693975904639231704611589748868088527174807294 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))^2 ≤ d^2 := by
    have hq : (0 : ℝ) ≤ ((4881819288564380286910789422370536661150877542693975904639231704611589748868088527174807294 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) := by norm_num
    have hdn : 0 ≤ d := by positivity
    exact (sq_le_sq₀ hq hdn).mpr hd
  have hd2' : (sevenNineDistanceLower[7]! : ℝ)^2 ≤ d^2 := by
    convert hd2 using 1 ; norm_num [sevenNineDistanceLower]
  have h00 : (sevenNineRadial 1 1 0 : ℝ)^2 + (sevenNineRadial 3 1 0 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[31]! : ℝ) * (2 * (sevenNineRadial 1 1 0 : ℝ) * (sevenNineRadial 3 1 0 : ℝ)) := by
    have hq : (sevenNineRadial 1 1 0)^2 + (sevenNineRadial 3 1 0)^2 - sevenNineDistanceLower[7]!^2 ≤
        sevenNineCosUpper[31]! * (2 * sevenNineRadial 1 1 0 * sevenNineRadial 3 1 0) := by native_decide
    have hqR :
        (sevenNineRadial 1 1 0 : ℝ)^2 + (sevenNineRadial 3 1 0 : ℝ)^2 - (sevenNineDistanceLower[7]! : ℝ)^2 ≤
          (sevenNineCosUpper[31]! : ℝ) * (2 * (sevenNineRadial 1 1 0 : ℝ) * (sevenNineRadial 3 1 0 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 1 1 0 : ℝ)^2 + (sevenNineRadial 3 1 0 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 1 1 0 : ℝ)^2 + (sevenNineRadial 3 1 0 : ℝ)^2 - (sevenNineDistanceLower[7]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h01 : (sevenNineRadial 1 1 0 : ℝ)^2 + (sevenNineRadial 3 1 1 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[31]! : ℝ) * (2 * (sevenNineRadial 1 1 0 : ℝ) * (sevenNineRadial 3 1 1 : ℝ)) := by
    have hq : (sevenNineRadial 1 1 0)^2 + (sevenNineRadial 3 1 1)^2 - sevenNineDistanceLower[7]!^2 ≤
        sevenNineCosUpper[31]! * (2 * sevenNineRadial 1 1 0 * sevenNineRadial 3 1 1) := by native_decide
    have hqR :
        (sevenNineRadial 1 1 0 : ℝ)^2 + (sevenNineRadial 3 1 1 : ℝ)^2 - (sevenNineDistanceLower[7]! : ℝ)^2 ≤
          (sevenNineCosUpper[31]! : ℝ) * (2 * (sevenNineRadial 1 1 0 : ℝ) * (sevenNineRadial 3 1 1 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 1 1 0 : ℝ)^2 + (sevenNineRadial 3 1 1 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 1 1 0 : ℝ)^2 + (sevenNineRadial 3 1 1 : ℝ)^2 - (sevenNineDistanceLower[7]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h10 : (sevenNineRadial 1 1 1 : ℝ)^2 + (sevenNineRadial 3 1 0 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[31]! : ℝ) * (2 * (sevenNineRadial 1 1 1 : ℝ) * (sevenNineRadial 3 1 0 : ℝ)) := by
    have hq : (sevenNineRadial 1 1 1)^2 + (sevenNineRadial 3 1 0)^2 - sevenNineDistanceLower[7]!^2 ≤
        sevenNineCosUpper[31]! * (2 * sevenNineRadial 1 1 1 * sevenNineRadial 3 1 0) := by native_decide
    have hqR :
        (sevenNineRadial 1 1 1 : ℝ)^2 + (sevenNineRadial 3 1 0 : ℝ)^2 - (sevenNineDistanceLower[7]! : ℝ)^2 ≤
          (sevenNineCosUpper[31]! : ℝ) * (2 * (sevenNineRadial 1 1 1 : ℝ) * (sevenNineRadial 3 1 0 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 1 1 1 : ℝ)^2 + (sevenNineRadial 3 1 0 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 1 1 1 : ℝ)^2 + (sevenNineRadial 3 1 0 : ℝ)^2 - (sevenNineDistanceLower[7]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h11 : (sevenNineRadial 1 1 1 : ℝ)^2 + (sevenNineRadial 3 1 1 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[31]! : ℝ) * (2 * (sevenNineRadial 1 1 1 : ℝ) * (sevenNineRadial 3 1 1 : ℝ)) := by
    have hq : (sevenNineRadial 1 1 1)^2 + (sevenNineRadial 3 1 1)^2 - sevenNineDistanceLower[7]!^2 ≤
        sevenNineCosUpper[31]! * (2 * sevenNineRadial 1 1 1 * sevenNineRadial 3 1 1) := by native_decide
    have hqR :
        (sevenNineRadial 1 1 1 : ℝ)^2 + (sevenNineRadial 3 1 1 : ℝ)^2 - (sevenNineDistanceLower[7]! : ℝ)^2 ≤
          (sevenNineCosUpper[31]! : ℝ) * (2 * (sevenNineRadial 1 1 1 : ℝ) * (sevenNineRadial 3 1 1 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 1 1 1 : ℝ)^2 + (sevenNineRadial 3 1 1 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 1 1 1 : ℝ)^2 + (sevenNineRadial 3 1 1 : ℝ)^2 - (sevenNineDistanceLower[7]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have htouch := corner_touch_cosine_bound haL haU hbL hbU
    (by norm_num [sevenNineRadial, sevenNineRadialBounds])
    (by norm_num [sevenNineRadial, sevenNineRadialBounds]) h00 h01 h10 h11
  have hcos : (sevenNineCosUpper[31]! : ℝ) ≤ Real.cos ((92427919726700038310 : ℝ) / 100000000000000000000) := by
    apply lower_bound_of_taylor_error
      (cosine_taylor_ninety_six_remainder (a := 0) (b := 4) (x := ((92427919726700038310 : ℝ) / 100000000000000000000) )
        (by norm_num) (by constructor <;> norm_num [Real.pi_gt_d20, Real.pi_lt_four]))
    rw [cosine_taylor_ninety_six_at_zero (b := 4) (x := ((92427919726700038310 : ℝ) / 100000000000000000000)) (by norm_num)]
    have hp : (sevenNineCosUpper[31]! : Rat) + (((92427919726700038310 : Rat) / 100000000000000000000) : Rat)^97 / (Nat.factorial 96) ≤
        Finset.sum (Finset.range 49) (fun k => (-1 : Rat)^k * (((92427919726700038310 : Rat) / 100000000000000000000) : Rat)^(2*k) / Nat.factorial (2*k)) := by native_decide
    have hpR : (sevenNineCosUpper[31]! : ℝ) + ((92427919726700038310 : ℝ) / 100000000000000000000)^97 / (Nat.factorial 96) ≤
        Finset.sum (Finset.range 49) (fun k => (-1 : ℝ)^k * ((92427919726700038310 : ℝ) / 100000000000000000000)^(2*k) / Nat.factorial (2*k)) := by
      norm_num [sevenNineCosUpper, Finset.sum_range_succ]
    simpa [sub_zero] using hpR
  have hangle : ((92427919726700038310 : ℝ) / 100000000000000000000) ≤ Real.arccos (touchCosine a b (Real.sqrt 5 + Real.sqrt 7)) := by
    exact angle_lower_bound_of_cosine (by norm_num)
      (by
        calc
          ((92427919726700038310 : ℝ) / 100000000000000000000) ≤ (314159265358979323846 : ℝ) / 100000000000000000000 := by norm_num
          _ ≤ Real.pi := by
            have hpi := Real.pi_gt_d20.le
            norm_num at hpi ⊢
            exact hpi) (le_trans htouch hcos)
  have hdata : sevenNineAngleLower[31]! = ((92427919726700038310 : Rat) / 100000000000000000000) := by native_decide
  have hdataR : (sevenNineAngleLower[31]! : ℝ) = ((92427919726700038310 : ℝ) / 100000000000000000000) := by
    have h := congrArg (fun q : Rat => (q : ℝ)) hdata
    convert h using 1 ; norm_num
  rw [hdataR]
  exact hangle

theorem sevenNineAngle_1_4_0_0 {a b : ℝ}
    (haL : (sevenNineRadial 1 0 0 : ℝ) ≤ a) (haU : a ≤ (sevenNineRadial 1 0 1 : ℝ))
    (hbL : (sevenNineRadial 4 0 0 : ℝ) ≤ b) (hbU : b ≤ (sevenNineRadial 4 0 1 : ℝ)) :
    (sevenNineAngleLower[32]! : ℝ) ≤ Real.arccos (touchCosine a b (Real.sqrt 5 + Real.sqrt 8)) := by
  let d : ℝ := Real.sqrt 5 + Real.sqrt 8
  have hd' : (((5064495102245979794012551117150672392579962110365421870624256721391985882562018977115189477 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) : ℝ) ≤ d := by
    dsimp [d]
    have h := rat_sum_sqrt_lower (q := ((5064495102245979794012551117150672392579962110365421870624256721391985882562018977115189477 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (qi := ((2236067977499789696409173668731276235440618359611525724270897245410520925637804899414414408378782274969508176150773783504 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (qj := ((2828427124746190097603377448419396157139343750753896146353359475981464956924214077700775068655283145470027692461824594049 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))
      (ni := 5) (nj := 8)
      (by convert sqrt_lower_5 using 1 ; norm_num)
      (by convert sqrt_lower_8 using 1 ; norm_num)
      (by native_decide)
    convert h using 1 ; norm_num
  have hd : (((5064495102245979794012551117150672392579962110365421870624256721391985882562018977115189477 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) ≤ d := by exact hd'
  have hd2 : (((5064495102245979794012551117150672392579962110365421870624256721391985882562018977115189477 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))^2 ≤ d^2 := by
    have hq : (0 : ℝ) ≤ ((5064495102245979794012551117150672392579962110365421870624256721391985882562018977115189477 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) := by norm_num
    have hdn : 0 ≤ d := by positivity
    exact (sq_le_sq₀ hq hdn).mpr hd
  have hd2' : (sevenNineDistanceLower[8]! : ℝ)^2 ≤ d^2 := by
    convert hd2 using 1 ; norm_num [sevenNineDistanceLower]
  have h00 : (sevenNineRadial 1 0 0 : ℝ)^2 + (sevenNineRadial 4 0 0 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[32]! : ℝ) * (2 * (sevenNineRadial 1 0 0 : ℝ) * (sevenNineRadial 4 0 0 : ℝ)) := by
    have hq : (sevenNineRadial 1 0 0)^2 + (sevenNineRadial 4 0 0)^2 - sevenNineDistanceLower[8]!^2 ≤
        sevenNineCosUpper[32]! * (2 * sevenNineRadial 1 0 0 * sevenNineRadial 4 0 0) := by native_decide
    have hqR :
        (sevenNineRadial 1 0 0 : ℝ)^2 + (sevenNineRadial 4 0 0 : ℝ)^2 - (sevenNineDistanceLower[8]! : ℝ)^2 ≤
          (sevenNineCosUpper[32]! : ℝ) * (2 * (sevenNineRadial 1 0 0 : ℝ) * (sevenNineRadial 4 0 0 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 1 0 0 : ℝ)^2 + (sevenNineRadial 4 0 0 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 1 0 0 : ℝ)^2 + (sevenNineRadial 4 0 0 : ℝ)^2 - (sevenNineDistanceLower[8]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h01 : (sevenNineRadial 1 0 0 : ℝ)^2 + (sevenNineRadial 4 0 1 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[32]! : ℝ) * (2 * (sevenNineRadial 1 0 0 : ℝ) * (sevenNineRadial 4 0 1 : ℝ)) := by
    have hq : (sevenNineRadial 1 0 0)^2 + (sevenNineRadial 4 0 1)^2 - sevenNineDistanceLower[8]!^2 ≤
        sevenNineCosUpper[32]! * (2 * sevenNineRadial 1 0 0 * sevenNineRadial 4 0 1) := by native_decide
    have hqR :
        (sevenNineRadial 1 0 0 : ℝ)^2 + (sevenNineRadial 4 0 1 : ℝ)^2 - (sevenNineDistanceLower[8]! : ℝ)^2 ≤
          (sevenNineCosUpper[32]! : ℝ) * (2 * (sevenNineRadial 1 0 0 : ℝ) * (sevenNineRadial 4 0 1 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 1 0 0 : ℝ)^2 + (sevenNineRadial 4 0 1 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 1 0 0 : ℝ)^2 + (sevenNineRadial 4 0 1 : ℝ)^2 - (sevenNineDistanceLower[8]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h10 : (sevenNineRadial 1 0 1 : ℝ)^2 + (sevenNineRadial 4 0 0 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[32]! : ℝ) * (2 * (sevenNineRadial 1 0 1 : ℝ) * (sevenNineRadial 4 0 0 : ℝ)) := by
    have hq : (sevenNineRadial 1 0 1)^2 + (sevenNineRadial 4 0 0)^2 - sevenNineDistanceLower[8]!^2 ≤
        sevenNineCosUpper[32]! * (2 * sevenNineRadial 1 0 1 * sevenNineRadial 4 0 0) := by native_decide
    have hqR :
        (sevenNineRadial 1 0 1 : ℝ)^2 + (sevenNineRadial 4 0 0 : ℝ)^2 - (sevenNineDistanceLower[8]! : ℝ)^2 ≤
          (sevenNineCosUpper[32]! : ℝ) * (2 * (sevenNineRadial 1 0 1 : ℝ) * (sevenNineRadial 4 0 0 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 1 0 1 : ℝ)^2 + (sevenNineRadial 4 0 0 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 1 0 1 : ℝ)^2 + (sevenNineRadial 4 0 0 : ℝ)^2 - (sevenNineDistanceLower[8]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h11 : (sevenNineRadial 1 0 1 : ℝ)^2 + (sevenNineRadial 4 0 1 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[32]! : ℝ) * (2 * (sevenNineRadial 1 0 1 : ℝ) * (sevenNineRadial 4 0 1 : ℝ)) := by
    have hq : (sevenNineRadial 1 0 1)^2 + (sevenNineRadial 4 0 1)^2 - sevenNineDistanceLower[8]!^2 ≤
        sevenNineCosUpper[32]! * (2 * sevenNineRadial 1 0 1 * sevenNineRadial 4 0 1) := by native_decide
    have hqR :
        (sevenNineRadial 1 0 1 : ℝ)^2 + (sevenNineRadial 4 0 1 : ℝ)^2 - (sevenNineDistanceLower[8]! : ℝ)^2 ≤
          (sevenNineCosUpper[32]! : ℝ) * (2 * (sevenNineRadial 1 0 1 : ℝ) * (sevenNineRadial 4 0 1 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 1 0 1 : ℝ)^2 + (sevenNineRadial 4 0 1 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 1 0 1 : ℝ)^2 + (sevenNineRadial 4 0 1 : ℝ)^2 - (sevenNineDistanceLower[8]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have htouch := corner_touch_cosine_bound haL haU hbL hbU
    (by norm_num [sevenNineRadial, sevenNineRadialBounds])
    (by norm_num [sevenNineRadial, sevenNineRadialBounds]) h00 h01 h10 h11
  have hcos : (sevenNineCosUpper[32]! : ℝ) ≤ Real.cos ((185714923950355442741 : ℝ) / 100000000000000000000) := by
    apply lower_bound_of_taylor_error
      (cosine_taylor_ninety_six_remainder (a := 0) (b := 4) (x := ((185714923950355442741 : ℝ) / 100000000000000000000) )
        (by norm_num) (by constructor <;> norm_num [Real.pi_gt_d20, Real.pi_lt_four]))
    rw [cosine_taylor_ninety_six_at_zero (b := 4) (x := ((185714923950355442741 : ℝ) / 100000000000000000000)) (by norm_num)]
    have hp : (sevenNineCosUpper[32]! : Rat) + (((185714923950355442741 : Rat) / 100000000000000000000) : Rat)^97 / (Nat.factorial 96) ≤
        Finset.sum (Finset.range 49) (fun k => (-1 : Rat)^k * (((185714923950355442741 : Rat) / 100000000000000000000) : Rat)^(2*k) / Nat.factorial (2*k)) := by native_decide
    have hpR : (sevenNineCosUpper[32]! : ℝ) + ((185714923950355442741 : ℝ) / 100000000000000000000)^97 / (Nat.factorial 96) ≤
        Finset.sum (Finset.range 49) (fun k => (-1 : ℝ)^k * ((185714923950355442741 : ℝ) / 100000000000000000000)^(2*k) / Nat.factorial (2*k)) := by
      norm_num [sevenNineCosUpper, Finset.sum_range_succ]
    simpa [sub_zero] using hpR
  have hangle : ((185714923950355442741 : ℝ) / 100000000000000000000) ≤ Real.arccos (touchCosine a b (Real.sqrt 5 + Real.sqrt 8)) := by
    exact angle_lower_bound_of_cosine (by norm_num)
      (by
        calc
          ((185714923950355442741 : ℝ) / 100000000000000000000) ≤ (314159265358979323846 : ℝ) / 100000000000000000000 := by norm_num
          _ ≤ Real.pi := by
            have hpi := Real.pi_gt_d20.le
            norm_num at hpi ⊢
            exact hpi) (le_trans htouch hcos)
  have hdata : sevenNineAngleLower[32]! = ((185714923950355442741 : Rat) / 100000000000000000000) := by native_decide
  have hdataR : (sevenNineAngleLower[32]! : ℝ) = ((185714923950355442741 : ℝ) / 100000000000000000000) := by
    have h := congrArg (fun q : Rat => (q : ℝ)) hdata
    convert h using 1 ; norm_num
  rw [hdataR]
  exact hangle

theorem sevenNineAngle_1_4_0_1 {a b : ℝ}
    (haL : (sevenNineRadial 1 0 0 : ℝ) ≤ a) (haU : a ≤ (sevenNineRadial 1 0 1 : ℝ))
    (hbL : (sevenNineRadial 4 1 0 : ℝ) ≤ b) (hbU : b ≤ (sevenNineRadial 4 1 1 : ℝ)) :
    (sevenNineAngleLower[33]! : ℝ) ≤ Real.arccos (touchCosine a b (Real.sqrt 5 + Real.sqrt 8)) := by
  let d : ℝ := Real.sqrt 5 + Real.sqrt 8
  have hd' : (((5064495102245979794012551117150672392579962110365421870624256721391985882562018977115189477 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) : ℝ) ≤ d := by
    dsimp [d]
    have h := rat_sum_sqrt_lower (q := ((5064495102245979794012551117150672392579962110365421870624256721391985882562018977115189477 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (qi := ((2236067977499789696409173668731276235440618359611525724270897245410520925637804899414414408378782274969508176150773783504 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (qj := ((2828427124746190097603377448419396157139343750753896146353359475981464956924214077700775068655283145470027692461824594049 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))
      (ni := 5) (nj := 8)
      (by convert sqrt_lower_5 using 1 ; norm_num)
      (by convert sqrt_lower_8 using 1 ; norm_num)
      (by native_decide)
    convert h using 1 ; norm_num
  have hd : (((5064495102245979794012551117150672392579962110365421870624256721391985882562018977115189477 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) ≤ d := by exact hd'
  have hd2 : (((5064495102245979794012551117150672392579962110365421870624256721391985882562018977115189477 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))^2 ≤ d^2 := by
    have hq : (0 : ℝ) ≤ ((5064495102245979794012551117150672392579962110365421870624256721391985882562018977115189477 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) := by norm_num
    have hdn : 0 ≤ d := by positivity
    exact (sq_le_sq₀ hq hdn).mpr hd
  have hd2' : (sevenNineDistanceLower[8]! : ℝ)^2 ≤ d^2 := by
    convert hd2 using 1 ; norm_num [sevenNineDistanceLower]
  have h00 : (sevenNineRadial 1 0 0 : ℝ)^2 + (sevenNineRadial 4 1 0 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[33]! : ℝ) * (2 * (sevenNineRadial 1 0 0 : ℝ) * (sevenNineRadial 4 1 0 : ℝ)) := by
    have hq : (sevenNineRadial 1 0 0)^2 + (sevenNineRadial 4 1 0)^2 - sevenNineDistanceLower[8]!^2 ≤
        sevenNineCosUpper[33]! * (2 * sevenNineRadial 1 0 0 * sevenNineRadial 4 1 0) := by native_decide
    have hqR :
        (sevenNineRadial 1 0 0 : ℝ)^2 + (sevenNineRadial 4 1 0 : ℝ)^2 - (sevenNineDistanceLower[8]! : ℝ)^2 ≤
          (sevenNineCosUpper[33]! : ℝ) * (2 * (sevenNineRadial 1 0 0 : ℝ) * (sevenNineRadial 4 1 0 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 1 0 0 : ℝ)^2 + (sevenNineRadial 4 1 0 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 1 0 0 : ℝ)^2 + (sevenNineRadial 4 1 0 : ℝ)^2 - (sevenNineDistanceLower[8]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h01 : (sevenNineRadial 1 0 0 : ℝ)^2 + (sevenNineRadial 4 1 1 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[33]! : ℝ) * (2 * (sevenNineRadial 1 0 0 : ℝ) * (sevenNineRadial 4 1 1 : ℝ)) := by
    have hq : (sevenNineRadial 1 0 0)^2 + (sevenNineRadial 4 1 1)^2 - sevenNineDistanceLower[8]!^2 ≤
        sevenNineCosUpper[33]! * (2 * sevenNineRadial 1 0 0 * sevenNineRadial 4 1 1) := by native_decide
    have hqR :
        (sevenNineRadial 1 0 0 : ℝ)^2 + (sevenNineRadial 4 1 1 : ℝ)^2 - (sevenNineDistanceLower[8]! : ℝ)^2 ≤
          (sevenNineCosUpper[33]! : ℝ) * (2 * (sevenNineRadial 1 0 0 : ℝ) * (sevenNineRadial 4 1 1 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 1 0 0 : ℝ)^2 + (sevenNineRadial 4 1 1 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 1 0 0 : ℝ)^2 + (sevenNineRadial 4 1 1 : ℝ)^2 - (sevenNineDistanceLower[8]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h10 : (sevenNineRadial 1 0 1 : ℝ)^2 + (sevenNineRadial 4 1 0 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[33]! : ℝ) * (2 * (sevenNineRadial 1 0 1 : ℝ) * (sevenNineRadial 4 1 0 : ℝ)) := by
    have hq : (sevenNineRadial 1 0 1)^2 + (sevenNineRadial 4 1 0)^2 - sevenNineDistanceLower[8]!^2 ≤
        sevenNineCosUpper[33]! * (2 * sevenNineRadial 1 0 1 * sevenNineRadial 4 1 0) := by native_decide
    have hqR :
        (sevenNineRadial 1 0 1 : ℝ)^2 + (sevenNineRadial 4 1 0 : ℝ)^2 - (sevenNineDistanceLower[8]! : ℝ)^2 ≤
          (sevenNineCosUpper[33]! : ℝ) * (2 * (sevenNineRadial 1 0 1 : ℝ) * (sevenNineRadial 4 1 0 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 1 0 1 : ℝ)^2 + (sevenNineRadial 4 1 0 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 1 0 1 : ℝ)^2 + (sevenNineRadial 4 1 0 : ℝ)^2 - (sevenNineDistanceLower[8]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h11 : (sevenNineRadial 1 0 1 : ℝ)^2 + (sevenNineRadial 4 1 1 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[33]! : ℝ) * (2 * (sevenNineRadial 1 0 1 : ℝ) * (sevenNineRadial 4 1 1 : ℝ)) := by
    have hq : (sevenNineRadial 1 0 1)^2 + (sevenNineRadial 4 1 1)^2 - sevenNineDistanceLower[8]!^2 ≤
        sevenNineCosUpper[33]! * (2 * sevenNineRadial 1 0 1 * sevenNineRadial 4 1 1) := by native_decide
    have hqR :
        (sevenNineRadial 1 0 1 : ℝ)^2 + (sevenNineRadial 4 1 1 : ℝ)^2 - (sevenNineDistanceLower[8]! : ℝ)^2 ≤
          (sevenNineCosUpper[33]! : ℝ) * (2 * (sevenNineRadial 1 0 1 : ℝ) * (sevenNineRadial 4 1 1 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 1 0 1 : ℝ)^2 + (sevenNineRadial 4 1 1 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 1 0 1 : ℝ)^2 + (sevenNineRadial 4 1 1 : ℝ)^2 - (sevenNineDistanceLower[8]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have htouch := corner_touch_cosine_bound haL haU hbL hbU
    (by norm_num [sevenNineRadial, sevenNineRadialBounds])
    (by norm_num [sevenNineRadial, sevenNineRadialBounds]) h00 h01 h10 h11
  have hcos : (sevenNineCosUpper[33]! : ℝ) ≤ Real.cos ((125139143270849411881 : ℝ) / 100000000000000000000) := by
    apply lower_bound_of_taylor_error
      (cosine_taylor_ninety_six_remainder (a := 0) (b := 4) (x := ((125139143270849411881 : ℝ) / 100000000000000000000) )
        (by norm_num) (by constructor <;> norm_num [Real.pi_gt_d20, Real.pi_lt_four]))
    rw [cosine_taylor_ninety_six_at_zero (b := 4) (x := ((125139143270849411881 : ℝ) / 100000000000000000000)) (by norm_num)]
    have hp : (sevenNineCosUpper[33]! : Rat) + (((125139143270849411881 : Rat) / 100000000000000000000) : Rat)^97 / (Nat.factorial 96) ≤
        Finset.sum (Finset.range 49) (fun k => (-1 : Rat)^k * (((125139143270849411881 : Rat) / 100000000000000000000) : Rat)^(2*k) / Nat.factorial (2*k)) := by native_decide
    have hpR : (sevenNineCosUpper[33]! : ℝ) + ((125139143270849411881 : ℝ) / 100000000000000000000)^97 / (Nat.factorial 96) ≤
        Finset.sum (Finset.range 49) (fun k => (-1 : ℝ)^k * ((125139143270849411881 : ℝ) / 100000000000000000000)^(2*k) / Nat.factorial (2*k)) := by
      norm_num [sevenNineCosUpper, Finset.sum_range_succ]
    simpa [sub_zero] using hpR
  have hangle : ((125139143270849411881 : ℝ) / 100000000000000000000) ≤ Real.arccos (touchCosine a b (Real.sqrt 5 + Real.sqrt 8)) := by
    exact angle_lower_bound_of_cosine (by norm_num)
      (by
        calc
          ((125139143270849411881 : ℝ) / 100000000000000000000) ≤ (314159265358979323846 : ℝ) / 100000000000000000000 := by norm_num
          _ ≤ Real.pi := by
            have hpi := Real.pi_gt_d20.le
            norm_num at hpi ⊢
            exact hpi) (le_trans htouch hcos)
  have hdata : sevenNineAngleLower[33]! = ((125139143270849411881 : Rat) / 100000000000000000000) := by native_decide
  have hdataR : (sevenNineAngleLower[33]! : ℝ) = ((125139143270849411881 : ℝ) / 100000000000000000000) := by
    have h := congrArg (fun q : Rat => (q : ℝ)) hdata
    convert h using 1 ; norm_num
  rw [hdataR]
  exact hangle

theorem sevenNineAngle_1_4_1_0 {a b : ℝ}
    (haL : (sevenNineRadial 1 1 0 : ℝ) ≤ a) (haU : a ≤ (sevenNineRadial 1 1 1 : ℝ))
    (hbL : (sevenNineRadial 4 0 0 : ℝ) ≤ b) (hbU : b ≤ (sevenNineRadial 4 0 1 : ℝ)) :
    (sevenNineAngleLower[34]! : ℝ) ≤ Real.arccos (touchCosine a b (Real.sqrt 5 + Real.sqrt 8)) := by
  let d : ℝ := Real.sqrt 5 + Real.sqrt 8
  have hd' : (((5064495102245979794012551117150672392579962110365421870624256721391985882562018977115189477 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) : ℝ) ≤ d := by
    dsimp [d]
    have h := rat_sum_sqrt_lower (q := ((5064495102245979794012551117150672392579962110365421870624256721391985882562018977115189477 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (qi := ((2236067977499789696409173668731276235440618359611525724270897245410520925637804899414414408378782274969508176150773783504 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (qj := ((2828427124746190097603377448419396157139343750753896146353359475981464956924214077700775068655283145470027692461824594049 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))
      (ni := 5) (nj := 8)
      (by convert sqrt_lower_5 using 1 ; norm_num)
      (by convert sqrt_lower_8 using 1 ; norm_num)
      (by native_decide)
    convert h using 1 ; norm_num
  have hd : (((5064495102245979794012551117150672392579962110365421870624256721391985882562018977115189477 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) ≤ d := by exact hd'
  have hd2 : (((5064495102245979794012551117150672392579962110365421870624256721391985882562018977115189477 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))^2 ≤ d^2 := by
    have hq : (0 : ℝ) ≤ ((5064495102245979794012551117150672392579962110365421870624256721391985882562018977115189477 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) := by norm_num
    have hdn : 0 ≤ d := by positivity
    exact (sq_le_sq₀ hq hdn).mpr hd
  have hd2' : (sevenNineDistanceLower[8]! : ℝ)^2 ≤ d^2 := by
    convert hd2 using 1 ; norm_num [sevenNineDistanceLower]
  have h00 : (sevenNineRadial 1 1 0 : ℝ)^2 + (sevenNineRadial 4 0 0 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[34]! : ℝ) * (2 * (sevenNineRadial 1 1 0 : ℝ) * (sevenNineRadial 4 0 0 : ℝ)) := by
    have hq : (sevenNineRadial 1 1 0)^2 + (sevenNineRadial 4 0 0)^2 - sevenNineDistanceLower[8]!^2 ≤
        sevenNineCosUpper[34]! * (2 * sevenNineRadial 1 1 0 * sevenNineRadial 4 0 0) := by native_decide
    have hqR :
        (sevenNineRadial 1 1 0 : ℝ)^2 + (sevenNineRadial 4 0 0 : ℝ)^2 - (sevenNineDistanceLower[8]! : ℝ)^2 ≤
          (sevenNineCosUpper[34]! : ℝ) * (2 * (sevenNineRadial 1 1 0 : ℝ) * (sevenNineRadial 4 0 0 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 1 1 0 : ℝ)^2 + (sevenNineRadial 4 0 0 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 1 1 0 : ℝ)^2 + (sevenNineRadial 4 0 0 : ℝ)^2 - (sevenNineDistanceLower[8]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h01 : (sevenNineRadial 1 1 0 : ℝ)^2 + (sevenNineRadial 4 0 1 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[34]! : ℝ) * (2 * (sevenNineRadial 1 1 0 : ℝ) * (sevenNineRadial 4 0 1 : ℝ)) := by
    have hq : (sevenNineRadial 1 1 0)^2 + (sevenNineRadial 4 0 1)^2 - sevenNineDistanceLower[8]!^2 ≤
        sevenNineCosUpper[34]! * (2 * sevenNineRadial 1 1 0 * sevenNineRadial 4 0 1) := by native_decide
    have hqR :
        (sevenNineRadial 1 1 0 : ℝ)^2 + (sevenNineRadial 4 0 1 : ℝ)^2 - (sevenNineDistanceLower[8]! : ℝ)^2 ≤
          (sevenNineCosUpper[34]! : ℝ) * (2 * (sevenNineRadial 1 1 0 : ℝ) * (sevenNineRadial 4 0 1 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 1 1 0 : ℝ)^2 + (sevenNineRadial 4 0 1 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 1 1 0 : ℝ)^2 + (sevenNineRadial 4 0 1 : ℝ)^2 - (sevenNineDistanceLower[8]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h10 : (sevenNineRadial 1 1 1 : ℝ)^2 + (sevenNineRadial 4 0 0 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[34]! : ℝ) * (2 * (sevenNineRadial 1 1 1 : ℝ) * (sevenNineRadial 4 0 0 : ℝ)) := by
    have hq : (sevenNineRadial 1 1 1)^2 + (sevenNineRadial 4 0 0)^2 - sevenNineDistanceLower[8]!^2 ≤
        sevenNineCosUpper[34]! * (2 * sevenNineRadial 1 1 1 * sevenNineRadial 4 0 0) := by native_decide
    have hqR :
        (sevenNineRadial 1 1 1 : ℝ)^2 + (sevenNineRadial 4 0 0 : ℝ)^2 - (sevenNineDistanceLower[8]! : ℝ)^2 ≤
          (sevenNineCosUpper[34]! : ℝ) * (2 * (sevenNineRadial 1 1 1 : ℝ) * (sevenNineRadial 4 0 0 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 1 1 1 : ℝ)^2 + (sevenNineRadial 4 0 0 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 1 1 1 : ℝ)^2 + (sevenNineRadial 4 0 0 : ℝ)^2 - (sevenNineDistanceLower[8]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h11 : (sevenNineRadial 1 1 1 : ℝ)^2 + (sevenNineRadial 4 0 1 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[34]! : ℝ) * (2 * (sevenNineRadial 1 1 1 : ℝ) * (sevenNineRadial 4 0 1 : ℝ)) := by
    have hq : (sevenNineRadial 1 1 1)^2 + (sevenNineRadial 4 0 1)^2 - sevenNineDistanceLower[8]!^2 ≤
        sevenNineCosUpper[34]! * (2 * sevenNineRadial 1 1 1 * sevenNineRadial 4 0 1) := by native_decide
    have hqR :
        (sevenNineRadial 1 1 1 : ℝ)^2 + (sevenNineRadial 4 0 1 : ℝ)^2 - (sevenNineDistanceLower[8]! : ℝ)^2 ≤
          (sevenNineCosUpper[34]! : ℝ) * (2 * (sevenNineRadial 1 1 1 : ℝ) * (sevenNineRadial 4 0 1 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 1 1 1 : ℝ)^2 + (sevenNineRadial 4 0 1 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 1 1 1 : ℝ)^2 + (sevenNineRadial 4 0 1 : ℝ)^2 - (sevenNineDistanceLower[8]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have htouch := corner_touch_cosine_bound haL haU hbL hbU
    (by norm_num [sevenNineRadial, sevenNineRadialBounds])
    (by norm_num [sevenNineRadial, sevenNineRadialBounds]) h00 h01 h10 h11
  have hcos : (sevenNineCosUpper[34]! : ℝ) ≤ Real.cos ((97193442534805857985 : ℝ) / 100000000000000000000) := by
    apply lower_bound_of_taylor_error
      (cosine_taylor_ninety_six_remainder (a := 0) (b := 4) (x := ((97193442534805857985 : ℝ) / 100000000000000000000) )
        (by norm_num) (by constructor <;> norm_num [Real.pi_gt_d20, Real.pi_lt_four]))
    rw [cosine_taylor_ninety_six_at_zero (b := 4) (x := ((97193442534805857985 : ℝ) / 100000000000000000000)) (by norm_num)]
    have hp : (sevenNineCosUpper[34]! : Rat) + (((97193442534805857985 : Rat) / 100000000000000000000) : Rat)^97 / (Nat.factorial 96) ≤
        Finset.sum (Finset.range 49) (fun k => (-1 : Rat)^k * (((97193442534805857985 : Rat) / 100000000000000000000) : Rat)^(2*k) / Nat.factorial (2*k)) := by native_decide
    have hpR : (sevenNineCosUpper[34]! : ℝ) + ((97193442534805857985 : ℝ) / 100000000000000000000)^97 / (Nat.factorial 96) ≤
        Finset.sum (Finset.range 49) (fun k => (-1 : ℝ)^k * ((97193442534805857985 : ℝ) / 100000000000000000000)^(2*k) / Nat.factorial (2*k)) := by
      norm_num [sevenNineCosUpper, Finset.sum_range_succ]
    simpa [sub_zero] using hpR
  have hangle : ((97193442534805857985 : ℝ) / 100000000000000000000) ≤ Real.arccos (touchCosine a b (Real.sqrt 5 + Real.sqrt 8)) := by
    exact angle_lower_bound_of_cosine (by norm_num)
      (by
        calc
          ((97193442534805857985 : ℝ) / 100000000000000000000) ≤ (314159265358979323846 : ℝ) / 100000000000000000000 := by norm_num
          _ ≤ Real.pi := by
            have hpi := Real.pi_gt_d20.le
            norm_num at hpi ⊢
            exact hpi) (le_trans htouch hcos)
  have hdata : sevenNineAngleLower[34]! = ((97193442534805857985 : Rat) / 100000000000000000000) := by native_decide
  have hdataR : (sevenNineAngleLower[34]! : ℝ) = ((97193442534805857985 : ℝ) / 100000000000000000000) := by
    have h := congrArg (fun q : Rat => (q : ℝ)) hdata
    convert h using 1 ; norm_num
  rw [hdataR]
  exact hangle

theorem sevenNineAngle_1_4_1_1 {a b : ℝ}
    (haL : (sevenNineRadial 1 1 0 : ℝ) ≤ a) (haU : a ≤ (sevenNineRadial 1 1 1 : ℝ))
    (hbL : (sevenNineRadial 4 1 0 : ℝ) ≤ b) (hbU : b ≤ (sevenNineRadial 4 1 1 : ℝ)) :
    (sevenNineAngleLower[35]! : ℝ) ≤ Real.arccos (touchCosine a b (Real.sqrt 5 + Real.sqrt 8)) := by
  let d : ℝ := Real.sqrt 5 + Real.sqrt 8
  have hd' : (((5064495102245979794012551117150672392579962110365421870624256721391985882562018977115189477 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) : ℝ) ≤ d := by
    dsimp [d]
    have h := rat_sum_sqrt_lower (q := ((5064495102245979794012551117150672392579962110365421870624256721391985882562018977115189477 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (qi := ((2236067977499789696409173668731276235440618359611525724270897245410520925637804899414414408378782274969508176150773783504 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (qj := ((2828427124746190097603377448419396157139343750753896146353359475981464956924214077700775068655283145470027692461824594049 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))
      (ni := 5) (nj := 8)
      (by convert sqrt_lower_5 using 1 ; norm_num)
      (by convert sqrt_lower_8 using 1 ; norm_num)
      (by native_decide)
    convert h using 1 ; norm_num
  have hd : (((5064495102245979794012551117150672392579962110365421870624256721391985882562018977115189477 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) ≤ d := by exact hd'
  have hd2 : (((5064495102245979794012551117150672392579962110365421870624256721391985882562018977115189477 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))^2 ≤ d^2 := by
    have hq : (0 : ℝ) ≤ ((5064495102245979794012551117150672392579962110365421870624256721391985882562018977115189477 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) := by norm_num
    have hdn : 0 ≤ d := by positivity
    exact (sq_le_sq₀ hq hdn).mpr hd
  have hd2' : (sevenNineDistanceLower[8]! : ℝ)^2 ≤ d^2 := by
    convert hd2 using 1 ; norm_num [sevenNineDistanceLower]
  have h00 : (sevenNineRadial 1 1 0 : ℝ)^2 + (sevenNineRadial 4 1 0 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[35]! : ℝ) * (2 * (sevenNineRadial 1 1 0 : ℝ) * (sevenNineRadial 4 1 0 : ℝ)) := by
    have hq : (sevenNineRadial 1 1 0)^2 + (sevenNineRadial 4 1 0)^2 - sevenNineDistanceLower[8]!^2 ≤
        sevenNineCosUpper[35]! * (2 * sevenNineRadial 1 1 0 * sevenNineRadial 4 1 0) := by native_decide
    have hqR :
        (sevenNineRadial 1 1 0 : ℝ)^2 + (sevenNineRadial 4 1 0 : ℝ)^2 - (sevenNineDistanceLower[8]! : ℝ)^2 ≤
          (sevenNineCosUpper[35]! : ℝ) * (2 * (sevenNineRadial 1 1 0 : ℝ) * (sevenNineRadial 4 1 0 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 1 1 0 : ℝ)^2 + (sevenNineRadial 4 1 0 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 1 1 0 : ℝ)^2 + (sevenNineRadial 4 1 0 : ℝ)^2 - (sevenNineDistanceLower[8]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h01 : (sevenNineRadial 1 1 0 : ℝ)^2 + (sevenNineRadial 4 1 1 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[35]! : ℝ) * (2 * (sevenNineRadial 1 1 0 : ℝ) * (sevenNineRadial 4 1 1 : ℝ)) := by
    have hq : (sevenNineRadial 1 1 0)^2 + (sevenNineRadial 4 1 1)^2 - sevenNineDistanceLower[8]!^2 ≤
        sevenNineCosUpper[35]! * (2 * sevenNineRadial 1 1 0 * sevenNineRadial 4 1 1) := by native_decide
    have hqR :
        (sevenNineRadial 1 1 0 : ℝ)^2 + (sevenNineRadial 4 1 1 : ℝ)^2 - (sevenNineDistanceLower[8]! : ℝ)^2 ≤
          (sevenNineCosUpper[35]! : ℝ) * (2 * (sevenNineRadial 1 1 0 : ℝ) * (sevenNineRadial 4 1 1 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 1 1 0 : ℝ)^2 + (sevenNineRadial 4 1 1 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 1 1 0 : ℝ)^2 + (sevenNineRadial 4 1 1 : ℝ)^2 - (sevenNineDistanceLower[8]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h10 : (sevenNineRadial 1 1 1 : ℝ)^2 + (sevenNineRadial 4 1 0 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[35]! : ℝ) * (2 * (sevenNineRadial 1 1 1 : ℝ) * (sevenNineRadial 4 1 0 : ℝ)) := by
    have hq : (sevenNineRadial 1 1 1)^2 + (sevenNineRadial 4 1 0)^2 - sevenNineDistanceLower[8]!^2 ≤
        sevenNineCosUpper[35]! * (2 * sevenNineRadial 1 1 1 * sevenNineRadial 4 1 0) := by native_decide
    have hqR :
        (sevenNineRadial 1 1 1 : ℝ)^2 + (sevenNineRadial 4 1 0 : ℝ)^2 - (sevenNineDistanceLower[8]! : ℝ)^2 ≤
          (sevenNineCosUpper[35]! : ℝ) * (2 * (sevenNineRadial 1 1 1 : ℝ) * (sevenNineRadial 4 1 0 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 1 1 1 : ℝ)^2 + (sevenNineRadial 4 1 0 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 1 1 1 : ℝ)^2 + (sevenNineRadial 4 1 0 : ℝ)^2 - (sevenNineDistanceLower[8]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h11 : (sevenNineRadial 1 1 1 : ℝ)^2 + (sevenNineRadial 4 1 1 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[35]! : ℝ) * (2 * (sevenNineRadial 1 1 1 : ℝ) * (sevenNineRadial 4 1 1 : ℝ)) := by
    have hq : (sevenNineRadial 1 1 1)^2 + (sevenNineRadial 4 1 1)^2 - sevenNineDistanceLower[8]!^2 ≤
        sevenNineCosUpper[35]! * (2 * sevenNineRadial 1 1 1 * sevenNineRadial 4 1 1) := by native_decide
    have hqR :
        (sevenNineRadial 1 1 1 : ℝ)^2 + (sevenNineRadial 4 1 1 : ℝ)^2 - (sevenNineDistanceLower[8]! : ℝ)^2 ≤
          (sevenNineCosUpper[35]! : ℝ) * (2 * (sevenNineRadial 1 1 1 : ℝ) * (sevenNineRadial 4 1 1 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 1 1 1 : ℝ)^2 + (sevenNineRadial 4 1 1 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 1 1 1 : ℝ)^2 + (sevenNineRadial 4 1 1 : ℝ)^2 - (sevenNineDistanceLower[8]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have htouch := corner_touch_cosine_bound haL haU hbL hbU
    (by norm_num [sevenNineRadial, sevenNineRadialBounds])
    (by norm_num [sevenNineRadial, sevenNineRadialBounds]) h00 h01 h10 h11
  have hcos : (sevenNineCosUpper[35]! : ℝ) ≤ Real.cos ((97683449617774210510 : ℝ) / 100000000000000000000) := by
    apply lower_bound_of_taylor_error
      (cosine_taylor_ninety_six_remainder (a := 0) (b := 4) (x := ((97683449617774210510 : ℝ) / 100000000000000000000) )
        (by norm_num) (by constructor <;> norm_num [Real.pi_gt_d20, Real.pi_lt_four]))
    rw [cosine_taylor_ninety_six_at_zero (b := 4) (x := ((97683449617774210510 : ℝ) / 100000000000000000000)) (by norm_num)]
    have hp : (sevenNineCosUpper[35]! : Rat) + (((97683449617774210510 : Rat) / 100000000000000000000) : Rat)^97 / (Nat.factorial 96) ≤
        Finset.sum (Finset.range 49) (fun k => (-1 : Rat)^k * (((97683449617774210510 : Rat) / 100000000000000000000) : Rat)^(2*k) / Nat.factorial (2*k)) := by native_decide
    have hpR : (sevenNineCosUpper[35]! : ℝ) + ((97683449617774210510 : ℝ) / 100000000000000000000)^97 / (Nat.factorial 96) ≤
        Finset.sum (Finset.range 49) (fun k => (-1 : ℝ)^k * ((97683449617774210510 : ℝ) / 100000000000000000000)^(2*k) / Nat.factorial (2*k)) := by
      norm_num [sevenNineCosUpper, Finset.sum_range_succ]
    simpa [sub_zero] using hpR
  have hangle : ((97683449617774210510 : ℝ) / 100000000000000000000) ≤ Real.arccos (touchCosine a b (Real.sqrt 5 + Real.sqrt 8)) := by
    exact angle_lower_bound_of_cosine (by norm_num)
      (by
        calc
          ((97683449617774210510 : ℝ) / 100000000000000000000) ≤ (314159265358979323846 : ℝ) / 100000000000000000000 := by norm_num
          _ ≤ Real.pi := by
            have hpi := Real.pi_gt_d20.le
            norm_num at hpi ⊢
            exact hpi) (le_trans htouch hcos)
  have hdata : sevenNineAngleLower[35]! = ((97683449617774210510 : Rat) / 100000000000000000000) := by native_decide
  have hdataR : (sevenNineAngleLower[35]! : ℝ) = ((97683449617774210510 : ℝ) / 100000000000000000000) := by
    have h := congrArg (fun q : Rat => (q : ℝ)) hdata
    convert h using 1 ; norm_num
  rw [hdataR]
  exact hangle

theorem sevenNineAngle_1_5_0_0 {a b : ℝ}
    (haL : (sevenNineRadial 1 0 0 : ℝ) ≤ a) (haU : a ≤ (sevenNineRadial 1 0 1 : ℝ))
    (hbL : (sevenNineRadial 5 0 0 : ℝ) ≤ b) (hbU : b ≤ (sevenNineRadial 5 0 1 : ℝ)) :
    (sevenNineAngleLower[36]! : ℝ) ≤ Real.arccos (touchCosine a b (Real.sqrt 5 + Real.sqrt 9)) := by
  let d : ℝ := Real.sqrt 5 + Real.sqrt 9
  have hd' : (((5236067977499789696409173668731276235440618359611525724270897245410520925637804899414414408 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) : ℝ) ≤ d := by
    dsimp [d]
    have h := rat_sum_sqrt_lower (q := ((5236067977499789696409173668731276235440618359611525724270897245410520925637804899414414408 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (qi := ((2236067977499789696409173668731276235440618359611525724270897245410520925637804899414414408378782274969508176150773783504 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (qj := ((3 : Rat) / 1))
      (ni := 5) (nj := 9)
      (by convert sqrt_lower_5 using 1 ; norm_num)
      (by convert sqrt_lower_9 using 1 ; norm_num)
      (by native_decide)
    convert h using 1 ; norm_num
  have hd : (((5236067977499789696409173668731276235440618359611525724270897245410520925637804899414414408 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) ≤ d := by exact hd'
  have hd2 : (((5236067977499789696409173668731276235440618359611525724270897245410520925637804899414414408 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))^2 ≤ d^2 := by
    have hq : (0 : ℝ) ≤ ((5236067977499789696409173668731276235440618359611525724270897245410520925637804899414414408 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) := by norm_num
    have hdn : 0 ≤ d := by positivity
    exact (sq_le_sq₀ hq hdn).mpr hd
  have hd2' : (sevenNineDistanceLower[9]! : ℝ)^2 ≤ d^2 := by
    convert hd2 using 1 ; norm_num [sevenNineDistanceLower]
  have h00 : (sevenNineRadial 1 0 0 : ℝ)^2 + (sevenNineRadial 5 0 0 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[36]! : ℝ) * (2 * (sevenNineRadial 1 0 0 : ℝ) * (sevenNineRadial 5 0 0 : ℝ)) := by
    have hq : (sevenNineRadial 1 0 0)^2 + (sevenNineRadial 5 0 0)^2 - sevenNineDistanceLower[9]!^2 ≤
        sevenNineCosUpper[36]! * (2 * sevenNineRadial 1 0 0 * sevenNineRadial 5 0 0) := by native_decide
    have hqR :
        (sevenNineRadial 1 0 0 : ℝ)^2 + (sevenNineRadial 5 0 0 : ℝ)^2 - (sevenNineDistanceLower[9]! : ℝ)^2 ≤
          (sevenNineCosUpper[36]! : ℝ) * (2 * (sevenNineRadial 1 0 0 : ℝ) * (sevenNineRadial 5 0 0 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 1 0 0 : ℝ)^2 + (sevenNineRadial 5 0 0 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 1 0 0 : ℝ)^2 + (sevenNineRadial 5 0 0 : ℝ)^2 - (sevenNineDistanceLower[9]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h01 : (sevenNineRadial 1 0 0 : ℝ)^2 + (sevenNineRadial 5 0 1 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[36]! : ℝ) * (2 * (sevenNineRadial 1 0 0 : ℝ) * (sevenNineRadial 5 0 1 : ℝ)) := by
    have hq : (sevenNineRadial 1 0 0)^2 + (sevenNineRadial 5 0 1)^2 - sevenNineDistanceLower[9]!^2 ≤
        sevenNineCosUpper[36]! * (2 * sevenNineRadial 1 0 0 * sevenNineRadial 5 0 1) := by native_decide
    have hqR :
        (sevenNineRadial 1 0 0 : ℝ)^2 + (sevenNineRadial 5 0 1 : ℝ)^2 - (sevenNineDistanceLower[9]! : ℝ)^2 ≤
          (sevenNineCosUpper[36]! : ℝ) * (2 * (sevenNineRadial 1 0 0 : ℝ) * (sevenNineRadial 5 0 1 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 1 0 0 : ℝ)^2 + (sevenNineRadial 5 0 1 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 1 0 0 : ℝ)^2 + (sevenNineRadial 5 0 1 : ℝ)^2 - (sevenNineDistanceLower[9]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h10 : (sevenNineRadial 1 0 1 : ℝ)^2 + (sevenNineRadial 5 0 0 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[36]! : ℝ) * (2 * (sevenNineRadial 1 0 1 : ℝ) * (sevenNineRadial 5 0 0 : ℝ)) := by
    have hq : (sevenNineRadial 1 0 1)^2 + (sevenNineRadial 5 0 0)^2 - sevenNineDistanceLower[9]!^2 ≤
        sevenNineCosUpper[36]! * (2 * sevenNineRadial 1 0 1 * sevenNineRadial 5 0 0) := by native_decide
    have hqR :
        (sevenNineRadial 1 0 1 : ℝ)^2 + (sevenNineRadial 5 0 0 : ℝ)^2 - (sevenNineDistanceLower[9]! : ℝ)^2 ≤
          (sevenNineCosUpper[36]! : ℝ) * (2 * (sevenNineRadial 1 0 1 : ℝ) * (sevenNineRadial 5 0 0 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 1 0 1 : ℝ)^2 + (sevenNineRadial 5 0 0 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 1 0 1 : ℝ)^2 + (sevenNineRadial 5 0 0 : ℝ)^2 - (sevenNineDistanceLower[9]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h11 : (sevenNineRadial 1 0 1 : ℝ)^2 + (sevenNineRadial 5 0 1 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[36]! : ℝ) * (2 * (sevenNineRadial 1 0 1 : ℝ) * (sevenNineRadial 5 0 1 : ℝ)) := by
    have hq : (sevenNineRadial 1 0 1)^2 + (sevenNineRadial 5 0 1)^2 - sevenNineDistanceLower[9]!^2 ≤
        sevenNineCosUpper[36]! * (2 * sevenNineRadial 1 0 1 * sevenNineRadial 5 0 1) := by native_decide
    have hqR :
        (sevenNineRadial 1 0 1 : ℝ)^2 + (sevenNineRadial 5 0 1 : ℝ)^2 - (sevenNineDistanceLower[9]! : ℝ)^2 ≤
          (sevenNineCosUpper[36]! : ℝ) * (2 * (sevenNineRadial 1 0 1 : ℝ) * (sevenNineRadial 5 0 1 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 1 0 1 : ℝ)^2 + (sevenNineRadial 5 0 1 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 1 0 1 : ℝ)^2 + (sevenNineRadial 5 0 1 : ℝ)^2 - (sevenNineDistanceLower[9]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have htouch := corner_touch_cosine_bound haL haU hbL hbU
    (by norm_num [sevenNineRadial, sevenNineRadialBounds])
    (by norm_num [sevenNineRadial, sevenNineRadialBounds]) h00 h01 h10 h11
  have hcos : (sevenNineCosUpper[36]! : ℝ) ≤ Real.cos ((195068856560129306024 : ℝ) / 100000000000000000000) := by
    apply lower_bound_of_taylor_error
      (cosine_taylor_ninety_six_remainder (a := 0) (b := 4) (x := ((195068856560129306024 : ℝ) / 100000000000000000000) )
        (by norm_num) (by constructor <;> norm_num [Real.pi_gt_d20, Real.pi_lt_four]))
    rw [cosine_taylor_ninety_six_at_zero (b := 4) (x := ((195068856560129306024 : ℝ) / 100000000000000000000)) (by norm_num)]
    have hp : (sevenNineCosUpper[36]! : Rat) + (((195068856560129306024 : Rat) / 100000000000000000000) : Rat)^97 / (Nat.factorial 96) ≤
        Finset.sum (Finset.range 49) (fun k => (-1 : Rat)^k * (((195068856560129306024 : Rat) / 100000000000000000000) : Rat)^(2*k) / Nat.factorial (2*k)) := by native_decide
    have hpR : (sevenNineCosUpper[36]! : ℝ) + ((195068856560129306024 : ℝ) / 100000000000000000000)^97 / (Nat.factorial 96) ≤
        Finset.sum (Finset.range 49) (fun k => (-1 : ℝ)^k * ((195068856560129306024 : ℝ) / 100000000000000000000)^(2*k) / Nat.factorial (2*k)) := by
      norm_num [sevenNineCosUpper, Finset.sum_range_succ]
    simpa [sub_zero] using hpR
  have hangle : ((195068856560129306024 : ℝ) / 100000000000000000000) ≤ Real.arccos (touchCosine a b (Real.sqrt 5 + Real.sqrt 9)) := by
    exact angle_lower_bound_of_cosine (by norm_num)
      (by
        calc
          ((195068856560129306024 : ℝ) / 100000000000000000000) ≤ (314159265358979323846 : ℝ) / 100000000000000000000 := by norm_num
          _ ≤ Real.pi := by
            have hpi := Real.pi_gt_d20.le
            norm_num at hpi ⊢
            exact hpi) (le_trans htouch hcos)
  have hdata : sevenNineAngleLower[36]! = ((195068856560129306024 : Rat) / 100000000000000000000) := by native_decide
  have hdataR : (sevenNineAngleLower[36]! : ℝ) = ((195068856560129306024 : ℝ) / 100000000000000000000) := by
    have h := congrArg (fun q : Rat => (q : ℝ)) hdata
    convert h using 1 ; norm_num
  rw [hdataR]
  exact hangle

theorem sevenNineAngle_1_5_0_1 {a b : ℝ}
    (haL : (sevenNineRadial 1 0 0 : ℝ) ≤ a) (haU : a ≤ (sevenNineRadial 1 0 1 : ℝ))
    (hbL : (sevenNineRadial 5 1 0 : ℝ) ≤ b) (hbU : b ≤ (sevenNineRadial 5 1 1 : ℝ)) :
    (sevenNineAngleLower[37]! : ℝ) ≤ Real.arccos (touchCosine a b (Real.sqrt 5 + Real.sqrt 9)) := by
  let d : ℝ := Real.sqrt 5 + Real.sqrt 9
  have hd' : (((5236067977499789696409173668731276235440618359611525724270897245410520925637804899414414408 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) : ℝ) ≤ d := by
    dsimp [d]
    have h := rat_sum_sqrt_lower (q := ((5236067977499789696409173668731276235440618359611525724270897245410520925637804899414414408 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (qi := ((2236067977499789696409173668731276235440618359611525724270897245410520925637804899414414408378782274969508176150773783504 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (qj := ((3 : Rat) / 1))
      (ni := 5) (nj := 9)
      (by convert sqrt_lower_5 using 1 ; norm_num)
      (by convert sqrt_lower_9 using 1 ; norm_num)
      (by native_decide)
    convert h using 1 ; norm_num
  have hd : (((5236067977499789696409173668731276235440618359611525724270897245410520925637804899414414408 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) ≤ d := by exact hd'
  have hd2 : (((5236067977499789696409173668731276235440618359611525724270897245410520925637804899414414408 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))^2 ≤ d^2 := by
    have hq : (0 : ℝ) ≤ ((5236067977499789696409173668731276235440618359611525724270897245410520925637804899414414408 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) := by norm_num
    have hdn : 0 ≤ d := by positivity
    exact (sq_le_sq₀ hq hdn).mpr hd
  have hd2' : (sevenNineDistanceLower[9]! : ℝ)^2 ≤ d^2 := by
    convert hd2 using 1 ; norm_num [sevenNineDistanceLower]
  have h00 : (sevenNineRadial 1 0 0 : ℝ)^2 + (sevenNineRadial 5 1 0 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[37]! : ℝ) * (2 * (sevenNineRadial 1 0 0 : ℝ) * (sevenNineRadial 5 1 0 : ℝ)) := by
    have hq : (sevenNineRadial 1 0 0)^2 + (sevenNineRadial 5 1 0)^2 - sevenNineDistanceLower[9]!^2 ≤
        sevenNineCosUpper[37]! * (2 * sevenNineRadial 1 0 0 * sevenNineRadial 5 1 0) := by native_decide
    have hqR :
        (sevenNineRadial 1 0 0 : ℝ)^2 + (sevenNineRadial 5 1 0 : ℝ)^2 - (sevenNineDistanceLower[9]! : ℝ)^2 ≤
          (sevenNineCosUpper[37]! : ℝ) * (2 * (sevenNineRadial 1 0 0 : ℝ) * (sevenNineRadial 5 1 0 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 1 0 0 : ℝ)^2 + (sevenNineRadial 5 1 0 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 1 0 0 : ℝ)^2 + (sevenNineRadial 5 1 0 : ℝ)^2 - (sevenNineDistanceLower[9]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h01 : (sevenNineRadial 1 0 0 : ℝ)^2 + (sevenNineRadial 5 1 1 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[37]! : ℝ) * (2 * (sevenNineRadial 1 0 0 : ℝ) * (sevenNineRadial 5 1 1 : ℝ)) := by
    have hq : (sevenNineRadial 1 0 0)^2 + (sevenNineRadial 5 1 1)^2 - sevenNineDistanceLower[9]!^2 ≤
        sevenNineCosUpper[37]! * (2 * sevenNineRadial 1 0 0 * sevenNineRadial 5 1 1) := by native_decide
    have hqR :
        (sevenNineRadial 1 0 0 : ℝ)^2 + (sevenNineRadial 5 1 1 : ℝ)^2 - (sevenNineDistanceLower[9]! : ℝ)^2 ≤
          (sevenNineCosUpper[37]! : ℝ) * (2 * (sevenNineRadial 1 0 0 : ℝ) * (sevenNineRadial 5 1 1 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 1 0 0 : ℝ)^2 + (sevenNineRadial 5 1 1 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 1 0 0 : ℝ)^2 + (sevenNineRadial 5 1 1 : ℝ)^2 - (sevenNineDistanceLower[9]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h10 : (sevenNineRadial 1 0 1 : ℝ)^2 + (sevenNineRadial 5 1 0 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[37]! : ℝ) * (2 * (sevenNineRadial 1 0 1 : ℝ) * (sevenNineRadial 5 1 0 : ℝ)) := by
    have hq : (sevenNineRadial 1 0 1)^2 + (sevenNineRadial 5 1 0)^2 - sevenNineDistanceLower[9]!^2 ≤
        sevenNineCosUpper[37]! * (2 * sevenNineRadial 1 0 1 * sevenNineRadial 5 1 0) := by native_decide
    have hqR :
        (sevenNineRadial 1 0 1 : ℝ)^2 + (sevenNineRadial 5 1 0 : ℝ)^2 - (sevenNineDistanceLower[9]! : ℝ)^2 ≤
          (sevenNineCosUpper[37]! : ℝ) * (2 * (sevenNineRadial 1 0 1 : ℝ) * (sevenNineRadial 5 1 0 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 1 0 1 : ℝ)^2 + (sevenNineRadial 5 1 0 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 1 0 1 : ℝ)^2 + (sevenNineRadial 5 1 0 : ℝ)^2 - (sevenNineDistanceLower[9]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h11 : (sevenNineRadial 1 0 1 : ℝ)^2 + (sevenNineRadial 5 1 1 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[37]! : ℝ) * (2 * (sevenNineRadial 1 0 1 : ℝ) * (sevenNineRadial 5 1 1 : ℝ)) := by
    have hq : (sevenNineRadial 1 0 1)^2 + (sevenNineRadial 5 1 1)^2 - sevenNineDistanceLower[9]!^2 ≤
        sevenNineCosUpper[37]! * (2 * sevenNineRadial 1 0 1 * sevenNineRadial 5 1 1) := by native_decide
    have hqR :
        (sevenNineRadial 1 0 1 : ℝ)^2 + (sevenNineRadial 5 1 1 : ℝ)^2 - (sevenNineDistanceLower[9]! : ℝ)^2 ≤
          (sevenNineCosUpper[37]! : ℝ) * (2 * (sevenNineRadial 1 0 1 : ℝ) * (sevenNineRadial 5 1 1 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 1 0 1 : ℝ)^2 + (sevenNineRadial 5 1 1 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 1 0 1 : ℝ)^2 + (sevenNineRadial 5 1 1 : ℝ)^2 - (sevenNineDistanceLower[9]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have htouch := corner_touch_cosine_bound haL haU hbL hbU
    (by norm_num [sevenNineRadial, sevenNineRadialBounds])
    (by norm_num [sevenNineRadial, sevenNineRadialBounds]) h00 h01 h10 h11
  have hcos : (sevenNineCosUpper[37]! : ℝ) ≤ Real.cos ((135639453988930998251 : ℝ) / 100000000000000000000) := by
    apply lower_bound_of_taylor_error
      (cosine_taylor_ninety_six_remainder (a := 0) (b := 4) (x := ((135639453988930998251 : ℝ) / 100000000000000000000) )
        (by norm_num) (by constructor <;> norm_num [Real.pi_gt_d20, Real.pi_lt_four]))
    rw [cosine_taylor_ninety_six_at_zero (b := 4) (x := ((135639453988930998251 : ℝ) / 100000000000000000000)) (by norm_num)]
    have hp : (sevenNineCosUpper[37]! : Rat) + (((135639453988930998251 : Rat) / 100000000000000000000) : Rat)^97 / (Nat.factorial 96) ≤
        Finset.sum (Finset.range 49) (fun k => (-1 : Rat)^k * (((135639453988930998251 : Rat) / 100000000000000000000) : Rat)^(2*k) / Nat.factorial (2*k)) := by native_decide
    have hpR : (sevenNineCosUpper[37]! : ℝ) + ((135639453988930998251 : ℝ) / 100000000000000000000)^97 / (Nat.factorial 96) ≤
        Finset.sum (Finset.range 49) (fun k => (-1 : ℝ)^k * ((135639453988930998251 : ℝ) / 100000000000000000000)^(2*k) / Nat.factorial (2*k)) := by
      norm_num [sevenNineCosUpper, Finset.sum_range_succ]
    simpa [sub_zero] using hpR
  have hangle : ((135639453988930998251 : ℝ) / 100000000000000000000) ≤ Real.arccos (touchCosine a b (Real.sqrt 5 + Real.sqrt 9)) := by
    exact angle_lower_bound_of_cosine (by norm_num)
      (by
        calc
          ((135639453988930998251 : ℝ) / 100000000000000000000) ≤ (314159265358979323846 : ℝ) / 100000000000000000000 := by norm_num
          _ ≤ Real.pi := by
            have hpi := Real.pi_gt_d20.le
            norm_num at hpi ⊢
            exact hpi) (le_trans htouch hcos)
  have hdata : sevenNineAngleLower[37]! = ((135639453988930998251 : Rat) / 100000000000000000000) := by native_decide
  have hdataR : (sevenNineAngleLower[37]! : ℝ) = ((135639453988930998251 : ℝ) / 100000000000000000000) := by
    have h := congrArg (fun q : Rat => (q : ℝ)) hdata
    convert h using 1 ; norm_num
  rw [hdataR]
  exact hangle

theorem sevenNineAngle_1_5_1_0 {a b : ℝ}
    (haL : (sevenNineRadial 1 1 0 : ℝ) ≤ a) (haU : a ≤ (sevenNineRadial 1 1 1 : ℝ))
    (hbL : (sevenNineRadial 5 0 0 : ℝ) ≤ b) (hbU : b ≤ (sevenNineRadial 5 0 1 : ℝ)) :
    (sevenNineAngleLower[38]! : ℝ) ≤ Real.arccos (touchCosine a b (Real.sqrt 5 + Real.sqrt 9)) := by
  let d : ℝ := Real.sqrt 5 + Real.sqrt 9
  have hd' : (((5236067977499789696409173668731276235440618359611525724270897245410520925637804899414414408 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) : ℝ) ≤ d := by
    dsimp [d]
    have h := rat_sum_sqrt_lower (q := ((5236067977499789696409173668731276235440618359611525724270897245410520925637804899414414408 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (qi := ((2236067977499789696409173668731276235440618359611525724270897245410520925637804899414414408378782274969508176150773783504 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (qj := ((3 : Rat) / 1))
      (ni := 5) (nj := 9)
      (by convert sqrt_lower_5 using 1 ; norm_num)
      (by convert sqrt_lower_9 using 1 ; norm_num)
      (by native_decide)
    convert h using 1 ; norm_num
  have hd : (((5236067977499789696409173668731276235440618359611525724270897245410520925637804899414414408 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) ≤ d := by exact hd'
  have hd2 : (((5236067977499789696409173668731276235440618359611525724270897245410520925637804899414414408 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))^2 ≤ d^2 := by
    have hq : (0 : ℝ) ≤ ((5236067977499789696409173668731276235440618359611525724270897245410520925637804899414414408 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) := by norm_num
    have hdn : 0 ≤ d := by positivity
    exact (sq_le_sq₀ hq hdn).mpr hd
  have hd2' : (sevenNineDistanceLower[9]! : ℝ)^2 ≤ d^2 := by
    convert hd2 using 1 ; norm_num [sevenNineDistanceLower]
  have h00 : (sevenNineRadial 1 1 0 : ℝ)^2 + (sevenNineRadial 5 0 0 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[38]! : ℝ) * (2 * (sevenNineRadial 1 1 0 : ℝ) * (sevenNineRadial 5 0 0 : ℝ)) := by
    have hq : (sevenNineRadial 1 1 0)^2 + (sevenNineRadial 5 0 0)^2 - sevenNineDistanceLower[9]!^2 ≤
        sevenNineCosUpper[38]! * (2 * sevenNineRadial 1 1 0 * sevenNineRadial 5 0 0) := by native_decide
    have hqR :
        (sevenNineRadial 1 1 0 : ℝ)^2 + (sevenNineRadial 5 0 0 : ℝ)^2 - (sevenNineDistanceLower[9]! : ℝ)^2 ≤
          (sevenNineCosUpper[38]! : ℝ) * (2 * (sevenNineRadial 1 1 0 : ℝ) * (sevenNineRadial 5 0 0 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 1 1 0 : ℝ)^2 + (sevenNineRadial 5 0 0 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 1 1 0 : ℝ)^2 + (sevenNineRadial 5 0 0 : ℝ)^2 - (sevenNineDistanceLower[9]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h01 : (sevenNineRadial 1 1 0 : ℝ)^2 + (sevenNineRadial 5 0 1 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[38]! : ℝ) * (2 * (sevenNineRadial 1 1 0 : ℝ) * (sevenNineRadial 5 0 1 : ℝ)) := by
    have hq : (sevenNineRadial 1 1 0)^2 + (sevenNineRadial 5 0 1)^2 - sevenNineDistanceLower[9]!^2 ≤
        sevenNineCosUpper[38]! * (2 * sevenNineRadial 1 1 0 * sevenNineRadial 5 0 1) := by native_decide
    have hqR :
        (sevenNineRadial 1 1 0 : ℝ)^2 + (sevenNineRadial 5 0 1 : ℝ)^2 - (sevenNineDistanceLower[9]! : ℝ)^2 ≤
          (sevenNineCosUpper[38]! : ℝ) * (2 * (sevenNineRadial 1 1 0 : ℝ) * (sevenNineRadial 5 0 1 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 1 1 0 : ℝ)^2 + (sevenNineRadial 5 0 1 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 1 1 0 : ℝ)^2 + (sevenNineRadial 5 0 1 : ℝ)^2 - (sevenNineDistanceLower[9]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h10 : (sevenNineRadial 1 1 1 : ℝ)^2 + (sevenNineRadial 5 0 0 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[38]! : ℝ) * (2 * (sevenNineRadial 1 1 1 : ℝ) * (sevenNineRadial 5 0 0 : ℝ)) := by
    have hq : (sevenNineRadial 1 1 1)^2 + (sevenNineRadial 5 0 0)^2 - sevenNineDistanceLower[9]!^2 ≤
        sevenNineCosUpper[38]! * (2 * sevenNineRadial 1 1 1 * sevenNineRadial 5 0 0) := by native_decide
    have hqR :
        (sevenNineRadial 1 1 1 : ℝ)^2 + (sevenNineRadial 5 0 0 : ℝ)^2 - (sevenNineDistanceLower[9]! : ℝ)^2 ≤
          (sevenNineCosUpper[38]! : ℝ) * (2 * (sevenNineRadial 1 1 1 : ℝ) * (sevenNineRadial 5 0 0 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 1 1 1 : ℝ)^2 + (sevenNineRadial 5 0 0 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 1 1 1 : ℝ)^2 + (sevenNineRadial 5 0 0 : ℝ)^2 - (sevenNineDistanceLower[9]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h11 : (sevenNineRadial 1 1 1 : ℝ)^2 + (sevenNineRadial 5 0 1 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[38]! : ℝ) * (2 * (sevenNineRadial 1 1 1 : ℝ) * (sevenNineRadial 5 0 1 : ℝ)) := by
    have hq : (sevenNineRadial 1 1 1)^2 + (sevenNineRadial 5 0 1)^2 - sevenNineDistanceLower[9]!^2 ≤
        sevenNineCosUpper[38]! * (2 * sevenNineRadial 1 1 1 * sevenNineRadial 5 0 1) := by native_decide
    have hqR :
        (sevenNineRadial 1 1 1 : ℝ)^2 + (sevenNineRadial 5 0 1 : ℝ)^2 - (sevenNineDistanceLower[9]! : ℝ)^2 ≤
          (sevenNineCosUpper[38]! : ℝ) * (2 * (sevenNineRadial 1 1 1 : ℝ) * (sevenNineRadial 5 0 1 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 1 1 1 : ℝ)^2 + (sevenNineRadial 5 0 1 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 1 1 1 : ℝ)^2 + (sevenNineRadial 5 0 1 : ℝ)^2 - (sevenNineDistanceLower[9]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have htouch := corner_touch_cosine_bound haL haU hbL hbU
    (by norm_num [sevenNineRadial, sevenNineRadialBounds])
    (by norm_num [sevenNineRadial, sevenNineRadialBounds]) h00 h01 h10 h11
  have hcos : (sevenNineCosUpper[38]! : ℝ) ≤ Real.cos ((114311567926335028090 : ℝ) / 100000000000000000000) := by
    apply lower_bound_of_taylor_error
      (cosine_taylor_ninety_six_remainder (a := 0) (b := 4) (x := ((114311567926335028090 : ℝ) / 100000000000000000000) )
        (by norm_num) (by constructor <;> norm_num [Real.pi_gt_d20, Real.pi_lt_four]))
    rw [cosine_taylor_ninety_six_at_zero (b := 4) (x := ((114311567926335028090 : ℝ) / 100000000000000000000)) (by norm_num)]
    have hp : (sevenNineCosUpper[38]! : Rat) + (((114311567926335028090 : Rat) / 100000000000000000000) : Rat)^97 / (Nat.factorial 96) ≤
        Finset.sum (Finset.range 49) (fun k => (-1 : Rat)^k * (((114311567926335028090 : Rat) / 100000000000000000000) : Rat)^(2*k) / Nat.factorial (2*k)) := by native_decide
    have hpR : (sevenNineCosUpper[38]! : ℝ) + ((114311567926335028090 : ℝ) / 100000000000000000000)^97 / (Nat.factorial 96) ≤
        Finset.sum (Finset.range 49) (fun k => (-1 : ℝ)^k * ((114311567926335028090 : ℝ) / 100000000000000000000)^(2*k) / Nat.factorial (2*k)) := by
      norm_num [sevenNineCosUpper, Finset.sum_range_succ]
    simpa [sub_zero] using hpR
  have hangle : ((114311567926335028090 : ℝ) / 100000000000000000000) ≤ Real.arccos (touchCosine a b (Real.sqrt 5 + Real.sqrt 9)) := by
    exact angle_lower_bound_of_cosine (by norm_num)
      (by
        calc
          ((114311567926335028090 : ℝ) / 100000000000000000000) ≤ (314159265358979323846 : ℝ) / 100000000000000000000 := by norm_num
          _ ≤ Real.pi := by
            have hpi := Real.pi_gt_d20.le
            norm_num at hpi ⊢
            exact hpi) (le_trans htouch hcos)
  have hdata : sevenNineAngleLower[38]! = ((114311567926335028090 : Rat) / 100000000000000000000) := by native_decide
  have hdataR : (sevenNineAngleLower[38]! : ℝ) = ((114311567926335028090 : ℝ) / 100000000000000000000) := by
    have h := congrArg (fun q : Rat => (q : ℝ)) hdata
    convert h using 1 ; norm_num
  rw [hdataR]
  exact hangle

theorem sevenNineAngle_1_5_1_1 {a b : ℝ}
    (haL : (sevenNineRadial 1 1 0 : ℝ) ≤ a) (haU : a ≤ (sevenNineRadial 1 1 1 : ℝ))
    (hbL : (sevenNineRadial 5 1 0 : ℝ) ≤ b) (hbU : b ≤ (sevenNineRadial 5 1 1 : ℝ)) :
    (sevenNineAngleLower[39]! : ℝ) ≤ Real.arccos (touchCosine a b (Real.sqrt 5 + Real.sqrt 9)) := by
  let d : ℝ := Real.sqrt 5 + Real.sqrt 9
  have hd' : (((5236067977499789696409173668731276235440618359611525724270897245410520925637804899414414408 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) : ℝ) ≤ d := by
    dsimp [d]
    have h := rat_sum_sqrt_lower (q := ((5236067977499789696409173668731276235440618359611525724270897245410520925637804899414414408 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (qi := ((2236067977499789696409173668731276235440618359611525724270897245410520925637804899414414408378782274969508176150773783504 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (qj := ((3 : Rat) / 1))
      (ni := 5) (nj := 9)
      (by convert sqrt_lower_5 using 1 ; norm_num)
      (by convert sqrt_lower_9 using 1 ; norm_num)
      (by native_decide)
    convert h using 1 ; norm_num
  have hd : (((5236067977499789696409173668731276235440618359611525724270897245410520925637804899414414408 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) ≤ d := by exact hd'
  have hd2 : (((5236067977499789696409173668731276235440618359611525724270897245410520925637804899414414408 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))^2 ≤ d^2 := by
    have hq : (0 : ℝ) ≤ ((5236067977499789696409173668731276235440618359611525724270897245410520925637804899414414408 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) := by norm_num
    have hdn : 0 ≤ d := by positivity
    exact (sq_le_sq₀ hq hdn).mpr hd
  have hd2' : (sevenNineDistanceLower[9]! : ℝ)^2 ≤ d^2 := by
    convert hd2 using 1 ; norm_num [sevenNineDistanceLower]
  have h00 : (sevenNineRadial 1 1 0 : ℝ)^2 + (sevenNineRadial 5 1 0 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[39]! : ℝ) * (2 * (sevenNineRadial 1 1 0 : ℝ) * (sevenNineRadial 5 1 0 : ℝ)) := by
    have hq : (sevenNineRadial 1 1 0)^2 + (sevenNineRadial 5 1 0)^2 - sevenNineDistanceLower[9]!^2 ≤
        sevenNineCosUpper[39]! * (2 * sevenNineRadial 1 1 0 * sevenNineRadial 5 1 0) := by native_decide
    have hqR :
        (sevenNineRadial 1 1 0 : ℝ)^2 + (sevenNineRadial 5 1 0 : ℝ)^2 - (sevenNineDistanceLower[9]! : ℝ)^2 ≤
          (sevenNineCosUpper[39]! : ℝ) * (2 * (sevenNineRadial 1 1 0 : ℝ) * (sevenNineRadial 5 1 0 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 1 1 0 : ℝ)^2 + (sevenNineRadial 5 1 0 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 1 1 0 : ℝ)^2 + (sevenNineRadial 5 1 0 : ℝ)^2 - (sevenNineDistanceLower[9]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h01 : (sevenNineRadial 1 1 0 : ℝ)^2 + (sevenNineRadial 5 1 1 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[39]! : ℝ) * (2 * (sevenNineRadial 1 1 0 : ℝ) * (sevenNineRadial 5 1 1 : ℝ)) := by
    have hq : (sevenNineRadial 1 1 0)^2 + (sevenNineRadial 5 1 1)^2 - sevenNineDistanceLower[9]!^2 ≤
        sevenNineCosUpper[39]! * (2 * sevenNineRadial 1 1 0 * sevenNineRadial 5 1 1) := by native_decide
    have hqR :
        (sevenNineRadial 1 1 0 : ℝ)^2 + (sevenNineRadial 5 1 1 : ℝ)^2 - (sevenNineDistanceLower[9]! : ℝ)^2 ≤
          (sevenNineCosUpper[39]! : ℝ) * (2 * (sevenNineRadial 1 1 0 : ℝ) * (sevenNineRadial 5 1 1 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 1 1 0 : ℝ)^2 + (sevenNineRadial 5 1 1 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 1 1 0 : ℝ)^2 + (sevenNineRadial 5 1 1 : ℝ)^2 - (sevenNineDistanceLower[9]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h10 : (sevenNineRadial 1 1 1 : ℝ)^2 + (sevenNineRadial 5 1 0 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[39]! : ℝ) * (2 * (sevenNineRadial 1 1 1 : ℝ) * (sevenNineRadial 5 1 0 : ℝ)) := by
    have hq : (sevenNineRadial 1 1 1)^2 + (sevenNineRadial 5 1 0)^2 - sevenNineDistanceLower[9]!^2 ≤
        sevenNineCosUpper[39]! * (2 * sevenNineRadial 1 1 1 * sevenNineRadial 5 1 0) := by native_decide
    have hqR :
        (sevenNineRadial 1 1 1 : ℝ)^2 + (sevenNineRadial 5 1 0 : ℝ)^2 - (sevenNineDistanceLower[9]! : ℝ)^2 ≤
          (sevenNineCosUpper[39]! : ℝ) * (2 * (sevenNineRadial 1 1 1 : ℝ) * (sevenNineRadial 5 1 0 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 1 1 1 : ℝ)^2 + (sevenNineRadial 5 1 0 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 1 1 1 : ℝ)^2 + (sevenNineRadial 5 1 0 : ℝ)^2 - (sevenNineDistanceLower[9]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h11 : (sevenNineRadial 1 1 1 : ℝ)^2 + (sevenNineRadial 5 1 1 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[39]! : ℝ) * (2 * (sevenNineRadial 1 1 1 : ℝ) * (sevenNineRadial 5 1 1 : ℝ)) := by
    have hq : (sevenNineRadial 1 1 1)^2 + (sevenNineRadial 5 1 1)^2 - sevenNineDistanceLower[9]!^2 ≤
        sevenNineCosUpper[39]! * (2 * sevenNineRadial 1 1 1 * sevenNineRadial 5 1 1) := by native_decide
    have hqR :
        (sevenNineRadial 1 1 1 : ℝ)^2 + (sevenNineRadial 5 1 1 : ℝ)^2 - (sevenNineDistanceLower[9]! : ℝ)^2 ≤
          (sevenNineCosUpper[39]! : ℝ) * (2 * (sevenNineRadial 1 1 1 : ℝ) * (sevenNineRadial 5 1 1 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 1 1 1 : ℝ)^2 + (sevenNineRadial 5 1 1 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 1 1 1 : ℝ)^2 + (sevenNineRadial 5 1 1 : ℝ)^2 - (sevenNineDistanceLower[9]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have htouch := corner_touch_cosine_bound haL haU hbL hbU
    (by norm_num [sevenNineRadial, sevenNineRadialBounds])
    (by norm_num [sevenNineRadial, sevenNineRadialBounds]) h00 h01 h10 h11
  have hcos : (sevenNineCosUpper[39]! : ℝ) ≤ Real.cos ((102794120711369334194 : ℝ) / 100000000000000000000) := by
    apply lower_bound_of_taylor_error
      (cosine_taylor_ninety_six_remainder (a := 0) (b := 4) (x := ((102794120711369334194 : ℝ) / 100000000000000000000) )
        (by norm_num) (by constructor <;> norm_num [Real.pi_gt_d20, Real.pi_lt_four]))
    rw [cosine_taylor_ninety_six_at_zero (b := 4) (x := ((102794120711369334194 : ℝ) / 100000000000000000000)) (by norm_num)]
    have hp : (sevenNineCosUpper[39]! : Rat) + (((102794120711369334194 : Rat) / 100000000000000000000) : Rat)^97 / (Nat.factorial 96) ≤
        Finset.sum (Finset.range 49) (fun k => (-1 : Rat)^k * (((102794120711369334194 : Rat) / 100000000000000000000) : Rat)^(2*k) / Nat.factorial (2*k)) := by native_decide
    have hpR : (sevenNineCosUpper[39]! : ℝ) + ((102794120711369334194 : ℝ) / 100000000000000000000)^97 / (Nat.factorial 96) ≤
        Finset.sum (Finset.range 49) (fun k => (-1 : ℝ)^k * ((102794120711369334194 : ℝ) / 100000000000000000000)^(2*k) / Nat.factorial (2*k)) := by
      norm_num [sevenNineCosUpper, Finset.sum_range_succ]
    simpa [sub_zero] using hpR
  have hangle : ((102794120711369334194 : ℝ) / 100000000000000000000) ≤ Real.arccos (touchCosine a b (Real.sqrt 5 + Real.sqrt 9)) := by
    exact angle_lower_bound_of_cosine (by norm_num)
      (by
        calc
          ((102794120711369334194 : ℝ) / 100000000000000000000) ≤ (314159265358979323846 : ℝ) / 100000000000000000000 := by norm_num
          _ ≤ Real.pi := by
            have hpi := Real.pi_gt_d20.le
            norm_num at hpi ⊢
            exact hpi) (le_trans htouch hcos)
  have hdata : sevenNineAngleLower[39]! = ((102794120711369334194 : Rat) / 100000000000000000000) := by native_decide
  have hdataR : (sevenNineAngleLower[39]! : ℝ) = ((102794120711369334194 : ℝ) / 100000000000000000000) := by
    have h := congrArg (fun q : Rat => (q : ℝ)) hdata
    convert h using 1 ; norm_num
  rw [hdataR]
  exact hangle

theorem sevenNineAngle_1_6_0_0 {a b : ℝ}
    (haL : (sevenNineRadial 1 0 0 : ℝ) ≤ a) (haU : a ≤ (sevenNineRadial 1 0 1 : ℝ))
    (hbL : (sevenNineRadial 6 0 0 : ℝ) ≤ b) (hbU : b ≤ (sevenNineRadial 6 0 1 : ℝ)) :
    (sevenNineAngleLower[40]! : ℝ) ≤ Real.arccos (touchCosine a b (Real.sqrt 5 + Real.sqrt 10)) := by
  let d : ℝ := Real.sqrt 5 + Real.sqrt 10
  have hd' : (((5398345637668169028408067213163994769160173498936742551128402098203115364277043120758662516 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) : ℝ) ≤ d := by
    dsimp [d]
    have h := rat_sum_sqrt_lower (q := ((5398345637668169028408067213163994769160173498936742551128402098203115364277043120758662516 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (qi := ((2236067977499789696409173668731276235440618359611525724270897245410520925637804899414414408378782274969508176150773783504 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (qj := ((3162277660168379331998893544432718533719555139325216826857504852792594438639238221344248108379300295187347284152840055148 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))
      (ni := 5) (nj := 10)
      (by convert sqrt_lower_5 using 1 ; norm_num)
      (by convert sqrt_lower_10 using 1 ; norm_num)
      (by native_decide)
    convert h using 1 ; norm_num
  have hd : (((5398345637668169028408067213163994769160173498936742551128402098203115364277043120758662516 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) ≤ d := by exact hd'
  have hd2 : (((5398345637668169028408067213163994769160173498936742551128402098203115364277043120758662516 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))^2 ≤ d^2 := by
    have hq : (0 : ℝ) ≤ ((5398345637668169028408067213163994769160173498936742551128402098203115364277043120758662516 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) := by norm_num
    have hdn : 0 ≤ d := by positivity
    exact (sq_le_sq₀ hq hdn).mpr hd
  have hd2' : (sevenNineDistanceLower[10]! : ℝ)^2 ≤ d^2 := by
    convert hd2 using 1 ; norm_num [sevenNineDistanceLower]
  have h00 : (sevenNineRadial 1 0 0 : ℝ)^2 + (sevenNineRadial 6 0 0 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[40]! : ℝ) * (2 * (sevenNineRadial 1 0 0 : ℝ) * (sevenNineRadial 6 0 0 : ℝ)) := by
    have hq : (sevenNineRadial 1 0 0)^2 + (sevenNineRadial 6 0 0)^2 - sevenNineDistanceLower[10]!^2 ≤
        sevenNineCosUpper[40]! * (2 * sevenNineRadial 1 0 0 * sevenNineRadial 6 0 0) := by native_decide
    have hqR :
        (sevenNineRadial 1 0 0 : ℝ)^2 + (sevenNineRadial 6 0 0 : ℝ)^2 - (sevenNineDistanceLower[10]! : ℝ)^2 ≤
          (sevenNineCosUpper[40]! : ℝ) * (2 * (sevenNineRadial 1 0 0 : ℝ) * (sevenNineRadial 6 0 0 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 1 0 0 : ℝ)^2 + (sevenNineRadial 6 0 0 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 1 0 0 : ℝ)^2 + (sevenNineRadial 6 0 0 : ℝ)^2 - (sevenNineDistanceLower[10]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h01 : (sevenNineRadial 1 0 0 : ℝ)^2 + (sevenNineRadial 6 0 1 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[40]! : ℝ) * (2 * (sevenNineRadial 1 0 0 : ℝ) * (sevenNineRadial 6 0 1 : ℝ)) := by
    have hq : (sevenNineRadial 1 0 0)^2 + (sevenNineRadial 6 0 1)^2 - sevenNineDistanceLower[10]!^2 ≤
        sevenNineCosUpper[40]! * (2 * sevenNineRadial 1 0 0 * sevenNineRadial 6 0 1) := by native_decide
    have hqR :
        (sevenNineRadial 1 0 0 : ℝ)^2 + (sevenNineRadial 6 0 1 : ℝ)^2 - (sevenNineDistanceLower[10]! : ℝ)^2 ≤
          (sevenNineCosUpper[40]! : ℝ) * (2 * (sevenNineRadial 1 0 0 : ℝ) * (sevenNineRadial 6 0 1 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 1 0 0 : ℝ)^2 + (sevenNineRadial 6 0 1 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 1 0 0 : ℝ)^2 + (sevenNineRadial 6 0 1 : ℝ)^2 - (sevenNineDistanceLower[10]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h10 : (sevenNineRadial 1 0 1 : ℝ)^2 + (sevenNineRadial 6 0 0 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[40]! : ℝ) * (2 * (sevenNineRadial 1 0 1 : ℝ) * (sevenNineRadial 6 0 0 : ℝ)) := by
    have hq : (sevenNineRadial 1 0 1)^2 + (sevenNineRadial 6 0 0)^2 - sevenNineDistanceLower[10]!^2 ≤
        sevenNineCosUpper[40]! * (2 * sevenNineRadial 1 0 1 * sevenNineRadial 6 0 0) := by native_decide
    have hqR :
        (sevenNineRadial 1 0 1 : ℝ)^2 + (sevenNineRadial 6 0 0 : ℝ)^2 - (sevenNineDistanceLower[10]! : ℝ)^2 ≤
          (sevenNineCosUpper[40]! : ℝ) * (2 * (sevenNineRadial 1 0 1 : ℝ) * (sevenNineRadial 6 0 0 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 1 0 1 : ℝ)^2 + (sevenNineRadial 6 0 0 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 1 0 1 : ℝ)^2 + (sevenNineRadial 6 0 0 : ℝ)^2 - (sevenNineDistanceLower[10]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h11 : (sevenNineRadial 1 0 1 : ℝ)^2 + (sevenNineRadial 6 0 1 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[40]! : ℝ) * (2 * (sevenNineRadial 1 0 1 : ℝ) * (sevenNineRadial 6 0 1 : ℝ)) := by
    have hq : (sevenNineRadial 1 0 1)^2 + (sevenNineRadial 6 0 1)^2 - sevenNineDistanceLower[10]!^2 ≤
        sevenNineCosUpper[40]! * (2 * sevenNineRadial 1 0 1 * sevenNineRadial 6 0 1) := by native_decide
    have hqR :
        (sevenNineRadial 1 0 1 : ℝ)^2 + (sevenNineRadial 6 0 1 : ℝ)^2 - (sevenNineDistanceLower[10]! : ℝ)^2 ≤
          (sevenNineCosUpper[40]! : ℝ) * (2 * (sevenNineRadial 1 0 1 : ℝ) * (sevenNineRadial 6 0 1 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 1 0 1 : ℝ)^2 + (sevenNineRadial 6 0 1 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 1 0 1 : ℝ)^2 + (sevenNineRadial 6 0 1 : ℝ)^2 - (sevenNineDistanceLower[10]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have htouch := corner_touch_cosine_bound haL haU hbL hbU
    (by norm_num [sevenNineRadial, sevenNineRadialBounds])
    (by norm_num [sevenNineRadial, sevenNineRadialBounds]) h00 h01 h10 h11
  have hcos : (sevenNineCosUpper[40]! : ℝ) ≤ Real.cos ((213475671412470423006 : ℝ) / 100000000000000000000) := by
    apply lower_bound_of_taylor_error
      (cosine_taylor_ninety_six_remainder (a := 0) (b := 4) (x := ((213475671412470423006 : ℝ) / 100000000000000000000) )
        (by norm_num) (by constructor <;> norm_num [Real.pi_gt_d20, Real.pi_lt_four]))
    rw [cosine_taylor_ninety_six_at_zero (b := 4) (x := ((213475671412470423006 : ℝ) / 100000000000000000000)) (by norm_num)]
    have hp : (sevenNineCosUpper[40]! : Rat) + (((213475671412470423006 : Rat) / 100000000000000000000) : Rat)^97 / (Nat.factorial 96) ≤
        Finset.sum (Finset.range 49) (fun k => (-1 : Rat)^k * (((213475671412470423006 : Rat) / 100000000000000000000) : Rat)^(2*k) / Nat.factorial (2*k)) := by native_decide
    have hpR : (sevenNineCosUpper[40]! : ℝ) + ((213475671412470423006 : ℝ) / 100000000000000000000)^97 / (Nat.factorial 96) ≤
        Finset.sum (Finset.range 49) (fun k => (-1 : ℝ)^k * ((213475671412470423006 : ℝ) / 100000000000000000000)^(2*k) / Nat.factorial (2*k)) := by
      norm_num [sevenNineCosUpper, Finset.sum_range_succ]
    simpa [sub_zero] using hpR
  have hangle : ((213475671412470423006 : ℝ) / 100000000000000000000) ≤ Real.arccos (touchCosine a b (Real.sqrt 5 + Real.sqrt 10)) := by
    exact angle_lower_bound_of_cosine (by norm_num)
      (by
        calc
          ((213475671412470423006 : ℝ) / 100000000000000000000) ≤ (314159265358979323846 : ℝ) / 100000000000000000000 := by norm_num
          _ ≤ Real.pi := by
            have hpi := Real.pi_gt_d20.le
            norm_num at hpi ⊢
            exact hpi) (le_trans htouch hcos)
  have hdata : sevenNineAngleLower[40]! = ((213475671412470423006 : Rat) / 100000000000000000000) := by native_decide
  have hdataR : (sevenNineAngleLower[40]! : ℝ) = ((213475671412470423006 : ℝ) / 100000000000000000000) := by
    have h := congrArg (fun q : Rat => (q : ℝ)) hdata
    convert h using 1 ; norm_num
  rw [hdataR]
  exact hangle

theorem sevenNineAngle_1_6_0_1 {a b : ℝ}
    (haL : (sevenNineRadial 1 0 0 : ℝ) ≤ a) (haU : a ≤ (sevenNineRadial 1 0 1 : ℝ))
    (hbL : (sevenNineRadial 6 1 0 : ℝ) ≤ b) (hbU : b ≤ (sevenNineRadial 6 1 1 : ℝ)) :
    (sevenNineAngleLower[41]! : ℝ) ≤ Real.arccos (touchCosine a b (Real.sqrt 5 + Real.sqrt 10)) := by
  let d : ℝ := Real.sqrt 5 + Real.sqrt 10
  have hd' : (((5398345637668169028408067213163994769160173498936742551128402098203115364277043120758662516 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) : ℝ) ≤ d := by
    dsimp [d]
    have h := rat_sum_sqrt_lower (q := ((5398345637668169028408067213163994769160173498936742551128402098203115364277043120758662516 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (qi := ((2236067977499789696409173668731276235440618359611525724270897245410520925637804899414414408378782274969508176150773783504 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (qj := ((3162277660168379331998893544432718533719555139325216826857504852792594438639238221344248108379300295187347284152840055148 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))
      (ni := 5) (nj := 10)
      (by convert sqrt_lower_5 using 1 ; norm_num)
      (by convert sqrt_lower_10 using 1 ; norm_num)
      (by native_decide)
    convert h using 1 ; norm_num
  have hd : (((5398345637668169028408067213163994769160173498936742551128402098203115364277043120758662516 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) ≤ d := by exact hd'
  have hd2 : (((5398345637668169028408067213163994769160173498936742551128402098203115364277043120758662516 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))^2 ≤ d^2 := by
    have hq : (0 : ℝ) ≤ ((5398345637668169028408067213163994769160173498936742551128402098203115364277043120758662516 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) := by norm_num
    have hdn : 0 ≤ d := by positivity
    exact (sq_le_sq₀ hq hdn).mpr hd
  have hd2' : (sevenNineDistanceLower[10]! : ℝ)^2 ≤ d^2 := by
    convert hd2 using 1 ; norm_num [sevenNineDistanceLower]
  have h00 : (sevenNineRadial 1 0 0 : ℝ)^2 + (sevenNineRadial 6 1 0 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[41]! : ℝ) * (2 * (sevenNineRadial 1 0 0 : ℝ) * (sevenNineRadial 6 1 0 : ℝ)) := by
    have hq : (sevenNineRadial 1 0 0)^2 + (sevenNineRadial 6 1 0)^2 - sevenNineDistanceLower[10]!^2 ≤
        sevenNineCosUpper[41]! * (2 * sevenNineRadial 1 0 0 * sevenNineRadial 6 1 0) := by native_decide
    have hqR :
        (sevenNineRadial 1 0 0 : ℝ)^2 + (sevenNineRadial 6 1 0 : ℝ)^2 - (sevenNineDistanceLower[10]! : ℝ)^2 ≤
          (sevenNineCosUpper[41]! : ℝ) * (2 * (sevenNineRadial 1 0 0 : ℝ) * (sevenNineRadial 6 1 0 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 1 0 0 : ℝ)^2 + (sevenNineRadial 6 1 0 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 1 0 0 : ℝ)^2 + (sevenNineRadial 6 1 0 : ℝ)^2 - (sevenNineDistanceLower[10]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h01 : (sevenNineRadial 1 0 0 : ℝ)^2 + (sevenNineRadial 6 1 1 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[41]! : ℝ) * (2 * (sevenNineRadial 1 0 0 : ℝ) * (sevenNineRadial 6 1 1 : ℝ)) := by
    have hq : (sevenNineRadial 1 0 0)^2 + (sevenNineRadial 6 1 1)^2 - sevenNineDistanceLower[10]!^2 ≤
        sevenNineCosUpper[41]! * (2 * sevenNineRadial 1 0 0 * sevenNineRadial 6 1 1) := by native_decide
    have hqR :
        (sevenNineRadial 1 0 0 : ℝ)^2 + (sevenNineRadial 6 1 1 : ℝ)^2 - (sevenNineDistanceLower[10]! : ℝ)^2 ≤
          (sevenNineCosUpper[41]! : ℝ) * (2 * (sevenNineRadial 1 0 0 : ℝ) * (sevenNineRadial 6 1 1 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 1 0 0 : ℝ)^2 + (sevenNineRadial 6 1 1 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 1 0 0 : ℝ)^2 + (sevenNineRadial 6 1 1 : ℝ)^2 - (sevenNineDistanceLower[10]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h10 : (sevenNineRadial 1 0 1 : ℝ)^2 + (sevenNineRadial 6 1 0 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[41]! : ℝ) * (2 * (sevenNineRadial 1 0 1 : ℝ) * (sevenNineRadial 6 1 0 : ℝ)) := by
    have hq : (sevenNineRadial 1 0 1)^2 + (sevenNineRadial 6 1 0)^2 - sevenNineDistanceLower[10]!^2 ≤
        sevenNineCosUpper[41]! * (2 * sevenNineRadial 1 0 1 * sevenNineRadial 6 1 0) := by native_decide
    have hqR :
        (sevenNineRadial 1 0 1 : ℝ)^2 + (sevenNineRadial 6 1 0 : ℝ)^2 - (sevenNineDistanceLower[10]! : ℝ)^2 ≤
          (sevenNineCosUpper[41]! : ℝ) * (2 * (sevenNineRadial 1 0 1 : ℝ) * (sevenNineRadial 6 1 0 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 1 0 1 : ℝ)^2 + (sevenNineRadial 6 1 0 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 1 0 1 : ℝ)^2 + (sevenNineRadial 6 1 0 : ℝ)^2 - (sevenNineDistanceLower[10]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h11 : (sevenNineRadial 1 0 1 : ℝ)^2 + (sevenNineRadial 6 1 1 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[41]! : ℝ) * (2 * (sevenNineRadial 1 0 1 : ℝ) * (sevenNineRadial 6 1 1 : ℝ)) := by
    have hq : (sevenNineRadial 1 0 1)^2 + (sevenNineRadial 6 1 1)^2 - sevenNineDistanceLower[10]!^2 ≤
        sevenNineCosUpper[41]! * (2 * sevenNineRadial 1 0 1 * sevenNineRadial 6 1 1) := by native_decide
    have hqR :
        (sevenNineRadial 1 0 1 : ℝ)^2 + (sevenNineRadial 6 1 1 : ℝ)^2 - (sevenNineDistanceLower[10]! : ℝ)^2 ≤
          (sevenNineCosUpper[41]! : ℝ) * (2 * (sevenNineRadial 1 0 1 : ℝ) * (sevenNineRadial 6 1 1 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 1 0 1 : ℝ)^2 + (sevenNineRadial 6 1 1 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 1 0 1 : ℝ)^2 + (sevenNineRadial 6 1 1 : ℝ)^2 - (sevenNineDistanceLower[10]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have htouch := corner_touch_cosine_bound haL haU hbL hbU
    (by norm_num [sevenNineRadial, sevenNineRadialBounds])
    (by norm_num [sevenNineRadial, sevenNineRadialBounds]) h00 h01 h10 h11
  have hcos : (sevenNineCosUpper[41]! : ℝ) ≤ Real.cos ((146031006929327691862 : ℝ) / 100000000000000000000) := by
    apply lower_bound_of_taylor_error
      (cosine_taylor_ninety_six_remainder (a := 0) (b := 4) (x := ((146031006929327691862 : ℝ) / 100000000000000000000) )
        (by norm_num) (by constructor <;> norm_num [Real.pi_gt_d20, Real.pi_lt_four]))
    rw [cosine_taylor_ninety_six_at_zero (b := 4) (x := ((146031006929327691862 : ℝ) / 100000000000000000000)) (by norm_num)]
    have hp : (sevenNineCosUpper[41]! : Rat) + (((146031006929327691862 : Rat) / 100000000000000000000) : Rat)^97 / (Nat.factorial 96) ≤
        Finset.sum (Finset.range 49) (fun k => (-1 : Rat)^k * (((146031006929327691862 : Rat) / 100000000000000000000) : Rat)^(2*k) / Nat.factorial (2*k)) := by native_decide
    have hpR : (sevenNineCosUpper[41]! : ℝ) + ((146031006929327691862 : ℝ) / 100000000000000000000)^97 / (Nat.factorial 96) ≤
        Finset.sum (Finset.range 49) (fun k => (-1 : ℝ)^k * ((146031006929327691862 : ℝ) / 100000000000000000000)^(2*k) / Nat.factorial (2*k)) := by
      norm_num [sevenNineCosUpper, Finset.sum_range_succ]
    simpa [sub_zero] using hpR
  have hangle : ((146031006929327691862 : ℝ) / 100000000000000000000) ≤ Real.arccos (touchCosine a b (Real.sqrt 5 + Real.sqrt 10)) := by
    exact angle_lower_bound_of_cosine (by norm_num)
      (by
        calc
          ((146031006929327691862 : ℝ) / 100000000000000000000) ≤ (314159265358979323846 : ℝ) / 100000000000000000000 := by norm_num
          _ ≤ Real.pi := by
            have hpi := Real.pi_gt_d20.le
            norm_num at hpi ⊢
            exact hpi) (le_trans htouch hcos)
  have hdata : sevenNineAngleLower[41]! = ((146031006929327691862 : Rat) / 100000000000000000000) := by native_decide
  have hdataR : (sevenNineAngleLower[41]! : ℝ) = ((146031006929327691862 : ℝ) / 100000000000000000000) := by
    have h := congrArg (fun q : Rat => (q : ℝ)) hdata
    convert h using 1 ; norm_num
  rw [hdataR]
  exact hangle

theorem sevenNineAngle_1_6_1_0 {a b : ℝ}
    (haL : (sevenNineRadial 1 1 0 : ℝ) ≤ a) (haU : a ≤ (sevenNineRadial 1 1 1 : ℝ))
    (hbL : (sevenNineRadial 6 0 0 : ℝ) ≤ b) (hbU : b ≤ (sevenNineRadial 6 0 1 : ℝ)) :
    (sevenNineAngleLower[42]! : ℝ) ≤ Real.arccos (touchCosine a b (Real.sqrt 5 + Real.sqrt 10)) := by
  let d : ℝ := Real.sqrt 5 + Real.sqrt 10
  have hd' : (((5398345637668169028408067213163994769160173498936742551128402098203115364277043120758662516 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) : ℝ) ≤ d := by
    dsimp [d]
    have h := rat_sum_sqrt_lower (q := ((5398345637668169028408067213163994769160173498936742551128402098203115364277043120758662516 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (qi := ((2236067977499789696409173668731276235440618359611525724270897245410520925637804899414414408378782274969508176150773783504 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (qj := ((3162277660168379331998893544432718533719555139325216826857504852792594438639238221344248108379300295187347284152840055148 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))
      (ni := 5) (nj := 10)
      (by convert sqrt_lower_5 using 1 ; norm_num)
      (by convert sqrt_lower_10 using 1 ; norm_num)
      (by native_decide)
    convert h using 1 ; norm_num
  have hd : (((5398345637668169028408067213163994769160173498936742551128402098203115364277043120758662516 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) ≤ d := by exact hd'
  have hd2 : (((5398345637668169028408067213163994769160173498936742551128402098203115364277043120758662516 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))^2 ≤ d^2 := by
    have hq : (0 : ℝ) ≤ ((5398345637668169028408067213163994769160173498936742551128402098203115364277043120758662516 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) := by norm_num
    have hdn : 0 ≤ d := by positivity
    exact (sq_le_sq₀ hq hdn).mpr hd
  have hd2' : (sevenNineDistanceLower[10]! : ℝ)^2 ≤ d^2 := by
    convert hd2 using 1 ; norm_num [sevenNineDistanceLower]
  have h00 : (sevenNineRadial 1 1 0 : ℝ)^2 + (sevenNineRadial 6 0 0 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[42]! : ℝ) * (2 * (sevenNineRadial 1 1 0 : ℝ) * (sevenNineRadial 6 0 0 : ℝ)) := by
    have hq : (sevenNineRadial 1 1 0)^2 + (sevenNineRadial 6 0 0)^2 - sevenNineDistanceLower[10]!^2 ≤
        sevenNineCosUpper[42]! * (2 * sevenNineRadial 1 1 0 * sevenNineRadial 6 0 0) := by native_decide
    have hqR :
        (sevenNineRadial 1 1 0 : ℝ)^2 + (sevenNineRadial 6 0 0 : ℝ)^2 - (sevenNineDistanceLower[10]! : ℝ)^2 ≤
          (sevenNineCosUpper[42]! : ℝ) * (2 * (sevenNineRadial 1 1 0 : ℝ) * (sevenNineRadial 6 0 0 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 1 1 0 : ℝ)^2 + (sevenNineRadial 6 0 0 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 1 1 0 : ℝ)^2 + (sevenNineRadial 6 0 0 : ℝ)^2 - (sevenNineDistanceLower[10]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h01 : (sevenNineRadial 1 1 0 : ℝ)^2 + (sevenNineRadial 6 0 1 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[42]! : ℝ) * (2 * (sevenNineRadial 1 1 0 : ℝ) * (sevenNineRadial 6 0 1 : ℝ)) := by
    have hq : (sevenNineRadial 1 1 0)^2 + (sevenNineRadial 6 0 1)^2 - sevenNineDistanceLower[10]!^2 ≤
        sevenNineCosUpper[42]! * (2 * sevenNineRadial 1 1 0 * sevenNineRadial 6 0 1) := by native_decide
    have hqR :
        (sevenNineRadial 1 1 0 : ℝ)^2 + (sevenNineRadial 6 0 1 : ℝ)^2 - (sevenNineDistanceLower[10]! : ℝ)^2 ≤
          (sevenNineCosUpper[42]! : ℝ) * (2 * (sevenNineRadial 1 1 0 : ℝ) * (sevenNineRadial 6 0 1 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 1 1 0 : ℝ)^2 + (sevenNineRadial 6 0 1 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 1 1 0 : ℝ)^2 + (sevenNineRadial 6 0 1 : ℝ)^2 - (sevenNineDistanceLower[10]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h10 : (sevenNineRadial 1 1 1 : ℝ)^2 + (sevenNineRadial 6 0 0 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[42]! : ℝ) * (2 * (sevenNineRadial 1 1 1 : ℝ) * (sevenNineRadial 6 0 0 : ℝ)) := by
    have hq : (sevenNineRadial 1 1 1)^2 + (sevenNineRadial 6 0 0)^2 - sevenNineDistanceLower[10]!^2 ≤
        sevenNineCosUpper[42]! * (2 * sevenNineRadial 1 1 1 * sevenNineRadial 6 0 0) := by native_decide
    have hqR :
        (sevenNineRadial 1 1 1 : ℝ)^2 + (sevenNineRadial 6 0 0 : ℝ)^2 - (sevenNineDistanceLower[10]! : ℝ)^2 ≤
          (sevenNineCosUpper[42]! : ℝ) * (2 * (sevenNineRadial 1 1 1 : ℝ) * (sevenNineRadial 6 0 0 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 1 1 1 : ℝ)^2 + (sevenNineRadial 6 0 0 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 1 1 1 : ℝ)^2 + (sevenNineRadial 6 0 0 : ℝ)^2 - (sevenNineDistanceLower[10]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h11 : (sevenNineRadial 1 1 1 : ℝ)^2 + (sevenNineRadial 6 0 1 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[42]! : ℝ) * (2 * (sevenNineRadial 1 1 1 : ℝ) * (sevenNineRadial 6 0 1 : ℝ)) := by
    have hq : (sevenNineRadial 1 1 1)^2 + (sevenNineRadial 6 0 1)^2 - sevenNineDistanceLower[10]!^2 ≤
        sevenNineCosUpper[42]! * (2 * sevenNineRadial 1 1 1 * sevenNineRadial 6 0 1) := by native_decide
    have hqR :
        (sevenNineRadial 1 1 1 : ℝ)^2 + (sevenNineRadial 6 0 1 : ℝ)^2 - (sevenNineDistanceLower[10]! : ℝ)^2 ≤
          (sevenNineCosUpper[42]! : ℝ) * (2 * (sevenNineRadial 1 1 1 : ℝ) * (sevenNineRadial 6 0 1 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 1 1 1 : ℝ)^2 + (sevenNineRadial 6 0 1 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 1 1 1 : ℝ)^2 + (sevenNineRadial 6 0 1 : ℝ)^2 - (sevenNineDistanceLower[10]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have htouch := corner_touch_cosine_bound haL haU hbL hbU
    (by norm_num [sevenNineRadial, sevenNineRadialBounds])
    (by norm_num [sevenNineRadial, sevenNineRadialBounds]) h00 h01 h10 h11
  have hcos : (sevenNineCosUpper[42]! : ℝ) ≤ Real.cos ((121185108972647733964 : ℝ) / 100000000000000000000) := by
    apply lower_bound_of_taylor_error
      (cosine_taylor_ninety_six_remainder (a := 0) (b := 4) (x := ((121185108972647733964 : ℝ) / 100000000000000000000) )
        (by norm_num) (by constructor <;> norm_num [Real.pi_gt_d20, Real.pi_lt_four]))
    rw [cosine_taylor_ninety_six_at_zero (b := 4) (x := ((121185108972647733964 : ℝ) / 100000000000000000000)) (by norm_num)]
    have hp : (sevenNineCosUpper[42]! : Rat) + (((121185108972647733964 : Rat) / 100000000000000000000) : Rat)^97 / (Nat.factorial 96) ≤
        Finset.sum (Finset.range 49) (fun k => (-1 : Rat)^k * (((121185108972647733964 : Rat) / 100000000000000000000) : Rat)^(2*k) / Nat.factorial (2*k)) := by native_decide
    have hpR : (sevenNineCosUpper[42]! : ℝ) + ((121185108972647733964 : ℝ) / 100000000000000000000)^97 / (Nat.factorial 96) ≤
        Finset.sum (Finset.range 49) (fun k => (-1 : ℝ)^k * ((121185108972647733964 : ℝ) / 100000000000000000000)^(2*k) / Nat.factorial (2*k)) := by
      norm_num [sevenNineCosUpper, Finset.sum_range_succ]
    simpa [sub_zero] using hpR
  have hangle : ((121185108972647733964 : ℝ) / 100000000000000000000) ≤ Real.arccos (touchCosine a b (Real.sqrt 5 + Real.sqrt 10)) := by
    exact angle_lower_bound_of_cosine (by norm_num)
      (by
        calc
          ((121185108972647733964 : ℝ) / 100000000000000000000) ≤ (314159265358979323846 : ℝ) / 100000000000000000000 := by norm_num
          _ ≤ Real.pi := by
            have hpi := Real.pi_gt_d20.le
            norm_num at hpi ⊢
            exact hpi) (le_trans htouch hcos)
  have hdata : sevenNineAngleLower[42]! = ((121185108972647733964 : Rat) / 100000000000000000000) := by native_decide
  have hdataR : (sevenNineAngleLower[42]! : ℝ) = ((121185108972647733964 : ℝ) / 100000000000000000000) := by
    have h := congrArg (fun q : Rat => (q : ℝ)) hdata
    convert h using 1 ; norm_num
  rw [hdataR]
  exact hangle

theorem sevenNineAngle_1_6_1_1 {a b : ℝ}
    (haL : (sevenNineRadial 1 1 0 : ℝ) ≤ a) (haU : a ≤ (sevenNineRadial 1 1 1 : ℝ))
    (hbL : (sevenNineRadial 6 1 0 : ℝ) ≤ b) (hbU : b ≤ (sevenNineRadial 6 1 1 : ℝ)) :
    (sevenNineAngleLower[43]! : ℝ) ≤ Real.arccos (touchCosine a b (Real.sqrt 5 + Real.sqrt 10)) := by
  let d : ℝ := Real.sqrt 5 + Real.sqrt 10
  have hd' : (((5398345637668169028408067213163994769160173498936742551128402098203115364277043120758662516 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) : ℝ) ≤ d := by
    dsimp [d]
    have h := rat_sum_sqrt_lower (q := ((5398345637668169028408067213163994769160173498936742551128402098203115364277043120758662516 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (qi := ((2236067977499789696409173668731276235440618359611525724270897245410520925637804899414414408378782274969508176150773783504 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (qj := ((3162277660168379331998893544432718533719555139325216826857504852792594438639238221344248108379300295187347284152840055148 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))
      (ni := 5) (nj := 10)
      (by convert sqrt_lower_5 using 1 ; norm_num)
      (by convert sqrt_lower_10 using 1 ; norm_num)
      (by native_decide)
    convert h using 1 ; norm_num
  have hd : (((5398345637668169028408067213163994769160173498936742551128402098203115364277043120758662516 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) ≤ d := by exact hd'
  have hd2 : (((5398345637668169028408067213163994769160173498936742551128402098203115364277043120758662516 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))^2 ≤ d^2 := by
    have hq : (0 : ℝ) ≤ ((5398345637668169028408067213163994769160173498936742551128402098203115364277043120758662516 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) := by norm_num
    have hdn : 0 ≤ d := by positivity
    exact (sq_le_sq₀ hq hdn).mpr hd
  have hd2' : (sevenNineDistanceLower[10]! : ℝ)^2 ≤ d^2 := by
    convert hd2 using 1 ; norm_num [sevenNineDistanceLower]
  have h00 : (sevenNineRadial 1 1 0 : ℝ)^2 + (sevenNineRadial 6 1 0 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[43]! : ℝ) * (2 * (sevenNineRadial 1 1 0 : ℝ) * (sevenNineRadial 6 1 0 : ℝ)) := by
    have hq : (sevenNineRadial 1 1 0)^2 + (sevenNineRadial 6 1 0)^2 - sevenNineDistanceLower[10]!^2 ≤
        sevenNineCosUpper[43]! * (2 * sevenNineRadial 1 1 0 * sevenNineRadial 6 1 0) := by native_decide
    have hqR :
        (sevenNineRadial 1 1 0 : ℝ)^2 + (sevenNineRadial 6 1 0 : ℝ)^2 - (sevenNineDistanceLower[10]! : ℝ)^2 ≤
          (sevenNineCosUpper[43]! : ℝ) * (2 * (sevenNineRadial 1 1 0 : ℝ) * (sevenNineRadial 6 1 0 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 1 1 0 : ℝ)^2 + (sevenNineRadial 6 1 0 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 1 1 0 : ℝ)^2 + (sevenNineRadial 6 1 0 : ℝ)^2 - (sevenNineDistanceLower[10]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h01 : (sevenNineRadial 1 1 0 : ℝ)^2 + (sevenNineRadial 6 1 1 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[43]! : ℝ) * (2 * (sevenNineRadial 1 1 0 : ℝ) * (sevenNineRadial 6 1 1 : ℝ)) := by
    have hq : (sevenNineRadial 1 1 0)^2 + (sevenNineRadial 6 1 1)^2 - sevenNineDistanceLower[10]!^2 ≤
        sevenNineCosUpper[43]! * (2 * sevenNineRadial 1 1 0 * sevenNineRadial 6 1 1) := by native_decide
    have hqR :
        (sevenNineRadial 1 1 0 : ℝ)^2 + (sevenNineRadial 6 1 1 : ℝ)^2 - (sevenNineDistanceLower[10]! : ℝ)^2 ≤
          (sevenNineCosUpper[43]! : ℝ) * (2 * (sevenNineRadial 1 1 0 : ℝ) * (sevenNineRadial 6 1 1 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 1 1 0 : ℝ)^2 + (sevenNineRadial 6 1 1 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 1 1 0 : ℝ)^2 + (sevenNineRadial 6 1 1 : ℝ)^2 - (sevenNineDistanceLower[10]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h10 : (sevenNineRadial 1 1 1 : ℝ)^2 + (sevenNineRadial 6 1 0 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[43]! : ℝ) * (2 * (sevenNineRadial 1 1 1 : ℝ) * (sevenNineRadial 6 1 0 : ℝ)) := by
    have hq : (sevenNineRadial 1 1 1)^2 + (sevenNineRadial 6 1 0)^2 - sevenNineDistanceLower[10]!^2 ≤
        sevenNineCosUpper[43]! * (2 * sevenNineRadial 1 1 1 * sevenNineRadial 6 1 0) := by native_decide
    have hqR :
        (sevenNineRadial 1 1 1 : ℝ)^2 + (sevenNineRadial 6 1 0 : ℝ)^2 - (sevenNineDistanceLower[10]! : ℝ)^2 ≤
          (sevenNineCosUpper[43]! : ℝ) * (2 * (sevenNineRadial 1 1 1 : ℝ) * (sevenNineRadial 6 1 0 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 1 1 1 : ℝ)^2 + (sevenNineRadial 6 1 0 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 1 1 1 : ℝ)^2 + (sevenNineRadial 6 1 0 : ℝ)^2 - (sevenNineDistanceLower[10]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h11 : (sevenNineRadial 1 1 1 : ℝ)^2 + (sevenNineRadial 6 1 1 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[43]! : ℝ) * (2 * (sevenNineRadial 1 1 1 : ℝ) * (sevenNineRadial 6 1 1 : ℝ)) := by
    have hq : (sevenNineRadial 1 1 1)^2 + (sevenNineRadial 6 1 1)^2 - sevenNineDistanceLower[10]!^2 ≤
        sevenNineCosUpper[43]! * (2 * sevenNineRadial 1 1 1 * sevenNineRadial 6 1 1) := by native_decide
    have hqR :
        (sevenNineRadial 1 1 1 : ℝ)^2 + (sevenNineRadial 6 1 1 : ℝ)^2 - (sevenNineDistanceLower[10]! : ℝ)^2 ≤
          (sevenNineCosUpper[43]! : ℝ) * (2 * (sevenNineRadial 1 1 1 : ℝ) * (sevenNineRadial 6 1 1 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 1 1 1 : ℝ)^2 + (sevenNineRadial 6 1 1 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 1 1 1 : ℝ)^2 + (sevenNineRadial 6 1 1 : ℝ)^2 - (sevenNineDistanceLower[10]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have htouch := corner_touch_cosine_bound haL haU hbL hbU
    (by norm_num [sevenNineRadial, sevenNineRadialBounds])
    (by norm_num [sevenNineRadial, sevenNineRadialBounds]) h00 h01 h10 h11
  have hcos : (sevenNineCosUpper[43]! : ℝ) ≤ Real.cos ((107812673195403123741 : ℝ) / 100000000000000000000) := by
    apply lower_bound_of_taylor_error
      (cosine_taylor_ninety_six_remainder (a := 0) (b := 4) (x := ((107812673195403123741 : ℝ) / 100000000000000000000) )
        (by norm_num) (by constructor <;> norm_num [Real.pi_gt_d20, Real.pi_lt_four]))
    rw [cosine_taylor_ninety_six_at_zero (b := 4) (x := ((107812673195403123741 : ℝ) / 100000000000000000000)) (by norm_num)]
    have hp : (sevenNineCosUpper[43]! : Rat) + (((107812673195403123741 : Rat) / 100000000000000000000) : Rat)^97 / (Nat.factorial 96) ≤
        Finset.sum (Finset.range 49) (fun k => (-1 : Rat)^k * (((107812673195403123741 : Rat) / 100000000000000000000) : Rat)^(2*k) / Nat.factorial (2*k)) := by native_decide
    have hpR : (sevenNineCosUpper[43]! : ℝ) + ((107812673195403123741 : ℝ) / 100000000000000000000)^97 / (Nat.factorial 96) ≤
        Finset.sum (Finset.range 49) (fun k => (-1 : ℝ)^k * ((107812673195403123741 : ℝ) / 100000000000000000000)^(2*k) / Nat.factorial (2*k)) := by
      norm_num [sevenNineCosUpper, Finset.sum_range_succ]
    simpa [sub_zero] using hpR
  have hangle : ((107812673195403123741 : ℝ) / 100000000000000000000) ≤ Real.arccos (touchCosine a b (Real.sqrt 5 + Real.sqrt 10)) := by
    exact angle_lower_bound_of_cosine (by norm_num)
      (by
        calc
          ((107812673195403123741 : ℝ) / 100000000000000000000) ≤ (314159265358979323846 : ℝ) / 100000000000000000000 := by norm_num
          _ ≤ Real.pi := by
            have hpi := Real.pi_gt_d20.le
            norm_num at hpi ⊢
            exact hpi) (le_trans htouch hcos)
  have hdata : sevenNineAngleLower[43]! = ((107812673195403123741 : Rat) / 100000000000000000000) := by native_decide
  have hdataR : (sevenNineAngleLower[43]! : ℝ) = ((107812673195403123741 : ℝ) / 100000000000000000000) := by
    have h := congrArg (fun q : Rat => (q : ℝ)) hdata
    convert h using 1 ; norm_num
  rw [hdataR]
  exact hangle

theorem sevenNineAngle_2_3_0_0 {a b : ℝ}
    (haL : (sevenNineRadial 2 0 0 : ℝ) ≤ a) (haU : a ≤ (sevenNineRadial 2 0 1 : ℝ))
    (hbL : (sevenNineRadial 3 0 0 : ℝ) ≤ b) (hbU : b ≤ (sevenNineRadial 3 0 1 : ℝ)) :
    (sevenNineAngleLower[44]! : ℝ) ≤ Real.arccos (touchCosine a b (Real.sqrt 6 + Real.sqrt 7)) := by
  let d : ℝ := Real.sqrt 6 + Real.sqrt 7
  have hd' : (((5095241053847768688698899828345151817676206663739120308801027026452029200687598654300252319 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) : ℝ) ≤ d := by
    dsimp [d]
    have h := rat_sum_sqrt_lower (q := ((5095241053847768688698899828345151817676206663739120308801027026452029200687598654300252319 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (qi := ((2449489742783178098197284074705891391965947480656670128432692567250960377457315026539859433104640234818594601226614189124 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (qj := ((2645751311064590590501615753639260425710259183082450180368334459201068823230283627760392886474543610615064578338497463095 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))
      (ni := 6) (nj := 7)
      (by convert sqrt_lower_6 using 1 ; norm_num)
      (by convert sqrt_lower_7 using 1 ; norm_num)
      (by native_decide)
    convert h using 1 ; norm_num
  have hd : (((5095241053847768688698899828345151817676206663739120308801027026452029200687598654300252319 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) ≤ d := by exact hd'
  have hd2 : (((5095241053847768688698899828345151817676206663739120308801027026452029200687598654300252319 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))^2 ≤ d^2 := by
    have hq : (0 : ℝ) ≤ ((5095241053847768688698899828345151817676206663739120308801027026452029200687598654300252319 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) := by norm_num
    have hdn : 0 ≤ d := by positivity
    exact (sq_le_sq₀ hq hdn).mpr hd
  have hd2' : (sevenNineDistanceLower[11]! : ℝ)^2 ≤ d^2 := by
    convert hd2 using 1 ; norm_num [sevenNineDistanceLower]
  have h00 : (sevenNineRadial 2 0 0 : ℝ)^2 + (sevenNineRadial 3 0 0 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[44]! : ℝ) * (2 * (sevenNineRadial 2 0 0 : ℝ) * (sevenNineRadial 3 0 0 : ℝ)) := by
    have hq : (sevenNineRadial 2 0 0)^2 + (sevenNineRadial 3 0 0)^2 - sevenNineDistanceLower[11]!^2 ≤
        sevenNineCosUpper[44]! * (2 * sevenNineRadial 2 0 0 * sevenNineRadial 3 0 0) := by native_decide
    have hqR :
        (sevenNineRadial 2 0 0 : ℝ)^2 + (sevenNineRadial 3 0 0 : ℝ)^2 - (sevenNineDistanceLower[11]! : ℝ)^2 ≤
          (sevenNineCosUpper[44]! : ℝ) * (2 * (sevenNineRadial 2 0 0 : ℝ) * (sevenNineRadial 3 0 0 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 2 0 0 : ℝ)^2 + (sevenNineRadial 3 0 0 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 2 0 0 : ℝ)^2 + (sevenNineRadial 3 0 0 : ℝ)^2 - (sevenNineDistanceLower[11]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h01 : (sevenNineRadial 2 0 0 : ℝ)^2 + (sevenNineRadial 3 0 1 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[44]! : ℝ) * (2 * (sevenNineRadial 2 0 0 : ℝ) * (sevenNineRadial 3 0 1 : ℝ)) := by
    have hq : (sevenNineRadial 2 0 0)^2 + (sevenNineRadial 3 0 1)^2 - sevenNineDistanceLower[11]!^2 ≤
        sevenNineCosUpper[44]! * (2 * sevenNineRadial 2 0 0 * sevenNineRadial 3 0 1) := by native_decide
    have hqR :
        (sevenNineRadial 2 0 0 : ℝ)^2 + (sevenNineRadial 3 0 1 : ℝ)^2 - (sevenNineDistanceLower[11]! : ℝ)^2 ≤
          (sevenNineCosUpper[44]! : ℝ) * (2 * (sevenNineRadial 2 0 0 : ℝ) * (sevenNineRadial 3 0 1 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 2 0 0 : ℝ)^2 + (sevenNineRadial 3 0 1 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 2 0 0 : ℝ)^2 + (sevenNineRadial 3 0 1 : ℝ)^2 - (sevenNineDistanceLower[11]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h10 : (sevenNineRadial 2 0 1 : ℝ)^2 + (sevenNineRadial 3 0 0 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[44]! : ℝ) * (2 * (sevenNineRadial 2 0 1 : ℝ) * (sevenNineRadial 3 0 0 : ℝ)) := by
    have hq : (sevenNineRadial 2 0 1)^2 + (sevenNineRadial 3 0 0)^2 - sevenNineDistanceLower[11]!^2 ≤
        sevenNineCosUpper[44]! * (2 * sevenNineRadial 2 0 1 * sevenNineRadial 3 0 0) := by native_decide
    have hqR :
        (sevenNineRadial 2 0 1 : ℝ)^2 + (sevenNineRadial 3 0 0 : ℝ)^2 - (sevenNineDistanceLower[11]! : ℝ)^2 ≤
          (sevenNineCosUpper[44]! : ℝ) * (2 * (sevenNineRadial 2 0 1 : ℝ) * (sevenNineRadial 3 0 0 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 2 0 1 : ℝ)^2 + (sevenNineRadial 3 0 0 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 2 0 1 : ℝ)^2 + (sevenNineRadial 3 0 0 : ℝ)^2 - (sevenNineDistanceLower[11]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h11 : (sevenNineRadial 2 0 1 : ℝ)^2 + (sevenNineRadial 3 0 1 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[44]! : ℝ) * (2 * (sevenNineRadial 2 0 1 : ℝ) * (sevenNineRadial 3 0 1 : ℝ)) := by
    have hq : (sevenNineRadial 2 0 1)^2 + (sevenNineRadial 3 0 1)^2 - sevenNineDistanceLower[11]!^2 ≤
        sevenNineCosUpper[44]! * (2 * sevenNineRadial 2 0 1 * sevenNineRadial 3 0 1) := by native_decide
    have hqR :
        (sevenNineRadial 2 0 1 : ℝ)^2 + (sevenNineRadial 3 0 1 : ℝ)^2 - (sevenNineDistanceLower[11]! : ℝ)^2 ≤
          (sevenNineCosUpper[44]! : ℝ) * (2 * (sevenNineRadial 2 0 1 : ℝ) * (sevenNineRadial 3 0 1 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 2 0 1 : ℝ)^2 + (sevenNineRadial 3 0 1 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 2 0 1 : ℝ)^2 + (sevenNineRadial 3 0 1 : ℝ)^2 - (sevenNineDistanceLower[11]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have htouch := corner_touch_cosine_bound haL haU hbL hbU
    (by norm_num [sevenNineRadial, sevenNineRadialBounds])
    (by norm_num [sevenNineRadial, sevenNineRadialBounds]) h00 h01 h10 h11
  have hcos : (sevenNineCosUpper[44]! : ℝ) ≤ Real.cos ((187347069658106888650 : ℝ) / 100000000000000000000) := by
    apply lower_bound_of_taylor_error
      (cosine_taylor_ninety_six_remainder (a := 0) (b := 4) (x := ((187347069658106888650 : ℝ) / 100000000000000000000) )
        (by norm_num) (by constructor <;> norm_num [Real.pi_gt_d20, Real.pi_lt_four]))
    rw [cosine_taylor_ninety_six_at_zero (b := 4) (x := ((187347069658106888650 : ℝ) / 100000000000000000000)) (by norm_num)]
    have hp : (sevenNineCosUpper[44]! : Rat) + (((187347069658106888650 : Rat) / 100000000000000000000) : Rat)^97 / (Nat.factorial 96) ≤
        Finset.sum (Finset.range 49) (fun k => (-1 : Rat)^k * (((187347069658106888650 : Rat) / 100000000000000000000) : Rat)^(2*k) / Nat.factorial (2*k)) := by native_decide
    have hpR : (sevenNineCosUpper[44]! : ℝ) + ((187347069658106888650 : ℝ) / 100000000000000000000)^97 / (Nat.factorial 96) ≤
        Finset.sum (Finset.range 49) (fun k => (-1 : ℝ)^k * ((187347069658106888650 : ℝ) / 100000000000000000000)^(2*k) / Nat.factorial (2*k)) := by
      norm_num [sevenNineCosUpper, Finset.sum_range_succ]
    simpa [sub_zero] using hpR
  have hangle : ((187347069658106888650 : ℝ) / 100000000000000000000) ≤ Real.arccos (touchCosine a b (Real.sqrt 6 + Real.sqrt 7)) := by
    exact angle_lower_bound_of_cosine (by norm_num)
      (by
        calc
          ((187347069658106888650 : ℝ) / 100000000000000000000) ≤ (314159265358979323846 : ℝ) / 100000000000000000000 := by norm_num
          _ ≤ Real.pi := by
            have hpi := Real.pi_gt_d20.le
            norm_num at hpi ⊢
            exact hpi) (le_trans htouch hcos)
  have hdata : sevenNineAngleLower[44]! = ((187347069658106888650 : Rat) / 100000000000000000000) := by native_decide
  have hdataR : (sevenNineAngleLower[44]! : ℝ) = ((187347069658106888650 : ℝ) / 100000000000000000000) := by
    have h := congrArg (fun q : Rat => (q : ℝ)) hdata
    convert h using 1 ; norm_num
  rw [hdataR]
  exact hangle

theorem sevenNineAngle_2_3_0_1 {a b : ℝ}
    (haL : (sevenNineRadial 2 0 0 : ℝ) ≤ a) (haU : a ≤ (sevenNineRadial 2 0 1 : ℝ))
    (hbL : (sevenNineRadial 3 1 0 : ℝ) ≤ b) (hbU : b ≤ (sevenNineRadial 3 1 1 : ℝ)) :
    (sevenNineAngleLower[45]! : ℝ) ≤ Real.arccos (touchCosine a b (Real.sqrt 6 + Real.sqrt 7)) := by
  let d : ℝ := Real.sqrt 6 + Real.sqrt 7
  have hd' : (((5095241053847768688698899828345151817676206663739120308801027026452029200687598654300252319 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) : ℝ) ≤ d := by
    dsimp [d]
    have h := rat_sum_sqrt_lower (q := ((5095241053847768688698899828345151817676206663739120308801027026452029200687598654300252319 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (qi := ((2449489742783178098197284074705891391965947480656670128432692567250960377457315026539859433104640234818594601226614189124 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (qj := ((2645751311064590590501615753639260425710259183082450180368334459201068823230283627760392886474543610615064578338497463095 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))
      (ni := 6) (nj := 7)
      (by convert sqrt_lower_6 using 1 ; norm_num)
      (by convert sqrt_lower_7 using 1 ; norm_num)
      (by native_decide)
    convert h using 1 ; norm_num
  have hd : (((5095241053847768688698899828345151817676206663739120308801027026452029200687598654300252319 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) ≤ d := by exact hd'
  have hd2 : (((5095241053847768688698899828345151817676206663739120308801027026452029200687598654300252319 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))^2 ≤ d^2 := by
    have hq : (0 : ℝ) ≤ ((5095241053847768688698899828345151817676206663739120308801027026452029200687598654300252319 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) := by norm_num
    have hdn : 0 ≤ d := by positivity
    exact (sq_le_sq₀ hq hdn).mpr hd
  have hd2' : (sevenNineDistanceLower[11]! : ℝ)^2 ≤ d^2 := by
    convert hd2 using 1 ; norm_num [sevenNineDistanceLower]
  have h00 : (sevenNineRadial 2 0 0 : ℝ)^2 + (sevenNineRadial 3 1 0 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[45]! : ℝ) * (2 * (sevenNineRadial 2 0 0 : ℝ) * (sevenNineRadial 3 1 0 : ℝ)) := by
    have hq : (sevenNineRadial 2 0 0)^2 + (sevenNineRadial 3 1 0)^2 - sevenNineDistanceLower[11]!^2 ≤
        sevenNineCosUpper[45]! * (2 * sevenNineRadial 2 0 0 * sevenNineRadial 3 1 0) := by native_decide
    have hqR :
        (sevenNineRadial 2 0 0 : ℝ)^2 + (sevenNineRadial 3 1 0 : ℝ)^2 - (sevenNineDistanceLower[11]! : ℝ)^2 ≤
          (sevenNineCosUpper[45]! : ℝ) * (2 * (sevenNineRadial 2 0 0 : ℝ) * (sevenNineRadial 3 1 0 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 2 0 0 : ℝ)^2 + (sevenNineRadial 3 1 0 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 2 0 0 : ℝ)^2 + (sevenNineRadial 3 1 0 : ℝ)^2 - (sevenNineDistanceLower[11]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h01 : (sevenNineRadial 2 0 0 : ℝ)^2 + (sevenNineRadial 3 1 1 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[45]! : ℝ) * (2 * (sevenNineRadial 2 0 0 : ℝ) * (sevenNineRadial 3 1 1 : ℝ)) := by
    have hq : (sevenNineRadial 2 0 0)^2 + (sevenNineRadial 3 1 1)^2 - sevenNineDistanceLower[11]!^2 ≤
        sevenNineCosUpper[45]! * (2 * sevenNineRadial 2 0 0 * sevenNineRadial 3 1 1) := by native_decide
    have hqR :
        (sevenNineRadial 2 0 0 : ℝ)^2 + (sevenNineRadial 3 1 1 : ℝ)^2 - (sevenNineDistanceLower[11]! : ℝ)^2 ≤
          (sevenNineCosUpper[45]! : ℝ) * (2 * (sevenNineRadial 2 0 0 : ℝ) * (sevenNineRadial 3 1 1 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 2 0 0 : ℝ)^2 + (sevenNineRadial 3 1 1 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 2 0 0 : ℝ)^2 + (sevenNineRadial 3 1 1 : ℝ)^2 - (sevenNineDistanceLower[11]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h10 : (sevenNineRadial 2 0 1 : ℝ)^2 + (sevenNineRadial 3 1 0 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[45]! : ℝ) * (2 * (sevenNineRadial 2 0 1 : ℝ) * (sevenNineRadial 3 1 0 : ℝ)) := by
    have hq : (sevenNineRadial 2 0 1)^2 + (sevenNineRadial 3 1 0)^2 - sevenNineDistanceLower[11]!^2 ≤
        sevenNineCosUpper[45]! * (2 * sevenNineRadial 2 0 1 * sevenNineRadial 3 1 0) := by native_decide
    have hqR :
        (sevenNineRadial 2 0 1 : ℝ)^2 + (sevenNineRadial 3 1 0 : ℝ)^2 - (sevenNineDistanceLower[11]! : ℝ)^2 ≤
          (sevenNineCosUpper[45]! : ℝ) * (2 * (sevenNineRadial 2 0 1 : ℝ) * (sevenNineRadial 3 1 0 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 2 0 1 : ℝ)^2 + (sevenNineRadial 3 1 0 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 2 0 1 : ℝ)^2 + (sevenNineRadial 3 1 0 : ℝ)^2 - (sevenNineDistanceLower[11]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h11 : (sevenNineRadial 2 0 1 : ℝ)^2 + (sevenNineRadial 3 1 1 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[45]! : ℝ) * (2 * (sevenNineRadial 2 0 1 : ℝ) * (sevenNineRadial 3 1 1 : ℝ)) := by
    have hq : (sevenNineRadial 2 0 1)^2 + (sevenNineRadial 3 1 1)^2 - sevenNineDistanceLower[11]!^2 ≤
        sevenNineCosUpper[45]! * (2 * sevenNineRadial 2 0 1 * sevenNineRadial 3 1 1) := by native_decide
    have hqR :
        (sevenNineRadial 2 0 1 : ℝ)^2 + (sevenNineRadial 3 1 1 : ℝ)^2 - (sevenNineDistanceLower[11]! : ℝ)^2 ≤
          (sevenNineCosUpper[45]! : ℝ) * (2 * (sevenNineRadial 2 0 1 : ℝ) * (sevenNineRadial 3 1 1 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 2 0 1 : ℝ)^2 + (sevenNineRadial 3 1 1 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 2 0 1 : ℝ)^2 + (sevenNineRadial 3 1 1 : ℝ)^2 - (sevenNineDistanceLower[11]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have htouch := corner_touch_cosine_bound haL haU hbL hbU
    (by norm_num [sevenNineRadial, sevenNineRadialBounds])
    (by norm_num [sevenNineRadial, sevenNineRadialBounds]) h00 h01 h10 h11
  have hcos : (sevenNineCosUpper[45]! : ℝ) ≤ Real.cos ((121274740582671082615 : ℝ) / 100000000000000000000) := by
    apply lower_bound_of_taylor_error
      (cosine_taylor_ninety_six_remainder (a := 0) (b := 4) (x := ((121274740582671082615 : ℝ) / 100000000000000000000) )
        (by norm_num) (by constructor <;> norm_num [Real.pi_gt_d20, Real.pi_lt_four]))
    rw [cosine_taylor_ninety_six_at_zero (b := 4) (x := ((121274740582671082615 : ℝ) / 100000000000000000000)) (by norm_num)]
    have hp : (sevenNineCosUpper[45]! : Rat) + (((121274740582671082615 : Rat) / 100000000000000000000) : Rat)^97 / (Nat.factorial 96) ≤
        Finset.sum (Finset.range 49) (fun k => (-1 : Rat)^k * (((121274740582671082615 : Rat) / 100000000000000000000) : Rat)^(2*k) / Nat.factorial (2*k)) := by native_decide
    have hpR : (sevenNineCosUpper[45]! : ℝ) + ((121274740582671082615 : ℝ) / 100000000000000000000)^97 / (Nat.factorial 96) ≤
        Finset.sum (Finset.range 49) (fun k => (-1 : ℝ)^k * ((121274740582671082615 : ℝ) / 100000000000000000000)^(2*k) / Nat.factorial (2*k)) := by
      norm_num [sevenNineCosUpper, Finset.sum_range_succ]
    simpa [sub_zero] using hpR
  have hangle : ((121274740582671082615 : ℝ) / 100000000000000000000) ≤ Real.arccos (touchCosine a b (Real.sqrt 6 + Real.sqrt 7)) := by
    exact angle_lower_bound_of_cosine (by norm_num)
      (by
        calc
          ((121274740582671082615 : ℝ) / 100000000000000000000) ≤ (314159265358979323846 : ℝ) / 100000000000000000000 := by norm_num
          _ ≤ Real.pi := by
            have hpi := Real.pi_gt_d20.le
            norm_num at hpi ⊢
            exact hpi) (le_trans htouch hcos)
  have hdata : sevenNineAngleLower[45]! = ((121274740582671082615 : Rat) / 100000000000000000000) := by native_decide
  have hdataR : (sevenNineAngleLower[45]! : ℝ) = ((121274740582671082615 : ℝ) / 100000000000000000000) := by
    have h := congrArg (fun q : Rat => (q : ℝ)) hdata
    convert h using 1 ; norm_num
  rw [hdataR]
  exact hangle

theorem sevenNineAngle_2_3_1_0 {a b : ℝ}
    (haL : (sevenNineRadial 2 1 0 : ℝ) ≤ a) (haU : a ≤ (sevenNineRadial 2 1 1 : ℝ))
    (hbL : (sevenNineRadial 3 0 0 : ℝ) ≤ b) (hbU : b ≤ (sevenNineRadial 3 0 1 : ℝ)) :
    (sevenNineAngleLower[46]! : ℝ) ≤ Real.arccos (touchCosine a b (Real.sqrt 6 + Real.sqrt 7)) := by
  let d : ℝ := Real.sqrt 6 + Real.sqrt 7
  have hd' : (((5095241053847768688698899828345151817676206663739120308801027026452029200687598654300252319 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) : ℝ) ≤ d := by
    dsimp [d]
    have h := rat_sum_sqrt_lower (q := ((5095241053847768688698899828345151817676206663739120308801027026452029200687598654300252319 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (qi := ((2449489742783178098197284074705891391965947480656670128432692567250960377457315026539859433104640234818594601226614189124 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (qj := ((2645751311064590590501615753639260425710259183082450180368334459201068823230283627760392886474543610615064578338497463095 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))
      (ni := 6) (nj := 7)
      (by convert sqrt_lower_6 using 1 ; norm_num)
      (by convert sqrt_lower_7 using 1 ; norm_num)
      (by native_decide)
    convert h using 1 ; norm_num
  have hd : (((5095241053847768688698899828345151817676206663739120308801027026452029200687598654300252319 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) ≤ d := by exact hd'
  have hd2 : (((5095241053847768688698899828345151817676206663739120308801027026452029200687598654300252319 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))^2 ≤ d^2 := by
    have hq : (0 : ℝ) ≤ ((5095241053847768688698899828345151817676206663739120308801027026452029200687598654300252319 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) := by norm_num
    have hdn : 0 ≤ d := by positivity
    exact (sq_le_sq₀ hq hdn).mpr hd
  have hd2' : (sevenNineDistanceLower[11]! : ℝ)^2 ≤ d^2 := by
    convert hd2 using 1 ; norm_num [sevenNineDistanceLower]
  have h00 : (sevenNineRadial 2 1 0 : ℝ)^2 + (sevenNineRadial 3 0 0 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[46]! : ℝ) * (2 * (sevenNineRadial 2 1 0 : ℝ) * (sevenNineRadial 3 0 0 : ℝ)) := by
    have hq : (sevenNineRadial 2 1 0)^2 + (sevenNineRadial 3 0 0)^2 - sevenNineDistanceLower[11]!^2 ≤
        sevenNineCosUpper[46]! * (2 * sevenNineRadial 2 1 0 * sevenNineRadial 3 0 0) := by native_decide
    have hqR :
        (sevenNineRadial 2 1 0 : ℝ)^2 + (sevenNineRadial 3 0 0 : ℝ)^2 - (sevenNineDistanceLower[11]! : ℝ)^2 ≤
          (sevenNineCosUpper[46]! : ℝ) * (2 * (sevenNineRadial 2 1 0 : ℝ) * (sevenNineRadial 3 0 0 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 2 1 0 : ℝ)^2 + (sevenNineRadial 3 0 0 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 2 1 0 : ℝ)^2 + (sevenNineRadial 3 0 0 : ℝ)^2 - (sevenNineDistanceLower[11]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h01 : (sevenNineRadial 2 1 0 : ℝ)^2 + (sevenNineRadial 3 0 1 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[46]! : ℝ) * (2 * (sevenNineRadial 2 1 0 : ℝ) * (sevenNineRadial 3 0 1 : ℝ)) := by
    have hq : (sevenNineRadial 2 1 0)^2 + (sevenNineRadial 3 0 1)^2 - sevenNineDistanceLower[11]!^2 ≤
        sevenNineCosUpper[46]! * (2 * sevenNineRadial 2 1 0 * sevenNineRadial 3 0 1) := by native_decide
    have hqR :
        (sevenNineRadial 2 1 0 : ℝ)^2 + (sevenNineRadial 3 0 1 : ℝ)^2 - (sevenNineDistanceLower[11]! : ℝ)^2 ≤
          (sevenNineCosUpper[46]! : ℝ) * (2 * (sevenNineRadial 2 1 0 : ℝ) * (sevenNineRadial 3 0 1 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 2 1 0 : ℝ)^2 + (sevenNineRadial 3 0 1 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 2 1 0 : ℝ)^2 + (sevenNineRadial 3 0 1 : ℝ)^2 - (sevenNineDistanceLower[11]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h10 : (sevenNineRadial 2 1 1 : ℝ)^2 + (sevenNineRadial 3 0 0 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[46]! : ℝ) * (2 * (sevenNineRadial 2 1 1 : ℝ) * (sevenNineRadial 3 0 0 : ℝ)) := by
    have hq : (sevenNineRadial 2 1 1)^2 + (sevenNineRadial 3 0 0)^2 - sevenNineDistanceLower[11]!^2 ≤
        sevenNineCosUpper[46]! * (2 * sevenNineRadial 2 1 1 * sevenNineRadial 3 0 0) := by native_decide
    have hqR :
        (sevenNineRadial 2 1 1 : ℝ)^2 + (sevenNineRadial 3 0 0 : ℝ)^2 - (sevenNineDistanceLower[11]! : ℝ)^2 ≤
          (sevenNineCosUpper[46]! : ℝ) * (2 * (sevenNineRadial 2 1 1 : ℝ) * (sevenNineRadial 3 0 0 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 2 1 1 : ℝ)^2 + (sevenNineRadial 3 0 0 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 2 1 1 : ℝ)^2 + (sevenNineRadial 3 0 0 : ℝ)^2 - (sevenNineDistanceLower[11]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h11 : (sevenNineRadial 2 1 1 : ℝ)^2 + (sevenNineRadial 3 0 1 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[46]! : ℝ) * (2 * (sevenNineRadial 2 1 1 : ℝ) * (sevenNineRadial 3 0 1 : ℝ)) := by
    have hq : (sevenNineRadial 2 1 1)^2 + (sevenNineRadial 3 0 1)^2 - sevenNineDistanceLower[11]!^2 ≤
        sevenNineCosUpper[46]! * (2 * sevenNineRadial 2 1 1 * sevenNineRadial 3 0 1) := by native_decide
    have hqR :
        (sevenNineRadial 2 1 1 : ℝ)^2 + (sevenNineRadial 3 0 1 : ℝ)^2 - (sevenNineDistanceLower[11]! : ℝ)^2 ≤
          (sevenNineCosUpper[46]! : ℝ) * (2 * (sevenNineRadial 2 1 1 : ℝ) * (sevenNineRadial 3 0 1 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 2 1 1 : ℝ)^2 + (sevenNineRadial 3 0 1 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 2 1 1 : ℝ)^2 + (sevenNineRadial 3 0 1 : ℝ)^2 - (sevenNineDistanceLower[11]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have htouch := corner_touch_cosine_bound haL haU hbL hbU
    (by norm_num [sevenNineRadial, sevenNineRadialBounds])
    (by norm_num [sevenNineRadial, sevenNineRadialBounds]) h00 h01 h10 h11
  have hcos : (sevenNineCosUpper[46]! : ℝ) ≤ Real.cos ((113812393119340095052 : ℝ) / 100000000000000000000) := by
    apply lower_bound_of_taylor_error
      (cosine_taylor_ninety_six_remainder (a := 0) (b := 4) (x := ((113812393119340095052 : ℝ) / 100000000000000000000) )
        (by norm_num) (by constructor <;> norm_num [Real.pi_gt_d20, Real.pi_lt_four]))
    rw [cosine_taylor_ninety_six_at_zero (b := 4) (x := ((113812393119340095052 : ℝ) / 100000000000000000000)) (by norm_num)]
    have hp : (sevenNineCosUpper[46]! : Rat) + (((113812393119340095052 : Rat) / 100000000000000000000) : Rat)^97 / (Nat.factorial 96) ≤
        Finset.sum (Finset.range 49) (fun k => (-1 : Rat)^k * (((113812393119340095052 : Rat) / 100000000000000000000) : Rat)^(2*k) / Nat.factorial (2*k)) := by native_decide
    have hpR : (sevenNineCosUpper[46]! : ℝ) + ((113812393119340095052 : ℝ) / 100000000000000000000)^97 / (Nat.factorial 96) ≤
        Finset.sum (Finset.range 49) (fun k => (-1 : ℝ)^k * ((113812393119340095052 : ℝ) / 100000000000000000000)^(2*k) / Nat.factorial (2*k)) := by
      norm_num [sevenNineCosUpper, Finset.sum_range_succ]
    simpa [sub_zero] using hpR
  have hangle : ((113812393119340095052 : ℝ) / 100000000000000000000) ≤ Real.arccos (touchCosine a b (Real.sqrt 6 + Real.sqrt 7)) := by
    exact angle_lower_bound_of_cosine (by norm_num)
      (by
        calc
          ((113812393119340095052 : ℝ) / 100000000000000000000) ≤ (314159265358979323846 : ℝ) / 100000000000000000000 := by norm_num
          _ ≤ Real.pi := by
            have hpi := Real.pi_gt_d20.le
            norm_num at hpi ⊢
            exact hpi) (le_trans htouch hcos)
  have hdata : sevenNineAngleLower[46]! = ((113812393119340095052 : Rat) / 100000000000000000000) := by native_decide
  have hdataR : (sevenNineAngleLower[46]! : ℝ) = ((113812393119340095052 : ℝ) / 100000000000000000000) := by
    have h := congrArg (fun q : Rat => (q : ℝ)) hdata
    convert h using 1 ; norm_num
  rw [hdataR]
  exact hangle

theorem sevenNineAngle_2_3_1_1 {a b : ℝ}
    (haL : (sevenNineRadial 2 1 0 : ℝ) ≤ a) (haU : a ≤ (sevenNineRadial 2 1 1 : ℝ))
    (hbL : (sevenNineRadial 3 1 0 : ℝ) ≤ b) (hbU : b ≤ (sevenNineRadial 3 1 1 : ℝ)) :
    (sevenNineAngleLower[47]! : ℝ) ≤ Real.arccos (touchCosine a b (Real.sqrt 6 + Real.sqrt 7)) := by
  let d : ℝ := Real.sqrt 6 + Real.sqrt 7
  have hd' : (((5095241053847768688698899828345151817676206663739120308801027026452029200687598654300252319 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) : ℝ) ≤ d := by
    dsimp [d]
    have h := rat_sum_sqrt_lower (q := ((5095241053847768688698899828345151817676206663739120308801027026452029200687598654300252319 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (qi := ((2449489742783178098197284074705891391965947480656670128432692567250960377457315026539859433104640234818594601226614189124 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (qj := ((2645751311064590590501615753639260425710259183082450180368334459201068823230283627760392886474543610615064578338497463095 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))
      (ni := 6) (nj := 7)
      (by convert sqrt_lower_6 using 1 ; norm_num)
      (by convert sqrt_lower_7 using 1 ; norm_num)
      (by native_decide)
    convert h using 1 ; norm_num
  have hd : (((5095241053847768688698899828345151817676206663739120308801027026452029200687598654300252319 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) ≤ d := by exact hd'
  have hd2 : (((5095241053847768688698899828345151817676206663739120308801027026452029200687598654300252319 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))^2 ≤ d^2 := by
    have hq : (0 : ℝ) ≤ ((5095241053847768688698899828345151817676206663739120308801027026452029200687598654300252319 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) := by norm_num
    have hdn : 0 ≤ d := by positivity
    exact (sq_le_sq₀ hq hdn).mpr hd
  have hd2' : (sevenNineDistanceLower[11]! : ℝ)^2 ≤ d^2 := by
    convert hd2 using 1 ; norm_num [sevenNineDistanceLower]
  have h00 : (sevenNineRadial 2 1 0 : ℝ)^2 + (sevenNineRadial 3 1 0 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[47]! : ℝ) * (2 * (sevenNineRadial 2 1 0 : ℝ) * (sevenNineRadial 3 1 0 : ℝ)) := by
    have hq : (sevenNineRadial 2 1 0)^2 + (sevenNineRadial 3 1 0)^2 - sevenNineDistanceLower[11]!^2 ≤
        sevenNineCosUpper[47]! * (2 * sevenNineRadial 2 1 0 * sevenNineRadial 3 1 0) := by native_decide
    have hqR :
        (sevenNineRadial 2 1 0 : ℝ)^2 + (sevenNineRadial 3 1 0 : ℝ)^2 - (sevenNineDistanceLower[11]! : ℝ)^2 ≤
          (sevenNineCosUpper[47]! : ℝ) * (2 * (sevenNineRadial 2 1 0 : ℝ) * (sevenNineRadial 3 1 0 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 2 1 0 : ℝ)^2 + (sevenNineRadial 3 1 0 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 2 1 0 : ℝ)^2 + (sevenNineRadial 3 1 0 : ℝ)^2 - (sevenNineDistanceLower[11]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h01 : (sevenNineRadial 2 1 0 : ℝ)^2 + (sevenNineRadial 3 1 1 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[47]! : ℝ) * (2 * (sevenNineRadial 2 1 0 : ℝ) * (sevenNineRadial 3 1 1 : ℝ)) := by
    have hq : (sevenNineRadial 2 1 0)^2 + (sevenNineRadial 3 1 1)^2 - sevenNineDistanceLower[11]!^2 ≤
        sevenNineCosUpper[47]! * (2 * sevenNineRadial 2 1 0 * sevenNineRadial 3 1 1) := by native_decide
    have hqR :
        (sevenNineRadial 2 1 0 : ℝ)^2 + (sevenNineRadial 3 1 1 : ℝ)^2 - (sevenNineDistanceLower[11]! : ℝ)^2 ≤
          (sevenNineCosUpper[47]! : ℝ) * (2 * (sevenNineRadial 2 1 0 : ℝ) * (sevenNineRadial 3 1 1 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 2 1 0 : ℝ)^2 + (sevenNineRadial 3 1 1 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 2 1 0 : ℝ)^2 + (sevenNineRadial 3 1 1 : ℝ)^2 - (sevenNineDistanceLower[11]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h10 : (sevenNineRadial 2 1 1 : ℝ)^2 + (sevenNineRadial 3 1 0 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[47]! : ℝ) * (2 * (sevenNineRadial 2 1 1 : ℝ) * (sevenNineRadial 3 1 0 : ℝ)) := by
    have hq : (sevenNineRadial 2 1 1)^2 + (sevenNineRadial 3 1 0)^2 - sevenNineDistanceLower[11]!^2 ≤
        sevenNineCosUpper[47]! * (2 * sevenNineRadial 2 1 1 * sevenNineRadial 3 1 0) := by native_decide
    have hqR :
        (sevenNineRadial 2 1 1 : ℝ)^2 + (sevenNineRadial 3 1 0 : ℝ)^2 - (sevenNineDistanceLower[11]! : ℝ)^2 ≤
          (sevenNineCosUpper[47]! : ℝ) * (2 * (sevenNineRadial 2 1 1 : ℝ) * (sevenNineRadial 3 1 0 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 2 1 1 : ℝ)^2 + (sevenNineRadial 3 1 0 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 2 1 1 : ℝ)^2 + (sevenNineRadial 3 1 0 : ℝ)^2 - (sevenNineDistanceLower[11]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h11 : (sevenNineRadial 2 1 1 : ℝ)^2 + (sevenNineRadial 3 1 1 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[47]! : ℝ) * (2 * (sevenNineRadial 2 1 1 : ℝ) * (sevenNineRadial 3 1 1 : ℝ)) := by
    have hq : (sevenNineRadial 2 1 1)^2 + (sevenNineRadial 3 1 1)^2 - sevenNineDistanceLower[11]!^2 ≤
        sevenNineCosUpper[47]! * (2 * sevenNineRadial 2 1 1 * sevenNineRadial 3 1 1) := by native_decide
    have hqR :
        (sevenNineRadial 2 1 1 : ℝ)^2 + (sevenNineRadial 3 1 1 : ℝ)^2 - (sevenNineDistanceLower[11]! : ℝ)^2 ≤
          (sevenNineCosUpper[47]! : ℝ) * (2 * (sevenNineRadial 2 1 1 : ℝ) * (sevenNineRadial 3 1 1 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 2 1 1 : ℝ)^2 + (sevenNineRadial 3 1 1 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 2 1 1 : ℝ)^2 + (sevenNineRadial 3 1 1 : ℝ)^2 - (sevenNineDistanceLower[11]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have htouch := corner_touch_cosine_bound haL haU hbL hbU
    (by norm_num [sevenNineRadial, sevenNineRadialBounds])
    (by norm_num [sevenNineRadial, sevenNineRadialBounds]) h00 h01 h10 h11
  have hcos : (sevenNineCosUpper[47]! : ℝ) ≤ Real.cos ((99153248582622268340 : ℝ) / 100000000000000000000) := by
    apply lower_bound_of_taylor_error
      (cosine_taylor_ninety_six_remainder (a := 0) (b := 4) (x := ((99153248582622268340 : ℝ) / 100000000000000000000) )
        (by norm_num) (by constructor <;> norm_num [Real.pi_gt_d20, Real.pi_lt_four]))
    rw [cosine_taylor_ninety_six_at_zero (b := 4) (x := ((99153248582622268340 : ℝ) / 100000000000000000000)) (by norm_num)]
    have hp : (sevenNineCosUpper[47]! : Rat) + (((99153248582622268340 : Rat) / 100000000000000000000) : Rat)^97 / (Nat.factorial 96) ≤
        Finset.sum (Finset.range 49) (fun k => (-1 : Rat)^k * (((99153248582622268340 : Rat) / 100000000000000000000) : Rat)^(2*k) / Nat.factorial (2*k)) := by native_decide
    have hpR : (sevenNineCosUpper[47]! : ℝ) + ((99153248582622268340 : ℝ) / 100000000000000000000)^97 / (Nat.factorial 96) ≤
        Finset.sum (Finset.range 49) (fun k => (-1 : ℝ)^k * ((99153248582622268340 : ℝ) / 100000000000000000000)^(2*k) / Nat.factorial (2*k)) := by
      norm_num [sevenNineCosUpper, Finset.sum_range_succ]
    simpa [sub_zero] using hpR
  have hangle : ((99153248582622268340 : ℝ) / 100000000000000000000) ≤ Real.arccos (touchCosine a b (Real.sqrt 6 + Real.sqrt 7)) := by
    exact angle_lower_bound_of_cosine (by norm_num)
      (by
        calc
          ((99153248582622268340 : ℝ) / 100000000000000000000) ≤ (314159265358979323846 : ℝ) / 100000000000000000000 := by norm_num
          _ ≤ Real.pi := by
            have hpi := Real.pi_gt_d20.le
            norm_num at hpi ⊢
            exact hpi) (le_trans htouch hcos)
  have hdata : sevenNineAngleLower[47]! = ((99153248582622268340 : Rat) / 100000000000000000000) := by native_decide
  have hdataR : (sevenNineAngleLower[47]! : ℝ) = ((99153248582622268340 : ℝ) / 100000000000000000000) := by
    have h := congrArg (fun q : Rat => (q : ℝ)) hdata
    convert h using 1 ; norm_num
  rw [hdataR]
  exact hangle

theorem sevenNineAngle_2_4_0_0 {a b : ℝ}
    (haL : (sevenNineRadial 2 0 0 : ℝ) ≤ a) (haU : a ≤ (sevenNineRadial 2 0 1 : ℝ))
    (hbL : (sevenNineRadial 4 0 0 : ℝ) ≤ b) (hbU : b ≤ (sevenNineRadial 4 0 1 : ℝ)) :
    (sevenNineAngleLower[48]! : ℝ) ≤ Real.arccos (touchCosine a b (Real.sqrt 6 + Real.sqrt 8)) := by
  let d : ℝ := Real.sqrt 6 + Real.sqrt 8
  have hd' : (((5277916867529368195800661523125287549105291231410566274786052043232425334381529104240634501 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) : ℝ) ≤ d := by
    dsimp [d]
    have h := rat_sum_sqrt_lower (q := ((5277916867529368195800661523125287549105291231410566274786052043232425334381529104240634501 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (qi := ((2449489742783178098197284074705891391965947480656670128432692567250960377457315026539859433104640234818594601226614189124 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (qj := ((2828427124746190097603377448419396157139343750753896146353359475981464956924214077700775068655283145470027692461824594049 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))
      (ni := 6) (nj := 8)
      (by convert sqrt_lower_6 using 1 ; norm_num)
      (by convert sqrt_lower_8 using 1 ; norm_num)
      (by native_decide)
    convert h using 1 ; norm_num
  have hd : (((5277916867529368195800661523125287549105291231410566274786052043232425334381529104240634501 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) ≤ d := by exact hd'
  have hd2 : (((5277916867529368195800661523125287549105291231410566274786052043232425334381529104240634501 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))^2 ≤ d^2 := by
    have hq : (0 : ℝ) ≤ ((5277916867529368195800661523125287549105291231410566274786052043232425334381529104240634501 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) := by norm_num
    have hdn : 0 ≤ d := by positivity
    exact (sq_le_sq₀ hq hdn).mpr hd
  have hd2' : (sevenNineDistanceLower[12]! : ℝ)^2 ≤ d^2 := by
    convert hd2 using 1 ; norm_num [sevenNineDistanceLower]
  have h00 : (sevenNineRadial 2 0 0 : ℝ)^2 + (sevenNineRadial 4 0 0 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[48]! : ℝ) * (2 * (sevenNineRadial 2 0 0 : ℝ) * (sevenNineRadial 4 0 0 : ℝ)) := by
    have hq : (sevenNineRadial 2 0 0)^2 + (sevenNineRadial 4 0 0)^2 - sevenNineDistanceLower[12]!^2 ≤
        sevenNineCosUpper[48]! * (2 * sevenNineRadial 2 0 0 * sevenNineRadial 4 0 0) := by native_decide
    have hqR :
        (sevenNineRadial 2 0 0 : ℝ)^2 + (sevenNineRadial 4 0 0 : ℝ)^2 - (sevenNineDistanceLower[12]! : ℝ)^2 ≤
          (sevenNineCosUpper[48]! : ℝ) * (2 * (sevenNineRadial 2 0 0 : ℝ) * (sevenNineRadial 4 0 0 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 2 0 0 : ℝ)^2 + (sevenNineRadial 4 0 0 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 2 0 0 : ℝ)^2 + (sevenNineRadial 4 0 0 : ℝ)^2 - (sevenNineDistanceLower[12]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h01 : (sevenNineRadial 2 0 0 : ℝ)^2 + (sevenNineRadial 4 0 1 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[48]! : ℝ) * (2 * (sevenNineRadial 2 0 0 : ℝ) * (sevenNineRadial 4 0 1 : ℝ)) := by
    have hq : (sevenNineRadial 2 0 0)^2 + (sevenNineRadial 4 0 1)^2 - sevenNineDistanceLower[12]!^2 ≤
        sevenNineCosUpper[48]! * (2 * sevenNineRadial 2 0 0 * sevenNineRadial 4 0 1) := by native_decide
    have hqR :
        (sevenNineRadial 2 0 0 : ℝ)^2 + (sevenNineRadial 4 0 1 : ℝ)^2 - (sevenNineDistanceLower[12]! : ℝ)^2 ≤
          (sevenNineCosUpper[48]! : ℝ) * (2 * (sevenNineRadial 2 0 0 : ℝ) * (sevenNineRadial 4 0 1 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 2 0 0 : ℝ)^2 + (sevenNineRadial 4 0 1 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 2 0 0 : ℝ)^2 + (sevenNineRadial 4 0 1 : ℝ)^2 - (sevenNineDistanceLower[12]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h10 : (sevenNineRadial 2 0 1 : ℝ)^2 + (sevenNineRadial 4 0 0 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[48]! : ℝ) * (2 * (sevenNineRadial 2 0 1 : ℝ) * (sevenNineRadial 4 0 0 : ℝ)) := by
    have hq : (sevenNineRadial 2 0 1)^2 + (sevenNineRadial 4 0 0)^2 - sevenNineDistanceLower[12]!^2 ≤
        sevenNineCosUpper[48]! * (2 * sevenNineRadial 2 0 1 * sevenNineRadial 4 0 0) := by native_decide
    have hqR :
        (sevenNineRadial 2 0 1 : ℝ)^2 + (sevenNineRadial 4 0 0 : ℝ)^2 - (sevenNineDistanceLower[12]! : ℝ)^2 ≤
          (sevenNineCosUpper[48]! : ℝ) * (2 * (sevenNineRadial 2 0 1 : ℝ) * (sevenNineRadial 4 0 0 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 2 0 1 : ℝ)^2 + (sevenNineRadial 4 0 0 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 2 0 1 : ℝ)^2 + (sevenNineRadial 4 0 0 : ℝ)^2 - (sevenNineDistanceLower[12]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h11 : (sevenNineRadial 2 0 1 : ℝ)^2 + (sevenNineRadial 4 0 1 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[48]! : ℝ) * (2 * (sevenNineRadial 2 0 1 : ℝ) * (sevenNineRadial 4 0 1 : ℝ)) := by
    have hq : (sevenNineRadial 2 0 1)^2 + (sevenNineRadial 4 0 1)^2 - sevenNineDistanceLower[12]!^2 ≤
        sevenNineCosUpper[48]! * (2 * sevenNineRadial 2 0 1 * sevenNineRadial 4 0 1) := by native_decide
    have hqR :
        (sevenNineRadial 2 0 1 : ℝ)^2 + (sevenNineRadial 4 0 1 : ℝ)^2 - (sevenNineDistanceLower[12]! : ℝ)^2 ≤
          (sevenNineCosUpper[48]! : ℝ) * (2 * (sevenNineRadial 2 0 1 : ℝ) * (sevenNineRadial 4 0 1 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 2 0 1 : ℝ)^2 + (sevenNineRadial 4 0 1 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 2 0 1 : ℝ)^2 + (sevenNineRadial 4 0 1 : ℝ)^2 - (sevenNineDistanceLower[12]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have htouch := corner_touch_cosine_bound haL haU hbL hbU
    (by norm_num [sevenNineRadial, sevenNineRadialBounds])
    (by norm_num [sevenNineRadial, sevenNineRadialBounds]) h00 h01 h10 h11
  have hcos : (sevenNineCosUpper[48]! : ℝ) ≤ Real.cos ((197449276919820997858 : ℝ) / 100000000000000000000) := by
    apply lower_bound_of_taylor_error
      (cosine_taylor_ninety_six_remainder (a := 0) (b := 4) (x := ((197449276919820997858 : ℝ) / 100000000000000000000) )
        (by norm_num) (by constructor <;> norm_num [Real.pi_gt_d20, Real.pi_lt_four]))
    rw [cosine_taylor_ninety_six_at_zero (b := 4) (x := ((197449276919820997858 : ℝ) / 100000000000000000000)) (by norm_num)]
    have hp : (sevenNineCosUpper[48]! : Rat) + (((197449276919820997858 : Rat) / 100000000000000000000) : Rat)^97 / (Nat.factorial 96) ≤
        Finset.sum (Finset.range 49) (fun k => (-1 : Rat)^k * (((197449276919820997858 : Rat) / 100000000000000000000) : Rat)^(2*k) / Nat.factorial (2*k)) := by native_decide
    have hpR : (sevenNineCosUpper[48]! : ℝ) + ((197449276919820997858 : ℝ) / 100000000000000000000)^97 / (Nat.factorial 96) ≤
        Finset.sum (Finset.range 49) (fun k => (-1 : ℝ)^k * ((197449276919820997858 : ℝ) / 100000000000000000000)^(2*k) / Nat.factorial (2*k)) := by
      norm_num [sevenNineCosUpper, Finset.sum_range_succ]
    simpa [sub_zero] using hpR
  have hangle : ((197449276919820997858 : ℝ) / 100000000000000000000) ≤ Real.arccos (touchCosine a b (Real.sqrt 6 + Real.sqrt 8)) := by
    exact angle_lower_bound_of_cosine (by norm_num)
      (by
        calc
          ((197449276919820997858 : ℝ) / 100000000000000000000) ≤ (314159265358979323846 : ℝ) / 100000000000000000000 := by norm_num
          _ ≤ Real.pi := by
            have hpi := Real.pi_gt_d20.le
            norm_num at hpi ⊢
            exact hpi) (le_trans htouch hcos)
  have hdata : sevenNineAngleLower[48]! = ((197449276919820997858 : Rat) / 100000000000000000000) := by native_decide
  have hdataR : (sevenNineAngleLower[48]! : ℝ) = ((197449276919820997858 : ℝ) / 100000000000000000000) := by
    have h := congrArg (fun q : Rat => (q : ℝ)) hdata
    convert h using 1 ; norm_num
  rw [hdataR]
  exact hangle

theorem sevenNineAngle_2_4_0_1 {a b : ℝ}
    (haL : (sevenNineRadial 2 0 0 : ℝ) ≤ a) (haU : a ≤ (sevenNineRadial 2 0 1 : ℝ))
    (hbL : (sevenNineRadial 4 1 0 : ℝ) ≤ b) (hbU : b ≤ (sevenNineRadial 4 1 1 : ℝ)) :
    (sevenNineAngleLower[49]! : ℝ) ≤ Real.arccos (touchCosine a b (Real.sqrt 6 + Real.sqrt 8)) := by
  let d : ℝ := Real.sqrt 6 + Real.sqrt 8
  have hd' : (((5277916867529368195800661523125287549105291231410566274786052043232425334381529104240634501 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) : ℝ) ≤ d := by
    dsimp [d]
    have h := rat_sum_sqrt_lower (q := ((5277916867529368195800661523125287549105291231410566274786052043232425334381529104240634501 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (qi := ((2449489742783178098197284074705891391965947480656670128432692567250960377457315026539859433104640234818594601226614189124 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (qj := ((2828427124746190097603377448419396157139343750753896146353359475981464956924214077700775068655283145470027692461824594049 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))
      (ni := 6) (nj := 8)
      (by convert sqrt_lower_6 using 1 ; norm_num)
      (by convert sqrt_lower_8 using 1 ; norm_num)
      (by native_decide)
    convert h using 1 ; norm_num
  have hd : (((5277916867529368195800661523125287549105291231410566274786052043232425334381529104240634501 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) ≤ d := by exact hd'
  have hd2 : (((5277916867529368195800661523125287549105291231410566274786052043232425334381529104240634501 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))^2 ≤ d^2 := by
    have hq : (0 : ℝ) ≤ ((5277916867529368195800661523125287549105291231410566274786052043232425334381529104240634501 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) := by norm_num
    have hdn : 0 ≤ d := by positivity
    exact (sq_le_sq₀ hq hdn).mpr hd
  have hd2' : (sevenNineDistanceLower[12]! : ℝ)^2 ≤ d^2 := by
    convert hd2 using 1 ; norm_num [sevenNineDistanceLower]
  have h00 : (sevenNineRadial 2 0 0 : ℝ)^2 + (sevenNineRadial 4 1 0 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[49]! : ℝ) * (2 * (sevenNineRadial 2 0 0 : ℝ) * (sevenNineRadial 4 1 0 : ℝ)) := by
    have hq : (sevenNineRadial 2 0 0)^2 + (sevenNineRadial 4 1 0)^2 - sevenNineDistanceLower[12]!^2 ≤
        sevenNineCosUpper[49]! * (2 * sevenNineRadial 2 0 0 * sevenNineRadial 4 1 0) := by native_decide
    have hqR :
        (sevenNineRadial 2 0 0 : ℝ)^2 + (sevenNineRadial 4 1 0 : ℝ)^2 - (sevenNineDistanceLower[12]! : ℝ)^2 ≤
          (sevenNineCosUpper[49]! : ℝ) * (2 * (sevenNineRadial 2 0 0 : ℝ) * (sevenNineRadial 4 1 0 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 2 0 0 : ℝ)^2 + (sevenNineRadial 4 1 0 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 2 0 0 : ℝ)^2 + (sevenNineRadial 4 1 0 : ℝ)^2 - (sevenNineDistanceLower[12]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h01 : (sevenNineRadial 2 0 0 : ℝ)^2 + (sevenNineRadial 4 1 1 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[49]! : ℝ) * (2 * (sevenNineRadial 2 0 0 : ℝ) * (sevenNineRadial 4 1 1 : ℝ)) := by
    have hq : (sevenNineRadial 2 0 0)^2 + (sevenNineRadial 4 1 1)^2 - sevenNineDistanceLower[12]!^2 ≤
        sevenNineCosUpper[49]! * (2 * sevenNineRadial 2 0 0 * sevenNineRadial 4 1 1) := by native_decide
    have hqR :
        (sevenNineRadial 2 0 0 : ℝ)^2 + (sevenNineRadial 4 1 1 : ℝ)^2 - (sevenNineDistanceLower[12]! : ℝ)^2 ≤
          (sevenNineCosUpper[49]! : ℝ) * (2 * (sevenNineRadial 2 0 0 : ℝ) * (sevenNineRadial 4 1 1 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 2 0 0 : ℝ)^2 + (sevenNineRadial 4 1 1 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 2 0 0 : ℝ)^2 + (sevenNineRadial 4 1 1 : ℝ)^2 - (sevenNineDistanceLower[12]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h10 : (sevenNineRadial 2 0 1 : ℝ)^2 + (sevenNineRadial 4 1 0 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[49]! : ℝ) * (2 * (sevenNineRadial 2 0 1 : ℝ) * (sevenNineRadial 4 1 0 : ℝ)) := by
    have hq : (sevenNineRadial 2 0 1)^2 + (sevenNineRadial 4 1 0)^2 - sevenNineDistanceLower[12]!^2 ≤
        sevenNineCosUpper[49]! * (2 * sevenNineRadial 2 0 1 * sevenNineRadial 4 1 0) := by native_decide
    have hqR :
        (sevenNineRadial 2 0 1 : ℝ)^2 + (sevenNineRadial 4 1 0 : ℝ)^2 - (sevenNineDistanceLower[12]! : ℝ)^2 ≤
          (sevenNineCosUpper[49]! : ℝ) * (2 * (sevenNineRadial 2 0 1 : ℝ) * (sevenNineRadial 4 1 0 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 2 0 1 : ℝ)^2 + (sevenNineRadial 4 1 0 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 2 0 1 : ℝ)^2 + (sevenNineRadial 4 1 0 : ℝ)^2 - (sevenNineDistanceLower[12]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h11 : (sevenNineRadial 2 0 1 : ℝ)^2 + (sevenNineRadial 4 1 1 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[49]! : ℝ) * (2 * (sevenNineRadial 2 0 1 : ℝ) * (sevenNineRadial 4 1 1 : ℝ)) := by
    have hq : (sevenNineRadial 2 0 1)^2 + (sevenNineRadial 4 1 1)^2 - sevenNineDistanceLower[12]!^2 ≤
        sevenNineCosUpper[49]! * (2 * sevenNineRadial 2 0 1 * sevenNineRadial 4 1 1) := by native_decide
    have hqR :
        (sevenNineRadial 2 0 1 : ℝ)^2 + (sevenNineRadial 4 1 1 : ℝ)^2 - (sevenNineDistanceLower[12]! : ℝ)^2 ≤
          (sevenNineCosUpper[49]! : ℝ) * (2 * (sevenNineRadial 2 0 1 : ℝ) * (sevenNineRadial 4 1 1 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 2 0 1 : ℝ)^2 + (sevenNineRadial 4 1 1 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 2 0 1 : ℝ)^2 + (sevenNineRadial 4 1 1 : ℝ)^2 - (sevenNineDistanceLower[12]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have htouch := corner_touch_cosine_bound haL haU hbL hbU
    (by norm_num [sevenNineRadial, sevenNineRadialBounds])
    (by norm_num [sevenNineRadial, sevenNineRadialBounds]) h00 h01 h10 h11
  have hcos : (sevenNineCosUpper[49]! : ℝ) ≤ Real.cos ((132308493226042711680 : ℝ) / 100000000000000000000) := by
    apply lower_bound_of_taylor_error
      (cosine_taylor_ninety_six_remainder (a := 0) (b := 4) (x := ((132308493226042711680 : ℝ) / 100000000000000000000) )
        (by norm_num) (by constructor <;> norm_num [Real.pi_gt_d20, Real.pi_lt_four]))
    rw [cosine_taylor_ninety_six_at_zero (b := 4) (x := ((132308493226042711680 : ℝ) / 100000000000000000000)) (by norm_num)]
    have hp : (sevenNineCosUpper[49]! : Rat) + (((132308493226042711680 : Rat) / 100000000000000000000) : Rat)^97 / (Nat.factorial 96) ≤
        Finset.sum (Finset.range 49) (fun k => (-1 : Rat)^k * (((132308493226042711680 : Rat) / 100000000000000000000) : Rat)^(2*k) / Nat.factorial (2*k)) := by native_decide
    have hpR : (sevenNineCosUpper[49]! : ℝ) + ((132308493226042711680 : ℝ) / 100000000000000000000)^97 / (Nat.factorial 96) ≤
        Finset.sum (Finset.range 49) (fun k => (-1 : ℝ)^k * ((132308493226042711680 : ℝ) / 100000000000000000000)^(2*k) / Nat.factorial (2*k)) := by
      norm_num [sevenNineCosUpper, Finset.sum_range_succ]
    simpa [sub_zero] using hpR
  have hangle : ((132308493226042711680 : ℝ) / 100000000000000000000) ≤ Real.arccos (touchCosine a b (Real.sqrt 6 + Real.sqrt 8)) := by
    exact angle_lower_bound_of_cosine (by norm_num)
      (by
        calc
          ((132308493226042711680 : ℝ) / 100000000000000000000) ≤ (314159265358979323846 : ℝ) / 100000000000000000000 := by norm_num
          _ ≤ Real.pi := by
            have hpi := Real.pi_gt_d20.le
            norm_num at hpi ⊢
            exact hpi) (le_trans htouch hcos)
  have hdata : sevenNineAngleLower[49]! = ((132308493226042711680 : Rat) / 100000000000000000000) := by native_decide
  have hdataR : (sevenNineAngleLower[49]! : ℝ) = ((132308493226042711680 : ℝ) / 100000000000000000000) := by
    have h := congrArg (fun q : Rat => (q : ℝ)) hdata
    convert h using 1 ; norm_num
  rw [hdataR]
  exact hangle

theorem sevenNineAngle_2_4_1_0 {a b : ℝ}
    (haL : (sevenNineRadial 2 1 0 : ℝ) ≤ a) (haU : a ≤ (sevenNineRadial 2 1 1 : ℝ))
    (hbL : (sevenNineRadial 4 0 0 : ℝ) ≤ b) (hbU : b ≤ (sevenNineRadial 4 0 1 : ℝ)) :
    (sevenNineAngleLower[50]! : ℝ) ≤ Real.arccos (touchCosine a b (Real.sqrt 6 + Real.sqrt 8)) := by
  let d : ℝ := Real.sqrt 6 + Real.sqrt 8
  have hd' : (((5277916867529368195800661523125287549105291231410566274786052043232425334381529104240634501 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) : ℝ) ≤ d := by
    dsimp [d]
    have h := rat_sum_sqrt_lower (q := ((5277916867529368195800661523125287549105291231410566274786052043232425334381529104240634501 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (qi := ((2449489742783178098197284074705891391965947480656670128432692567250960377457315026539859433104640234818594601226614189124 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (qj := ((2828427124746190097603377448419396157139343750753896146353359475981464956924214077700775068655283145470027692461824594049 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))
      (ni := 6) (nj := 8)
      (by convert sqrt_lower_6 using 1 ; norm_num)
      (by convert sqrt_lower_8 using 1 ; norm_num)
      (by native_decide)
    convert h using 1 ; norm_num
  have hd : (((5277916867529368195800661523125287549105291231410566274786052043232425334381529104240634501 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) ≤ d := by exact hd'
  have hd2 : (((5277916867529368195800661523125287549105291231410566274786052043232425334381529104240634501 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))^2 ≤ d^2 := by
    have hq : (0 : ℝ) ≤ ((5277916867529368195800661523125287549105291231410566274786052043232425334381529104240634501 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) := by norm_num
    have hdn : 0 ≤ d := by positivity
    exact (sq_le_sq₀ hq hdn).mpr hd
  have hd2' : (sevenNineDistanceLower[12]! : ℝ)^2 ≤ d^2 := by
    convert hd2 using 1 ; norm_num [sevenNineDistanceLower]
  have h00 : (sevenNineRadial 2 1 0 : ℝ)^2 + (sevenNineRadial 4 0 0 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[50]! : ℝ) * (2 * (sevenNineRadial 2 1 0 : ℝ) * (sevenNineRadial 4 0 0 : ℝ)) := by
    have hq : (sevenNineRadial 2 1 0)^2 + (sevenNineRadial 4 0 0)^2 - sevenNineDistanceLower[12]!^2 ≤
        sevenNineCosUpper[50]! * (2 * sevenNineRadial 2 1 0 * sevenNineRadial 4 0 0) := by native_decide
    have hqR :
        (sevenNineRadial 2 1 0 : ℝ)^2 + (sevenNineRadial 4 0 0 : ℝ)^2 - (sevenNineDistanceLower[12]! : ℝ)^2 ≤
          (sevenNineCosUpper[50]! : ℝ) * (2 * (sevenNineRadial 2 1 0 : ℝ) * (sevenNineRadial 4 0 0 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 2 1 0 : ℝ)^2 + (sevenNineRadial 4 0 0 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 2 1 0 : ℝ)^2 + (sevenNineRadial 4 0 0 : ℝ)^2 - (sevenNineDistanceLower[12]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h01 : (sevenNineRadial 2 1 0 : ℝ)^2 + (sevenNineRadial 4 0 1 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[50]! : ℝ) * (2 * (sevenNineRadial 2 1 0 : ℝ) * (sevenNineRadial 4 0 1 : ℝ)) := by
    have hq : (sevenNineRadial 2 1 0)^2 + (sevenNineRadial 4 0 1)^2 - sevenNineDistanceLower[12]!^2 ≤
        sevenNineCosUpper[50]! * (2 * sevenNineRadial 2 1 0 * sevenNineRadial 4 0 1) := by native_decide
    have hqR :
        (sevenNineRadial 2 1 0 : ℝ)^2 + (sevenNineRadial 4 0 1 : ℝ)^2 - (sevenNineDistanceLower[12]! : ℝ)^2 ≤
          (sevenNineCosUpper[50]! : ℝ) * (2 * (sevenNineRadial 2 1 0 : ℝ) * (sevenNineRadial 4 0 1 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 2 1 0 : ℝ)^2 + (sevenNineRadial 4 0 1 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 2 1 0 : ℝ)^2 + (sevenNineRadial 4 0 1 : ℝ)^2 - (sevenNineDistanceLower[12]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h10 : (sevenNineRadial 2 1 1 : ℝ)^2 + (sevenNineRadial 4 0 0 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[50]! : ℝ) * (2 * (sevenNineRadial 2 1 1 : ℝ) * (sevenNineRadial 4 0 0 : ℝ)) := by
    have hq : (sevenNineRadial 2 1 1)^2 + (sevenNineRadial 4 0 0)^2 - sevenNineDistanceLower[12]!^2 ≤
        sevenNineCosUpper[50]! * (2 * sevenNineRadial 2 1 1 * sevenNineRadial 4 0 0) := by native_decide
    have hqR :
        (sevenNineRadial 2 1 1 : ℝ)^2 + (sevenNineRadial 4 0 0 : ℝ)^2 - (sevenNineDistanceLower[12]! : ℝ)^2 ≤
          (sevenNineCosUpper[50]! : ℝ) * (2 * (sevenNineRadial 2 1 1 : ℝ) * (sevenNineRadial 4 0 0 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 2 1 1 : ℝ)^2 + (sevenNineRadial 4 0 0 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 2 1 1 : ℝ)^2 + (sevenNineRadial 4 0 0 : ℝ)^2 - (sevenNineDistanceLower[12]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h11 : (sevenNineRadial 2 1 1 : ℝ)^2 + (sevenNineRadial 4 0 1 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[50]! : ℝ) * (2 * (sevenNineRadial 2 1 1 : ℝ) * (sevenNineRadial 4 0 1 : ℝ)) := by
    have hq : (sevenNineRadial 2 1 1)^2 + (sevenNineRadial 4 0 1)^2 - sevenNineDistanceLower[12]!^2 ≤
        sevenNineCosUpper[50]! * (2 * sevenNineRadial 2 1 1 * sevenNineRadial 4 0 1) := by native_decide
    have hqR :
        (sevenNineRadial 2 1 1 : ℝ)^2 + (sevenNineRadial 4 0 1 : ℝ)^2 - (sevenNineDistanceLower[12]! : ℝ)^2 ≤
          (sevenNineCosUpper[50]! : ℝ) * (2 * (sevenNineRadial 2 1 1 : ℝ) * (sevenNineRadial 4 0 1 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 2 1 1 : ℝ)^2 + (sevenNineRadial 4 0 1 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 2 1 1 : ℝ)^2 + (sevenNineRadial 4 0 1 : ℝ)^2 - (sevenNineDistanceLower[12]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have htouch := corner_touch_cosine_bound haL haU hbL hbU
    (by norm_num [sevenNineRadial, sevenNineRadialBounds])
    (by norm_num [sevenNineRadial, sevenNineRadialBounds]) h00 h01 h10 h11
  have hcos : (sevenNineCosUpper[50]! : ℝ) ≤ Real.cos ((121983068530135240844 : ℝ) / 100000000000000000000) := by
    apply lower_bound_of_taylor_error
      (cosine_taylor_ninety_six_remainder (a := 0) (b := 4) (x := ((121983068530135240844 : ℝ) / 100000000000000000000) )
        (by norm_num) (by constructor <;> norm_num [Real.pi_gt_d20, Real.pi_lt_four]))
    rw [cosine_taylor_ninety_six_at_zero (b := 4) (x := ((121983068530135240844 : ℝ) / 100000000000000000000)) (by norm_num)]
    have hp : (sevenNineCosUpper[50]! : Rat) + (((121983068530135240844 : Rat) / 100000000000000000000) : Rat)^97 / (Nat.factorial 96) ≤
        Finset.sum (Finset.range 49) (fun k => (-1 : Rat)^k * (((121983068530135240844 : Rat) / 100000000000000000000) : Rat)^(2*k) / Nat.factorial (2*k)) := by native_decide
    have hpR : (sevenNineCosUpper[50]! : ℝ) + ((121983068530135240844 : ℝ) / 100000000000000000000)^97 / (Nat.factorial 96) ≤
        Finset.sum (Finset.range 49) (fun k => (-1 : ℝ)^k * ((121983068530135240844 : ℝ) / 100000000000000000000)^(2*k) / Nat.factorial (2*k)) := by
      norm_num [sevenNineCosUpper, Finset.sum_range_succ]
    simpa [sub_zero] using hpR
  have hangle : ((121983068530135240844 : ℝ) / 100000000000000000000) ≤ Real.arccos (touchCosine a b (Real.sqrt 6 + Real.sqrt 8)) := by
    exact angle_lower_bound_of_cosine (by norm_num)
      (by
        calc
          ((121983068530135240844 : ℝ) / 100000000000000000000) ≤ (314159265358979323846 : ℝ) / 100000000000000000000 := by norm_num
          _ ≤ Real.pi := by
            have hpi := Real.pi_gt_d20.le
            norm_num at hpi ⊢
            exact hpi) (le_trans htouch hcos)
  have hdata : sevenNineAngleLower[50]! = ((121983068530135240844 : Rat) / 100000000000000000000) := by native_decide
  have hdataR : (sevenNineAngleLower[50]! : ℝ) = ((121983068530135240844 : ℝ) / 100000000000000000000) := by
    have h := congrArg (fun q : Rat => (q : ℝ)) hdata
    convert h using 1 ; norm_num
  rw [hdataR]
  exact hangle

theorem sevenNineAngle_2_4_1_1 {a b : ℝ}
    (haL : (sevenNineRadial 2 1 0 : ℝ) ≤ a) (haU : a ≤ (sevenNineRadial 2 1 1 : ℝ))
    (hbL : (sevenNineRadial 4 1 0 : ℝ) ≤ b) (hbU : b ≤ (sevenNineRadial 4 1 1 : ℝ)) :
    (sevenNineAngleLower[51]! : ℝ) ≤ Real.arccos (touchCosine a b (Real.sqrt 6 + Real.sqrt 8)) := by
  let d : ℝ := Real.sqrt 6 + Real.sqrt 8
  have hd' : (((5277916867529368195800661523125287549105291231410566274786052043232425334381529104240634501 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) : ℝ) ≤ d := by
    dsimp [d]
    have h := rat_sum_sqrt_lower (q := ((5277916867529368195800661523125287549105291231410566274786052043232425334381529104240634501 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (qi := ((2449489742783178098197284074705891391965947480656670128432692567250960377457315026539859433104640234818594601226614189124 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (qj := ((2828427124746190097603377448419396157139343750753896146353359475981464956924214077700775068655283145470027692461824594049 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))
      (ni := 6) (nj := 8)
      (by convert sqrt_lower_6 using 1 ; norm_num)
      (by convert sqrt_lower_8 using 1 ; norm_num)
      (by native_decide)
    convert h using 1 ; norm_num
  have hd : (((5277916867529368195800661523125287549105291231410566274786052043232425334381529104240634501 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) ≤ d := by exact hd'
  have hd2 : (((5277916867529368195800661523125287549105291231410566274786052043232425334381529104240634501 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))^2 ≤ d^2 := by
    have hq : (0 : ℝ) ≤ ((5277916867529368195800661523125287549105291231410566274786052043232425334381529104240634501 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) := by norm_num
    have hdn : 0 ≤ d := by positivity
    exact (sq_le_sq₀ hq hdn).mpr hd
  have hd2' : (sevenNineDistanceLower[12]! : ℝ)^2 ≤ d^2 := by
    convert hd2 using 1 ; norm_num [sevenNineDistanceLower]
  have h00 : (sevenNineRadial 2 1 0 : ℝ)^2 + (sevenNineRadial 4 1 0 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[51]! : ℝ) * (2 * (sevenNineRadial 2 1 0 : ℝ) * (sevenNineRadial 4 1 0 : ℝ)) := by
    have hq : (sevenNineRadial 2 1 0)^2 + (sevenNineRadial 4 1 0)^2 - sevenNineDistanceLower[12]!^2 ≤
        sevenNineCosUpper[51]! * (2 * sevenNineRadial 2 1 0 * sevenNineRadial 4 1 0) := by native_decide
    have hqR :
        (sevenNineRadial 2 1 0 : ℝ)^2 + (sevenNineRadial 4 1 0 : ℝ)^2 - (sevenNineDistanceLower[12]! : ℝ)^2 ≤
          (sevenNineCosUpper[51]! : ℝ) * (2 * (sevenNineRadial 2 1 0 : ℝ) * (sevenNineRadial 4 1 0 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 2 1 0 : ℝ)^2 + (sevenNineRadial 4 1 0 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 2 1 0 : ℝ)^2 + (sevenNineRadial 4 1 0 : ℝ)^2 - (sevenNineDistanceLower[12]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h01 : (sevenNineRadial 2 1 0 : ℝ)^2 + (sevenNineRadial 4 1 1 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[51]! : ℝ) * (2 * (sevenNineRadial 2 1 0 : ℝ) * (sevenNineRadial 4 1 1 : ℝ)) := by
    have hq : (sevenNineRadial 2 1 0)^2 + (sevenNineRadial 4 1 1)^2 - sevenNineDistanceLower[12]!^2 ≤
        sevenNineCosUpper[51]! * (2 * sevenNineRadial 2 1 0 * sevenNineRadial 4 1 1) := by native_decide
    have hqR :
        (sevenNineRadial 2 1 0 : ℝ)^2 + (sevenNineRadial 4 1 1 : ℝ)^2 - (sevenNineDistanceLower[12]! : ℝ)^2 ≤
          (sevenNineCosUpper[51]! : ℝ) * (2 * (sevenNineRadial 2 1 0 : ℝ) * (sevenNineRadial 4 1 1 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 2 1 0 : ℝ)^2 + (sevenNineRadial 4 1 1 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 2 1 0 : ℝ)^2 + (sevenNineRadial 4 1 1 : ℝ)^2 - (sevenNineDistanceLower[12]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h10 : (sevenNineRadial 2 1 1 : ℝ)^2 + (sevenNineRadial 4 1 0 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[51]! : ℝ) * (2 * (sevenNineRadial 2 1 1 : ℝ) * (sevenNineRadial 4 1 0 : ℝ)) := by
    have hq : (sevenNineRadial 2 1 1)^2 + (sevenNineRadial 4 1 0)^2 - sevenNineDistanceLower[12]!^2 ≤
        sevenNineCosUpper[51]! * (2 * sevenNineRadial 2 1 1 * sevenNineRadial 4 1 0) := by native_decide
    have hqR :
        (sevenNineRadial 2 1 1 : ℝ)^2 + (sevenNineRadial 4 1 0 : ℝ)^2 - (sevenNineDistanceLower[12]! : ℝ)^2 ≤
          (sevenNineCosUpper[51]! : ℝ) * (2 * (sevenNineRadial 2 1 1 : ℝ) * (sevenNineRadial 4 1 0 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 2 1 1 : ℝ)^2 + (sevenNineRadial 4 1 0 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 2 1 1 : ℝ)^2 + (sevenNineRadial 4 1 0 : ℝ)^2 - (sevenNineDistanceLower[12]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h11 : (sevenNineRadial 2 1 1 : ℝ)^2 + (sevenNineRadial 4 1 1 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[51]! : ℝ) * (2 * (sevenNineRadial 2 1 1 : ℝ) * (sevenNineRadial 4 1 1 : ℝ)) := by
    have hq : (sevenNineRadial 2 1 1)^2 + (sevenNineRadial 4 1 1)^2 - sevenNineDistanceLower[12]!^2 ≤
        sevenNineCosUpper[51]! * (2 * sevenNineRadial 2 1 1 * sevenNineRadial 4 1 1) := by native_decide
    have hqR :
        (sevenNineRadial 2 1 1 : ℝ)^2 + (sevenNineRadial 4 1 1 : ℝ)^2 - (sevenNineDistanceLower[12]! : ℝ)^2 ≤
          (sevenNineCosUpper[51]! : ℝ) * (2 * (sevenNineRadial 2 1 1 : ℝ) * (sevenNineRadial 4 1 1 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 2 1 1 : ℝ)^2 + (sevenNineRadial 4 1 1 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 2 1 1 : ℝ)^2 + (sevenNineRadial 4 1 1 : ℝ)^2 - (sevenNineDistanceLower[12]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have htouch := corner_touch_cosine_bound haL haU hbL hbU
    (by norm_num [sevenNineRadial, sevenNineRadialBounds])
    (by norm_num [sevenNineRadial, sevenNineRadialBounds]) h00 h01 h10 h11
  have hcos : (sevenNineCosUpper[51]! : ℝ) ≤ Real.cos ((104866216128012819086 : ℝ) / 100000000000000000000) := by
    apply lower_bound_of_taylor_error
      (cosine_taylor_ninety_six_remainder (a := 0) (b := 4) (x := ((104866216128012819086 : ℝ) / 100000000000000000000) )
        (by norm_num) (by constructor <;> norm_num [Real.pi_gt_d20, Real.pi_lt_four]))
    rw [cosine_taylor_ninety_six_at_zero (b := 4) (x := ((104866216128012819086 : ℝ) / 100000000000000000000)) (by norm_num)]
    have hp : (sevenNineCosUpper[51]! : Rat) + (((104866216128012819086 : Rat) / 100000000000000000000) : Rat)^97 / (Nat.factorial 96) ≤
        Finset.sum (Finset.range 49) (fun k => (-1 : Rat)^k * (((104866216128012819086 : Rat) / 100000000000000000000) : Rat)^(2*k) / Nat.factorial (2*k)) := by native_decide
    have hpR : (sevenNineCosUpper[51]! : ℝ) + ((104866216128012819086 : ℝ) / 100000000000000000000)^97 / (Nat.factorial 96) ≤
        Finset.sum (Finset.range 49) (fun k => (-1 : ℝ)^k * ((104866216128012819086 : ℝ) / 100000000000000000000)^(2*k) / Nat.factorial (2*k)) := by
      norm_num [sevenNineCosUpper, Finset.sum_range_succ]
    simpa [sub_zero] using hpR
  have hangle : ((104866216128012819086 : ℝ) / 100000000000000000000) ≤ Real.arccos (touchCosine a b (Real.sqrt 6 + Real.sqrt 8)) := by
    exact angle_lower_bound_of_cosine (by norm_num)
      (by
        calc
          ((104866216128012819086 : ℝ) / 100000000000000000000) ≤ (314159265358979323846 : ℝ) / 100000000000000000000 := by norm_num
          _ ≤ Real.pi := by
            have hpi := Real.pi_gt_d20.le
            norm_num at hpi ⊢
            exact hpi) (le_trans htouch hcos)
  have hdata : sevenNineAngleLower[51]! = ((104866216128012819086 : Rat) / 100000000000000000000) := by native_decide
  have hdataR : (sevenNineAngleLower[51]! : ℝ) = ((104866216128012819086 : ℝ) / 100000000000000000000) := by
    have h := congrArg (fun q : Rat => (q : ℝ)) hdata
    convert h using 1 ; norm_num
  rw [hdataR]
  exact hangle

theorem sevenNineAngle_2_5_0_0 {a b : ℝ}
    (haL : (sevenNineRadial 2 0 0 : ℝ) ≤ a) (haU : a ≤ (sevenNineRadial 2 0 1 : ℝ))
    (hbL : (sevenNineRadial 5 0 0 : ℝ) ≤ b) (hbU : b ≤ (sevenNineRadial 5 0 1 : ℝ)) :
    (sevenNineAngleLower[52]! : ℝ) ≤ Real.arccos (touchCosine a b (Real.sqrt 6 + Real.sqrt 9)) := by
  let d : ℝ := Real.sqrt 6 + Real.sqrt 9
  have hd' : (((5449489742783178098197284074705891391965947480656670128432692567250960377457315026539859433 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) : ℝ) ≤ d := by
    dsimp [d]
    have h := rat_sum_sqrt_lower (q := ((5449489742783178098197284074705891391965947480656670128432692567250960377457315026539859433 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (qi := ((2449489742783178098197284074705891391965947480656670128432692567250960377457315026539859433104640234818594601226614189124 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (qj := ((3 : Rat) / 1))
      (ni := 6) (nj := 9)
      (by convert sqrt_lower_6 using 1 ; norm_num)
      (by convert sqrt_lower_9 using 1 ; norm_num)
      (by native_decide)
    convert h using 1 ; norm_num
  have hd : (((5449489742783178098197284074705891391965947480656670128432692567250960377457315026539859433 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) ≤ d := by exact hd'
  have hd2 : (((5449489742783178098197284074705891391965947480656670128432692567250960377457315026539859433 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))^2 ≤ d^2 := by
    have hq : (0 : ℝ) ≤ ((5449489742783178098197284074705891391965947480656670128432692567250960377457315026539859433 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) := by norm_num
    have hdn : 0 ≤ d := by positivity
    exact (sq_le_sq₀ hq hdn).mpr hd
  have hd2' : (sevenNineDistanceLower[13]! : ℝ)^2 ≤ d^2 := by
    convert hd2 using 1 ; norm_num [sevenNineDistanceLower]
  have h00 : (sevenNineRadial 2 0 0 : ℝ)^2 + (sevenNineRadial 5 0 0 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[52]! : ℝ) * (2 * (sevenNineRadial 2 0 0 : ℝ) * (sevenNineRadial 5 0 0 : ℝ)) := by
    have hq : (sevenNineRadial 2 0 0)^2 + (sevenNineRadial 5 0 0)^2 - sevenNineDistanceLower[13]!^2 ≤
        sevenNineCosUpper[52]! * (2 * sevenNineRadial 2 0 0 * sevenNineRadial 5 0 0) := by native_decide
    have hqR :
        (sevenNineRadial 2 0 0 : ℝ)^2 + (sevenNineRadial 5 0 0 : ℝ)^2 - (sevenNineDistanceLower[13]! : ℝ)^2 ≤
          (sevenNineCosUpper[52]! : ℝ) * (2 * (sevenNineRadial 2 0 0 : ℝ) * (sevenNineRadial 5 0 0 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 2 0 0 : ℝ)^2 + (sevenNineRadial 5 0 0 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 2 0 0 : ℝ)^2 + (sevenNineRadial 5 0 0 : ℝ)^2 - (sevenNineDistanceLower[13]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h01 : (sevenNineRadial 2 0 0 : ℝ)^2 + (sevenNineRadial 5 0 1 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[52]! : ℝ) * (2 * (sevenNineRadial 2 0 0 : ℝ) * (sevenNineRadial 5 0 1 : ℝ)) := by
    have hq : (sevenNineRadial 2 0 0)^2 + (sevenNineRadial 5 0 1)^2 - sevenNineDistanceLower[13]!^2 ≤
        sevenNineCosUpper[52]! * (2 * sevenNineRadial 2 0 0 * sevenNineRadial 5 0 1) := by native_decide
    have hqR :
        (sevenNineRadial 2 0 0 : ℝ)^2 + (sevenNineRadial 5 0 1 : ℝ)^2 - (sevenNineDistanceLower[13]! : ℝ)^2 ≤
          (sevenNineCosUpper[52]! : ℝ) * (2 * (sevenNineRadial 2 0 0 : ℝ) * (sevenNineRadial 5 0 1 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 2 0 0 : ℝ)^2 + (sevenNineRadial 5 0 1 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 2 0 0 : ℝ)^2 + (sevenNineRadial 5 0 1 : ℝ)^2 - (sevenNineDistanceLower[13]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h10 : (sevenNineRadial 2 0 1 : ℝ)^2 + (sevenNineRadial 5 0 0 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[52]! : ℝ) * (2 * (sevenNineRadial 2 0 1 : ℝ) * (sevenNineRadial 5 0 0 : ℝ)) := by
    have hq : (sevenNineRadial 2 0 1)^2 + (sevenNineRadial 5 0 0)^2 - sevenNineDistanceLower[13]!^2 ≤
        sevenNineCosUpper[52]! * (2 * sevenNineRadial 2 0 1 * sevenNineRadial 5 0 0) := by native_decide
    have hqR :
        (sevenNineRadial 2 0 1 : ℝ)^2 + (sevenNineRadial 5 0 0 : ℝ)^2 - (sevenNineDistanceLower[13]! : ℝ)^2 ≤
          (sevenNineCosUpper[52]! : ℝ) * (2 * (sevenNineRadial 2 0 1 : ℝ) * (sevenNineRadial 5 0 0 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 2 0 1 : ℝ)^2 + (sevenNineRadial 5 0 0 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 2 0 1 : ℝ)^2 + (sevenNineRadial 5 0 0 : ℝ)^2 - (sevenNineDistanceLower[13]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h11 : (sevenNineRadial 2 0 1 : ℝ)^2 + (sevenNineRadial 5 0 1 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[52]! : ℝ) * (2 * (sevenNineRadial 2 0 1 : ℝ) * (sevenNineRadial 5 0 1 : ℝ)) := by
    have hq : (sevenNineRadial 2 0 1)^2 + (sevenNineRadial 5 0 1)^2 - sevenNineDistanceLower[13]!^2 ≤
        sevenNineCosUpper[52]! * (2 * sevenNineRadial 2 0 1 * sevenNineRadial 5 0 1) := by native_decide
    have hqR :
        (sevenNineRadial 2 0 1 : ℝ)^2 + (sevenNineRadial 5 0 1 : ℝ)^2 - (sevenNineDistanceLower[13]! : ℝ)^2 ≤
          (sevenNineCosUpper[52]! : ℝ) * (2 * (sevenNineRadial 2 0 1 : ℝ) * (sevenNineRadial 5 0 1 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 2 0 1 : ℝ)^2 + (sevenNineRadial 5 0 1 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 2 0 1 : ℝ)^2 + (sevenNineRadial 5 0 1 : ℝ)^2 - (sevenNineDistanceLower[13]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have htouch := corner_touch_cosine_bound haL haU hbL hbU
    (by norm_num [sevenNineRadial, sevenNineRadialBounds])
    (by norm_num [sevenNineRadial, sevenNineRadialBounds]) h00 h01 h10 h11
  have hcos : (sevenNineCosUpper[52]! : ℝ) ≤ Real.cos ((207698446044386570197 : ℝ) / 100000000000000000000) := by
    apply lower_bound_of_taylor_error
      (cosine_taylor_ninety_six_remainder (a := 0) (b := 4) (x := ((207698446044386570197 : ℝ) / 100000000000000000000) )
        (by norm_num) (by constructor <;> norm_num [Real.pi_gt_d20, Real.pi_lt_four]))
    rw [cosine_taylor_ninety_six_at_zero (b := 4) (x := ((207698446044386570197 : ℝ) / 100000000000000000000)) (by norm_num)]
    have hp : (sevenNineCosUpper[52]! : Rat) + (((207698446044386570197 : Rat) / 100000000000000000000) : Rat)^97 / (Nat.factorial 96) ≤
        Finset.sum (Finset.range 49) (fun k => (-1 : Rat)^k * (((207698446044386570197 : Rat) / 100000000000000000000) : Rat)^(2*k) / Nat.factorial (2*k)) := by native_decide
    have hpR : (sevenNineCosUpper[52]! : ℝ) + ((207698446044386570197 : ℝ) / 100000000000000000000)^97 / (Nat.factorial 96) ≤
        Finset.sum (Finset.range 49) (fun k => (-1 : ℝ)^k * ((207698446044386570197 : ℝ) / 100000000000000000000)^(2*k) / Nat.factorial (2*k)) := by
      norm_num [sevenNineCosUpper, Finset.sum_range_succ]
    simpa [sub_zero] using hpR
  have hangle : ((207698446044386570197 : ℝ) / 100000000000000000000) ≤ Real.arccos (touchCosine a b (Real.sqrt 6 + Real.sqrt 9)) := by
    exact angle_lower_bound_of_cosine (by norm_num)
      (by
        calc
          ((207698446044386570197 : ℝ) / 100000000000000000000) ≤ (314159265358979323846 : ℝ) / 100000000000000000000 := by norm_num
          _ ≤ Real.pi := by
            have hpi := Real.pi_gt_d20.le
            norm_num at hpi ⊢
            exact hpi) (le_trans htouch hcos)
  have hdata : sevenNineAngleLower[52]! = ((207698446044386570197 : Rat) / 100000000000000000000) := by native_decide
  have hdataR : (sevenNineAngleLower[52]! : ℝ) = ((207698446044386570197 : ℝ) / 100000000000000000000) := by
    have h := congrArg (fun q : Rat => (q : ℝ)) hdata
    convert h using 1 ; norm_num
  rw [hdataR]
  exact hangle

theorem sevenNineAngle_2_5_0_1 {a b : ℝ}
    (haL : (sevenNineRadial 2 0 0 : ℝ) ≤ a) (haU : a ≤ (sevenNineRadial 2 0 1 : ℝ))
    (hbL : (sevenNineRadial 5 1 0 : ℝ) ≤ b) (hbU : b ≤ (sevenNineRadial 5 1 1 : ℝ)) :
    (sevenNineAngleLower[53]! : ℝ) ≤ Real.arccos (touchCosine a b (Real.sqrt 6 + Real.sqrt 9)) := by
  let d : ℝ := Real.sqrt 6 + Real.sqrt 9
  have hd' : (((5449489742783178098197284074705891391965947480656670128432692567250960377457315026539859433 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) : ℝ) ≤ d := by
    dsimp [d]
    have h := rat_sum_sqrt_lower (q := ((5449489742783178098197284074705891391965947480656670128432692567250960377457315026539859433 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (qi := ((2449489742783178098197284074705891391965947480656670128432692567250960377457315026539859433104640234818594601226614189124 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (qj := ((3 : Rat) / 1))
      (ni := 6) (nj := 9)
      (by convert sqrt_lower_6 using 1 ; norm_num)
      (by convert sqrt_lower_9 using 1 ; norm_num)
      (by native_decide)
    convert h using 1 ; norm_num
  have hd : (((5449489742783178098197284074705891391965947480656670128432692567250960377457315026539859433 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) ≤ d := by exact hd'
  have hd2 : (((5449489742783178098197284074705891391965947480656670128432692567250960377457315026539859433 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))^2 ≤ d^2 := by
    have hq : (0 : ℝ) ≤ ((5449489742783178098197284074705891391965947480656670128432692567250960377457315026539859433 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) := by norm_num
    have hdn : 0 ≤ d := by positivity
    exact (sq_le_sq₀ hq hdn).mpr hd
  have hd2' : (sevenNineDistanceLower[13]! : ℝ)^2 ≤ d^2 := by
    convert hd2 using 1 ; norm_num [sevenNineDistanceLower]
  have h00 : (sevenNineRadial 2 0 0 : ℝ)^2 + (sevenNineRadial 5 1 0 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[53]! : ℝ) * (2 * (sevenNineRadial 2 0 0 : ℝ) * (sevenNineRadial 5 1 0 : ℝ)) := by
    have hq : (sevenNineRadial 2 0 0)^2 + (sevenNineRadial 5 1 0)^2 - sevenNineDistanceLower[13]!^2 ≤
        sevenNineCosUpper[53]! * (2 * sevenNineRadial 2 0 0 * sevenNineRadial 5 1 0) := by native_decide
    have hqR :
        (sevenNineRadial 2 0 0 : ℝ)^2 + (sevenNineRadial 5 1 0 : ℝ)^2 - (sevenNineDistanceLower[13]! : ℝ)^2 ≤
          (sevenNineCosUpper[53]! : ℝ) * (2 * (sevenNineRadial 2 0 0 : ℝ) * (sevenNineRadial 5 1 0 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 2 0 0 : ℝ)^2 + (sevenNineRadial 5 1 0 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 2 0 0 : ℝ)^2 + (sevenNineRadial 5 1 0 : ℝ)^2 - (sevenNineDistanceLower[13]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h01 : (sevenNineRadial 2 0 0 : ℝ)^2 + (sevenNineRadial 5 1 1 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[53]! : ℝ) * (2 * (sevenNineRadial 2 0 0 : ℝ) * (sevenNineRadial 5 1 1 : ℝ)) := by
    have hq : (sevenNineRadial 2 0 0)^2 + (sevenNineRadial 5 1 1)^2 - sevenNineDistanceLower[13]!^2 ≤
        sevenNineCosUpper[53]! * (2 * sevenNineRadial 2 0 0 * sevenNineRadial 5 1 1) := by native_decide
    have hqR :
        (sevenNineRadial 2 0 0 : ℝ)^2 + (sevenNineRadial 5 1 1 : ℝ)^2 - (sevenNineDistanceLower[13]! : ℝ)^2 ≤
          (sevenNineCosUpper[53]! : ℝ) * (2 * (sevenNineRadial 2 0 0 : ℝ) * (sevenNineRadial 5 1 1 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 2 0 0 : ℝ)^2 + (sevenNineRadial 5 1 1 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 2 0 0 : ℝ)^2 + (sevenNineRadial 5 1 1 : ℝ)^2 - (sevenNineDistanceLower[13]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h10 : (sevenNineRadial 2 0 1 : ℝ)^2 + (sevenNineRadial 5 1 0 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[53]! : ℝ) * (2 * (sevenNineRadial 2 0 1 : ℝ) * (sevenNineRadial 5 1 0 : ℝ)) := by
    have hq : (sevenNineRadial 2 0 1)^2 + (sevenNineRadial 5 1 0)^2 - sevenNineDistanceLower[13]!^2 ≤
        sevenNineCosUpper[53]! * (2 * sevenNineRadial 2 0 1 * sevenNineRadial 5 1 0) := by native_decide
    have hqR :
        (sevenNineRadial 2 0 1 : ℝ)^2 + (sevenNineRadial 5 1 0 : ℝ)^2 - (sevenNineDistanceLower[13]! : ℝ)^2 ≤
          (sevenNineCosUpper[53]! : ℝ) * (2 * (sevenNineRadial 2 0 1 : ℝ) * (sevenNineRadial 5 1 0 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 2 0 1 : ℝ)^2 + (sevenNineRadial 5 1 0 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 2 0 1 : ℝ)^2 + (sevenNineRadial 5 1 0 : ℝ)^2 - (sevenNineDistanceLower[13]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h11 : (sevenNineRadial 2 0 1 : ℝ)^2 + (sevenNineRadial 5 1 1 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[53]! : ℝ) * (2 * (sevenNineRadial 2 0 1 : ℝ) * (sevenNineRadial 5 1 1 : ℝ)) := by
    have hq : (sevenNineRadial 2 0 1)^2 + (sevenNineRadial 5 1 1)^2 - sevenNineDistanceLower[13]!^2 ≤
        sevenNineCosUpper[53]! * (2 * sevenNineRadial 2 0 1 * sevenNineRadial 5 1 1) := by native_decide
    have hqR :
        (sevenNineRadial 2 0 1 : ℝ)^2 + (sevenNineRadial 5 1 1 : ℝ)^2 - (sevenNineDistanceLower[13]! : ℝ)^2 ≤
          (sevenNineCosUpper[53]! : ℝ) * (2 * (sevenNineRadial 2 0 1 : ℝ) * (sevenNineRadial 5 1 1 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 2 0 1 : ℝ)^2 + (sevenNineRadial 5 1 1 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 2 0 1 : ℝ)^2 + (sevenNineRadial 5 1 1 : ℝ)^2 - (sevenNineDistanceLower[13]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have htouch := corner_touch_cosine_bound haL haU hbL hbU
    (by norm_num [sevenNineRadial, sevenNineRadialBounds])
    (by norm_num [sevenNineRadial, sevenNineRadialBounds]) h00 h01 h10 h11
  have hcos : (sevenNineCosUpper[53]! : ℝ) ≤ Real.cos ((143116860305577001537 : ℝ) / 100000000000000000000) := by
    apply lower_bound_of_taylor_error
      (cosine_taylor_ninety_six_remainder (a := 0) (b := 4) (x := ((143116860305577001537 : ℝ) / 100000000000000000000) )
        (by norm_num) (by constructor <;> norm_num [Real.pi_gt_d20, Real.pi_lt_four]))
    rw [cosine_taylor_ninety_six_at_zero (b := 4) (x := ((143116860305577001537 : ℝ) / 100000000000000000000)) (by norm_num)]
    have hp : (sevenNineCosUpper[53]! : Rat) + (((143116860305577001537 : Rat) / 100000000000000000000) : Rat)^97 / (Nat.factorial 96) ≤
        Finset.sum (Finset.range 49) (fun k => (-1 : Rat)^k * (((143116860305577001537 : Rat) / 100000000000000000000) : Rat)^(2*k) / Nat.factorial (2*k)) := by native_decide
    have hpR : (sevenNineCosUpper[53]! : ℝ) + ((143116860305577001537 : ℝ) / 100000000000000000000)^97 / (Nat.factorial 96) ≤
        Finset.sum (Finset.range 49) (fun k => (-1 : ℝ)^k * ((143116860305577001537 : ℝ) / 100000000000000000000)^(2*k) / Nat.factorial (2*k)) := by
      norm_num [sevenNineCosUpper, Finset.sum_range_succ]
    simpa [sub_zero] using hpR
  have hangle : ((143116860305577001537 : ℝ) / 100000000000000000000) ≤ Real.arccos (touchCosine a b (Real.sqrt 6 + Real.sqrt 9)) := by
    exact angle_lower_bound_of_cosine (by norm_num)
      (by
        calc
          ((143116860305577001537 : ℝ) / 100000000000000000000) ≤ (314159265358979323846 : ℝ) / 100000000000000000000 := by norm_num
          _ ≤ Real.pi := by
            have hpi := Real.pi_gt_d20.le
            norm_num at hpi ⊢
            exact hpi) (le_trans htouch hcos)
  have hdata : sevenNineAngleLower[53]! = ((143116860305577001537 : Rat) / 100000000000000000000) := by native_decide
  have hdataR : (sevenNineAngleLower[53]! : ℝ) = ((143116860305577001537 : ℝ) / 100000000000000000000) := by
    have h := congrArg (fun q : Rat => (q : ℝ)) hdata
    convert h using 1 ; norm_num
  rw [hdataR]
  exact hangle

theorem sevenNineAngle_2_5_1_0 {a b : ℝ}
    (haL : (sevenNineRadial 2 1 0 : ℝ) ≤ a) (haU : a ≤ (sevenNineRadial 2 1 1 : ℝ))
    (hbL : (sevenNineRadial 5 0 0 : ℝ) ≤ b) (hbU : b ≤ (sevenNineRadial 5 0 1 : ℝ)) :
    (sevenNineAngleLower[54]! : ℝ) ≤ Real.arccos (touchCosine a b (Real.sqrt 6 + Real.sqrt 9)) := by
  let d : ℝ := Real.sqrt 6 + Real.sqrt 9
  have hd' : (((5449489742783178098197284074705891391965947480656670128432692567250960377457315026539859433 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) : ℝ) ≤ d := by
    dsimp [d]
    have h := rat_sum_sqrt_lower (q := ((5449489742783178098197284074705891391965947480656670128432692567250960377457315026539859433 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (qi := ((2449489742783178098197284074705891391965947480656670128432692567250960377457315026539859433104640234818594601226614189124 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (qj := ((3 : Rat) / 1))
      (ni := 6) (nj := 9)
      (by convert sqrt_lower_6 using 1 ; norm_num)
      (by convert sqrt_lower_9 using 1 ; norm_num)
      (by native_decide)
    convert h using 1 ; norm_num
  have hd : (((5449489742783178098197284074705891391965947480656670128432692567250960377457315026539859433 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) ≤ d := by exact hd'
  have hd2 : (((5449489742783178098197284074705891391965947480656670128432692567250960377457315026539859433 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))^2 ≤ d^2 := by
    have hq : (0 : ℝ) ≤ ((5449489742783178098197284074705891391965947480656670128432692567250960377457315026539859433 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) := by norm_num
    have hdn : 0 ≤ d := by positivity
    exact (sq_le_sq₀ hq hdn).mpr hd
  have hd2' : (sevenNineDistanceLower[13]! : ℝ)^2 ≤ d^2 := by
    convert hd2 using 1 ; norm_num [sevenNineDistanceLower]
  have h00 : (sevenNineRadial 2 1 0 : ℝ)^2 + (sevenNineRadial 5 0 0 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[54]! : ℝ) * (2 * (sevenNineRadial 2 1 0 : ℝ) * (sevenNineRadial 5 0 0 : ℝ)) := by
    have hq : (sevenNineRadial 2 1 0)^2 + (sevenNineRadial 5 0 0)^2 - sevenNineDistanceLower[13]!^2 ≤
        sevenNineCosUpper[54]! * (2 * sevenNineRadial 2 1 0 * sevenNineRadial 5 0 0) := by native_decide
    have hqR :
        (sevenNineRadial 2 1 0 : ℝ)^2 + (sevenNineRadial 5 0 0 : ℝ)^2 - (sevenNineDistanceLower[13]! : ℝ)^2 ≤
          (sevenNineCosUpper[54]! : ℝ) * (2 * (sevenNineRadial 2 1 0 : ℝ) * (sevenNineRadial 5 0 0 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 2 1 0 : ℝ)^2 + (sevenNineRadial 5 0 0 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 2 1 0 : ℝ)^2 + (sevenNineRadial 5 0 0 : ℝ)^2 - (sevenNineDistanceLower[13]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h01 : (sevenNineRadial 2 1 0 : ℝ)^2 + (sevenNineRadial 5 0 1 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[54]! : ℝ) * (2 * (sevenNineRadial 2 1 0 : ℝ) * (sevenNineRadial 5 0 1 : ℝ)) := by
    have hq : (sevenNineRadial 2 1 0)^2 + (sevenNineRadial 5 0 1)^2 - sevenNineDistanceLower[13]!^2 ≤
        sevenNineCosUpper[54]! * (2 * sevenNineRadial 2 1 0 * sevenNineRadial 5 0 1) := by native_decide
    have hqR :
        (sevenNineRadial 2 1 0 : ℝ)^2 + (sevenNineRadial 5 0 1 : ℝ)^2 - (sevenNineDistanceLower[13]! : ℝ)^2 ≤
          (sevenNineCosUpper[54]! : ℝ) * (2 * (sevenNineRadial 2 1 0 : ℝ) * (sevenNineRadial 5 0 1 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 2 1 0 : ℝ)^2 + (sevenNineRadial 5 0 1 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 2 1 0 : ℝ)^2 + (sevenNineRadial 5 0 1 : ℝ)^2 - (sevenNineDistanceLower[13]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h10 : (sevenNineRadial 2 1 1 : ℝ)^2 + (sevenNineRadial 5 0 0 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[54]! : ℝ) * (2 * (sevenNineRadial 2 1 1 : ℝ) * (sevenNineRadial 5 0 0 : ℝ)) := by
    have hq : (sevenNineRadial 2 1 1)^2 + (sevenNineRadial 5 0 0)^2 - sevenNineDistanceLower[13]!^2 ≤
        sevenNineCosUpper[54]! * (2 * sevenNineRadial 2 1 1 * sevenNineRadial 5 0 0) := by native_decide
    have hqR :
        (sevenNineRadial 2 1 1 : ℝ)^2 + (sevenNineRadial 5 0 0 : ℝ)^2 - (sevenNineDistanceLower[13]! : ℝ)^2 ≤
          (sevenNineCosUpper[54]! : ℝ) * (2 * (sevenNineRadial 2 1 1 : ℝ) * (sevenNineRadial 5 0 0 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 2 1 1 : ℝ)^2 + (sevenNineRadial 5 0 0 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 2 1 1 : ℝ)^2 + (sevenNineRadial 5 0 0 : ℝ)^2 - (sevenNineDistanceLower[13]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h11 : (sevenNineRadial 2 1 1 : ℝ)^2 + (sevenNineRadial 5 0 1 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[54]! : ℝ) * (2 * (sevenNineRadial 2 1 1 : ℝ) * (sevenNineRadial 5 0 1 : ℝ)) := by
    have hq : (sevenNineRadial 2 1 1)^2 + (sevenNineRadial 5 0 1)^2 - sevenNineDistanceLower[13]!^2 ≤
        sevenNineCosUpper[54]! * (2 * sevenNineRadial 2 1 1 * sevenNineRadial 5 0 1) := by native_decide
    have hqR :
        (sevenNineRadial 2 1 1 : ℝ)^2 + (sevenNineRadial 5 0 1 : ℝ)^2 - (sevenNineDistanceLower[13]! : ℝ)^2 ≤
          (sevenNineCosUpper[54]! : ℝ) * (2 * (sevenNineRadial 2 1 1 : ℝ) * (sevenNineRadial 5 0 1 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 2 1 1 : ℝ)^2 + (sevenNineRadial 5 0 1 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 2 1 1 : ℝ)^2 + (sevenNineRadial 5 0 1 : ℝ)^2 - (sevenNineDistanceLower[13]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have htouch := corner_touch_cosine_bound haL haU hbL hbU
    (by norm_num [sevenNineRadial, sevenNineRadialBounds])
    (by norm_num [sevenNineRadial, sevenNineRadialBounds]) h00 h01 h10 h11
  have hcos : (sevenNineCosUpper[54]! : ℝ) ≤ Real.cos ((127613818593400488397 : ℝ) / 100000000000000000000) := by
    apply lower_bound_of_taylor_error
      (cosine_taylor_ninety_six_remainder (a := 0) (b := 4) (x := ((127613818593400488397 : ℝ) / 100000000000000000000) )
        (by norm_num) (by constructor <;> norm_num [Real.pi_gt_d20, Real.pi_lt_four]))
    rw [cosine_taylor_ninety_six_at_zero (b := 4) (x := ((127613818593400488397 : ℝ) / 100000000000000000000)) (by norm_num)]
    have hp : (sevenNineCosUpper[54]! : Rat) + (((127613818593400488397 : Rat) / 100000000000000000000) : Rat)^97 / (Nat.factorial 96) ≤
        Finset.sum (Finset.range 49) (fun k => (-1 : Rat)^k * (((127613818593400488397 : Rat) / 100000000000000000000) : Rat)^(2*k) / Nat.factorial (2*k)) := by native_decide
    have hpR : (sevenNineCosUpper[54]! : ℝ) + ((127613818593400488397 : ℝ) / 100000000000000000000)^97 / (Nat.factorial 96) ≤
        Finset.sum (Finset.range 49) (fun k => (-1 : ℝ)^k * ((127613818593400488397 : ℝ) / 100000000000000000000)^(2*k) / Nat.factorial (2*k)) := by
      norm_num [sevenNineCosUpper, Finset.sum_range_succ]
    simpa [sub_zero] using hpR
  have hangle : ((127613818593400488397 : ℝ) / 100000000000000000000) ≤ Real.arccos (touchCosine a b (Real.sqrt 6 + Real.sqrt 9)) := by
    exact angle_lower_bound_of_cosine (by norm_num)
      (by
        calc
          ((127613818593400488397 : ℝ) / 100000000000000000000) ≤ (314159265358979323846 : ℝ) / 100000000000000000000 := by norm_num
          _ ≤ Real.pi := by
            have hpi := Real.pi_gt_d20.le
            norm_num at hpi ⊢
            exact hpi) (le_trans htouch hcos)
  have hdata : sevenNineAngleLower[54]! = ((127613818593400488397 : Rat) / 100000000000000000000) := by native_decide
  have hdataR : (sevenNineAngleLower[54]! : ℝ) = ((127613818593400488397 : ℝ) / 100000000000000000000) := by
    have h := congrArg (fun q : Rat => (q : ℝ)) hdata
    convert h using 1 ; norm_num
  rw [hdataR]
  exact hangle

theorem sevenNineAngle_2_5_1_1 {a b : ℝ}
    (haL : (sevenNineRadial 2 1 0 : ℝ) ≤ a) (haU : a ≤ (sevenNineRadial 2 1 1 : ℝ))
    (hbL : (sevenNineRadial 5 1 0 : ℝ) ≤ b) (hbU : b ≤ (sevenNineRadial 5 1 1 : ℝ)) :
    (sevenNineAngleLower[55]! : ℝ) ≤ Real.arccos (touchCosine a b (Real.sqrt 6 + Real.sqrt 9)) := by
  let d : ℝ := Real.sqrt 6 + Real.sqrt 9
  have hd' : (((5449489742783178098197284074705891391965947480656670128432692567250960377457315026539859433 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) : ℝ) ≤ d := by
    dsimp [d]
    have h := rat_sum_sqrt_lower (q := ((5449489742783178098197284074705891391965947480656670128432692567250960377457315026539859433 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (qi := ((2449489742783178098197284074705891391965947480656670128432692567250960377457315026539859433104640234818594601226614189124 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (qj := ((3 : Rat) / 1))
      (ni := 6) (nj := 9)
      (by convert sqrt_lower_6 using 1 ; norm_num)
      (by convert sqrt_lower_9 using 1 ; norm_num)
      (by native_decide)
    convert h using 1 ; norm_num
  have hd : (((5449489742783178098197284074705891391965947480656670128432692567250960377457315026539859433 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) ≤ d := by exact hd'
  have hd2 : (((5449489742783178098197284074705891391965947480656670128432692567250960377457315026539859433 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))^2 ≤ d^2 := by
    have hq : (0 : ℝ) ≤ ((5449489742783178098197284074705891391965947480656670128432692567250960377457315026539859433 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) := by norm_num
    have hdn : 0 ≤ d := by positivity
    exact (sq_le_sq₀ hq hdn).mpr hd
  have hd2' : (sevenNineDistanceLower[13]! : ℝ)^2 ≤ d^2 := by
    convert hd2 using 1 ; norm_num [sevenNineDistanceLower]
  have h00 : (sevenNineRadial 2 1 0 : ℝ)^2 + (sevenNineRadial 5 1 0 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[55]! : ℝ) * (2 * (sevenNineRadial 2 1 0 : ℝ) * (sevenNineRadial 5 1 0 : ℝ)) := by
    have hq : (sevenNineRadial 2 1 0)^2 + (sevenNineRadial 5 1 0)^2 - sevenNineDistanceLower[13]!^2 ≤
        sevenNineCosUpper[55]! * (2 * sevenNineRadial 2 1 0 * sevenNineRadial 5 1 0) := by native_decide
    have hqR :
        (sevenNineRadial 2 1 0 : ℝ)^2 + (sevenNineRadial 5 1 0 : ℝ)^2 - (sevenNineDistanceLower[13]! : ℝ)^2 ≤
          (sevenNineCosUpper[55]! : ℝ) * (2 * (sevenNineRadial 2 1 0 : ℝ) * (sevenNineRadial 5 1 0 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 2 1 0 : ℝ)^2 + (sevenNineRadial 5 1 0 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 2 1 0 : ℝ)^2 + (sevenNineRadial 5 1 0 : ℝ)^2 - (sevenNineDistanceLower[13]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h01 : (sevenNineRadial 2 1 0 : ℝ)^2 + (sevenNineRadial 5 1 1 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[55]! : ℝ) * (2 * (sevenNineRadial 2 1 0 : ℝ) * (sevenNineRadial 5 1 1 : ℝ)) := by
    have hq : (sevenNineRadial 2 1 0)^2 + (sevenNineRadial 5 1 1)^2 - sevenNineDistanceLower[13]!^2 ≤
        sevenNineCosUpper[55]! * (2 * sevenNineRadial 2 1 0 * sevenNineRadial 5 1 1) := by native_decide
    have hqR :
        (sevenNineRadial 2 1 0 : ℝ)^2 + (sevenNineRadial 5 1 1 : ℝ)^2 - (sevenNineDistanceLower[13]! : ℝ)^2 ≤
          (sevenNineCosUpper[55]! : ℝ) * (2 * (sevenNineRadial 2 1 0 : ℝ) * (sevenNineRadial 5 1 1 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 2 1 0 : ℝ)^2 + (sevenNineRadial 5 1 1 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 2 1 0 : ℝ)^2 + (sevenNineRadial 5 1 1 : ℝ)^2 - (sevenNineDistanceLower[13]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h10 : (sevenNineRadial 2 1 1 : ℝ)^2 + (sevenNineRadial 5 1 0 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[55]! : ℝ) * (2 * (sevenNineRadial 2 1 1 : ℝ) * (sevenNineRadial 5 1 0 : ℝ)) := by
    have hq : (sevenNineRadial 2 1 1)^2 + (sevenNineRadial 5 1 0)^2 - sevenNineDistanceLower[13]!^2 ≤
        sevenNineCosUpper[55]! * (2 * sevenNineRadial 2 1 1 * sevenNineRadial 5 1 0) := by native_decide
    have hqR :
        (sevenNineRadial 2 1 1 : ℝ)^2 + (sevenNineRadial 5 1 0 : ℝ)^2 - (sevenNineDistanceLower[13]! : ℝ)^2 ≤
          (sevenNineCosUpper[55]! : ℝ) * (2 * (sevenNineRadial 2 1 1 : ℝ) * (sevenNineRadial 5 1 0 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 2 1 1 : ℝ)^2 + (sevenNineRadial 5 1 0 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 2 1 1 : ℝ)^2 + (sevenNineRadial 5 1 0 : ℝ)^2 - (sevenNineDistanceLower[13]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h11 : (sevenNineRadial 2 1 1 : ℝ)^2 + (sevenNineRadial 5 1 1 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[55]! : ℝ) * (2 * (sevenNineRadial 2 1 1 : ℝ) * (sevenNineRadial 5 1 1 : ℝ)) := by
    have hq : (sevenNineRadial 2 1 1)^2 + (sevenNineRadial 5 1 1)^2 - sevenNineDistanceLower[13]!^2 ≤
        sevenNineCosUpper[55]! * (2 * sevenNineRadial 2 1 1 * sevenNineRadial 5 1 1) := by native_decide
    have hqR :
        (sevenNineRadial 2 1 1 : ℝ)^2 + (sevenNineRadial 5 1 1 : ℝ)^2 - (sevenNineDistanceLower[13]! : ℝ)^2 ≤
          (sevenNineCosUpper[55]! : ℝ) * (2 * (sevenNineRadial 2 1 1 : ℝ) * (sevenNineRadial 5 1 1 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 2 1 1 : ℝ)^2 + (sevenNineRadial 5 1 1 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 2 1 1 : ℝ)^2 + (sevenNineRadial 5 1 1 : ℝ)^2 - (sevenNineDistanceLower[13]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have htouch := corner_touch_cosine_bound haL haU hbL hbU
    (by norm_num [sevenNineRadial, sevenNineRadialBounds])
    (by norm_num [sevenNineRadial, sevenNineRadialBounds]) h00 h01 h10 h11
  have hcos : (sevenNineCosUpper[55]! : ℝ) ≤ Real.cos ((110435855526514949216 : ℝ) / 100000000000000000000) := by
    apply lower_bound_of_taylor_error
      (cosine_taylor_ninety_six_remainder (a := 0) (b := 4) (x := ((110435855526514949216 : ℝ) / 100000000000000000000) )
        (by norm_num) (by constructor <;> norm_num [Real.pi_gt_d20, Real.pi_lt_four]))
    rw [cosine_taylor_ninety_six_at_zero (b := 4) (x := ((110435855526514949216 : ℝ) / 100000000000000000000)) (by norm_num)]
    have hp : (sevenNineCosUpper[55]! : Rat) + (((110435855526514949216 : Rat) / 100000000000000000000) : Rat)^97 / (Nat.factorial 96) ≤
        Finset.sum (Finset.range 49) (fun k => (-1 : Rat)^k * (((110435855526514949216 : Rat) / 100000000000000000000) : Rat)^(2*k) / Nat.factorial (2*k)) := by native_decide
    have hpR : (sevenNineCosUpper[55]! : ℝ) + ((110435855526514949216 : ℝ) / 100000000000000000000)^97 / (Nat.factorial 96) ≤
        Finset.sum (Finset.range 49) (fun k => (-1 : ℝ)^k * ((110435855526514949216 : ℝ) / 100000000000000000000)^(2*k) / Nat.factorial (2*k)) := by
      norm_num [sevenNineCosUpper, Finset.sum_range_succ]
    simpa [sub_zero] using hpR
  have hangle : ((110435855526514949216 : ℝ) / 100000000000000000000) ≤ Real.arccos (touchCosine a b (Real.sqrt 6 + Real.sqrt 9)) := by
    exact angle_lower_bound_of_cosine (by norm_num)
      (by
        calc
          ((110435855526514949216 : ℝ) / 100000000000000000000) ≤ (314159265358979323846 : ℝ) / 100000000000000000000 := by norm_num
          _ ≤ Real.pi := by
            have hpi := Real.pi_gt_d20.le
            norm_num at hpi ⊢
            exact hpi) (le_trans htouch hcos)
  have hdata : sevenNineAngleLower[55]! = ((110435855526514949216 : Rat) / 100000000000000000000) := by native_decide
  have hdataR : (sevenNineAngleLower[55]! : ℝ) = ((110435855526514949216 : ℝ) / 100000000000000000000) := by
    have h := congrArg (fun q : Rat => (q : ℝ)) hdata
    convert h using 1 ; norm_num
  rw [hdataR]
  exact hangle

theorem sevenNineAngle_2_6_0_0 {a b : ℝ}
    (haL : (sevenNineRadial 2 0 0 : ℝ) ≤ a) (haU : a ≤ (sevenNineRadial 2 0 1 : ℝ))
    (hbL : (sevenNineRadial 6 0 0 : ℝ) ≤ b) (hbU : b ≤ (sevenNineRadial 6 0 1 : ℝ)) :
    (sevenNineAngleLower[56]! : ℝ) ≤ Real.arccos (touchCosine a b (Real.sqrt 6 + Real.sqrt 10)) := by
  let d : ℝ := Real.sqrt 6 + Real.sqrt 10
  have hd' : (((5611767402951557430196177619138609925685502619981886955290197420043554816096553247884107541 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) : ℝ) ≤ d := by
    dsimp [d]
    have h := rat_sum_sqrt_lower (q := ((5611767402951557430196177619138609925685502619981886955290197420043554816096553247884107541 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (qi := ((2449489742783178098197284074705891391965947480656670128432692567250960377457315026539859433104640234818594601226614189124 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (qj := ((3162277660168379331998893544432718533719555139325216826857504852792594438639238221344248108379300295187347284152840055148 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))
      (ni := 6) (nj := 10)
      (by convert sqrt_lower_6 using 1 ; norm_num)
      (by convert sqrt_lower_10 using 1 ; norm_num)
      (by native_decide)
    convert h using 1 ; norm_num
  have hd : (((5611767402951557430196177619138609925685502619981886955290197420043554816096553247884107541 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) ≤ d := by exact hd'
  have hd2 : (((5611767402951557430196177619138609925685502619981886955290197420043554816096553247884107541 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))^2 ≤ d^2 := by
    have hq : (0 : ℝ) ≤ ((5611767402951557430196177619138609925685502619981886955290197420043554816096553247884107541 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) := by norm_num
    have hdn : 0 ≤ d := by positivity
    exact (sq_le_sq₀ hq hdn).mpr hd
  have hd2' : (sevenNineDistanceLower[14]! : ℝ)^2 ≤ d^2 := by
    convert hd2 using 1 ; norm_num [sevenNineDistanceLower]
  have h00 : (sevenNineRadial 2 0 0 : ℝ)^2 + (sevenNineRadial 6 0 0 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[56]! : ℝ) * (2 * (sevenNineRadial 2 0 0 : ℝ) * (sevenNineRadial 6 0 0 : ℝ)) := by
    have hq : (sevenNineRadial 2 0 0)^2 + (sevenNineRadial 6 0 0)^2 - sevenNineDistanceLower[14]!^2 ≤
        sevenNineCosUpper[56]! * (2 * sevenNineRadial 2 0 0 * sevenNineRadial 6 0 0) := by native_decide
    have hqR :
        (sevenNineRadial 2 0 0 : ℝ)^2 + (sevenNineRadial 6 0 0 : ℝ)^2 - (sevenNineDistanceLower[14]! : ℝ)^2 ≤
          (sevenNineCosUpper[56]! : ℝ) * (2 * (sevenNineRadial 2 0 0 : ℝ) * (sevenNineRadial 6 0 0 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 2 0 0 : ℝ)^2 + (sevenNineRadial 6 0 0 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 2 0 0 : ℝ)^2 + (sevenNineRadial 6 0 0 : ℝ)^2 - (sevenNineDistanceLower[14]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h01 : (sevenNineRadial 2 0 0 : ℝ)^2 + (sevenNineRadial 6 0 1 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[56]! : ℝ) * (2 * (sevenNineRadial 2 0 0 : ℝ) * (sevenNineRadial 6 0 1 : ℝ)) := by
    have hq : (sevenNineRadial 2 0 0)^2 + (sevenNineRadial 6 0 1)^2 - sevenNineDistanceLower[14]!^2 ≤
        sevenNineCosUpper[56]! * (2 * sevenNineRadial 2 0 0 * sevenNineRadial 6 0 1) := by native_decide
    have hqR :
        (sevenNineRadial 2 0 0 : ℝ)^2 + (sevenNineRadial 6 0 1 : ℝ)^2 - (sevenNineDistanceLower[14]! : ℝ)^2 ≤
          (sevenNineCosUpper[56]! : ℝ) * (2 * (sevenNineRadial 2 0 0 : ℝ) * (sevenNineRadial 6 0 1 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 2 0 0 : ℝ)^2 + (sevenNineRadial 6 0 1 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 2 0 0 : ℝ)^2 + (sevenNineRadial 6 0 1 : ℝ)^2 - (sevenNineDistanceLower[14]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h10 : (sevenNineRadial 2 0 1 : ℝ)^2 + (sevenNineRadial 6 0 0 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[56]! : ℝ) * (2 * (sevenNineRadial 2 0 1 : ℝ) * (sevenNineRadial 6 0 0 : ℝ)) := by
    have hq : (sevenNineRadial 2 0 1)^2 + (sevenNineRadial 6 0 0)^2 - sevenNineDistanceLower[14]!^2 ≤
        sevenNineCosUpper[56]! * (2 * sevenNineRadial 2 0 1 * sevenNineRadial 6 0 0) := by native_decide
    have hqR :
        (sevenNineRadial 2 0 1 : ℝ)^2 + (sevenNineRadial 6 0 0 : ℝ)^2 - (sevenNineDistanceLower[14]! : ℝ)^2 ≤
          (sevenNineCosUpper[56]! : ℝ) * (2 * (sevenNineRadial 2 0 1 : ℝ) * (sevenNineRadial 6 0 0 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 2 0 1 : ℝ)^2 + (sevenNineRadial 6 0 0 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 2 0 1 : ℝ)^2 + (sevenNineRadial 6 0 0 : ℝ)^2 - (sevenNineDistanceLower[14]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h11 : (sevenNineRadial 2 0 1 : ℝ)^2 + (sevenNineRadial 6 0 1 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[56]! : ℝ) * (2 * (sevenNineRadial 2 0 1 : ℝ) * (sevenNineRadial 6 0 1 : ℝ)) := by
    have hq : (sevenNineRadial 2 0 1)^2 + (sevenNineRadial 6 0 1)^2 - sevenNineDistanceLower[14]!^2 ≤
        sevenNineCosUpper[56]! * (2 * sevenNineRadial 2 0 1 * sevenNineRadial 6 0 1) := by native_decide
    have hqR :
        (sevenNineRadial 2 0 1 : ℝ)^2 + (sevenNineRadial 6 0 1 : ℝ)^2 - (sevenNineDistanceLower[14]! : ℝ)^2 ≤
          (sevenNineCosUpper[56]! : ℝ) * (2 * (sevenNineRadial 2 0 1 : ℝ) * (sevenNineRadial 6 0 1 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 2 0 1 : ℝ)^2 + (sevenNineRadial 6 0 1 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 2 0 1 : ℝ)^2 + (sevenNineRadial 6 0 1 : ℝ)^2 - (sevenNineDistanceLower[14]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have htouch := corner_touch_cosine_bound haL haU hbL hbU
    (by norm_num [sevenNineRadial, sevenNineRadialBounds])
    (by norm_num [sevenNineRadial, sevenNineRadialBounds]) h00 h01 h10 h11
  have hcos : (sevenNineCosUpper[56]! : ℝ) ≤ Real.cos ((228946434782751093300 : ℝ) / 100000000000000000000) := by
    apply lower_bound_of_taylor_error
      (cosine_taylor_ninety_six_remainder (a := 0) (b := 4) (x := ((228946434782751093300 : ℝ) / 100000000000000000000) )
        (by norm_num) (by constructor <;> norm_num [Real.pi_gt_d20, Real.pi_lt_four]))
    rw [cosine_taylor_ninety_six_at_zero (b := 4) (x := ((228946434782751093300 : ℝ) / 100000000000000000000)) (by norm_num)]
    have hp : (sevenNineCosUpper[56]! : Rat) + (((228946434782751093300 : Rat) / 100000000000000000000) : Rat)^97 / (Nat.factorial 96) ≤
        Finset.sum (Finset.range 49) (fun k => (-1 : Rat)^k * (((228946434782751093300 : Rat) / 100000000000000000000) : Rat)^(2*k) / Nat.factorial (2*k)) := by native_decide
    have hpR : (sevenNineCosUpper[56]! : ℝ) + ((228946434782751093300 : ℝ) / 100000000000000000000)^97 / (Nat.factorial 96) ≤
        Finset.sum (Finset.range 49) (fun k => (-1 : ℝ)^k * ((228946434782751093300 : ℝ) / 100000000000000000000)^(2*k) / Nat.factorial (2*k)) := by
      norm_num [sevenNineCosUpper, Finset.sum_range_succ]
    simpa [sub_zero] using hpR
  have hangle : ((228946434782751093300 : ℝ) / 100000000000000000000) ≤ Real.arccos (touchCosine a b (Real.sqrt 6 + Real.sqrt 10)) := by
    exact angle_lower_bound_of_cosine (by norm_num)
      (by
        calc
          ((228946434782751093300 : ℝ) / 100000000000000000000) ≤ (314159265358979323846 : ℝ) / 100000000000000000000 := by norm_num
          _ ≤ Real.pi := by
            have hpi := Real.pi_gt_d20.le
            norm_num at hpi ⊢
            exact hpi) (le_trans htouch hcos)
  have hdata : sevenNineAngleLower[56]! = ((228946434782751093300 : Rat) / 100000000000000000000) := by native_decide
  have hdataR : (sevenNineAngleLower[56]! : ℝ) = ((228946434782751093300 : ℝ) / 100000000000000000000) := by
    have h := congrArg (fun q : Rat => (q : ℝ)) hdata
    convert h using 1 ; norm_num
  rw [hdataR]
  exact hangle

theorem sevenNineAngle_2_6_0_1 {a b : ℝ}
    (haL : (sevenNineRadial 2 0 0 : ℝ) ≤ a) (haU : a ≤ (sevenNineRadial 2 0 1 : ℝ))
    (hbL : (sevenNineRadial 6 1 0 : ℝ) ≤ b) (hbU : b ≤ (sevenNineRadial 6 1 1 : ℝ)) :
    (sevenNineAngleLower[57]! : ℝ) ≤ Real.arccos (touchCosine a b (Real.sqrt 6 + Real.sqrt 10)) := by
  let d : ℝ := Real.sqrt 6 + Real.sqrt 10
  have hd' : (((5611767402951557430196177619138609925685502619981886955290197420043554816096553247884107541 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) : ℝ) ≤ d := by
    dsimp [d]
    have h := rat_sum_sqrt_lower (q := ((5611767402951557430196177619138609925685502619981886955290197420043554816096553247884107541 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (qi := ((2449489742783178098197284074705891391965947480656670128432692567250960377457315026539859433104640234818594601226614189124 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (qj := ((3162277660168379331998893544432718533719555139325216826857504852792594438639238221344248108379300295187347284152840055148 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))
      (ni := 6) (nj := 10)
      (by convert sqrt_lower_6 using 1 ; norm_num)
      (by convert sqrt_lower_10 using 1 ; norm_num)
      (by native_decide)
    convert h using 1 ; norm_num
  have hd : (((5611767402951557430196177619138609925685502619981886955290197420043554816096553247884107541 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) ≤ d := by exact hd'
  have hd2 : (((5611767402951557430196177619138609925685502619981886955290197420043554816096553247884107541 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))^2 ≤ d^2 := by
    have hq : (0 : ℝ) ≤ ((5611767402951557430196177619138609925685502619981886955290197420043554816096553247884107541 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) := by norm_num
    have hdn : 0 ≤ d := by positivity
    exact (sq_le_sq₀ hq hdn).mpr hd
  have hd2' : (sevenNineDistanceLower[14]! : ℝ)^2 ≤ d^2 := by
    convert hd2 using 1 ; norm_num [sevenNineDistanceLower]
  have h00 : (sevenNineRadial 2 0 0 : ℝ)^2 + (sevenNineRadial 6 1 0 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[57]! : ℝ) * (2 * (sevenNineRadial 2 0 0 : ℝ) * (sevenNineRadial 6 1 0 : ℝ)) := by
    have hq : (sevenNineRadial 2 0 0)^2 + (sevenNineRadial 6 1 0)^2 - sevenNineDistanceLower[14]!^2 ≤
        sevenNineCosUpper[57]! * (2 * sevenNineRadial 2 0 0 * sevenNineRadial 6 1 0) := by native_decide
    have hqR :
        (sevenNineRadial 2 0 0 : ℝ)^2 + (sevenNineRadial 6 1 0 : ℝ)^2 - (sevenNineDistanceLower[14]! : ℝ)^2 ≤
          (sevenNineCosUpper[57]! : ℝ) * (2 * (sevenNineRadial 2 0 0 : ℝ) * (sevenNineRadial 6 1 0 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 2 0 0 : ℝ)^2 + (sevenNineRadial 6 1 0 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 2 0 0 : ℝ)^2 + (sevenNineRadial 6 1 0 : ℝ)^2 - (sevenNineDistanceLower[14]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h01 : (sevenNineRadial 2 0 0 : ℝ)^2 + (sevenNineRadial 6 1 1 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[57]! : ℝ) * (2 * (sevenNineRadial 2 0 0 : ℝ) * (sevenNineRadial 6 1 1 : ℝ)) := by
    have hq : (sevenNineRadial 2 0 0)^2 + (sevenNineRadial 6 1 1)^2 - sevenNineDistanceLower[14]!^2 ≤
        sevenNineCosUpper[57]! * (2 * sevenNineRadial 2 0 0 * sevenNineRadial 6 1 1) := by native_decide
    have hqR :
        (sevenNineRadial 2 0 0 : ℝ)^2 + (sevenNineRadial 6 1 1 : ℝ)^2 - (sevenNineDistanceLower[14]! : ℝ)^2 ≤
          (sevenNineCosUpper[57]! : ℝ) * (2 * (sevenNineRadial 2 0 0 : ℝ) * (sevenNineRadial 6 1 1 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 2 0 0 : ℝ)^2 + (sevenNineRadial 6 1 1 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 2 0 0 : ℝ)^2 + (sevenNineRadial 6 1 1 : ℝ)^2 - (sevenNineDistanceLower[14]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h10 : (sevenNineRadial 2 0 1 : ℝ)^2 + (sevenNineRadial 6 1 0 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[57]! : ℝ) * (2 * (sevenNineRadial 2 0 1 : ℝ) * (sevenNineRadial 6 1 0 : ℝ)) := by
    have hq : (sevenNineRadial 2 0 1)^2 + (sevenNineRadial 6 1 0)^2 - sevenNineDistanceLower[14]!^2 ≤
        sevenNineCosUpper[57]! * (2 * sevenNineRadial 2 0 1 * sevenNineRadial 6 1 0) := by native_decide
    have hqR :
        (sevenNineRadial 2 0 1 : ℝ)^2 + (sevenNineRadial 6 1 0 : ℝ)^2 - (sevenNineDistanceLower[14]! : ℝ)^2 ≤
          (sevenNineCosUpper[57]! : ℝ) * (2 * (sevenNineRadial 2 0 1 : ℝ) * (sevenNineRadial 6 1 0 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 2 0 1 : ℝ)^2 + (sevenNineRadial 6 1 0 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 2 0 1 : ℝ)^2 + (sevenNineRadial 6 1 0 : ℝ)^2 - (sevenNineDistanceLower[14]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h11 : (sevenNineRadial 2 0 1 : ℝ)^2 + (sevenNineRadial 6 1 1 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[57]! : ℝ) * (2 * (sevenNineRadial 2 0 1 : ℝ) * (sevenNineRadial 6 1 1 : ℝ)) := by
    have hq : (sevenNineRadial 2 0 1)^2 + (sevenNineRadial 6 1 1)^2 - sevenNineDistanceLower[14]!^2 ≤
        sevenNineCosUpper[57]! * (2 * sevenNineRadial 2 0 1 * sevenNineRadial 6 1 1) := by native_decide
    have hqR :
        (sevenNineRadial 2 0 1 : ℝ)^2 + (sevenNineRadial 6 1 1 : ℝ)^2 - (sevenNineDistanceLower[14]! : ℝ)^2 ≤
          (sevenNineCosUpper[57]! : ℝ) * (2 * (sevenNineRadial 2 0 1 : ℝ) * (sevenNineRadial 6 1 1 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 2 0 1 : ℝ)^2 + (sevenNineRadial 6 1 1 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 2 0 1 : ℝ)^2 + (sevenNineRadial 6 1 1 : ℝ)^2 - (sevenNineDistanceLower[14]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have htouch := corner_touch_cosine_bound haL haU hbL hbU
    (by norm_num [sevenNineRadial, sevenNineRadialBounds])
    (by norm_num [sevenNineRadial, sevenNineRadialBounds]) h00 h01 h10 h11
  have hcos : (sevenNineCosUpper[57]! : ℝ) ≤ Real.cos ((153895006843973957533 : ℝ) / 100000000000000000000) := by
    apply lower_bound_of_taylor_error
      (cosine_taylor_ninety_six_remainder (a := 0) (b := 4) (x := ((153895006843973957533 : ℝ) / 100000000000000000000) )
        (by norm_num) (by constructor <;> norm_num [Real.pi_gt_d20, Real.pi_lt_four]))
    rw [cosine_taylor_ninety_six_at_zero (b := 4) (x := ((153895006843973957533 : ℝ) / 100000000000000000000)) (by norm_num)]
    have hp : (sevenNineCosUpper[57]! : Rat) + (((153895006843973957533 : Rat) / 100000000000000000000) : Rat)^97 / (Nat.factorial 96) ≤
        Finset.sum (Finset.range 49) (fun k => (-1 : Rat)^k * (((153895006843973957533 : Rat) / 100000000000000000000) : Rat)^(2*k) / Nat.factorial (2*k)) := by native_decide
    have hpR : (sevenNineCosUpper[57]! : ℝ) + ((153895006843973957533 : ℝ) / 100000000000000000000)^97 / (Nat.factorial 96) ≤
        Finset.sum (Finset.range 49) (fun k => (-1 : ℝ)^k * ((153895006843973957533 : ℝ) / 100000000000000000000)^(2*k) / Nat.factorial (2*k)) := by
      norm_num [sevenNineCosUpper, Finset.sum_range_succ]
    simpa [sub_zero] using hpR
  have hangle : ((153895006843973957533 : ℝ) / 100000000000000000000) ≤ Real.arccos (touchCosine a b (Real.sqrt 6 + Real.sqrt 10)) := by
    exact angle_lower_bound_of_cosine (by norm_num)
      (by
        calc
          ((153895006843973957533 : ℝ) / 100000000000000000000) ≤ (314159265358979323846 : ℝ) / 100000000000000000000 := by norm_num
          _ ≤ Real.pi := by
            have hpi := Real.pi_gt_d20.le
            norm_num at hpi ⊢
            exact hpi) (le_trans htouch hcos)
  have hdata : sevenNineAngleLower[57]! = ((153895006843973957533 : Rat) / 100000000000000000000) := by native_decide
  have hdataR : (sevenNineAngleLower[57]! : ℝ) = ((153895006843973957533 : ℝ) / 100000000000000000000) := by
    have h := congrArg (fun q : Rat => (q : ℝ)) hdata
    convert h using 1 ; norm_num
  rw [hdataR]
  exact hangle

theorem sevenNineAngle_2_6_1_0 {a b : ℝ}
    (haL : (sevenNineRadial 2 1 0 : ℝ) ≤ a) (haU : a ≤ (sevenNineRadial 2 1 1 : ℝ))
    (hbL : (sevenNineRadial 6 0 0 : ℝ) ≤ b) (hbU : b ≤ (sevenNineRadial 6 0 1 : ℝ)) :
    (sevenNineAngleLower[58]! : ℝ) ≤ Real.arccos (touchCosine a b (Real.sqrt 6 + Real.sqrt 10)) := by
  let d : ℝ := Real.sqrt 6 + Real.sqrt 10
  have hd' : (((5611767402951557430196177619138609925685502619981886955290197420043554816096553247884107541 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) : ℝ) ≤ d := by
    dsimp [d]
    have h := rat_sum_sqrt_lower (q := ((5611767402951557430196177619138609925685502619981886955290197420043554816096553247884107541 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (qi := ((2449489742783178098197284074705891391965947480656670128432692567250960377457315026539859433104640234818594601226614189124 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (qj := ((3162277660168379331998893544432718533719555139325216826857504852792594438639238221344248108379300295187347284152840055148 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))
      (ni := 6) (nj := 10)
      (by convert sqrt_lower_6 using 1 ; norm_num)
      (by convert sqrt_lower_10 using 1 ; norm_num)
      (by native_decide)
    convert h using 1 ; norm_num
  have hd : (((5611767402951557430196177619138609925685502619981886955290197420043554816096553247884107541 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) ≤ d := by exact hd'
  have hd2 : (((5611767402951557430196177619138609925685502619981886955290197420043554816096553247884107541 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))^2 ≤ d^2 := by
    have hq : (0 : ℝ) ≤ ((5611767402951557430196177619138609925685502619981886955290197420043554816096553247884107541 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) := by norm_num
    have hdn : 0 ≤ d := by positivity
    exact (sq_le_sq₀ hq hdn).mpr hd
  have hd2' : (sevenNineDistanceLower[14]! : ℝ)^2 ≤ d^2 := by
    convert hd2 using 1 ; norm_num [sevenNineDistanceLower]
  have h00 : (sevenNineRadial 2 1 0 : ℝ)^2 + (sevenNineRadial 6 0 0 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[58]! : ℝ) * (2 * (sevenNineRadial 2 1 0 : ℝ) * (sevenNineRadial 6 0 0 : ℝ)) := by
    have hq : (sevenNineRadial 2 1 0)^2 + (sevenNineRadial 6 0 0)^2 - sevenNineDistanceLower[14]!^2 ≤
        sevenNineCosUpper[58]! * (2 * sevenNineRadial 2 1 0 * sevenNineRadial 6 0 0) := by native_decide
    have hqR :
        (sevenNineRadial 2 1 0 : ℝ)^2 + (sevenNineRadial 6 0 0 : ℝ)^2 - (sevenNineDistanceLower[14]! : ℝ)^2 ≤
          (sevenNineCosUpper[58]! : ℝ) * (2 * (sevenNineRadial 2 1 0 : ℝ) * (sevenNineRadial 6 0 0 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 2 1 0 : ℝ)^2 + (sevenNineRadial 6 0 0 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 2 1 0 : ℝ)^2 + (sevenNineRadial 6 0 0 : ℝ)^2 - (sevenNineDistanceLower[14]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h01 : (sevenNineRadial 2 1 0 : ℝ)^2 + (sevenNineRadial 6 0 1 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[58]! : ℝ) * (2 * (sevenNineRadial 2 1 0 : ℝ) * (sevenNineRadial 6 0 1 : ℝ)) := by
    have hq : (sevenNineRadial 2 1 0)^2 + (sevenNineRadial 6 0 1)^2 - sevenNineDistanceLower[14]!^2 ≤
        sevenNineCosUpper[58]! * (2 * sevenNineRadial 2 1 0 * sevenNineRadial 6 0 1) := by native_decide
    have hqR :
        (sevenNineRadial 2 1 0 : ℝ)^2 + (sevenNineRadial 6 0 1 : ℝ)^2 - (sevenNineDistanceLower[14]! : ℝ)^2 ≤
          (sevenNineCosUpper[58]! : ℝ) * (2 * (sevenNineRadial 2 1 0 : ℝ) * (sevenNineRadial 6 0 1 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 2 1 0 : ℝ)^2 + (sevenNineRadial 6 0 1 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 2 1 0 : ℝ)^2 + (sevenNineRadial 6 0 1 : ℝ)^2 - (sevenNineDistanceLower[14]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h10 : (sevenNineRadial 2 1 1 : ℝ)^2 + (sevenNineRadial 6 0 0 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[58]! : ℝ) * (2 * (sevenNineRadial 2 1 1 : ℝ) * (sevenNineRadial 6 0 0 : ℝ)) := by
    have hq : (sevenNineRadial 2 1 1)^2 + (sevenNineRadial 6 0 0)^2 - sevenNineDistanceLower[14]!^2 ≤
        sevenNineCosUpper[58]! * (2 * sevenNineRadial 2 1 1 * sevenNineRadial 6 0 0) := by native_decide
    have hqR :
        (sevenNineRadial 2 1 1 : ℝ)^2 + (sevenNineRadial 6 0 0 : ℝ)^2 - (sevenNineDistanceLower[14]! : ℝ)^2 ≤
          (sevenNineCosUpper[58]! : ℝ) * (2 * (sevenNineRadial 2 1 1 : ℝ) * (sevenNineRadial 6 0 0 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 2 1 1 : ℝ)^2 + (sevenNineRadial 6 0 0 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 2 1 1 : ℝ)^2 + (sevenNineRadial 6 0 0 : ℝ)^2 - (sevenNineDistanceLower[14]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h11 : (sevenNineRadial 2 1 1 : ℝ)^2 + (sevenNineRadial 6 0 1 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[58]! : ℝ) * (2 * (sevenNineRadial 2 1 1 : ℝ) * (sevenNineRadial 6 0 1 : ℝ)) := by
    have hq : (sevenNineRadial 2 1 1)^2 + (sevenNineRadial 6 0 1)^2 - sevenNineDistanceLower[14]!^2 ≤
        sevenNineCosUpper[58]! * (2 * sevenNineRadial 2 1 1 * sevenNineRadial 6 0 1) := by native_decide
    have hqR :
        (sevenNineRadial 2 1 1 : ℝ)^2 + (sevenNineRadial 6 0 1 : ℝ)^2 - (sevenNineDistanceLower[14]! : ℝ)^2 ≤
          (sevenNineCosUpper[58]! : ℝ) * (2 * (sevenNineRadial 2 1 1 : ℝ) * (sevenNineRadial 6 0 1 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 2 1 1 : ℝ)^2 + (sevenNineRadial 6 0 1 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 2 1 1 : ℝ)^2 + (sevenNineRadial 6 0 1 : ℝ)^2 - (sevenNineDistanceLower[14]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have htouch := corner_touch_cosine_bound haL haU hbL hbU
    (by norm_num [sevenNineRadial, sevenNineRadialBounds])
    (by norm_num [sevenNineRadial, sevenNineRadialBounds]) h00 h01 h10 h11
  have hcos : (sevenNineCosUpper[58]! : ℝ) ≤ Real.cos ((134830926895590003291 : ℝ) / 100000000000000000000) := by
    apply lower_bound_of_taylor_error
      (cosine_taylor_ninety_six_remainder (a := 0) (b := 4) (x := ((134830926895590003291 : ℝ) / 100000000000000000000) )
        (by norm_num) (by constructor <;> norm_num [Real.pi_gt_d20, Real.pi_lt_four]))
    rw [cosine_taylor_ninety_six_at_zero (b := 4) (x := ((134830926895590003291 : ℝ) / 100000000000000000000)) (by norm_num)]
    have hp : (sevenNineCosUpper[58]! : Rat) + (((134830926895590003291 : Rat) / 100000000000000000000) : Rat)^97 / (Nat.factorial 96) ≤
        Finset.sum (Finset.range 49) (fun k => (-1 : Rat)^k * (((134830926895590003291 : Rat) / 100000000000000000000) : Rat)^(2*k) / Nat.factorial (2*k)) := by native_decide
    have hpR : (sevenNineCosUpper[58]! : ℝ) + ((134830926895590003291 : ℝ) / 100000000000000000000)^97 / (Nat.factorial 96) ≤
        Finset.sum (Finset.range 49) (fun k => (-1 : ℝ)^k * ((134830926895590003291 : ℝ) / 100000000000000000000)^(2*k) / Nat.factorial (2*k)) := by
      norm_num [sevenNineCosUpper, Finset.sum_range_succ]
    simpa [sub_zero] using hpR
  have hangle : ((134830926895590003291 : ℝ) / 100000000000000000000) ≤ Real.arccos (touchCosine a b (Real.sqrt 6 + Real.sqrt 10)) := by
    exact angle_lower_bound_of_cosine (by norm_num)
      (by
        calc
          ((134830926895590003291 : ℝ) / 100000000000000000000) ≤ (314159265358979323846 : ℝ) / 100000000000000000000 := by norm_num
          _ ≤ Real.pi := by
            have hpi := Real.pi_gt_d20.le
            norm_num at hpi ⊢
            exact hpi) (le_trans htouch hcos)
  have hdata : sevenNineAngleLower[58]! = ((134830926895590003291 : Rat) / 100000000000000000000) := by native_decide
  have hdataR : (sevenNineAngleLower[58]! : ℝ) = ((134830926895590003291 : ℝ) / 100000000000000000000) := by
    have h := congrArg (fun q : Rat => (q : ℝ)) hdata
    convert h using 1 ; norm_num
  rw [hdataR]
  exact hangle

theorem sevenNineAngle_2_6_1_1 {a b : ℝ}
    (haL : (sevenNineRadial 2 1 0 : ℝ) ≤ a) (haU : a ≤ (sevenNineRadial 2 1 1 : ℝ))
    (hbL : (sevenNineRadial 6 1 0 : ℝ) ≤ b) (hbU : b ≤ (sevenNineRadial 6 1 1 : ℝ)) :
    (sevenNineAngleLower[59]! : ℝ) ≤ Real.arccos (touchCosine a b (Real.sqrt 6 + Real.sqrt 10)) := by
  let d : ℝ := Real.sqrt 6 + Real.sqrt 10
  have hd' : (((5611767402951557430196177619138609925685502619981886955290197420043554816096553247884107541 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) : ℝ) ≤ d := by
    dsimp [d]
    have h := rat_sum_sqrt_lower (q := ((5611767402951557430196177619138609925685502619981886955290197420043554816096553247884107541 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (qi := ((2449489742783178098197284074705891391965947480656670128432692567250960377457315026539859433104640234818594601226614189124 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (qj := ((3162277660168379331998893544432718533719555139325216826857504852792594438639238221344248108379300295187347284152840055148 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))
      (ni := 6) (nj := 10)
      (by convert sqrt_lower_6 using 1 ; norm_num)
      (by convert sqrt_lower_10 using 1 ; norm_num)
      (by native_decide)
    convert h using 1 ; norm_num
  have hd : (((5611767402951557430196177619138609925685502619981886955290197420043554816096553247884107541 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) ≤ d := by exact hd'
  have hd2 : (((5611767402951557430196177619138609925685502619981886955290197420043554816096553247884107541 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))^2 ≤ d^2 := by
    have hq : (0 : ℝ) ≤ ((5611767402951557430196177619138609925685502619981886955290197420043554816096553247884107541 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) := by norm_num
    have hdn : 0 ≤ d := by positivity
    exact (sq_le_sq₀ hq hdn).mpr hd
  have hd2' : (sevenNineDistanceLower[14]! : ℝ)^2 ≤ d^2 := by
    convert hd2 using 1 ; norm_num [sevenNineDistanceLower]
  have h00 : (sevenNineRadial 2 1 0 : ℝ)^2 + (sevenNineRadial 6 1 0 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[59]! : ℝ) * (2 * (sevenNineRadial 2 1 0 : ℝ) * (sevenNineRadial 6 1 0 : ℝ)) := by
    have hq : (sevenNineRadial 2 1 0)^2 + (sevenNineRadial 6 1 0)^2 - sevenNineDistanceLower[14]!^2 ≤
        sevenNineCosUpper[59]! * (2 * sevenNineRadial 2 1 0 * sevenNineRadial 6 1 0) := by native_decide
    have hqR :
        (sevenNineRadial 2 1 0 : ℝ)^2 + (sevenNineRadial 6 1 0 : ℝ)^2 - (sevenNineDistanceLower[14]! : ℝ)^2 ≤
          (sevenNineCosUpper[59]! : ℝ) * (2 * (sevenNineRadial 2 1 0 : ℝ) * (sevenNineRadial 6 1 0 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 2 1 0 : ℝ)^2 + (sevenNineRadial 6 1 0 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 2 1 0 : ℝ)^2 + (sevenNineRadial 6 1 0 : ℝ)^2 - (sevenNineDistanceLower[14]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h01 : (sevenNineRadial 2 1 0 : ℝ)^2 + (sevenNineRadial 6 1 1 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[59]! : ℝ) * (2 * (sevenNineRadial 2 1 0 : ℝ) * (sevenNineRadial 6 1 1 : ℝ)) := by
    have hq : (sevenNineRadial 2 1 0)^2 + (sevenNineRadial 6 1 1)^2 - sevenNineDistanceLower[14]!^2 ≤
        sevenNineCosUpper[59]! * (2 * sevenNineRadial 2 1 0 * sevenNineRadial 6 1 1) := by native_decide
    have hqR :
        (sevenNineRadial 2 1 0 : ℝ)^2 + (sevenNineRadial 6 1 1 : ℝ)^2 - (sevenNineDistanceLower[14]! : ℝ)^2 ≤
          (sevenNineCosUpper[59]! : ℝ) * (2 * (sevenNineRadial 2 1 0 : ℝ) * (sevenNineRadial 6 1 1 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 2 1 0 : ℝ)^2 + (sevenNineRadial 6 1 1 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 2 1 0 : ℝ)^2 + (sevenNineRadial 6 1 1 : ℝ)^2 - (sevenNineDistanceLower[14]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h10 : (sevenNineRadial 2 1 1 : ℝ)^2 + (sevenNineRadial 6 1 0 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[59]! : ℝ) * (2 * (sevenNineRadial 2 1 1 : ℝ) * (sevenNineRadial 6 1 0 : ℝ)) := by
    have hq : (sevenNineRadial 2 1 1)^2 + (sevenNineRadial 6 1 0)^2 - sevenNineDistanceLower[14]!^2 ≤
        sevenNineCosUpper[59]! * (2 * sevenNineRadial 2 1 1 * sevenNineRadial 6 1 0) := by native_decide
    have hqR :
        (sevenNineRadial 2 1 1 : ℝ)^2 + (sevenNineRadial 6 1 0 : ℝ)^2 - (sevenNineDistanceLower[14]! : ℝ)^2 ≤
          (sevenNineCosUpper[59]! : ℝ) * (2 * (sevenNineRadial 2 1 1 : ℝ) * (sevenNineRadial 6 1 0 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 2 1 1 : ℝ)^2 + (sevenNineRadial 6 1 0 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 2 1 1 : ℝ)^2 + (sevenNineRadial 6 1 0 : ℝ)^2 - (sevenNineDistanceLower[14]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h11 : (sevenNineRadial 2 1 1 : ℝ)^2 + (sevenNineRadial 6 1 1 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[59]! : ℝ) * (2 * (sevenNineRadial 2 1 1 : ℝ) * (sevenNineRadial 6 1 1 : ℝ)) := by
    have hq : (sevenNineRadial 2 1 1)^2 + (sevenNineRadial 6 1 1)^2 - sevenNineDistanceLower[14]!^2 ≤
        sevenNineCosUpper[59]! * (2 * sevenNineRadial 2 1 1 * sevenNineRadial 6 1 1) := by native_decide
    have hqR :
        (sevenNineRadial 2 1 1 : ℝ)^2 + (sevenNineRadial 6 1 1 : ℝ)^2 - (sevenNineDistanceLower[14]! : ℝ)^2 ≤
          (sevenNineCosUpper[59]! : ℝ) * (2 * (sevenNineRadial 2 1 1 : ℝ) * (sevenNineRadial 6 1 1 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 2 1 1 : ℝ)^2 + (sevenNineRadial 6 1 1 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 2 1 1 : ℝ)^2 + (sevenNineRadial 6 1 1 : ℝ)^2 - (sevenNineDistanceLower[14]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have htouch := corner_touch_cosine_bound haL haU hbL hbU
    (by norm_num [sevenNineRadial, sevenNineRadialBounds])
    (by norm_num [sevenNineRadial, sevenNineRadialBounds]) h00 h01 h10 h11
  have hcos : (sevenNineCosUpper[59]! : ℝ) ≤ Real.cos ((115920050328711048703 : ℝ) / 100000000000000000000) := by
    apply lower_bound_of_taylor_error
      (cosine_taylor_ninety_six_remainder (a := 0) (b := 4) (x := ((115920050328711048703 : ℝ) / 100000000000000000000) )
        (by norm_num) (by constructor <;> norm_num [Real.pi_gt_d20, Real.pi_lt_four]))
    rw [cosine_taylor_ninety_six_at_zero (b := 4) (x := ((115920050328711048703 : ℝ) / 100000000000000000000)) (by norm_num)]
    have hp : (sevenNineCosUpper[59]! : Rat) + (((115920050328711048703 : Rat) / 100000000000000000000) : Rat)^97 / (Nat.factorial 96) ≤
        Finset.sum (Finset.range 49) (fun k => (-1 : Rat)^k * (((115920050328711048703 : Rat) / 100000000000000000000) : Rat)^(2*k) / Nat.factorial (2*k)) := by native_decide
    have hpR : (sevenNineCosUpper[59]! : ℝ) + ((115920050328711048703 : ℝ) / 100000000000000000000)^97 / (Nat.factorial 96) ≤
        Finset.sum (Finset.range 49) (fun k => (-1 : ℝ)^k * ((115920050328711048703 : ℝ) / 100000000000000000000)^(2*k) / Nat.factorial (2*k)) := by
      norm_num [sevenNineCosUpper, Finset.sum_range_succ]
    simpa [sub_zero] using hpR
  have hangle : ((115920050328711048703 : ℝ) / 100000000000000000000) ≤ Real.arccos (touchCosine a b (Real.sqrt 6 + Real.sqrt 10)) := by
    exact angle_lower_bound_of_cosine (by norm_num)
      (by
        calc
          ((115920050328711048703 : ℝ) / 100000000000000000000) ≤ (314159265358979323846 : ℝ) / 100000000000000000000 := by norm_num
          _ ≤ Real.pi := by
            have hpi := Real.pi_gt_d20.le
            norm_num at hpi ⊢
            exact hpi) (le_trans htouch hcos)
  have hdata : sevenNineAngleLower[59]! = ((115920050328711048703 : Rat) / 100000000000000000000) := by native_decide
  have hdataR : (sevenNineAngleLower[59]! : ℝ) = ((115920050328711048703 : ℝ) / 100000000000000000000) := by
    have h := congrArg (fun q : Rat => (q : ℝ)) hdata
    convert h using 1 ; norm_num
  rw [hdataR]
  exact hangle

theorem sevenNineAngle_3_4_0_0 {a b : ℝ}
    (haL : (sevenNineRadial 3 0 0 : ℝ) ≤ a) (haU : a ≤ (sevenNineRadial 3 0 1 : ℝ))
    (hbL : (sevenNineRadial 4 0 0 : ℝ) ≤ b) (hbU : b ≤ (sevenNineRadial 4 0 1 : ℝ)) :
    (sevenNineAngleLower[60]! : ℝ) ≤ Real.arccos (touchCosine a b (Real.sqrt 7 + Real.sqrt 8)) := by
  let d : ℝ := Real.sqrt 7 + Real.sqrt 8
  have hd' : (((5474178435810780688104993202058656582849602933836346326721693935182533780154497705461167955 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) : ℝ) ≤ d := by
    dsimp [d]
    have h := rat_sum_sqrt_lower (q := ((5474178435810780688104993202058656582849602933836346326721693935182533780154497705461167955 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (qi := ((2645751311064590590501615753639260425710259183082450180368334459201068823230283627760392886474543610615064578338497463095 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (qj := ((2828427124746190097603377448419396157139343750753896146353359475981464956924214077700775068655283145470027692461824594049 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))
      (ni := 7) (nj := 8)
      (by convert sqrt_lower_7 using 1 ; norm_num)
      (by convert sqrt_lower_8 using 1 ; norm_num)
      (by native_decide)
    convert h using 1 ; norm_num
  have hd : (((5474178435810780688104993202058656582849602933836346326721693935182533780154497705461167955 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) ≤ d := by exact hd'
  have hd2 : (((5474178435810780688104993202058656582849602933836346326721693935182533780154497705461167955 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))^2 ≤ d^2 := by
    have hq : (0 : ℝ) ≤ ((5474178435810780688104993202058656582849602933836346326721693935182533780154497705461167955 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) := by norm_num
    have hdn : 0 ≤ d := by positivity
    exact (sq_le_sq₀ hq hdn).mpr hd
  have hd2' : (sevenNineDistanceLower[15]! : ℝ)^2 ≤ d^2 := by
    convert hd2 using 1 ; norm_num [sevenNineDistanceLower]
  have h00 : (sevenNineRadial 3 0 0 : ℝ)^2 + (sevenNineRadial 4 0 0 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[60]! : ℝ) * (2 * (sevenNineRadial 3 0 0 : ℝ) * (sevenNineRadial 4 0 0 : ℝ)) := by
    have hq : (sevenNineRadial 3 0 0)^2 + (sevenNineRadial 4 0 0)^2 - sevenNineDistanceLower[15]!^2 ≤
        sevenNineCosUpper[60]! * (2 * sevenNineRadial 3 0 0 * sevenNineRadial 4 0 0) := by native_decide
    have hqR :
        (sevenNineRadial 3 0 0 : ℝ)^2 + (sevenNineRadial 4 0 0 : ℝ)^2 - (sevenNineDistanceLower[15]! : ℝ)^2 ≤
          (sevenNineCosUpper[60]! : ℝ) * (2 * (sevenNineRadial 3 0 0 : ℝ) * (sevenNineRadial 4 0 0 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 3 0 0 : ℝ)^2 + (sevenNineRadial 4 0 0 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 3 0 0 : ℝ)^2 + (sevenNineRadial 4 0 0 : ℝ)^2 - (sevenNineDistanceLower[15]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h01 : (sevenNineRadial 3 0 0 : ℝ)^2 + (sevenNineRadial 4 0 1 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[60]! : ℝ) * (2 * (sevenNineRadial 3 0 0 : ℝ) * (sevenNineRadial 4 0 1 : ℝ)) := by
    have hq : (sevenNineRadial 3 0 0)^2 + (sevenNineRadial 4 0 1)^2 - sevenNineDistanceLower[15]!^2 ≤
        sevenNineCosUpper[60]! * (2 * sevenNineRadial 3 0 0 * sevenNineRadial 4 0 1) := by native_decide
    have hqR :
        (sevenNineRadial 3 0 0 : ℝ)^2 + (sevenNineRadial 4 0 1 : ℝ)^2 - (sevenNineDistanceLower[15]! : ℝ)^2 ≤
          (sevenNineCosUpper[60]! : ℝ) * (2 * (sevenNineRadial 3 0 0 : ℝ) * (sevenNineRadial 4 0 1 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 3 0 0 : ℝ)^2 + (sevenNineRadial 4 0 1 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 3 0 0 : ℝ)^2 + (sevenNineRadial 4 0 1 : ℝ)^2 - (sevenNineDistanceLower[15]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h10 : (sevenNineRadial 3 0 1 : ℝ)^2 + (sevenNineRadial 4 0 0 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[60]! : ℝ) * (2 * (sevenNineRadial 3 0 1 : ℝ) * (sevenNineRadial 4 0 0 : ℝ)) := by
    have hq : (sevenNineRadial 3 0 1)^2 + (sevenNineRadial 4 0 0)^2 - sevenNineDistanceLower[15]!^2 ≤
        sevenNineCosUpper[60]! * (2 * sevenNineRadial 3 0 1 * sevenNineRadial 4 0 0) := by native_decide
    have hqR :
        (sevenNineRadial 3 0 1 : ℝ)^2 + (sevenNineRadial 4 0 0 : ℝ)^2 - (sevenNineDistanceLower[15]! : ℝ)^2 ≤
          (sevenNineCosUpper[60]! : ℝ) * (2 * (sevenNineRadial 3 0 1 : ℝ) * (sevenNineRadial 4 0 0 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 3 0 1 : ℝ)^2 + (sevenNineRadial 4 0 0 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 3 0 1 : ℝ)^2 + (sevenNineRadial 4 0 0 : ℝ)^2 - (sevenNineDistanceLower[15]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h11 : (sevenNineRadial 3 0 1 : ℝ)^2 + (sevenNineRadial 4 0 1 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[60]! : ℝ) * (2 * (sevenNineRadial 3 0 1 : ℝ) * (sevenNineRadial 4 0 1 : ℝ)) := by
    have hq : (sevenNineRadial 3 0 1)^2 + (sevenNineRadial 4 0 1)^2 - sevenNineDistanceLower[15]!^2 ≤
        sevenNineCosUpper[60]! * (2 * sevenNineRadial 3 0 1 * sevenNineRadial 4 0 1) := by native_decide
    have hqR :
        (sevenNineRadial 3 0 1 : ℝ)^2 + (sevenNineRadial 4 0 1 : ℝ)^2 - (sevenNineDistanceLower[15]! : ℝ)^2 ≤
          (sevenNineCosUpper[60]! : ℝ) * (2 * (sevenNineRadial 3 0 1 : ℝ) * (sevenNineRadial 4 0 1 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 3 0 1 : ℝ)^2 + (sevenNineRadial 4 0 1 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 3 0 1 : ℝ)^2 + (sevenNineRadial 4 0 1 : ℝ)^2 - (sevenNineDistanceLower[15]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have htouch := corner_touch_cosine_bound haL haU hbL hbU
    (by norm_num [sevenNineRadial, sevenNineRadialBounds])
    (by norm_num [sevenNineRadial, sevenNineRadialBounds]) h00 h01 h10 h11
  have hcos : (sevenNineCosUpper[60]! : ℝ) ≤ Real.cos ((209246952756694015039 : ℝ) / 100000000000000000000) := by
    apply lower_bound_of_taylor_error
      (cosine_taylor_ninety_six_remainder (a := 0) (b := 4) (x := ((209246952756694015039 : ℝ) / 100000000000000000000) )
        (by norm_num) (by constructor <;> norm_num [Real.pi_gt_d20, Real.pi_lt_four]))
    rw [cosine_taylor_ninety_six_at_zero (b := 4) (x := ((209246952756694015039 : ℝ) / 100000000000000000000)) (by norm_num)]
    have hp : (sevenNineCosUpper[60]! : Rat) + (((209246952756694015039 : Rat) / 100000000000000000000) : Rat)^97 / (Nat.factorial 96) ≤
        Finset.sum (Finset.range 49) (fun k => (-1 : Rat)^k * (((209246952756694015039 : Rat) / 100000000000000000000) : Rat)^(2*k) / Nat.factorial (2*k)) := by native_decide
    have hpR : (sevenNineCosUpper[60]! : ℝ) + ((209246952756694015039 : ℝ) / 100000000000000000000)^97 / (Nat.factorial 96) ≤
        Finset.sum (Finset.range 49) (fun k => (-1 : ℝ)^k * ((209246952756694015039 : ℝ) / 100000000000000000000)^(2*k) / Nat.factorial (2*k)) := by
      norm_num [sevenNineCosUpper, Finset.sum_range_succ]
    simpa [sub_zero] using hpR
  have hangle : ((209246952756694015039 : ℝ) / 100000000000000000000) ≤ Real.arccos (touchCosine a b (Real.sqrt 7 + Real.sqrt 8)) := by
    exact angle_lower_bound_of_cosine (by norm_num)
      (by
        calc
          ((209246952756694015039 : ℝ) / 100000000000000000000) ≤ (314159265358979323846 : ℝ) / 100000000000000000000 := by norm_num
          _ ≤ Real.pi := by
            have hpi := Real.pi_gt_d20.le
            norm_num at hpi ⊢
            exact hpi) (le_trans htouch hcos)
  have hdata : sevenNineAngleLower[60]! = ((209246952756694015039 : Rat) / 100000000000000000000) := by native_decide
  have hdataR : (sevenNineAngleLower[60]! : ℝ) = ((209246952756694015039 : ℝ) / 100000000000000000000) := by
    have h := congrArg (fun q : Rat => (q : ℝ)) hdata
    convert h using 1 ; norm_num
  rw [hdataR]
  exact hangle

theorem sevenNineAngle_3_4_0_1 {a b : ℝ}
    (haL : (sevenNineRadial 3 0 0 : ℝ) ≤ a) (haU : a ≤ (sevenNineRadial 3 0 1 : ℝ))
    (hbL : (sevenNineRadial 4 1 0 : ℝ) ≤ b) (hbU : b ≤ (sevenNineRadial 4 1 1 : ℝ)) :
    (sevenNineAngleLower[61]! : ℝ) ≤ Real.arccos (touchCosine a b (Real.sqrt 7 + Real.sqrt 8)) := by
  let d : ℝ := Real.sqrt 7 + Real.sqrt 8
  have hd' : (((5474178435810780688104993202058656582849602933836346326721693935182533780154497705461167955 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) : ℝ) ≤ d := by
    dsimp [d]
    have h := rat_sum_sqrt_lower (q := ((5474178435810780688104993202058656582849602933836346326721693935182533780154497705461167955 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (qi := ((2645751311064590590501615753639260425710259183082450180368334459201068823230283627760392886474543610615064578338497463095 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (qj := ((2828427124746190097603377448419396157139343750753896146353359475981464956924214077700775068655283145470027692461824594049 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))
      (ni := 7) (nj := 8)
      (by convert sqrt_lower_7 using 1 ; norm_num)
      (by convert sqrt_lower_8 using 1 ; norm_num)
      (by native_decide)
    convert h using 1 ; norm_num
  have hd : (((5474178435810780688104993202058656582849602933836346326721693935182533780154497705461167955 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) ≤ d := by exact hd'
  have hd2 : (((5474178435810780688104993202058656582849602933836346326721693935182533780154497705461167955 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))^2 ≤ d^2 := by
    have hq : (0 : ℝ) ≤ ((5474178435810780688104993202058656582849602933836346326721693935182533780154497705461167955 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) := by norm_num
    have hdn : 0 ≤ d := by positivity
    exact (sq_le_sq₀ hq hdn).mpr hd
  have hd2' : (sevenNineDistanceLower[15]! : ℝ)^2 ≤ d^2 := by
    convert hd2 using 1 ; norm_num [sevenNineDistanceLower]
  have h00 : (sevenNineRadial 3 0 0 : ℝ)^2 + (sevenNineRadial 4 1 0 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[61]! : ℝ) * (2 * (sevenNineRadial 3 0 0 : ℝ) * (sevenNineRadial 4 1 0 : ℝ)) := by
    have hq : (sevenNineRadial 3 0 0)^2 + (sevenNineRadial 4 1 0)^2 - sevenNineDistanceLower[15]!^2 ≤
        sevenNineCosUpper[61]! * (2 * sevenNineRadial 3 0 0 * sevenNineRadial 4 1 0) := by native_decide
    have hqR :
        (sevenNineRadial 3 0 0 : ℝ)^2 + (sevenNineRadial 4 1 0 : ℝ)^2 - (sevenNineDistanceLower[15]! : ℝ)^2 ≤
          (sevenNineCosUpper[61]! : ℝ) * (2 * (sevenNineRadial 3 0 0 : ℝ) * (sevenNineRadial 4 1 0 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 3 0 0 : ℝ)^2 + (sevenNineRadial 4 1 0 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 3 0 0 : ℝ)^2 + (sevenNineRadial 4 1 0 : ℝ)^2 - (sevenNineDistanceLower[15]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h01 : (sevenNineRadial 3 0 0 : ℝ)^2 + (sevenNineRadial 4 1 1 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[61]! : ℝ) * (2 * (sevenNineRadial 3 0 0 : ℝ) * (sevenNineRadial 4 1 1 : ℝ)) := by
    have hq : (sevenNineRadial 3 0 0)^2 + (sevenNineRadial 4 1 1)^2 - sevenNineDistanceLower[15]!^2 ≤
        sevenNineCosUpper[61]! * (2 * sevenNineRadial 3 0 0 * sevenNineRadial 4 1 1) := by native_decide
    have hqR :
        (sevenNineRadial 3 0 0 : ℝ)^2 + (sevenNineRadial 4 1 1 : ℝ)^2 - (sevenNineDistanceLower[15]! : ℝ)^2 ≤
          (sevenNineCosUpper[61]! : ℝ) * (2 * (sevenNineRadial 3 0 0 : ℝ) * (sevenNineRadial 4 1 1 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 3 0 0 : ℝ)^2 + (sevenNineRadial 4 1 1 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 3 0 0 : ℝ)^2 + (sevenNineRadial 4 1 1 : ℝ)^2 - (sevenNineDistanceLower[15]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h10 : (sevenNineRadial 3 0 1 : ℝ)^2 + (sevenNineRadial 4 1 0 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[61]! : ℝ) * (2 * (sevenNineRadial 3 0 1 : ℝ) * (sevenNineRadial 4 1 0 : ℝ)) := by
    have hq : (sevenNineRadial 3 0 1)^2 + (sevenNineRadial 4 1 0)^2 - sevenNineDistanceLower[15]!^2 ≤
        sevenNineCosUpper[61]! * (2 * sevenNineRadial 3 0 1 * sevenNineRadial 4 1 0) := by native_decide
    have hqR :
        (sevenNineRadial 3 0 1 : ℝ)^2 + (sevenNineRadial 4 1 0 : ℝ)^2 - (sevenNineDistanceLower[15]! : ℝ)^2 ≤
          (sevenNineCosUpper[61]! : ℝ) * (2 * (sevenNineRadial 3 0 1 : ℝ) * (sevenNineRadial 4 1 0 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 3 0 1 : ℝ)^2 + (sevenNineRadial 4 1 0 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 3 0 1 : ℝ)^2 + (sevenNineRadial 4 1 0 : ℝ)^2 - (sevenNineDistanceLower[15]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h11 : (sevenNineRadial 3 0 1 : ℝ)^2 + (sevenNineRadial 4 1 1 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[61]! : ℝ) * (2 * (sevenNineRadial 3 0 1 : ℝ) * (sevenNineRadial 4 1 1 : ℝ)) := by
    have hq : (sevenNineRadial 3 0 1)^2 + (sevenNineRadial 4 1 1)^2 - sevenNineDistanceLower[15]!^2 ≤
        sevenNineCosUpper[61]! * (2 * sevenNineRadial 3 0 1 * sevenNineRadial 4 1 1) := by native_decide
    have hqR :
        (sevenNineRadial 3 0 1 : ℝ)^2 + (sevenNineRadial 4 1 1 : ℝ)^2 - (sevenNineDistanceLower[15]! : ℝ)^2 ≤
          (sevenNineCosUpper[61]! : ℝ) * (2 * (sevenNineRadial 3 0 1 : ℝ) * (sevenNineRadial 4 1 1 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 3 0 1 : ℝ)^2 + (sevenNineRadial 4 1 1 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 3 0 1 : ℝ)^2 + (sevenNineRadial 4 1 1 : ℝ)^2 - (sevenNineDistanceLower[15]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have htouch := corner_touch_cosine_bound haL haU hbL hbU
    (by norm_num [sevenNineRadial, sevenNineRadialBounds])
    (by norm_num [sevenNineRadial, sevenNineRadialBounds]) h00 h01 h10 h11
  have hcos : (sevenNineCosUpper[61]! : ℝ) ≤ Real.cos ((139042337362672191327 : ℝ) / 100000000000000000000) := by
    apply lower_bound_of_taylor_error
      (cosine_taylor_ninety_six_remainder (a := 0) (b := 4) (x := ((139042337362672191327 : ℝ) / 100000000000000000000) )
        (by norm_num) (by constructor <;> norm_num [Real.pi_gt_d20, Real.pi_lt_four]))
    rw [cosine_taylor_ninety_six_at_zero (b := 4) (x := ((139042337362672191327 : ℝ) / 100000000000000000000)) (by norm_num)]
    have hp : (sevenNineCosUpper[61]! : Rat) + (((139042337362672191327 : Rat) / 100000000000000000000) : Rat)^97 / (Nat.factorial 96) ≤
        Finset.sum (Finset.range 49) (fun k => (-1 : Rat)^k * (((139042337362672191327 : Rat) / 100000000000000000000) : Rat)^(2*k) / Nat.factorial (2*k)) := by native_decide
    have hpR : (sevenNineCosUpper[61]! : ℝ) + ((139042337362672191327 : ℝ) / 100000000000000000000)^97 / (Nat.factorial 96) ≤
        Finset.sum (Finset.range 49) (fun k => (-1 : ℝ)^k * ((139042337362672191327 : ℝ) / 100000000000000000000)^(2*k) / Nat.factorial (2*k)) := by
      norm_num [sevenNineCosUpper, Finset.sum_range_succ]
    simpa [sub_zero] using hpR
  have hangle : ((139042337362672191327 : ℝ) / 100000000000000000000) ≤ Real.arccos (touchCosine a b (Real.sqrt 7 + Real.sqrt 8)) := by
    exact angle_lower_bound_of_cosine (by norm_num)
      (by
        calc
          ((139042337362672191327 : ℝ) / 100000000000000000000) ≤ (314159265358979323846 : ℝ) / 100000000000000000000 := by norm_num
          _ ≤ Real.pi := by
            have hpi := Real.pi_gt_d20.le
            norm_num at hpi ⊢
            exact hpi) (le_trans htouch hcos)
  have hdata : sevenNineAngleLower[61]! = ((139042337362672191327 : Rat) / 100000000000000000000) := by native_decide
  have hdataR : (sevenNineAngleLower[61]! : ℝ) = ((139042337362672191327 : ℝ) / 100000000000000000000) := by
    have h := congrArg (fun q : Rat => (q : ℝ)) hdata
    convert h using 1 ; norm_num
  rw [hdataR]
  exact hangle

theorem sevenNineAngle_3_4_1_0 {a b : ℝ}
    (haL : (sevenNineRadial 3 1 0 : ℝ) ≤ a) (haU : a ≤ (sevenNineRadial 3 1 1 : ℝ))
    (hbL : (sevenNineRadial 4 0 0 : ℝ) ≤ b) (hbU : b ≤ (sevenNineRadial 4 0 1 : ℝ)) :
    (sevenNineAngleLower[62]! : ℝ) ≤ Real.arccos (touchCosine a b (Real.sqrt 7 + Real.sqrt 8)) := by
  let d : ℝ := Real.sqrt 7 + Real.sqrt 8
  have hd' : (((5474178435810780688104993202058656582849602933836346326721693935182533780154497705461167955 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) : ℝ) ≤ d := by
    dsimp [d]
    have h := rat_sum_sqrt_lower (q := ((5474178435810780688104993202058656582849602933836346326721693935182533780154497705461167955 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (qi := ((2645751311064590590501615753639260425710259183082450180368334459201068823230283627760392886474543610615064578338497463095 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (qj := ((2828427124746190097603377448419396157139343750753896146353359475981464956924214077700775068655283145470027692461824594049 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))
      (ni := 7) (nj := 8)
      (by convert sqrt_lower_7 using 1 ; norm_num)
      (by convert sqrt_lower_8 using 1 ; norm_num)
      (by native_decide)
    convert h using 1 ; norm_num
  have hd : (((5474178435810780688104993202058656582849602933836346326721693935182533780154497705461167955 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) ≤ d := by exact hd'
  have hd2 : (((5474178435810780688104993202058656582849602933836346326721693935182533780154497705461167955 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))^2 ≤ d^2 := by
    have hq : (0 : ℝ) ≤ ((5474178435810780688104993202058656582849602933836346326721693935182533780154497705461167955 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) := by norm_num
    have hdn : 0 ≤ d := by positivity
    exact (sq_le_sq₀ hq hdn).mpr hd
  have hd2' : (sevenNineDistanceLower[15]! : ℝ)^2 ≤ d^2 := by
    convert hd2 using 1 ; norm_num [sevenNineDistanceLower]
  have h00 : (sevenNineRadial 3 1 0 : ℝ)^2 + (sevenNineRadial 4 0 0 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[62]! : ℝ) * (2 * (sevenNineRadial 3 1 0 : ℝ) * (sevenNineRadial 4 0 0 : ℝ)) := by
    have hq : (sevenNineRadial 3 1 0)^2 + (sevenNineRadial 4 0 0)^2 - sevenNineDistanceLower[15]!^2 ≤
        sevenNineCosUpper[62]! * (2 * sevenNineRadial 3 1 0 * sevenNineRadial 4 0 0) := by native_decide
    have hqR :
        (sevenNineRadial 3 1 0 : ℝ)^2 + (sevenNineRadial 4 0 0 : ℝ)^2 - (sevenNineDistanceLower[15]! : ℝ)^2 ≤
          (sevenNineCosUpper[62]! : ℝ) * (2 * (sevenNineRadial 3 1 0 : ℝ) * (sevenNineRadial 4 0 0 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 3 1 0 : ℝ)^2 + (sevenNineRadial 4 0 0 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 3 1 0 : ℝ)^2 + (sevenNineRadial 4 0 0 : ℝ)^2 - (sevenNineDistanceLower[15]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h01 : (sevenNineRadial 3 1 0 : ℝ)^2 + (sevenNineRadial 4 0 1 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[62]! : ℝ) * (2 * (sevenNineRadial 3 1 0 : ℝ) * (sevenNineRadial 4 0 1 : ℝ)) := by
    have hq : (sevenNineRadial 3 1 0)^2 + (sevenNineRadial 4 0 1)^2 - sevenNineDistanceLower[15]!^2 ≤
        sevenNineCosUpper[62]! * (2 * sevenNineRadial 3 1 0 * sevenNineRadial 4 0 1) := by native_decide
    have hqR :
        (sevenNineRadial 3 1 0 : ℝ)^2 + (sevenNineRadial 4 0 1 : ℝ)^2 - (sevenNineDistanceLower[15]! : ℝ)^2 ≤
          (sevenNineCosUpper[62]! : ℝ) * (2 * (sevenNineRadial 3 1 0 : ℝ) * (sevenNineRadial 4 0 1 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 3 1 0 : ℝ)^2 + (sevenNineRadial 4 0 1 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 3 1 0 : ℝ)^2 + (sevenNineRadial 4 0 1 : ℝ)^2 - (sevenNineDistanceLower[15]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h10 : (sevenNineRadial 3 1 1 : ℝ)^2 + (sevenNineRadial 4 0 0 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[62]! : ℝ) * (2 * (sevenNineRadial 3 1 1 : ℝ) * (sevenNineRadial 4 0 0 : ℝ)) := by
    have hq : (sevenNineRadial 3 1 1)^2 + (sevenNineRadial 4 0 0)^2 - sevenNineDistanceLower[15]!^2 ≤
        sevenNineCosUpper[62]! * (2 * sevenNineRadial 3 1 1 * sevenNineRadial 4 0 0) := by native_decide
    have hqR :
        (sevenNineRadial 3 1 1 : ℝ)^2 + (sevenNineRadial 4 0 0 : ℝ)^2 - (sevenNineDistanceLower[15]! : ℝ)^2 ≤
          (sevenNineCosUpper[62]! : ℝ) * (2 * (sevenNineRadial 3 1 1 : ℝ) * (sevenNineRadial 4 0 0 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 3 1 1 : ℝ)^2 + (sevenNineRadial 4 0 0 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 3 1 1 : ℝ)^2 + (sevenNineRadial 4 0 0 : ℝ)^2 - (sevenNineDistanceLower[15]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h11 : (sevenNineRadial 3 1 1 : ℝ)^2 + (sevenNineRadial 4 0 1 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[62]! : ℝ) * (2 * (sevenNineRadial 3 1 1 : ℝ) * (sevenNineRadial 4 0 1 : ℝ)) := by
    have hq : (sevenNineRadial 3 1 1)^2 + (sevenNineRadial 4 0 1)^2 - sevenNineDistanceLower[15]!^2 ≤
        sevenNineCosUpper[62]! * (2 * sevenNineRadial 3 1 1 * sevenNineRadial 4 0 1) := by native_decide
    have hqR :
        (sevenNineRadial 3 1 1 : ℝ)^2 + (sevenNineRadial 4 0 1 : ℝ)^2 - (sevenNineDistanceLower[15]! : ℝ)^2 ≤
          (sevenNineCosUpper[62]! : ℝ) * (2 * (sevenNineRadial 3 1 1 : ℝ) * (sevenNineRadial 4 0 1 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 3 1 1 : ℝ)^2 + (sevenNineRadial 4 0 1 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 3 1 1 : ℝ)^2 + (sevenNineRadial 4 0 1 : ℝ)^2 - (sevenNineDistanceLower[15]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have htouch := corner_touch_cosine_bound haL haU hbL hbU
    (by norm_num [sevenNineRadial, sevenNineRadialBounds])
    (by norm_num [sevenNineRadial, sevenNineRadialBounds]) h00 h01 h10 h11
  have hcos : (sevenNineCosUpper[62]! : ℝ) ≤ Real.cos ((133879845658986293644 : ℝ) / 100000000000000000000) := by
    apply lower_bound_of_taylor_error
      (cosine_taylor_ninety_six_remainder (a := 0) (b := 4) (x := ((133879845658986293644 : ℝ) / 100000000000000000000) )
        (by norm_num) (by constructor <;> norm_num [Real.pi_gt_d20, Real.pi_lt_four]))
    rw [cosine_taylor_ninety_six_at_zero (b := 4) (x := ((133879845658986293644 : ℝ) / 100000000000000000000)) (by norm_num)]
    have hp : (sevenNineCosUpper[62]! : Rat) + (((133879845658986293644 : Rat) / 100000000000000000000) : Rat)^97 / (Nat.factorial 96) ≤
        Finset.sum (Finset.range 49) (fun k => (-1 : Rat)^k * (((133879845658986293644 : Rat) / 100000000000000000000) : Rat)^(2*k) / Nat.factorial (2*k)) := by native_decide
    have hpR : (sevenNineCosUpper[62]! : ℝ) + ((133879845658986293644 : ℝ) / 100000000000000000000)^97 / (Nat.factorial 96) ≤
        Finset.sum (Finset.range 49) (fun k => (-1 : ℝ)^k * ((133879845658986293644 : ℝ) / 100000000000000000000)^(2*k) / Nat.factorial (2*k)) := by
      norm_num [sevenNineCosUpper, Finset.sum_range_succ]
    simpa [sub_zero] using hpR
  have hangle : ((133879845658986293644 : ℝ) / 100000000000000000000) ≤ Real.arccos (touchCosine a b (Real.sqrt 7 + Real.sqrt 8)) := by
    exact angle_lower_bound_of_cosine (by norm_num)
      (by
        calc
          ((133879845658986293644 : ℝ) / 100000000000000000000) ≤ (314159265358979323846 : ℝ) / 100000000000000000000 := by norm_num
          _ ≤ Real.pi := by
            have hpi := Real.pi_gt_d20.le
            norm_num at hpi ⊢
            exact hpi) (le_trans htouch hcos)
  have hdata : sevenNineAngleLower[62]! = ((133879845658986293644 : Rat) / 100000000000000000000) := by native_decide
  have hdataR : (sevenNineAngleLower[62]! : ℝ) = ((133879845658986293644 : ℝ) / 100000000000000000000) := by
    have h := congrArg (fun q : Rat => (q : ℝ)) hdata
    convert h using 1 ; norm_num
  rw [hdataR]
  exact hangle

theorem sevenNineAngle_3_4_1_1 {a b : ℝ}
    (haL : (sevenNineRadial 3 1 0 : ℝ) ≤ a) (haU : a ≤ (sevenNineRadial 3 1 1 : ℝ))
    (hbL : (sevenNineRadial 4 1 0 : ℝ) ≤ b) (hbU : b ≤ (sevenNineRadial 4 1 1 : ℝ)) :
    (sevenNineAngleLower[63]! : ℝ) ≤ Real.arccos (touchCosine a b (Real.sqrt 7 + Real.sqrt 8)) := by
  let d : ℝ := Real.sqrt 7 + Real.sqrt 8
  have hd' : (((5474178435810780688104993202058656582849602933836346326721693935182533780154497705461167955 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) : ℝ) ≤ d := by
    dsimp [d]
    have h := rat_sum_sqrt_lower (q := ((5474178435810780688104993202058656582849602933836346326721693935182533780154497705461167955 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (qi := ((2645751311064590590501615753639260425710259183082450180368334459201068823230283627760392886474543610615064578338497463095 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (qj := ((2828427124746190097603377448419396157139343750753896146353359475981464956924214077700775068655283145470027692461824594049 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))
      (ni := 7) (nj := 8)
      (by convert sqrt_lower_7 using 1 ; norm_num)
      (by convert sqrt_lower_8 using 1 ; norm_num)
      (by native_decide)
    convert h using 1 ; norm_num
  have hd : (((5474178435810780688104993202058656582849602933836346326721693935182533780154497705461167955 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) ≤ d := by exact hd'
  have hd2 : (((5474178435810780688104993202058656582849602933836346326721693935182533780154497705461167955 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))^2 ≤ d^2 := by
    have hq : (0 : ℝ) ≤ ((5474178435810780688104993202058656582849602933836346326721693935182533780154497705461167955 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) := by norm_num
    have hdn : 0 ≤ d := by positivity
    exact (sq_le_sq₀ hq hdn).mpr hd
  have hd2' : (sevenNineDistanceLower[15]! : ℝ)^2 ≤ d^2 := by
    convert hd2 using 1 ; norm_num [sevenNineDistanceLower]
  have h00 : (sevenNineRadial 3 1 0 : ℝ)^2 + (sevenNineRadial 4 1 0 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[63]! : ℝ) * (2 * (sevenNineRadial 3 1 0 : ℝ) * (sevenNineRadial 4 1 0 : ℝ)) := by
    have hq : (sevenNineRadial 3 1 0)^2 + (sevenNineRadial 4 1 0)^2 - sevenNineDistanceLower[15]!^2 ≤
        sevenNineCosUpper[63]! * (2 * sevenNineRadial 3 1 0 * sevenNineRadial 4 1 0) := by native_decide
    have hqR :
        (sevenNineRadial 3 1 0 : ℝ)^2 + (sevenNineRadial 4 1 0 : ℝ)^2 - (sevenNineDistanceLower[15]! : ℝ)^2 ≤
          (sevenNineCosUpper[63]! : ℝ) * (2 * (sevenNineRadial 3 1 0 : ℝ) * (sevenNineRadial 4 1 0 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 3 1 0 : ℝ)^2 + (sevenNineRadial 4 1 0 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 3 1 0 : ℝ)^2 + (sevenNineRadial 4 1 0 : ℝ)^2 - (sevenNineDistanceLower[15]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h01 : (sevenNineRadial 3 1 0 : ℝ)^2 + (sevenNineRadial 4 1 1 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[63]! : ℝ) * (2 * (sevenNineRadial 3 1 0 : ℝ) * (sevenNineRadial 4 1 1 : ℝ)) := by
    have hq : (sevenNineRadial 3 1 0)^2 + (sevenNineRadial 4 1 1)^2 - sevenNineDistanceLower[15]!^2 ≤
        sevenNineCosUpper[63]! * (2 * sevenNineRadial 3 1 0 * sevenNineRadial 4 1 1) := by native_decide
    have hqR :
        (sevenNineRadial 3 1 0 : ℝ)^2 + (sevenNineRadial 4 1 1 : ℝ)^2 - (sevenNineDistanceLower[15]! : ℝ)^2 ≤
          (sevenNineCosUpper[63]! : ℝ) * (2 * (sevenNineRadial 3 1 0 : ℝ) * (sevenNineRadial 4 1 1 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 3 1 0 : ℝ)^2 + (sevenNineRadial 4 1 1 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 3 1 0 : ℝ)^2 + (sevenNineRadial 4 1 1 : ℝ)^2 - (sevenNineDistanceLower[15]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h10 : (sevenNineRadial 3 1 1 : ℝ)^2 + (sevenNineRadial 4 1 0 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[63]! : ℝ) * (2 * (sevenNineRadial 3 1 1 : ℝ) * (sevenNineRadial 4 1 0 : ℝ)) := by
    have hq : (sevenNineRadial 3 1 1)^2 + (sevenNineRadial 4 1 0)^2 - sevenNineDistanceLower[15]!^2 ≤
        sevenNineCosUpper[63]! * (2 * sevenNineRadial 3 1 1 * sevenNineRadial 4 1 0) := by native_decide
    have hqR :
        (sevenNineRadial 3 1 1 : ℝ)^2 + (sevenNineRadial 4 1 0 : ℝ)^2 - (sevenNineDistanceLower[15]! : ℝ)^2 ≤
          (sevenNineCosUpper[63]! : ℝ) * (2 * (sevenNineRadial 3 1 1 : ℝ) * (sevenNineRadial 4 1 0 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 3 1 1 : ℝ)^2 + (sevenNineRadial 4 1 0 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 3 1 1 : ℝ)^2 + (sevenNineRadial 4 1 0 : ℝ)^2 - (sevenNineDistanceLower[15]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h11 : (sevenNineRadial 3 1 1 : ℝ)^2 + (sevenNineRadial 4 1 1 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[63]! : ℝ) * (2 * (sevenNineRadial 3 1 1 : ℝ) * (sevenNineRadial 4 1 1 : ℝ)) := by
    have hq : (sevenNineRadial 3 1 1)^2 + (sevenNineRadial 4 1 1)^2 - sevenNineDistanceLower[15]!^2 ≤
        sevenNineCosUpper[63]! * (2 * sevenNineRadial 3 1 1 * sevenNineRadial 4 1 1) := by native_decide
    have hqR :
        (sevenNineRadial 3 1 1 : ℝ)^2 + (sevenNineRadial 4 1 1 : ℝ)^2 - (sevenNineDistanceLower[15]! : ℝ)^2 ≤
          (sevenNineCosUpper[63]! : ℝ) * (2 * (sevenNineRadial 3 1 1 : ℝ) * (sevenNineRadial 4 1 1 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 3 1 1 : ℝ)^2 + (sevenNineRadial 4 1 1 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 3 1 1 : ℝ)^2 + (sevenNineRadial 4 1 1 : ℝ)^2 - (sevenNineDistanceLower[15]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have htouch := corner_touch_cosine_bound haL haU hbL hbU
    (by norm_num [sevenNineRadial, sevenNineRadialBounds])
    (by norm_num [sevenNineRadial, sevenNineRadialBounds]) h00 h01 h10 h11
  have hcos : (sevenNineCosUpper[63]! : ℝ) ≤ Real.cos ((111704137290316721995 : ℝ) / 100000000000000000000) := by
    apply lower_bound_of_taylor_error
      (cosine_taylor_ninety_six_remainder (a := 0) (b := 4) (x := ((111704137290316721995 : ℝ) / 100000000000000000000) )
        (by norm_num) (by constructor <;> norm_num [Real.pi_gt_d20, Real.pi_lt_four]))
    rw [cosine_taylor_ninety_six_at_zero (b := 4) (x := ((111704137290316721995 : ℝ) / 100000000000000000000)) (by norm_num)]
    have hp : (sevenNineCosUpper[63]! : Rat) + (((111704137290316721995 : Rat) / 100000000000000000000) : Rat)^97 / (Nat.factorial 96) ≤
        Finset.sum (Finset.range 49) (fun k => (-1 : Rat)^k * (((111704137290316721995 : Rat) / 100000000000000000000) : Rat)^(2*k) / Nat.factorial (2*k)) := by native_decide
    have hpR : (sevenNineCosUpper[63]! : ℝ) + ((111704137290316721995 : ℝ) / 100000000000000000000)^97 / (Nat.factorial 96) ≤
        Finset.sum (Finset.range 49) (fun k => (-1 : ℝ)^k * ((111704137290316721995 : ℝ) / 100000000000000000000)^(2*k) / Nat.factorial (2*k)) := by
      norm_num [sevenNineCosUpper, Finset.sum_range_succ]
    simpa [sub_zero] using hpR
  have hangle : ((111704137290316721995 : ℝ) / 100000000000000000000) ≤ Real.arccos (touchCosine a b (Real.sqrt 7 + Real.sqrt 8)) := by
    exact angle_lower_bound_of_cosine (by norm_num)
      (by
        calc
          ((111704137290316721995 : ℝ) / 100000000000000000000) ≤ (314159265358979323846 : ℝ) / 100000000000000000000 := by norm_num
          _ ≤ Real.pi := by
            have hpi := Real.pi_gt_d20.le
            norm_num at hpi ⊢
            exact hpi) (le_trans htouch hcos)
  have hdata : sevenNineAngleLower[63]! = ((111704137290316721995 : Rat) / 100000000000000000000) := by native_decide
  have hdataR : (sevenNineAngleLower[63]! : ℝ) = ((111704137290316721995 : ℝ) / 100000000000000000000) := by
    have h := congrArg (fun q : Rat => (q : ℝ)) hdata
    convert h using 1 ; norm_num
  rw [hdataR]
  exact hangle

theorem sevenNineAngle_3_5_0_0 {a b : ℝ}
    (haL : (sevenNineRadial 3 0 0 : ℝ) ≤ a) (haU : a ≤ (sevenNineRadial 3 0 1 : ℝ))
    (hbL : (sevenNineRadial 5 0 0 : ℝ) ≤ b) (hbU : b ≤ (sevenNineRadial 5 0 1 : ℝ)) :
    (sevenNineAngleLower[64]! : ℝ) ≤ Real.arccos (touchCosine a b (Real.sqrt 7 + Real.sqrt 9)) := by
  let d : ℝ := Real.sqrt 7 + Real.sqrt 9
  have hd' : (((5645751311064590590501615753639260425710259183082450180368334459201068823230283627760392886 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) : ℝ) ≤ d := by
    dsimp [d]
    have h := rat_sum_sqrt_lower (q := ((5645751311064590590501615753639260425710259183082450180368334459201068823230283627760392886 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (qi := ((2645751311064590590501615753639260425710259183082450180368334459201068823230283627760392886474543610615064578338497463095 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (qj := ((3 : Rat) / 1))
      (ni := 7) (nj := 9)
      (by convert sqrt_lower_7 using 1 ; norm_num)
      (by convert sqrt_lower_9 using 1 ; norm_num)
      (by native_decide)
    convert h using 1 ; norm_num
  have hd : (((5645751311064590590501615753639260425710259183082450180368334459201068823230283627760392886 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) ≤ d := by exact hd'
  have hd2 : (((5645751311064590590501615753639260425710259183082450180368334459201068823230283627760392886 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))^2 ≤ d^2 := by
    have hq : (0 : ℝ) ≤ ((5645751311064590590501615753639260425710259183082450180368334459201068823230283627760392886 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) := by norm_num
    have hdn : 0 ≤ d := by positivity
    exact (sq_le_sq₀ hq hdn).mpr hd
  have hd2' : (sevenNineDistanceLower[16]! : ℝ)^2 ≤ d^2 := by
    convert hd2 using 1 ; norm_num [sevenNineDistanceLower]
  have h00 : (sevenNineRadial 3 0 0 : ℝ)^2 + (sevenNineRadial 5 0 0 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[64]! : ℝ) * (2 * (sevenNineRadial 3 0 0 : ℝ) * (sevenNineRadial 5 0 0 : ℝ)) := by
    have hq : (sevenNineRadial 3 0 0)^2 + (sevenNineRadial 5 0 0)^2 - sevenNineDistanceLower[16]!^2 ≤
        sevenNineCosUpper[64]! * (2 * sevenNineRadial 3 0 0 * sevenNineRadial 5 0 0) := by native_decide
    have hqR :
        (sevenNineRadial 3 0 0 : ℝ)^2 + (sevenNineRadial 5 0 0 : ℝ)^2 - (sevenNineDistanceLower[16]! : ℝ)^2 ≤
          (sevenNineCosUpper[64]! : ℝ) * (2 * (sevenNineRadial 3 0 0 : ℝ) * (sevenNineRadial 5 0 0 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 3 0 0 : ℝ)^2 + (sevenNineRadial 5 0 0 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 3 0 0 : ℝ)^2 + (sevenNineRadial 5 0 0 : ℝ)^2 - (sevenNineDistanceLower[16]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h01 : (sevenNineRadial 3 0 0 : ℝ)^2 + (sevenNineRadial 5 0 1 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[64]! : ℝ) * (2 * (sevenNineRadial 3 0 0 : ℝ) * (sevenNineRadial 5 0 1 : ℝ)) := by
    have hq : (sevenNineRadial 3 0 0)^2 + (sevenNineRadial 5 0 1)^2 - sevenNineDistanceLower[16]!^2 ≤
        sevenNineCosUpper[64]! * (2 * sevenNineRadial 3 0 0 * sevenNineRadial 5 0 1) := by native_decide
    have hqR :
        (sevenNineRadial 3 0 0 : ℝ)^2 + (sevenNineRadial 5 0 1 : ℝ)^2 - (sevenNineDistanceLower[16]! : ℝ)^2 ≤
          (sevenNineCosUpper[64]! : ℝ) * (2 * (sevenNineRadial 3 0 0 : ℝ) * (sevenNineRadial 5 0 1 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 3 0 0 : ℝ)^2 + (sevenNineRadial 5 0 1 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 3 0 0 : ℝ)^2 + (sevenNineRadial 5 0 1 : ℝ)^2 - (sevenNineDistanceLower[16]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h10 : (sevenNineRadial 3 0 1 : ℝ)^2 + (sevenNineRadial 5 0 0 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[64]! : ℝ) * (2 * (sevenNineRadial 3 0 1 : ℝ) * (sevenNineRadial 5 0 0 : ℝ)) := by
    have hq : (sevenNineRadial 3 0 1)^2 + (sevenNineRadial 5 0 0)^2 - sevenNineDistanceLower[16]!^2 ≤
        sevenNineCosUpper[64]! * (2 * sevenNineRadial 3 0 1 * sevenNineRadial 5 0 0) := by native_decide
    have hqR :
        (sevenNineRadial 3 0 1 : ℝ)^2 + (sevenNineRadial 5 0 0 : ℝ)^2 - (sevenNineDistanceLower[16]! : ℝ)^2 ≤
          (sevenNineCosUpper[64]! : ℝ) * (2 * (sevenNineRadial 3 0 1 : ℝ) * (sevenNineRadial 5 0 0 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 3 0 1 : ℝ)^2 + (sevenNineRadial 5 0 0 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 3 0 1 : ℝ)^2 + (sevenNineRadial 5 0 0 : ℝ)^2 - (sevenNineDistanceLower[16]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h11 : (sevenNineRadial 3 0 1 : ℝ)^2 + (sevenNineRadial 5 0 1 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[64]! : ℝ) * (2 * (sevenNineRadial 3 0 1 : ℝ) * (sevenNineRadial 5 0 1 : ℝ)) := by
    have hq : (sevenNineRadial 3 0 1)^2 + (sevenNineRadial 5 0 1)^2 - sevenNineDistanceLower[16]!^2 ≤
        sevenNineCosUpper[64]! * (2 * sevenNineRadial 3 0 1 * sevenNineRadial 5 0 1) := by native_decide
    have hqR :
        (sevenNineRadial 3 0 1 : ℝ)^2 + (sevenNineRadial 5 0 1 : ℝ)^2 - (sevenNineDistanceLower[16]! : ℝ)^2 ≤
          (sevenNineCosUpper[64]! : ℝ) * (2 * (sevenNineRadial 3 0 1 : ℝ) * (sevenNineRadial 5 0 1 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 3 0 1 : ℝ)^2 + (sevenNineRadial 5 0 1 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 3 0 1 : ℝ)^2 + (sevenNineRadial 5 0 1 : ℝ)^2 - (sevenNineDistanceLower[16]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have htouch := corner_touch_cosine_bound haL haU hbL hbU
    (by norm_num [sevenNineRadial, sevenNineRadialBounds])
    (by norm_num [sevenNineRadial, sevenNineRadialBounds]) h00 h01 h10 h11
  have hcos : (sevenNineCosUpper[64]! : ℝ) ≤ Real.cos ((220647703192400634600 : ℝ) / 100000000000000000000) := by
    apply lower_bound_of_taylor_error
      (cosine_taylor_ninety_six_remainder (a := 0) (b := 4) (x := ((220647703192400634600 : ℝ) / 100000000000000000000) )
        (by norm_num) (by constructor <;> norm_num [Real.pi_gt_d20, Real.pi_lt_four]))
    rw [cosine_taylor_ninety_six_at_zero (b := 4) (x := ((220647703192400634600 : ℝ) / 100000000000000000000)) (by norm_num)]
    have hp : (sevenNineCosUpper[64]! : Rat) + (((220647703192400634600 : Rat) / 100000000000000000000) : Rat)^97 / (Nat.factorial 96) ≤
        Finset.sum (Finset.range 49) (fun k => (-1 : Rat)^k * (((220647703192400634600 : Rat) / 100000000000000000000) : Rat)^(2*k) / Nat.factorial (2*k)) := by native_decide
    have hpR : (sevenNineCosUpper[64]! : ℝ) + ((220647703192400634600 : ℝ) / 100000000000000000000)^97 / (Nat.factorial 96) ≤
        Finset.sum (Finset.range 49) (fun k => (-1 : ℝ)^k * ((220647703192400634600 : ℝ) / 100000000000000000000)^(2*k) / Nat.factorial (2*k)) := by
      norm_num [sevenNineCosUpper, Finset.sum_range_succ]
    simpa [sub_zero] using hpR
  have hangle : ((220647703192400634600 : ℝ) / 100000000000000000000) ≤ Real.arccos (touchCosine a b (Real.sqrt 7 + Real.sqrt 9)) := by
    exact angle_lower_bound_of_cosine (by norm_num)
      (by
        calc
          ((220647703192400634600 : ℝ) / 100000000000000000000) ≤ (314159265358979323846 : ℝ) / 100000000000000000000 := by norm_num
          _ ≤ Real.pi := by
            have hpi := Real.pi_gt_d20.le
            norm_num at hpi ⊢
            exact hpi) (le_trans htouch hcos)
  have hdata : sevenNineAngleLower[64]! = ((220647703192400634600 : Rat) / 100000000000000000000) := by native_decide
  have hdataR : (sevenNineAngleLower[64]! : ℝ) = ((220647703192400634600 : ℝ) / 100000000000000000000) := by
    have h := congrArg (fun q : Rat => (q : ℝ)) hdata
    convert h using 1 ; norm_num
  rw [hdataR]
  exact hangle

theorem sevenNineAngle_3_5_0_1 {a b : ℝ}
    (haL : (sevenNineRadial 3 0 0 : ℝ) ≤ a) (haU : a ≤ (sevenNineRadial 3 0 1 : ℝ))
    (hbL : (sevenNineRadial 5 1 0 : ℝ) ≤ b) (hbU : b ≤ (sevenNineRadial 5 1 1 : ℝ)) :
    (sevenNineAngleLower[65]! : ℝ) ≤ Real.arccos (touchCosine a b (Real.sqrt 7 + Real.sqrt 9)) := by
  let d : ℝ := Real.sqrt 7 + Real.sqrt 9
  have hd' : (((5645751311064590590501615753639260425710259183082450180368334459201068823230283627760392886 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) : ℝ) ≤ d := by
    dsimp [d]
    have h := rat_sum_sqrt_lower (q := ((5645751311064590590501615753639260425710259183082450180368334459201068823230283627760392886 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (qi := ((2645751311064590590501615753639260425710259183082450180368334459201068823230283627760392886474543610615064578338497463095 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (qj := ((3 : Rat) / 1))
      (ni := 7) (nj := 9)
      (by convert sqrt_lower_7 using 1 ; norm_num)
      (by convert sqrt_lower_9 using 1 ; norm_num)
      (by native_decide)
    convert h using 1 ; norm_num
  have hd : (((5645751311064590590501615753639260425710259183082450180368334459201068823230283627760392886 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) ≤ d := by exact hd'
  have hd2 : (((5645751311064590590501615753639260425710259183082450180368334459201068823230283627760392886 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))^2 ≤ d^2 := by
    have hq : (0 : ℝ) ≤ ((5645751311064590590501615753639260425710259183082450180368334459201068823230283627760392886 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) := by norm_num
    have hdn : 0 ≤ d := by positivity
    exact (sq_le_sq₀ hq hdn).mpr hd
  have hd2' : (sevenNineDistanceLower[16]! : ℝ)^2 ≤ d^2 := by
    convert hd2 using 1 ; norm_num [sevenNineDistanceLower]
  have h00 : (sevenNineRadial 3 0 0 : ℝ)^2 + (sevenNineRadial 5 1 0 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[65]! : ℝ) * (2 * (sevenNineRadial 3 0 0 : ℝ) * (sevenNineRadial 5 1 0 : ℝ)) := by
    have hq : (sevenNineRadial 3 0 0)^2 + (sevenNineRadial 5 1 0)^2 - sevenNineDistanceLower[16]!^2 ≤
        sevenNineCosUpper[65]! * (2 * sevenNineRadial 3 0 0 * sevenNineRadial 5 1 0) := by native_decide
    have hqR :
        (sevenNineRadial 3 0 0 : ℝ)^2 + (sevenNineRadial 5 1 0 : ℝ)^2 - (sevenNineDistanceLower[16]! : ℝ)^2 ≤
          (sevenNineCosUpper[65]! : ℝ) * (2 * (sevenNineRadial 3 0 0 : ℝ) * (sevenNineRadial 5 1 0 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 3 0 0 : ℝ)^2 + (sevenNineRadial 5 1 0 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 3 0 0 : ℝ)^2 + (sevenNineRadial 5 1 0 : ℝ)^2 - (sevenNineDistanceLower[16]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h01 : (sevenNineRadial 3 0 0 : ℝ)^2 + (sevenNineRadial 5 1 1 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[65]! : ℝ) * (2 * (sevenNineRadial 3 0 0 : ℝ) * (sevenNineRadial 5 1 1 : ℝ)) := by
    have hq : (sevenNineRadial 3 0 0)^2 + (sevenNineRadial 5 1 1)^2 - sevenNineDistanceLower[16]!^2 ≤
        sevenNineCosUpper[65]! * (2 * sevenNineRadial 3 0 0 * sevenNineRadial 5 1 1) := by native_decide
    have hqR :
        (sevenNineRadial 3 0 0 : ℝ)^2 + (sevenNineRadial 5 1 1 : ℝ)^2 - (sevenNineDistanceLower[16]! : ℝ)^2 ≤
          (sevenNineCosUpper[65]! : ℝ) * (2 * (sevenNineRadial 3 0 0 : ℝ) * (sevenNineRadial 5 1 1 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 3 0 0 : ℝ)^2 + (sevenNineRadial 5 1 1 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 3 0 0 : ℝ)^2 + (sevenNineRadial 5 1 1 : ℝ)^2 - (sevenNineDistanceLower[16]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h10 : (sevenNineRadial 3 0 1 : ℝ)^2 + (sevenNineRadial 5 1 0 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[65]! : ℝ) * (2 * (sevenNineRadial 3 0 1 : ℝ) * (sevenNineRadial 5 1 0 : ℝ)) := by
    have hq : (sevenNineRadial 3 0 1)^2 + (sevenNineRadial 5 1 0)^2 - sevenNineDistanceLower[16]!^2 ≤
        sevenNineCosUpper[65]! * (2 * sevenNineRadial 3 0 1 * sevenNineRadial 5 1 0) := by native_decide
    have hqR :
        (sevenNineRadial 3 0 1 : ℝ)^2 + (sevenNineRadial 5 1 0 : ℝ)^2 - (sevenNineDistanceLower[16]! : ℝ)^2 ≤
          (sevenNineCosUpper[65]! : ℝ) * (2 * (sevenNineRadial 3 0 1 : ℝ) * (sevenNineRadial 5 1 0 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 3 0 1 : ℝ)^2 + (sevenNineRadial 5 1 0 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 3 0 1 : ℝ)^2 + (sevenNineRadial 5 1 0 : ℝ)^2 - (sevenNineDistanceLower[16]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h11 : (sevenNineRadial 3 0 1 : ℝ)^2 + (sevenNineRadial 5 1 1 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[65]! : ℝ) * (2 * (sevenNineRadial 3 0 1 : ℝ) * (sevenNineRadial 5 1 1 : ℝ)) := by
    have hq : (sevenNineRadial 3 0 1)^2 + (sevenNineRadial 5 1 1)^2 - sevenNineDistanceLower[16]!^2 ≤
        sevenNineCosUpper[65]! * (2 * sevenNineRadial 3 0 1 * sevenNineRadial 5 1 1) := by native_decide
    have hqR :
        (sevenNineRadial 3 0 1 : ℝ)^2 + (sevenNineRadial 5 1 1 : ℝ)^2 - (sevenNineDistanceLower[16]! : ℝ)^2 ≤
          (sevenNineCosUpper[65]! : ℝ) * (2 * (sevenNineRadial 3 0 1 : ℝ) * (sevenNineRadial 5 1 1 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 3 0 1 : ℝ)^2 + (sevenNineRadial 5 1 1 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 3 0 1 : ℝ)^2 + (sevenNineRadial 5 1 1 : ℝ)^2 - (sevenNineDistanceLower[16]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have htouch := corner_touch_cosine_bound haL haU hbL hbU
    (by norm_num [sevenNineRadial, sevenNineRadialBounds])
    (by norm_num [sevenNineRadial, sevenNineRadialBounds]) h00 h01 h10 h11
  have hcos : (sevenNineCosUpper[65]! : ℝ) ≤ Real.cos ((150183331847107346011 : ℝ) / 100000000000000000000) := by
    apply lower_bound_of_taylor_error
      (cosine_taylor_ninety_six_remainder (a := 0) (b := 4) (x := ((150183331847107346011 : ℝ) / 100000000000000000000) )
        (by norm_num) (by constructor <;> norm_num [Real.pi_gt_d20, Real.pi_lt_four]))
    rw [cosine_taylor_ninety_six_at_zero (b := 4) (x := ((150183331847107346011 : ℝ) / 100000000000000000000)) (by norm_num)]
    have hp : (sevenNineCosUpper[65]! : Rat) + (((150183331847107346011 : Rat) / 100000000000000000000) : Rat)^97 / (Nat.factorial 96) ≤
        Finset.sum (Finset.range 49) (fun k => (-1 : Rat)^k * (((150183331847107346011 : Rat) / 100000000000000000000) : Rat)^(2*k) / Nat.factorial (2*k)) := by native_decide
    have hpR : (sevenNineCosUpper[65]! : ℝ) + ((150183331847107346011 : ℝ) / 100000000000000000000)^97 / (Nat.factorial 96) ≤
        Finset.sum (Finset.range 49) (fun k => (-1 : ℝ)^k * ((150183331847107346011 : ℝ) / 100000000000000000000)^(2*k) / Nat.factorial (2*k)) := by
      norm_num [sevenNineCosUpper, Finset.sum_range_succ]
    simpa [sub_zero] using hpR
  have hangle : ((150183331847107346011 : ℝ) / 100000000000000000000) ≤ Real.arccos (touchCosine a b (Real.sqrt 7 + Real.sqrt 9)) := by
    exact angle_lower_bound_of_cosine (by norm_num)
      (by
        calc
          ((150183331847107346011 : ℝ) / 100000000000000000000) ≤ (314159265358979323846 : ℝ) / 100000000000000000000 := by norm_num
          _ ≤ Real.pi := by
            have hpi := Real.pi_gt_d20.le
            norm_num at hpi ⊢
            exact hpi) (le_trans htouch hcos)
  have hdata : sevenNineAngleLower[65]! = ((150183331847107346011 : Rat) / 100000000000000000000) := by native_decide
  have hdataR : (sevenNineAngleLower[65]! : ℝ) = ((150183331847107346011 : ℝ) / 100000000000000000000) := by
    have h := congrArg (fun q : Rat => (q : ℝ)) hdata
    convert h using 1 ; norm_num
  rw [hdataR]
  exact hangle

theorem sevenNineAngle_3_5_1_0 {a b : ℝ}
    (haL : (sevenNineRadial 3 1 0 : ℝ) ≤ a) (haU : a ≤ (sevenNineRadial 3 1 1 : ℝ))
    (hbL : (sevenNineRadial 5 0 0 : ℝ) ≤ b) (hbU : b ≤ (sevenNineRadial 5 0 1 : ℝ)) :
    (sevenNineAngleLower[66]! : ℝ) ≤ Real.arccos (touchCosine a b (Real.sqrt 7 + Real.sqrt 9)) := by
  let d : ℝ := Real.sqrt 7 + Real.sqrt 9
  have hd' : (((5645751311064590590501615753639260425710259183082450180368334459201068823230283627760392886 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) : ℝ) ≤ d := by
    dsimp [d]
    have h := rat_sum_sqrt_lower (q := ((5645751311064590590501615753639260425710259183082450180368334459201068823230283627760392886 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (qi := ((2645751311064590590501615753639260425710259183082450180368334459201068823230283627760392886474543610615064578338497463095 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (qj := ((3 : Rat) / 1))
      (ni := 7) (nj := 9)
      (by convert sqrt_lower_7 using 1 ; norm_num)
      (by convert sqrt_lower_9 using 1 ; norm_num)
      (by native_decide)
    convert h using 1 ; norm_num
  have hd : (((5645751311064590590501615753639260425710259183082450180368334459201068823230283627760392886 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) ≤ d := by exact hd'
  have hd2 : (((5645751311064590590501615753639260425710259183082450180368334459201068823230283627760392886 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))^2 ≤ d^2 := by
    have hq : (0 : ℝ) ≤ ((5645751311064590590501615753639260425710259183082450180368334459201068823230283627760392886 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) := by norm_num
    have hdn : 0 ≤ d := by positivity
    exact (sq_le_sq₀ hq hdn).mpr hd
  have hd2' : (sevenNineDistanceLower[16]! : ℝ)^2 ≤ d^2 := by
    convert hd2 using 1 ; norm_num [sevenNineDistanceLower]
  have h00 : (sevenNineRadial 3 1 0 : ℝ)^2 + (sevenNineRadial 5 0 0 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[66]! : ℝ) * (2 * (sevenNineRadial 3 1 0 : ℝ) * (sevenNineRadial 5 0 0 : ℝ)) := by
    have hq : (sevenNineRadial 3 1 0)^2 + (sevenNineRadial 5 0 0)^2 - sevenNineDistanceLower[16]!^2 ≤
        sevenNineCosUpper[66]! * (2 * sevenNineRadial 3 1 0 * sevenNineRadial 5 0 0) := by native_decide
    have hqR :
        (sevenNineRadial 3 1 0 : ℝ)^2 + (sevenNineRadial 5 0 0 : ℝ)^2 - (sevenNineDistanceLower[16]! : ℝ)^2 ≤
          (sevenNineCosUpper[66]! : ℝ) * (2 * (sevenNineRadial 3 1 0 : ℝ) * (sevenNineRadial 5 0 0 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 3 1 0 : ℝ)^2 + (sevenNineRadial 5 0 0 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 3 1 0 : ℝ)^2 + (sevenNineRadial 5 0 0 : ℝ)^2 - (sevenNineDistanceLower[16]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h01 : (sevenNineRadial 3 1 0 : ℝ)^2 + (sevenNineRadial 5 0 1 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[66]! : ℝ) * (2 * (sevenNineRadial 3 1 0 : ℝ) * (sevenNineRadial 5 0 1 : ℝ)) := by
    have hq : (sevenNineRadial 3 1 0)^2 + (sevenNineRadial 5 0 1)^2 - sevenNineDistanceLower[16]!^2 ≤
        sevenNineCosUpper[66]! * (2 * sevenNineRadial 3 1 0 * sevenNineRadial 5 0 1) := by native_decide
    have hqR :
        (sevenNineRadial 3 1 0 : ℝ)^2 + (sevenNineRadial 5 0 1 : ℝ)^2 - (sevenNineDistanceLower[16]! : ℝ)^2 ≤
          (sevenNineCosUpper[66]! : ℝ) * (2 * (sevenNineRadial 3 1 0 : ℝ) * (sevenNineRadial 5 0 1 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 3 1 0 : ℝ)^2 + (sevenNineRadial 5 0 1 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 3 1 0 : ℝ)^2 + (sevenNineRadial 5 0 1 : ℝ)^2 - (sevenNineDistanceLower[16]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h10 : (sevenNineRadial 3 1 1 : ℝ)^2 + (sevenNineRadial 5 0 0 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[66]! : ℝ) * (2 * (sevenNineRadial 3 1 1 : ℝ) * (sevenNineRadial 5 0 0 : ℝ)) := by
    have hq : (sevenNineRadial 3 1 1)^2 + (sevenNineRadial 5 0 0)^2 - sevenNineDistanceLower[16]!^2 ≤
        sevenNineCosUpper[66]! * (2 * sevenNineRadial 3 1 1 * sevenNineRadial 5 0 0) := by native_decide
    have hqR :
        (sevenNineRadial 3 1 1 : ℝ)^2 + (sevenNineRadial 5 0 0 : ℝ)^2 - (sevenNineDistanceLower[16]! : ℝ)^2 ≤
          (sevenNineCosUpper[66]! : ℝ) * (2 * (sevenNineRadial 3 1 1 : ℝ) * (sevenNineRadial 5 0 0 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 3 1 1 : ℝ)^2 + (sevenNineRadial 5 0 0 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 3 1 1 : ℝ)^2 + (sevenNineRadial 5 0 0 : ℝ)^2 - (sevenNineDistanceLower[16]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h11 : (sevenNineRadial 3 1 1 : ℝ)^2 + (sevenNineRadial 5 0 1 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[66]! : ℝ) * (2 * (sevenNineRadial 3 1 1 : ℝ) * (sevenNineRadial 5 0 1 : ℝ)) := by
    have hq : (sevenNineRadial 3 1 1)^2 + (sevenNineRadial 5 0 1)^2 - sevenNineDistanceLower[16]!^2 ≤
        sevenNineCosUpper[66]! * (2 * sevenNineRadial 3 1 1 * sevenNineRadial 5 0 1) := by native_decide
    have hqR :
        (sevenNineRadial 3 1 1 : ℝ)^2 + (sevenNineRadial 5 0 1 : ℝ)^2 - (sevenNineDistanceLower[16]! : ℝ)^2 ≤
          (sevenNineCosUpper[66]! : ℝ) * (2 * (sevenNineRadial 3 1 1 : ℝ) * (sevenNineRadial 5 0 1 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 3 1 1 : ℝ)^2 + (sevenNineRadial 5 0 1 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 3 1 1 : ℝ)^2 + (sevenNineRadial 5 0 1 : ℝ)^2 - (sevenNineDistanceLower[16]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have htouch := corner_touch_cosine_bound haL haU hbL hbU
    (by norm_num [sevenNineRadial, sevenNineRadialBounds])
    (by norm_num [sevenNineRadial, sevenNineRadialBounds]) h00 h01 h10 h11
  have hcos : (sevenNineCosUpper[66]! : ℝ) ≤ Real.cos ((139741967868709437129 : ℝ) / 100000000000000000000) := by
    apply lower_bound_of_taylor_error
      (cosine_taylor_ninety_six_remainder (a := 0) (b := 4) (x := ((139741967868709437129 : ℝ) / 100000000000000000000) )
        (by norm_num) (by constructor <;> norm_num [Real.pi_gt_d20, Real.pi_lt_four]))
    rw [cosine_taylor_ninety_six_at_zero (b := 4) (x := ((139741967868709437129 : ℝ) / 100000000000000000000)) (by norm_num)]
    have hp : (sevenNineCosUpper[66]! : Rat) + (((139741967868709437129 : Rat) / 100000000000000000000) : Rat)^97 / (Nat.factorial 96) ≤
        Finset.sum (Finset.range 49) (fun k => (-1 : Rat)^k * (((139741967868709437129 : Rat) / 100000000000000000000) : Rat)^(2*k) / Nat.factorial (2*k)) := by native_decide
    have hpR : (sevenNineCosUpper[66]! : ℝ) + ((139741967868709437129 : ℝ) / 100000000000000000000)^97 / (Nat.factorial 96) ≤
        Finset.sum (Finset.range 49) (fun k => (-1 : ℝ)^k * ((139741967868709437129 : ℝ) / 100000000000000000000)^(2*k) / Nat.factorial (2*k)) := by
      norm_num [sevenNineCosUpper, Finset.sum_range_succ]
    simpa [sub_zero] using hpR
  have hangle : ((139741967868709437129 : ℝ) / 100000000000000000000) ≤ Real.arccos (touchCosine a b (Real.sqrt 7 + Real.sqrt 9)) := by
    exact angle_lower_bound_of_cosine (by norm_num)
      (by
        calc
          ((139741967868709437129 : ℝ) / 100000000000000000000) ≤ (314159265358979323846 : ℝ) / 100000000000000000000 := by norm_num
          _ ≤ Real.pi := by
            have hpi := Real.pi_gt_d20.le
            norm_num at hpi ⊢
            exact hpi) (le_trans htouch hcos)
  have hdata : sevenNineAngleLower[66]! = ((139741967868709437129 : Rat) / 100000000000000000000) := by native_decide
  have hdataR : (sevenNineAngleLower[66]! : ℝ) = ((139741967868709437129 : ℝ) / 100000000000000000000) := by
    have h := congrArg (fun q : Rat => (q : ℝ)) hdata
    convert h using 1 ; norm_num
  rw [hdataR]
  exact hangle

theorem sevenNineAngle_3_5_1_1 {a b : ℝ}
    (haL : (sevenNineRadial 3 1 0 : ℝ) ≤ a) (haU : a ≤ (sevenNineRadial 3 1 1 : ℝ))
    (hbL : (sevenNineRadial 5 1 0 : ℝ) ≤ b) (hbU : b ≤ (sevenNineRadial 5 1 1 : ℝ)) :
    (sevenNineAngleLower[67]! : ℝ) ≤ Real.arccos (touchCosine a b (Real.sqrt 7 + Real.sqrt 9)) := by
  let d : ℝ := Real.sqrt 7 + Real.sqrt 9
  have hd' : (((5645751311064590590501615753639260425710259183082450180368334459201068823230283627760392886 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) : ℝ) ≤ d := by
    dsimp [d]
    have h := rat_sum_sqrt_lower (q := ((5645751311064590590501615753639260425710259183082450180368334459201068823230283627760392886 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (qi := ((2645751311064590590501615753639260425710259183082450180368334459201068823230283627760392886474543610615064578338497463095 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (qj := ((3 : Rat) / 1))
      (ni := 7) (nj := 9)
      (by convert sqrt_lower_7 using 1 ; norm_num)
      (by convert sqrt_lower_9 using 1 ; norm_num)
      (by native_decide)
    convert h using 1 ; norm_num
  have hd : (((5645751311064590590501615753639260425710259183082450180368334459201068823230283627760392886 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) ≤ d := by exact hd'
  have hd2 : (((5645751311064590590501615753639260425710259183082450180368334459201068823230283627760392886 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))^2 ≤ d^2 := by
    have hq : (0 : ℝ) ≤ ((5645751311064590590501615753639260425710259183082450180368334459201068823230283627760392886 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) := by norm_num
    have hdn : 0 ≤ d := by positivity
    exact (sq_le_sq₀ hq hdn).mpr hd
  have hd2' : (sevenNineDistanceLower[16]! : ℝ)^2 ≤ d^2 := by
    convert hd2 using 1 ; norm_num [sevenNineDistanceLower]
  have h00 : (sevenNineRadial 3 1 0 : ℝ)^2 + (sevenNineRadial 5 1 0 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[67]! : ℝ) * (2 * (sevenNineRadial 3 1 0 : ℝ) * (sevenNineRadial 5 1 0 : ℝ)) := by
    have hq : (sevenNineRadial 3 1 0)^2 + (sevenNineRadial 5 1 0)^2 - sevenNineDistanceLower[16]!^2 ≤
        sevenNineCosUpper[67]! * (2 * sevenNineRadial 3 1 0 * sevenNineRadial 5 1 0) := by native_decide
    have hqR :
        (sevenNineRadial 3 1 0 : ℝ)^2 + (sevenNineRadial 5 1 0 : ℝ)^2 - (sevenNineDistanceLower[16]! : ℝ)^2 ≤
          (sevenNineCosUpper[67]! : ℝ) * (2 * (sevenNineRadial 3 1 0 : ℝ) * (sevenNineRadial 5 1 0 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 3 1 0 : ℝ)^2 + (sevenNineRadial 5 1 0 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 3 1 0 : ℝ)^2 + (sevenNineRadial 5 1 0 : ℝ)^2 - (sevenNineDistanceLower[16]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h01 : (sevenNineRadial 3 1 0 : ℝ)^2 + (sevenNineRadial 5 1 1 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[67]! : ℝ) * (2 * (sevenNineRadial 3 1 0 : ℝ) * (sevenNineRadial 5 1 1 : ℝ)) := by
    have hq : (sevenNineRadial 3 1 0)^2 + (sevenNineRadial 5 1 1)^2 - sevenNineDistanceLower[16]!^2 ≤
        sevenNineCosUpper[67]! * (2 * sevenNineRadial 3 1 0 * sevenNineRadial 5 1 1) := by native_decide
    have hqR :
        (sevenNineRadial 3 1 0 : ℝ)^2 + (sevenNineRadial 5 1 1 : ℝ)^2 - (sevenNineDistanceLower[16]! : ℝ)^2 ≤
          (sevenNineCosUpper[67]! : ℝ) * (2 * (sevenNineRadial 3 1 0 : ℝ) * (sevenNineRadial 5 1 1 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 3 1 0 : ℝ)^2 + (sevenNineRadial 5 1 1 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 3 1 0 : ℝ)^2 + (sevenNineRadial 5 1 1 : ℝ)^2 - (sevenNineDistanceLower[16]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h10 : (sevenNineRadial 3 1 1 : ℝ)^2 + (sevenNineRadial 5 1 0 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[67]! : ℝ) * (2 * (sevenNineRadial 3 1 1 : ℝ) * (sevenNineRadial 5 1 0 : ℝ)) := by
    have hq : (sevenNineRadial 3 1 1)^2 + (sevenNineRadial 5 1 0)^2 - sevenNineDistanceLower[16]!^2 ≤
        sevenNineCosUpper[67]! * (2 * sevenNineRadial 3 1 1 * sevenNineRadial 5 1 0) := by native_decide
    have hqR :
        (sevenNineRadial 3 1 1 : ℝ)^2 + (sevenNineRadial 5 1 0 : ℝ)^2 - (sevenNineDistanceLower[16]! : ℝ)^2 ≤
          (sevenNineCosUpper[67]! : ℝ) * (2 * (sevenNineRadial 3 1 1 : ℝ) * (sevenNineRadial 5 1 0 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 3 1 1 : ℝ)^2 + (sevenNineRadial 5 1 0 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 3 1 1 : ℝ)^2 + (sevenNineRadial 5 1 0 : ℝ)^2 - (sevenNineDistanceLower[16]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h11 : (sevenNineRadial 3 1 1 : ℝ)^2 + (sevenNineRadial 5 1 1 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[67]! : ℝ) * (2 * (sevenNineRadial 3 1 1 : ℝ) * (sevenNineRadial 5 1 1 : ℝ)) := by
    have hq : (sevenNineRadial 3 1 1)^2 + (sevenNineRadial 5 1 1)^2 - sevenNineDistanceLower[16]!^2 ≤
        sevenNineCosUpper[67]! * (2 * sevenNineRadial 3 1 1 * sevenNineRadial 5 1 1) := by native_decide
    have hqR :
        (sevenNineRadial 3 1 1 : ℝ)^2 + (sevenNineRadial 5 1 1 : ℝ)^2 - (sevenNineDistanceLower[16]! : ℝ)^2 ≤
          (sevenNineCosUpper[67]! : ℝ) * (2 * (sevenNineRadial 3 1 1 : ℝ) * (sevenNineRadial 5 1 1 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 3 1 1 : ℝ)^2 + (sevenNineRadial 5 1 1 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 3 1 1 : ℝ)^2 + (sevenNineRadial 5 1 1 : ℝ)^2 - (sevenNineDistanceLower[16]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have htouch := corner_touch_cosine_bound haL haU hbL hbU
    (by norm_num [sevenNineRadial, sevenNineRadialBounds])
    (by norm_num [sevenNineRadial, sevenNineRadialBounds]) h00 h01 h10 h11
  have hcos : (sevenNineCosUpper[67]! : ℝ) ≤ Real.cos ((117730621067653899677 : ℝ) / 100000000000000000000) := by
    apply lower_bound_of_taylor_error
      (cosine_taylor_ninety_six_remainder (a := 0) (b := 4) (x := ((117730621067653899677 : ℝ) / 100000000000000000000) )
        (by norm_num) (by constructor <;> norm_num [Real.pi_gt_d20, Real.pi_lt_four]))
    rw [cosine_taylor_ninety_six_at_zero (b := 4) (x := ((117730621067653899677 : ℝ) / 100000000000000000000)) (by norm_num)]
    have hp : (sevenNineCosUpper[67]! : Rat) + (((117730621067653899677 : Rat) / 100000000000000000000) : Rat)^97 / (Nat.factorial 96) ≤
        Finset.sum (Finset.range 49) (fun k => (-1 : Rat)^k * (((117730621067653899677 : Rat) / 100000000000000000000) : Rat)^(2*k) / Nat.factorial (2*k)) := by native_decide
    have hpR : (sevenNineCosUpper[67]! : ℝ) + ((117730621067653899677 : ℝ) / 100000000000000000000)^97 / (Nat.factorial 96) ≤
        Finset.sum (Finset.range 49) (fun k => (-1 : ℝ)^k * ((117730621067653899677 : ℝ) / 100000000000000000000)^(2*k) / Nat.factorial (2*k)) := by
      norm_num [sevenNineCosUpper, Finset.sum_range_succ]
    simpa [sub_zero] using hpR
  have hangle : ((117730621067653899677 : ℝ) / 100000000000000000000) ≤ Real.arccos (touchCosine a b (Real.sqrt 7 + Real.sqrt 9)) := by
    exact angle_lower_bound_of_cosine (by norm_num)
      (by
        calc
          ((117730621067653899677 : ℝ) / 100000000000000000000) ≤ (314159265358979323846 : ℝ) / 100000000000000000000 := by norm_num
          _ ≤ Real.pi := by
            have hpi := Real.pi_gt_d20.le
            norm_num at hpi ⊢
            exact hpi) (le_trans htouch hcos)
  have hdata : sevenNineAngleLower[67]! = ((117730621067653899677 : Rat) / 100000000000000000000) := by native_decide
  have hdataR : (sevenNineAngleLower[67]! : ℝ) = ((117730621067653899677 : ℝ) / 100000000000000000000) := by
    have h := congrArg (fun q : Rat => (q : ℝ)) hdata
    convert h using 1 ; norm_num
  rw [hdataR]
  exact hangle

theorem sevenNineAngle_3_6_0_0 {a b : ℝ}
    (haL : (sevenNineRadial 3 0 0 : ℝ) ≤ a) (haU : a ≤ (sevenNineRadial 3 0 1 : ℝ))
    (hbL : (sevenNineRadial 6 0 0 : ℝ) ≤ b) (hbU : b ≤ (sevenNineRadial 6 0 1 : ℝ)) :
    (sevenNineAngleLower[68]! : ℝ) ≤ Real.arccos (touchCosine a b (Real.sqrt 7 + Real.sqrt 10)) := by
  let d : ℝ := Real.sqrt 7 + Real.sqrt 10
  have hd' : (((5808028971232969922500509298071978959429814322407667007225839311993663261869521849104640994 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) : ℝ) ≤ d := by
    dsimp [d]
    have h := rat_sum_sqrt_lower (q := ((5808028971232969922500509298071978959429814322407667007225839311993663261869521849104640994 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (qi := ((2645751311064590590501615753639260425710259183082450180368334459201068823230283627760392886474543610615064578338497463095 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (qj := ((3162277660168379331998893544432718533719555139325216826857504852792594438639238221344248108379300295187347284152840055148 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))
      (ni := 7) (nj := 10)
      (by convert sqrt_lower_7 using 1 ; norm_num)
      (by convert sqrt_lower_10 using 1 ; norm_num)
      (by native_decide)
    convert h using 1 ; norm_num
  have hd : (((5808028971232969922500509298071978959429814322407667007225839311993663261869521849104640994 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) ≤ d := by exact hd'
  have hd2 : (((5808028971232969922500509298071978959429814322407667007225839311993663261869521849104640994 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))^2 ≤ d^2 := by
    have hq : (0 : ℝ) ≤ ((5808028971232969922500509298071978959429814322407667007225839311993663261869521849104640994 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) := by norm_num
    have hdn : 0 ≤ d := by positivity
    exact (sq_le_sq₀ hq hdn).mpr hd
  have hd2' : (sevenNineDistanceLower[17]! : ℝ)^2 ≤ d^2 := by
    convert hd2 using 1 ; norm_num [sevenNineDistanceLower]
  have h00 : (sevenNineRadial 3 0 0 : ℝ)^2 + (sevenNineRadial 6 0 0 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[68]! : ℝ) * (2 * (sevenNineRadial 3 0 0 : ℝ) * (sevenNineRadial 6 0 0 : ℝ)) := by
    have hq : (sevenNineRadial 3 0 0)^2 + (sevenNineRadial 6 0 0)^2 - sevenNineDistanceLower[17]!^2 ≤
        sevenNineCosUpper[68]! * (2 * sevenNineRadial 3 0 0 * sevenNineRadial 6 0 0) := by native_decide
    have hqR :
        (sevenNineRadial 3 0 0 : ℝ)^2 + (sevenNineRadial 6 0 0 : ℝ)^2 - (sevenNineDistanceLower[17]! : ℝ)^2 ≤
          (sevenNineCosUpper[68]! : ℝ) * (2 * (sevenNineRadial 3 0 0 : ℝ) * (sevenNineRadial 6 0 0 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 3 0 0 : ℝ)^2 + (sevenNineRadial 6 0 0 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 3 0 0 : ℝ)^2 + (sevenNineRadial 6 0 0 : ℝ)^2 - (sevenNineDistanceLower[17]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h01 : (sevenNineRadial 3 0 0 : ℝ)^2 + (sevenNineRadial 6 0 1 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[68]! : ℝ) * (2 * (sevenNineRadial 3 0 0 : ℝ) * (sevenNineRadial 6 0 1 : ℝ)) := by
    have hq : (sevenNineRadial 3 0 0)^2 + (sevenNineRadial 6 0 1)^2 - sevenNineDistanceLower[17]!^2 ≤
        sevenNineCosUpper[68]! * (2 * sevenNineRadial 3 0 0 * sevenNineRadial 6 0 1) := by native_decide
    have hqR :
        (sevenNineRadial 3 0 0 : ℝ)^2 + (sevenNineRadial 6 0 1 : ℝ)^2 - (sevenNineDistanceLower[17]! : ℝ)^2 ≤
          (sevenNineCosUpper[68]! : ℝ) * (2 * (sevenNineRadial 3 0 0 : ℝ) * (sevenNineRadial 6 0 1 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 3 0 0 : ℝ)^2 + (sevenNineRadial 6 0 1 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 3 0 0 : ℝ)^2 + (sevenNineRadial 6 0 1 : ℝ)^2 - (sevenNineDistanceLower[17]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h10 : (sevenNineRadial 3 0 1 : ℝ)^2 + (sevenNineRadial 6 0 0 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[68]! : ℝ) * (2 * (sevenNineRadial 3 0 1 : ℝ) * (sevenNineRadial 6 0 0 : ℝ)) := by
    have hq : (sevenNineRadial 3 0 1)^2 + (sevenNineRadial 6 0 0)^2 - sevenNineDistanceLower[17]!^2 ≤
        sevenNineCosUpper[68]! * (2 * sevenNineRadial 3 0 1 * sevenNineRadial 6 0 0) := by native_decide
    have hqR :
        (sevenNineRadial 3 0 1 : ℝ)^2 + (sevenNineRadial 6 0 0 : ℝ)^2 - (sevenNineDistanceLower[17]! : ℝ)^2 ≤
          (sevenNineCosUpper[68]! : ℝ) * (2 * (sevenNineRadial 3 0 1 : ℝ) * (sevenNineRadial 6 0 0 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 3 0 1 : ℝ)^2 + (sevenNineRadial 6 0 0 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 3 0 1 : ℝ)^2 + (sevenNineRadial 6 0 0 : ℝ)^2 - (sevenNineDistanceLower[17]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h11 : (sevenNineRadial 3 0 1 : ℝ)^2 + (sevenNineRadial 6 0 1 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[68]! : ℝ) * (2 * (sevenNineRadial 3 0 1 : ℝ) * (sevenNineRadial 6 0 1 : ℝ)) := by
    have hq : (sevenNineRadial 3 0 1)^2 + (sevenNineRadial 6 0 1)^2 - sevenNineDistanceLower[17]!^2 ≤
        sevenNineCosUpper[68]! * (2 * sevenNineRadial 3 0 1 * sevenNineRadial 6 0 1) := by native_decide
    have hqR :
        (sevenNineRadial 3 0 1 : ℝ)^2 + (sevenNineRadial 6 0 1 : ℝ)^2 - (sevenNineDistanceLower[17]! : ℝ)^2 ≤
          (sevenNineCosUpper[68]! : ℝ) * (2 * (sevenNineRadial 3 0 1 : ℝ) * (sevenNineRadial 6 0 1 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 3 0 1 : ℝ)^2 + (sevenNineRadial 6 0 1 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 3 0 1 : ℝ)^2 + (sevenNineRadial 6 0 1 : ℝ)^2 - (sevenNineDistanceLower[17]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have htouch := corner_touch_cosine_bound haL haU hbL hbU
    (by norm_num [sevenNineRadial, sevenNineRadialBounds])
    (by norm_num [sevenNineRadial, sevenNineRadialBounds]) h00 h01 h10 h11
  have hcos : (sevenNineCosUpper[68]! : ℝ) ≤ Real.cos ((245990090740280379931 : ℝ) / 100000000000000000000) := by
    apply lower_bound_of_taylor_error
      (cosine_taylor_ninety_six_remainder (a := 0) (b := 4) (x := ((245990090740280379931 : ℝ) / 100000000000000000000) )
        (by norm_num) (by constructor <;> norm_num [Real.pi_gt_d20, Real.pi_lt_four]))
    rw [cosine_taylor_ninety_six_at_zero (b := 4) (x := ((245990090740280379931 : ℝ) / 100000000000000000000)) (by norm_num)]
    have hp : (sevenNineCosUpper[68]! : Rat) + (((245990090740280379931 : Rat) / 100000000000000000000) : Rat)^97 / (Nat.factorial 96) ≤
        Finset.sum (Finset.range 49) (fun k => (-1 : Rat)^k * (((245990090740280379931 : Rat) / 100000000000000000000) : Rat)^(2*k) / Nat.factorial (2*k)) := by native_decide
    have hpR : (sevenNineCosUpper[68]! : ℝ) + ((245990090740280379931 : ℝ) / 100000000000000000000)^97 / (Nat.factorial 96) ≤
        Finset.sum (Finset.range 49) (fun k => (-1 : ℝ)^k * ((245990090740280379931 : ℝ) / 100000000000000000000)^(2*k) / Nat.factorial (2*k)) := by
      norm_num [sevenNineCosUpper, Finset.sum_range_succ]
    simpa [sub_zero] using hpR
  have hangle : ((245990090740280379931 : ℝ) / 100000000000000000000) ≤ Real.arccos (touchCosine a b (Real.sqrt 7 + Real.sqrt 10)) := by
    exact angle_lower_bound_of_cosine (by norm_num)
      (by
        calc
          ((245990090740280379931 : ℝ) / 100000000000000000000) ≤ (314159265358979323846 : ℝ) / 100000000000000000000 := by norm_num
          _ ≤ Real.pi := by
            have hpi := Real.pi_gt_d20.le
            norm_num at hpi ⊢
            exact hpi) (le_trans htouch hcos)
  have hdata : sevenNineAngleLower[68]! = ((245990090740280379931 : Rat) / 100000000000000000000) := by native_decide
  have hdataR : (sevenNineAngleLower[68]! : ℝ) = ((245990090740280379931 : ℝ) / 100000000000000000000) := by
    have h := congrArg (fun q : Rat => (q : ℝ)) hdata
    convert h using 1 ; norm_num
  rw [hdataR]
  exact hangle

theorem sevenNineAngle_3_6_0_1 {a b : ℝ}
    (haL : (sevenNineRadial 3 0 0 : ℝ) ≤ a) (haU : a ≤ (sevenNineRadial 3 0 1 : ℝ))
    (hbL : (sevenNineRadial 6 1 0 : ℝ) ≤ b) (hbU : b ≤ (sevenNineRadial 6 1 1 : ℝ)) :
    (sevenNineAngleLower[69]! : ℝ) ≤ Real.arccos (touchCosine a b (Real.sqrt 7 + Real.sqrt 10)) := by
  let d : ℝ := Real.sqrt 7 + Real.sqrt 10
  have hd' : (((5808028971232969922500509298071978959429814322407667007225839311993663261869521849104640994 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) : ℝ) ≤ d := by
    dsimp [d]
    have h := rat_sum_sqrt_lower (q := ((5808028971232969922500509298071978959429814322407667007225839311993663261869521849104640994 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (qi := ((2645751311064590590501615753639260425710259183082450180368334459201068823230283627760392886474543610615064578338497463095 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (qj := ((3162277660168379331998893544432718533719555139325216826857504852792594438639238221344248108379300295187347284152840055148 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))
      (ni := 7) (nj := 10)
      (by convert sqrt_lower_7 using 1 ; norm_num)
      (by convert sqrt_lower_10 using 1 ; norm_num)
      (by native_decide)
    convert h using 1 ; norm_num
  have hd : (((5808028971232969922500509298071978959429814322407667007225839311993663261869521849104640994 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) ≤ d := by exact hd'
  have hd2 : (((5808028971232969922500509298071978959429814322407667007225839311993663261869521849104640994 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))^2 ≤ d^2 := by
    have hq : (0 : ℝ) ≤ ((5808028971232969922500509298071978959429814322407667007225839311993663261869521849104640994 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) := by norm_num
    have hdn : 0 ≤ d := by positivity
    exact (sq_le_sq₀ hq hdn).mpr hd
  have hd2' : (sevenNineDistanceLower[17]! : ℝ)^2 ≤ d^2 := by
    convert hd2 using 1 ; norm_num [sevenNineDistanceLower]
  have h00 : (sevenNineRadial 3 0 0 : ℝ)^2 + (sevenNineRadial 6 1 0 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[69]! : ℝ) * (2 * (sevenNineRadial 3 0 0 : ℝ) * (sevenNineRadial 6 1 0 : ℝ)) := by
    have hq : (sevenNineRadial 3 0 0)^2 + (sevenNineRadial 6 1 0)^2 - sevenNineDistanceLower[17]!^2 ≤
        sevenNineCosUpper[69]! * (2 * sevenNineRadial 3 0 0 * sevenNineRadial 6 1 0) := by native_decide
    have hqR :
        (sevenNineRadial 3 0 0 : ℝ)^2 + (sevenNineRadial 6 1 0 : ℝ)^2 - (sevenNineDistanceLower[17]! : ℝ)^2 ≤
          (sevenNineCosUpper[69]! : ℝ) * (2 * (sevenNineRadial 3 0 0 : ℝ) * (sevenNineRadial 6 1 0 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 3 0 0 : ℝ)^2 + (sevenNineRadial 6 1 0 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 3 0 0 : ℝ)^2 + (sevenNineRadial 6 1 0 : ℝ)^2 - (sevenNineDistanceLower[17]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h01 : (sevenNineRadial 3 0 0 : ℝ)^2 + (sevenNineRadial 6 1 1 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[69]! : ℝ) * (2 * (sevenNineRadial 3 0 0 : ℝ) * (sevenNineRadial 6 1 1 : ℝ)) := by
    have hq : (sevenNineRadial 3 0 0)^2 + (sevenNineRadial 6 1 1)^2 - sevenNineDistanceLower[17]!^2 ≤
        sevenNineCosUpper[69]! * (2 * sevenNineRadial 3 0 0 * sevenNineRadial 6 1 1) := by native_decide
    have hqR :
        (sevenNineRadial 3 0 0 : ℝ)^2 + (sevenNineRadial 6 1 1 : ℝ)^2 - (sevenNineDistanceLower[17]! : ℝ)^2 ≤
          (sevenNineCosUpper[69]! : ℝ) * (2 * (sevenNineRadial 3 0 0 : ℝ) * (sevenNineRadial 6 1 1 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 3 0 0 : ℝ)^2 + (sevenNineRadial 6 1 1 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 3 0 0 : ℝ)^2 + (sevenNineRadial 6 1 1 : ℝ)^2 - (sevenNineDistanceLower[17]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h10 : (sevenNineRadial 3 0 1 : ℝ)^2 + (sevenNineRadial 6 1 0 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[69]! : ℝ) * (2 * (sevenNineRadial 3 0 1 : ℝ) * (sevenNineRadial 6 1 0 : ℝ)) := by
    have hq : (sevenNineRadial 3 0 1)^2 + (sevenNineRadial 6 1 0)^2 - sevenNineDistanceLower[17]!^2 ≤
        sevenNineCosUpper[69]! * (2 * sevenNineRadial 3 0 1 * sevenNineRadial 6 1 0) := by native_decide
    have hqR :
        (sevenNineRadial 3 0 1 : ℝ)^2 + (sevenNineRadial 6 1 0 : ℝ)^2 - (sevenNineDistanceLower[17]! : ℝ)^2 ≤
          (sevenNineCosUpper[69]! : ℝ) * (2 * (sevenNineRadial 3 0 1 : ℝ) * (sevenNineRadial 6 1 0 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 3 0 1 : ℝ)^2 + (sevenNineRadial 6 1 0 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 3 0 1 : ℝ)^2 + (sevenNineRadial 6 1 0 : ℝ)^2 - (sevenNineDistanceLower[17]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h11 : (sevenNineRadial 3 0 1 : ℝ)^2 + (sevenNineRadial 6 1 1 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[69]! : ℝ) * (2 * (sevenNineRadial 3 0 1 : ℝ) * (sevenNineRadial 6 1 1 : ℝ)) := by
    have hq : (sevenNineRadial 3 0 1)^2 + (sevenNineRadial 6 1 1)^2 - sevenNineDistanceLower[17]!^2 ≤
        sevenNineCosUpper[69]! * (2 * sevenNineRadial 3 0 1 * sevenNineRadial 6 1 1) := by native_decide
    have hqR :
        (sevenNineRadial 3 0 1 : ℝ)^2 + (sevenNineRadial 6 1 1 : ℝ)^2 - (sevenNineDistanceLower[17]! : ℝ)^2 ≤
          (sevenNineCosUpper[69]! : ℝ) * (2 * (sevenNineRadial 3 0 1 : ℝ) * (sevenNineRadial 6 1 1 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 3 0 1 : ℝ)^2 + (sevenNineRadial 6 1 1 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 3 0 1 : ℝ)^2 + (sevenNineRadial 6 1 1 : ℝ)^2 - (sevenNineDistanceLower[17]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have htouch := corner_touch_cosine_bound haL haU hbL hbU
    (by norm_num [sevenNineRadial, sevenNineRadialBounds])
    (by norm_num [sevenNineRadial, sevenNineRadialBounds]) h00 h01 h10 h11
  have hcos : (sevenNineCosUpper[69]! : ℝ) ≤ Real.cos ((161376736998800349316 : ℝ) / 100000000000000000000) := by
    apply lower_bound_of_taylor_error
      (cosine_taylor_ninety_six_remainder (a := 0) (b := 4) (x := ((161376736998800349316 : ℝ) / 100000000000000000000) )
        (by norm_num) (by constructor <;> norm_num [Real.pi_gt_d20, Real.pi_lt_four]))
    rw [cosine_taylor_ninety_six_at_zero (b := 4) (x := ((161376736998800349316 : ℝ) / 100000000000000000000)) (by norm_num)]
    have hp : (sevenNineCosUpper[69]! : Rat) + (((161376736998800349316 : Rat) / 100000000000000000000) : Rat)^97 / (Nat.factorial 96) ≤
        Finset.sum (Finset.range 49) (fun k => (-1 : Rat)^k * (((161376736998800349316 : Rat) / 100000000000000000000) : Rat)^(2*k) / Nat.factorial (2*k)) := by native_decide
    have hpR : (sevenNineCosUpper[69]! : ℝ) + ((161376736998800349316 : ℝ) / 100000000000000000000)^97 / (Nat.factorial 96) ≤
        Finset.sum (Finset.range 49) (fun k => (-1 : ℝ)^k * ((161376736998800349316 : ℝ) / 100000000000000000000)^(2*k) / Nat.factorial (2*k)) := by
      norm_num [sevenNineCosUpper, Finset.sum_range_succ]
    simpa [sub_zero] using hpR
  have hangle : ((161376736998800349316 : ℝ) / 100000000000000000000) ≤ Real.arccos (touchCosine a b (Real.sqrt 7 + Real.sqrt 10)) := by
    exact angle_lower_bound_of_cosine (by norm_num)
      (by
        calc
          ((161376736998800349316 : ℝ) / 100000000000000000000) ≤ (314159265358979323846 : ℝ) / 100000000000000000000 := by norm_num
          _ ≤ Real.pi := by
            have hpi := Real.pi_gt_d20.le
            norm_num at hpi ⊢
            exact hpi) (le_trans htouch hcos)
  have hdata : sevenNineAngleLower[69]! = ((161376736998800349316 : Rat) / 100000000000000000000) := by native_decide
  have hdataR : (sevenNineAngleLower[69]! : ℝ) = ((161376736998800349316 : ℝ) / 100000000000000000000) := by
    have h := congrArg (fun q : Rat => (q : ℝ)) hdata
    convert h using 1 ; norm_num
  rw [hdataR]
  exact hangle

theorem sevenNineAngle_3_6_1_0 {a b : ℝ}
    (haL : (sevenNineRadial 3 1 0 : ℝ) ≤ a) (haU : a ≤ (sevenNineRadial 3 1 1 : ℝ))
    (hbL : (sevenNineRadial 6 0 0 : ℝ) ≤ b) (hbU : b ≤ (sevenNineRadial 6 0 1 : ℝ)) :
    (sevenNineAngleLower[70]! : ℝ) ≤ Real.arccos (touchCosine a b (Real.sqrt 7 + Real.sqrt 10)) := by
  let d : ℝ := Real.sqrt 7 + Real.sqrt 10
  have hd' : (((5808028971232969922500509298071978959429814322407667007225839311993663261869521849104640994 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) : ℝ) ≤ d := by
    dsimp [d]
    have h := rat_sum_sqrt_lower (q := ((5808028971232969922500509298071978959429814322407667007225839311993663261869521849104640994 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (qi := ((2645751311064590590501615753639260425710259183082450180368334459201068823230283627760392886474543610615064578338497463095 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (qj := ((3162277660168379331998893544432718533719555139325216826857504852792594438639238221344248108379300295187347284152840055148 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))
      (ni := 7) (nj := 10)
      (by convert sqrt_lower_7 using 1 ; norm_num)
      (by convert sqrt_lower_10 using 1 ; norm_num)
      (by native_decide)
    convert h using 1 ; norm_num
  have hd : (((5808028971232969922500509298071978959429814322407667007225839311993663261869521849104640994 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) ≤ d := by exact hd'
  have hd2 : (((5808028971232969922500509298071978959429814322407667007225839311993663261869521849104640994 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))^2 ≤ d^2 := by
    have hq : (0 : ℝ) ≤ ((5808028971232969922500509298071978959429814322407667007225839311993663261869521849104640994 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) := by norm_num
    have hdn : 0 ≤ d := by positivity
    exact (sq_le_sq₀ hq hdn).mpr hd
  have hd2' : (sevenNineDistanceLower[17]! : ℝ)^2 ≤ d^2 := by
    convert hd2 using 1 ; norm_num [sevenNineDistanceLower]
  have h00 : (sevenNineRadial 3 1 0 : ℝ)^2 + (sevenNineRadial 6 0 0 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[70]! : ℝ) * (2 * (sevenNineRadial 3 1 0 : ℝ) * (sevenNineRadial 6 0 0 : ℝ)) := by
    have hq : (sevenNineRadial 3 1 0)^2 + (sevenNineRadial 6 0 0)^2 - sevenNineDistanceLower[17]!^2 ≤
        sevenNineCosUpper[70]! * (2 * sevenNineRadial 3 1 0 * sevenNineRadial 6 0 0) := by native_decide
    have hqR :
        (sevenNineRadial 3 1 0 : ℝ)^2 + (sevenNineRadial 6 0 0 : ℝ)^2 - (sevenNineDistanceLower[17]! : ℝ)^2 ≤
          (sevenNineCosUpper[70]! : ℝ) * (2 * (sevenNineRadial 3 1 0 : ℝ) * (sevenNineRadial 6 0 0 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 3 1 0 : ℝ)^2 + (sevenNineRadial 6 0 0 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 3 1 0 : ℝ)^2 + (sevenNineRadial 6 0 0 : ℝ)^2 - (sevenNineDistanceLower[17]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h01 : (sevenNineRadial 3 1 0 : ℝ)^2 + (sevenNineRadial 6 0 1 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[70]! : ℝ) * (2 * (sevenNineRadial 3 1 0 : ℝ) * (sevenNineRadial 6 0 1 : ℝ)) := by
    have hq : (sevenNineRadial 3 1 0)^2 + (sevenNineRadial 6 0 1)^2 - sevenNineDistanceLower[17]!^2 ≤
        sevenNineCosUpper[70]! * (2 * sevenNineRadial 3 1 0 * sevenNineRadial 6 0 1) := by native_decide
    have hqR :
        (sevenNineRadial 3 1 0 : ℝ)^2 + (sevenNineRadial 6 0 1 : ℝ)^2 - (sevenNineDistanceLower[17]! : ℝ)^2 ≤
          (sevenNineCosUpper[70]! : ℝ) * (2 * (sevenNineRadial 3 1 0 : ℝ) * (sevenNineRadial 6 0 1 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 3 1 0 : ℝ)^2 + (sevenNineRadial 6 0 1 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 3 1 0 : ℝ)^2 + (sevenNineRadial 6 0 1 : ℝ)^2 - (sevenNineDistanceLower[17]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h10 : (sevenNineRadial 3 1 1 : ℝ)^2 + (sevenNineRadial 6 0 0 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[70]! : ℝ) * (2 * (sevenNineRadial 3 1 1 : ℝ) * (sevenNineRadial 6 0 0 : ℝ)) := by
    have hq : (sevenNineRadial 3 1 1)^2 + (sevenNineRadial 6 0 0)^2 - sevenNineDistanceLower[17]!^2 ≤
        sevenNineCosUpper[70]! * (2 * sevenNineRadial 3 1 1 * sevenNineRadial 6 0 0) := by native_decide
    have hqR :
        (sevenNineRadial 3 1 1 : ℝ)^2 + (sevenNineRadial 6 0 0 : ℝ)^2 - (sevenNineDistanceLower[17]! : ℝ)^2 ≤
          (sevenNineCosUpper[70]! : ℝ) * (2 * (sevenNineRadial 3 1 1 : ℝ) * (sevenNineRadial 6 0 0 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 3 1 1 : ℝ)^2 + (sevenNineRadial 6 0 0 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 3 1 1 : ℝ)^2 + (sevenNineRadial 6 0 0 : ℝ)^2 - (sevenNineDistanceLower[17]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h11 : (sevenNineRadial 3 1 1 : ℝ)^2 + (sevenNineRadial 6 0 1 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[70]! : ℝ) * (2 * (sevenNineRadial 3 1 1 : ℝ) * (sevenNineRadial 6 0 1 : ℝ)) := by
    have hq : (sevenNineRadial 3 1 1)^2 + (sevenNineRadial 6 0 1)^2 - sevenNineDistanceLower[17]!^2 ≤
        sevenNineCosUpper[70]! * (2 * sevenNineRadial 3 1 1 * sevenNineRadial 6 0 1) := by native_decide
    have hqR :
        (sevenNineRadial 3 1 1 : ℝ)^2 + (sevenNineRadial 6 0 1 : ℝ)^2 - (sevenNineDistanceLower[17]! : ℝ)^2 ≤
          (sevenNineCosUpper[70]! : ℝ) * (2 * (sevenNineRadial 3 1 1 : ℝ) * (sevenNineRadial 6 0 1 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 3 1 1 : ℝ)^2 + (sevenNineRadial 6 0 1 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 3 1 1 : ℝ)^2 + (sevenNineRadial 6 0 1 : ℝ)^2 - (sevenNineDistanceLower[17]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have htouch := corner_touch_cosine_bound haL haU hbL hbU
    (by norm_num [sevenNineRadial, sevenNineRadialBounds])
    (by norm_num [sevenNineRadial, sevenNineRadialBounds]) h00 h01 h10 h11
  have hcos : (sevenNineCosUpper[70]! : ℝ) ≤ Real.cos ((147950752648930417527 : ℝ) / 100000000000000000000) := by
    apply lower_bound_of_taylor_error
      (cosine_taylor_ninety_six_remainder (a := 0) (b := 4) (x := ((147950752648930417527 : ℝ) / 100000000000000000000) )
        (by norm_num) (by constructor <;> norm_num [Real.pi_gt_d20, Real.pi_lt_four]))
    rw [cosine_taylor_ninety_six_at_zero (b := 4) (x := ((147950752648930417527 : ℝ) / 100000000000000000000)) (by norm_num)]
    have hp : (sevenNineCosUpper[70]! : Rat) + (((147950752648930417527 : Rat) / 100000000000000000000) : Rat)^97 / (Nat.factorial 96) ≤
        Finset.sum (Finset.range 49) (fun k => (-1 : Rat)^k * (((147950752648930417527 : Rat) / 100000000000000000000) : Rat)^(2*k) / Nat.factorial (2*k)) := by native_decide
    have hpR : (sevenNineCosUpper[70]! : ℝ) + ((147950752648930417527 : ℝ) / 100000000000000000000)^97 / (Nat.factorial 96) ≤
        Finset.sum (Finset.range 49) (fun k => (-1 : ℝ)^k * ((147950752648930417527 : ℝ) / 100000000000000000000)^(2*k) / Nat.factorial (2*k)) := by
      norm_num [sevenNineCosUpper, Finset.sum_range_succ]
    simpa [sub_zero] using hpR
  have hangle : ((147950752648930417527 : ℝ) / 100000000000000000000) ≤ Real.arccos (touchCosine a b (Real.sqrt 7 + Real.sqrt 10)) := by
    exact angle_lower_bound_of_cosine (by norm_num)
      (by
        calc
          ((147950752648930417527 : ℝ) / 100000000000000000000) ≤ (314159265358979323846 : ℝ) / 100000000000000000000 := by norm_num
          _ ≤ Real.pi := by
            have hpi := Real.pi_gt_d20.le
            norm_num at hpi ⊢
            exact hpi) (le_trans htouch hcos)
  have hdata : sevenNineAngleLower[70]! = ((147950752648930417527 : Rat) / 100000000000000000000) := by native_decide
  have hdataR : (sevenNineAngleLower[70]! : ℝ) = ((147950752648930417527 : ℝ) / 100000000000000000000) := by
    have h := congrArg (fun q : Rat => (q : ℝ)) hdata
    convert h using 1 ; norm_num
  rw [hdataR]
  exact hangle

theorem sevenNineAngle_3_6_1_1 {a b : ℝ}
    (haL : (sevenNineRadial 3 1 0 : ℝ) ≤ a) (haU : a ≤ (sevenNineRadial 3 1 1 : ℝ))
    (hbL : (sevenNineRadial 6 1 0 : ℝ) ≤ b) (hbU : b ≤ (sevenNineRadial 6 1 1 : ℝ)) :
    (sevenNineAngleLower[71]! : ℝ) ≤ Real.arccos (touchCosine a b (Real.sqrt 7 + Real.sqrt 10)) := by
  let d : ℝ := Real.sqrt 7 + Real.sqrt 10
  have hd' : (((5808028971232969922500509298071978959429814322407667007225839311993663261869521849104640994 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) : ℝ) ≤ d := by
    dsimp [d]
    have h := rat_sum_sqrt_lower (q := ((5808028971232969922500509298071978959429814322407667007225839311993663261869521849104640994 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (qi := ((2645751311064590590501615753639260425710259183082450180368334459201068823230283627760392886474543610615064578338497463095 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (qj := ((3162277660168379331998893544432718533719555139325216826857504852792594438639238221344248108379300295187347284152840055148 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))
      (ni := 7) (nj := 10)
      (by convert sqrt_lower_7 using 1 ; norm_num)
      (by convert sqrt_lower_10 using 1 ; norm_num)
      (by native_decide)
    convert h using 1 ; norm_num
  have hd : (((5808028971232969922500509298071978959429814322407667007225839311993663261869521849104640994 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) ≤ d := by exact hd'
  have hd2 : (((5808028971232969922500509298071978959429814322407667007225839311993663261869521849104640994 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))^2 ≤ d^2 := by
    have hq : (0 : ℝ) ≤ ((5808028971232969922500509298071978959429814322407667007225839311993663261869521849104640994 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) := by norm_num
    have hdn : 0 ≤ d := by positivity
    exact (sq_le_sq₀ hq hdn).mpr hd
  have hd2' : (sevenNineDistanceLower[17]! : ℝ)^2 ≤ d^2 := by
    convert hd2 using 1 ; norm_num [sevenNineDistanceLower]
  have h00 : (sevenNineRadial 3 1 0 : ℝ)^2 + (sevenNineRadial 6 1 0 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[71]! : ℝ) * (2 * (sevenNineRadial 3 1 0 : ℝ) * (sevenNineRadial 6 1 0 : ℝ)) := by
    have hq : (sevenNineRadial 3 1 0)^2 + (sevenNineRadial 6 1 0)^2 - sevenNineDistanceLower[17]!^2 ≤
        sevenNineCosUpper[71]! * (2 * sevenNineRadial 3 1 0 * sevenNineRadial 6 1 0) := by native_decide
    have hqR :
        (sevenNineRadial 3 1 0 : ℝ)^2 + (sevenNineRadial 6 1 0 : ℝ)^2 - (sevenNineDistanceLower[17]! : ℝ)^2 ≤
          (sevenNineCosUpper[71]! : ℝ) * (2 * (sevenNineRadial 3 1 0 : ℝ) * (sevenNineRadial 6 1 0 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 3 1 0 : ℝ)^2 + (sevenNineRadial 6 1 0 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 3 1 0 : ℝ)^2 + (sevenNineRadial 6 1 0 : ℝ)^2 - (sevenNineDistanceLower[17]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h01 : (sevenNineRadial 3 1 0 : ℝ)^2 + (sevenNineRadial 6 1 1 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[71]! : ℝ) * (2 * (sevenNineRadial 3 1 0 : ℝ) * (sevenNineRadial 6 1 1 : ℝ)) := by
    have hq : (sevenNineRadial 3 1 0)^2 + (sevenNineRadial 6 1 1)^2 - sevenNineDistanceLower[17]!^2 ≤
        sevenNineCosUpper[71]! * (2 * sevenNineRadial 3 1 0 * sevenNineRadial 6 1 1) := by native_decide
    have hqR :
        (sevenNineRadial 3 1 0 : ℝ)^2 + (sevenNineRadial 6 1 1 : ℝ)^2 - (sevenNineDistanceLower[17]! : ℝ)^2 ≤
          (sevenNineCosUpper[71]! : ℝ) * (2 * (sevenNineRadial 3 1 0 : ℝ) * (sevenNineRadial 6 1 1 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 3 1 0 : ℝ)^2 + (sevenNineRadial 6 1 1 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 3 1 0 : ℝ)^2 + (sevenNineRadial 6 1 1 : ℝ)^2 - (sevenNineDistanceLower[17]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h10 : (sevenNineRadial 3 1 1 : ℝ)^2 + (sevenNineRadial 6 1 0 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[71]! : ℝ) * (2 * (sevenNineRadial 3 1 1 : ℝ) * (sevenNineRadial 6 1 0 : ℝ)) := by
    have hq : (sevenNineRadial 3 1 1)^2 + (sevenNineRadial 6 1 0)^2 - sevenNineDistanceLower[17]!^2 ≤
        sevenNineCosUpper[71]! * (2 * sevenNineRadial 3 1 1 * sevenNineRadial 6 1 0) := by native_decide
    have hqR :
        (sevenNineRadial 3 1 1 : ℝ)^2 + (sevenNineRadial 6 1 0 : ℝ)^2 - (sevenNineDistanceLower[17]! : ℝ)^2 ≤
          (sevenNineCosUpper[71]! : ℝ) * (2 * (sevenNineRadial 3 1 1 : ℝ) * (sevenNineRadial 6 1 0 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 3 1 1 : ℝ)^2 + (sevenNineRadial 6 1 0 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 3 1 1 : ℝ)^2 + (sevenNineRadial 6 1 0 : ℝ)^2 - (sevenNineDistanceLower[17]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h11 : (sevenNineRadial 3 1 1 : ℝ)^2 + (sevenNineRadial 6 1 1 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[71]! : ℝ) * (2 * (sevenNineRadial 3 1 1 : ℝ) * (sevenNineRadial 6 1 1 : ℝ)) := by
    have hq : (sevenNineRadial 3 1 1)^2 + (sevenNineRadial 6 1 1)^2 - sevenNineDistanceLower[17]!^2 ≤
        sevenNineCosUpper[71]! * (2 * sevenNineRadial 3 1 1 * sevenNineRadial 6 1 1) := by native_decide
    have hqR :
        (sevenNineRadial 3 1 1 : ℝ)^2 + (sevenNineRadial 6 1 1 : ℝ)^2 - (sevenNineDistanceLower[17]! : ℝ)^2 ≤
          (sevenNineCosUpper[71]! : ℝ) * (2 * (sevenNineRadial 3 1 1 : ℝ) * (sevenNineRadial 6 1 1 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 3 1 1 : ℝ)^2 + (sevenNineRadial 6 1 1 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 3 1 1 : ℝ)^2 + (sevenNineRadial 6 1 1 : ℝ)^2 - (sevenNineDistanceLower[17]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have htouch := corner_touch_cosine_bound haL haU hbL hbU
    (by norm_num [sevenNineRadial, sevenNineRadialBounds])
    (by norm_num [sevenNineRadial, sevenNineRadialBounds]) h00 h01 h10 h11
  have hcos : (sevenNineCosUpper[71]! : ℝ) ≤ Real.cos ((123682281654054946930 : ℝ) / 100000000000000000000) := by
    apply lower_bound_of_taylor_error
      (cosine_taylor_ninety_six_remainder (a := 0) (b := 4) (x := ((123682281654054946930 : ℝ) / 100000000000000000000) )
        (by norm_num) (by constructor <;> norm_num [Real.pi_gt_d20, Real.pi_lt_four]))
    rw [cosine_taylor_ninety_six_at_zero (b := 4) (x := ((123682281654054946930 : ℝ) / 100000000000000000000)) (by norm_num)]
    have hp : (sevenNineCosUpper[71]! : Rat) + (((123682281654054946930 : Rat) / 100000000000000000000) : Rat)^97 / (Nat.factorial 96) ≤
        Finset.sum (Finset.range 49) (fun k => (-1 : Rat)^k * (((123682281654054946930 : Rat) / 100000000000000000000) : Rat)^(2*k) / Nat.factorial (2*k)) := by native_decide
    have hpR : (sevenNineCosUpper[71]! : ℝ) + ((123682281654054946930 : ℝ) / 100000000000000000000)^97 / (Nat.factorial 96) ≤
        Finset.sum (Finset.range 49) (fun k => (-1 : ℝ)^k * ((123682281654054946930 : ℝ) / 100000000000000000000)^(2*k) / Nat.factorial (2*k)) := by
      norm_num [sevenNineCosUpper, Finset.sum_range_succ]
    simpa [sub_zero] using hpR
  have hangle : ((123682281654054946930 : ℝ) / 100000000000000000000) ≤ Real.arccos (touchCosine a b (Real.sqrt 7 + Real.sqrt 10)) := by
    exact angle_lower_bound_of_cosine (by norm_num)
      (by
        calc
          ((123682281654054946930 : ℝ) / 100000000000000000000) ≤ (314159265358979323846 : ℝ) / 100000000000000000000 := by norm_num
          _ ≤ Real.pi := by
            have hpi := Real.pi_gt_d20.le
            norm_num at hpi ⊢
            exact hpi) (le_trans htouch hcos)
  have hdata : sevenNineAngleLower[71]! = ((123682281654054946930 : Rat) / 100000000000000000000) := by native_decide
  have hdataR : (sevenNineAngleLower[71]! : ℝ) = ((123682281654054946930 : ℝ) / 100000000000000000000) := by
    have h := congrArg (fun q : Rat => (q : ℝ)) hdata
    convert h using 1 ; norm_num
  rw [hdataR]
  exact hangle

theorem sevenNineAngle_4_5_0_0 {a b : ℝ}
    (haL : (sevenNineRadial 4 0 0 : ℝ) ≤ a) (haU : a ≤ (sevenNineRadial 4 0 1 : ℝ))
    (hbL : (sevenNineRadial 5 0 0 : ℝ) ≤ b) (hbU : b ≤ (sevenNineRadial 5 0 1 : ℝ)) :
    (sevenNineAngleLower[72]! : ℝ) ≤ Real.arccos (touchCosine a b (Real.sqrt 8 + Real.sqrt 9)) := by
  let d : ℝ := Real.sqrt 8 + Real.sqrt 9
  have hd' : (((5828427124746190097603377448419396157139343750753896146353359475981464956924214077700775068 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) : ℝ) ≤ d := by
    dsimp [d]
    have h := rat_sum_sqrt_lower (q := ((5828427124746190097603377448419396157139343750753896146353359475981464956924214077700775068 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (qi := ((2828427124746190097603377448419396157139343750753896146353359475981464956924214077700775068655283145470027692461824594049 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (qj := ((3 : Rat) / 1))
      (ni := 8) (nj := 9)
      (by convert sqrt_lower_8 using 1 ; norm_num)
      (by convert sqrt_lower_9 using 1 ; norm_num)
      (by native_decide)
    convert h using 1 ; norm_num
  have hd : (((5828427124746190097603377448419396157139343750753896146353359475981464956924214077700775068 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) ≤ d := by exact hd'
  have hd2 : (((5828427124746190097603377448419396157139343750753896146353359475981464956924214077700775068 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))^2 ≤ d^2 := by
    have hq : (0 : ℝ) ≤ ((5828427124746190097603377448419396157139343750753896146353359475981464956924214077700775068 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) := by norm_num
    have hdn : 0 ≤ d := by positivity
    exact (sq_le_sq₀ hq hdn).mpr hd
  have hd2' : (sevenNineDistanceLower[18]! : ℝ)^2 ≤ d^2 := by
    convert hd2 using 1 ; norm_num [sevenNineDistanceLower]
  have h00 : (sevenNineRadial 4 0 0 : ℝ)^2 + (sevenNineRadial 5 0 0 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[72]! : ℝ) * (2 * (sevenNineRadial 4 0 0 : ℝ) * (sevenNineRadial 5 0 0 : ℝ)) := by
    have hq : (sevenNineRadial 4 0 0)^2 + (sevenNineRadial 5 0 0)^2 - sevenNineDistanceLower[18]!^2 ≤
        sevenNineCosUpper[72]! * (2 * sevenNineRadial 4 0 0 * sevenNineRadial 5 0 0) := by native_decide
    have hqR :
        (sevenNineRadial 4 0 0 : ℝ)^2 + (sevenNineRadial 5 0 0 : ℝ)^2 - (sevenNineDistanceLower[18]! : ℝ)^2 ≤
          (sevenNineCosUpper[72]! : ℝ) * (2 * (sevenNineRadial 4 0 0 : ℝ) * (sevenNineRadial 5 0 0 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 4 0 0 : ℝ)^2 + (sevenNineRadial 5 0 0 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 4 0 0 : ℝ)^2 + (sevenNineRadial 5 0 0 : ℝ)^2 - (sevenNineDistanceLower[18]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h01 : (sevenNineRadial 4 0 0 : ℝ)^2 + (sevenNineRadial 5 0 1 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[72]! : ℝ) * (2 * (sevenNineRadial 4 0 0 : ℝ) * (sevenNineRadial 5 0 1 : ℝ)) := by
    have hq : (sevenNineRadial 4 0 0)^2 + (sevenNineRadial 5 0 1)^2 - sevenNineDistanceLower[18]!^2 ≤
        sevenNineCosUpper[72]! * (2 * sevenNineRadial 4 0 0 * sevenNineRadial 5 0 1) := by native_decide
    have hqR :
        (sevenNineRadial 4 0 0 : ℝ)^2 + (sevenNineRadial 5 0 1 : ℝ)^2 - (sevenNineDistanceLower[18]! : ℝ)^2 ≤
          (sevenNineCosUpper[72]! : ℝ) * (2 * (sevenNineRadial 4 0 0 : ℝ) * (sevenNineRadial 5 0 1 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 4 0 0 : ℝ)^2 + (sevenNineRadial 5 0 1 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 4 0 0 : ℝ)^2 + (sevenNineRadial 5 0 1 : ℝ)^2 - (sevenNineDistanceLower[18]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h10 : (sevenNineRadial 4 0 1 : ℝ)^2 + (sevenNineRadial 5 0 0 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[72]! : ℝ) * (2 * (sevenNineRadial 4 0 1 : ℝ) * (sevenNineRadial 5 0 0 : ℝ)) := by
    have hq : (sevenNineRadial 4 0 1)^2 + (sevenNineRadial 5 0 0)^2 - sevenNineDistanceLower[18]!^2 ≤
        sevenNineCosUpper[72]! * (2 * sevenNineRadial 4 0 1 * sevenNineRadial 5 0 0) := by native_decide
    have hqR :
        (sevenNineRadial 4 0 1 : ℝ)^2 + (sevenNineRadial 5 0 0 : ℝ)^2 - (sevenNineDistanceLower[18]! : ℝ)^2 ≤
          (sevenNineCosUpper[72]! : ℝ) * (2 * (sevenNineRadial 4 0 1 : ℝ) * (sevenNineRadial 5 0 0 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 4 0 1 : ℝ)^2 + (sevenNineRadial 5 0 0 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 4 0 1 : ℝ)^2 + (sevenNineRadial 5 0 0 : ℝ)^2 - (sevenNineDistanceLower[18]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h11 : (sevenNineRadial 4 0 1 : ℝ)^2 + (sevenNineRadial 5 0 1 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[72]! : ℝ) * (2 * (sevenNineRadial 4 0 1 : ℝ) * (sevenNineRadial 5 0 1 : ℝ)) := by
    have hq : (sevenNineRadial 4 0 1)^2 + (sevenNineRadial 5 0 1)^2 - sevenNineDistanceLower[18]!^2 ≤
        sevenNineCosUpper[72]! * (2 * sevenNineRadial 4 0 1 * sevenNineRadial 5 0 1) := by native_decide
    have hqR :
        (sevenNineRadial 4 0 1 : ℝ)^2 + (sevenNineRadial 5 0 1 : ℝ)^2 - (sevenNineDistanceLower[18]! : ℝ)^2 ≤
          (sevenNineCosUpper[72]! : ℝ) * (2 * (sevenNineRadial 4 0 1 : ℝ) * (sevenNineRadial 5 0 1 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 4 0 1 : ℝ)^2 + (sevenNineRadial 5 0 1 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 4 0 1 : ℝ)^2 + (sevenNineRadial 5 0 1 : ℝ)^2 - (sevenNineDistanceLower[18]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have htouch := corner_touch_cosine_bound haL haU hbL hbU
    (by norm_num [sevenNineRadial, sevenNineRadialBounds])
    (by norm_num [sevenNineRadial, sevenNineRadialBounds]) h00 h01 h10 h11
  have hcos : (sevenNineCosUpper[72]! : ℝ) ≤ Real.cos ((234413487974596573341 : ℝ) / 100000000000000000000) := by
    apply lower_bound_of_taylor_error
      (cosine_taylor_ninety_six_remainder (a := 0) (b := 4) (x := ((234413487974596573341 : ℝ) / 100000000000000000000) )
        (by norm_num) (by constructor <;> norm_num [Real.pi_gt_d20, Real.pi_lt_four]))
    rw [cosine_taylor_ninety_six_at_zero (b := 4) (x := ((234413487974596573341 : ℝ) / 100000000000000000000)) (by norm_num)]
    have hp : (sevenNineCosUpper[72]! : Rat) + (((234413487974596573341 : Rat) / 100000000000000000000) : Rat)^97 / (Nat.factorial 96) ≤
        Finset.sum (Finset.range 49) (fun k => (-1 : Rat)^k * (((234413487974596573341 : Rat) / 100000000000000000000) : Rat)^(2*k) / Nat.factorial (2*k)) := by native_decide
    have hpR : (sevenNineCosUpper[72]! : ℝ) + ((234413487974596573341 : ℝ) / 100000000000000000000)^97 / (Nat.factorial 96) ≤
        Finset.sum (Finset.range 49) (fun k => (-1 : ℝ)^k * ((234413487974596573341 : ℝ) / 100000000000000000000)^(2*k) / Nat.factorial (2*k)) := by
      norm_num [sevenNineCosUpper, Finset.sum_range_succ]
    simpa [sub_zero] using hpR
  have hangle : ((234413487974596573341 : ℝ) / 100000000000000000000) ≤ Real.arccos (touchCosine a b (Real.sqrt 8 + Real.sqrt 9)) := by
    exact angle_lower_bound_of_cosine (by norm_num)
      (by
        calc
          ((234413487974596573341 : ℝ) / 100000000000000000000) ≤ (314159265358979323846 : ℝ) / 100000000000000000000 := by norm_num
          _ ≤ Real.pi := by
            have hpi := Real.pi_gt_d20.le
            norm_num at hpi ⊢
            exact hpi) (le_trans htouch hcos)
  have hdata : sevenNineAngleLower[72]! = ((234413487974596573341 : Rat) / 100000000000000000000) := by native_decide
  have hdataR : (sevenNineAngleLower[72]! : ℝ) = ((234413487974596573341 : ℝ) / 100000000000000000000) := by
    have h := congrArg (fun q : Rat => (q : ℝ)) hdata
    convert h using 1 ; norm_num
  rw [hdataR]
  exact hangle

theorem sevenNineAngle_4_5_0_1 {a b : ℝ}
    (haL : (sevenNineRadial 4 0 0 : ℝ) ≤ a) (haU : a ≤ (sevenNineRadial 4 0 1 : ℝ))
    (hbL : (sevenNineRadial 5 1 0 : ℝ) ≤ b) (hbU : b ≤ (sevenNineRadial 5 1 1 : ℝ)) :
    (sevenNineAngleLower[73]! : ℝ) ≤ Real.arccos (touchCosine a b (Real.sqrt 8 + Real.sqrt 9)) := by
  let d : ℝ := Real.sqrt 8 + Real.sqrt 9
  have hd' : (((5828427124746190097603377448419396157139343750753896146353359475981464956924214077700775068 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) : ℝ) ≤ d := by
    dsimp [d]
    have h := rat_sum_sqrt_lower (q := ((5828427124746190097603377448419396157139343750753896146353359475981464956924214077700775068 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (qi := ((2828427124746190097603377448419396157139343750753896146353359475981464956924214077700775068655283145470027692461824594049 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (qj := ((3 : Rat) / 1))
      (ni := 8) (nj := 9)
      (by convert sqrt_lower_8 using 1 ; norm_num)
      (by convert sqrt_lower_9 using 1 ; norm_num)
      (by native_decide)
    convert h using 1 ; norm_num
  have hd : (((5828427124746190097603377448419396157139343750753896146353359475981464956924214077700775068 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) ≤ d := by exact hd'
  have hd2 : (((5828427124746190097603377448419396157139343750753896146353359475981464956924214077700775068 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))^2 ≤ d^2 := by
    have hq : (0 : ℝ) ≤ ((5828427124746190097603377448419396157139343750753896146353359475981464956924214077700775068 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) := by norm_num
    have hdn : 0 ≤ d := by positivity
    exact (sq_le_sq₀ hq hdn).mpr hd
  have hd2' : (sevenNineDistanceLower[18]! : ℝ)^2 ≤ d^2 := by
    convert hd2 using 1 ; norm_num [sevenNineDistanceLower]
  have h00 : (sevenNineRadial 4 0 0 : ℝ)^2 + (sevenNineRadial 5 1 0 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[73]! : ℝ) * (2 * (sevenNineRadial 4 0 0 : ℝ) * (sevenNineRadial 5 1 0 : ℝ)) := by
    have hq : (sevenNineRadial 4 0 0)^2 + (sevenNineRadial 5 1 0)^2 - sevenNineDistanceLower[18]!^2 ≤
        sevenNineCosUpper[73]! * (2 * sevenNineRadial 4 0 0 * sevenNineRadial 5 1 0) := by native_decide
    have hqR :
        (sevenNineRadial 4 0 0 : ℝ)^2 + (sevenNineRadial 5 1 0 : ℝ)^2 - (sevenNineDistanceLower[18]! : ℝ)^2 ≤
          (sevenNineCosUpper[73]! : ℝ) * (2 * (sevenNineRadial 4 0 0 : ℝ) * (sevenNineRadial 5 1 0 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 4 0 0 : ℝ)^2 + (sevenNineRadial 5 1 0 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 4 0 0 : ℝ)^2 + (sevenNineRadial 5 1 0 : ℝ)^2 - (sevenNineDistanceLower[18]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h01 : (sevenNineRadial 4 0 0 : ℝ)^2 + (sevenNineRadial 5 1 1 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[73]! : ℝ) * (2 * (sevenNineRadial 4 0 0 : ℝ) * (sevenNineRadial 5 1 1 : ℝ)) := by
    have hq : (sevenNineRadial 4 0 0)^2 + (sevenNineRadial 5 1 1)^2 - sevenNineDistanceLower[18]!^2 ≤
        sevenNineCosUpper[73]! * (2 * sevenNineRadial 4 0 0 * sevenNineRadial 5 1 1) := by native_decide
    have hqR :
        (sevenNineRadial 4 0 0 : ℝ)^2 + (sevenNineRadial 5 1 1 : ℝ)^2 - (sevenNineDistanceLower[18]! : ℝ)^2 ≤
          (sevenNineCosUpper[73]! : ℝ) * (2 * (sevenNineRadial 4 0 0 : ℝ) * (sevenNineRadial 5 1 1 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 4 0 0 : ℝ)^2 + (sevenNineRadial 5 1 1 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 4 0 0 : ℝ)^2 + (sevenNineRadial 5 1 1 : ℝ)^2 - (sevenNineDistanceLower[18]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h10 : (sevenNineRadial 4 0 1 : ℝ)^2 + (sevenNineRadial 5 1 0 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[73]! : ℝ) * (2 * (sevenNineRadial 4 0 1 : ℝ) * (sevenNineRadial 5 1 0 : ℝ)) := by
    have hq : (sevenNineRadial 4 0 1)^2 + (sevenNineRadial 5 1 0)^2 - sevenNineDistanceLower[18]!^2 ≤
        sevenNineCosUpper[73]! * (2 * sevenNineRadial 4 0 1 * sevenNineRadial 5 1 0) := by native_decide
    have hqR :
        (sevenNineRadial 4 0 1 : ℝ)^2 + (sevenNineRadial 5 1 0 : ℝ)^2 - (sevenNineDistanceLower[18]! : ℝ)^2 ≤
          (sevenNineCosUpper[73]! : ℝ) * (2 * (sevenNineRadial 4 0 1 : ℝ) * (sevenNineRadial 5 1 0 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 4 0 1 : ℝ)^2 + (sevenNineRadial 5 1 0 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 4 0 1 : ℝ)^2 + (sevenNineRadial 5 1 0 : ℝ)^2 - (sevenNineDistanceLower[18]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h11 : (sevenNineRadial 4 0 1 : ℝ)^2 + (sevenNineRadial 5 1 1 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[73]! : ℝ) * (2 * (sevenNineRadial 4 0 1 : ℝ) * (sevenNineRadial 5 1 1 : ℝ)) := by
    have hq : (sevenNineRadial 4 0 1)^2 + (sevenNineRadial 5 1 1)^2 - sevenNineDistanceLower[18]!^2 ≤
        sevenNineCosUpper[73]! * (2 * sevenNineRadial 4 0 1 * sevenNineRadial 5 1 1) := by native_decide
    have hqR :
        (sevenNineRadial 4 0 1 : ℝ)^2 + (sevenNineRadial 5 1 1 : ℝ)^2 - (sevenNineDistanceLower[18]! : ℝ)^2 ≤
          (sevenNineCosUpper[73]! : ℝ) * (2 * (sevenNineRadial 4 0 1 : ℝ) * (sevenNineRadial 5 1 1 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 4 0 1 : ℝ)^2 + (sevenNineRadial 5 1 1 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 4 0 1 : ℝ)^2 + (sevenNineRadial 5 1 1 : ℝ)^2 - (sevenNineDistanceLower[18]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have htouch := corner_touch_cosine_bound haL haU hbL hbU
    (by norm_num [sevenNineRadial, sevenNineRadialBounds])
    (by norm_num [sevenNineRadial, sevenNineRadialBounds]) h00 h01 h10 h11
  have hcos : (sevenNineCosUpper[73]! : ℝ) ≤ Real.cos ((156952375972214773305 : ℝ) / 100000000000000000000) := by
    apply lower_bound_of_taylor_error
      (cosine_taylor_ninety_six_remainder (a := 0) (b := 4) (x := ((156952375972214773305 : ℝ) / 100000000000000000000) )
        (by norm_num) (by constructor <;> norm_num [Real.pi_gt_d20, Real.pi_lt_four]))
    rw [cosine_taylor_ninety_six_at_zero (b := 4) (x := ((156952375972214773305 : ℝ) / 100000000000000000000)) (by norm_num)]
    have hp : (sevenNineCosUpper[73]! : Rat) + (((156952375972214773305 : Rat) / 100000000000000000000) : Rat)^97 / (Nat.factorial 96) ≤
        Finset.sum (Finset.range 49) (fun k => (-1 : Rat)^k * (((156952375972214773305 : Rat) / 100000000000000000000) : Rat)^(2*k) / Nat.factorial (2*k)) := by native_decide
    have hpR : (sevenNineCosUpper[73]! : ℝ) + ((156952375972214773305 : ℝ) / 100000000000000000000)^97 / (Nat.factorial 96) ≤
        Finset.sum (Finset.range 49) (fun k => (-1 : ℝ)^k * ((156952375972214773305 : ℝ) / 100000000000000000000)^(2*k) / Nat.factorial (2*k)) := by
      norm_num [sevenNineCosUpper, Finset.sum_range_succ]
    simpa [sub_zero] using hpR
  have hangle : ((156952375972214773305 : ℝ) / 100000000000000000000) ≤ Real.arccos (touchCosine a b (Real.sqrt 8 + Real.sqrt 9)) := by
    exact angle_lower_bound_of_cosine (by norm_num)
      (by
        calc
          ((156952375972214773305 : ℝ) / 100000000000000000000) ≤ (314159265358979323846 : ℝ) / 100000000000000000000 := by norm_num
          _ ≤ Real.pi := by
            have hpi := Real.pi_gt_d20.le
            norm_num at hpi ⊢
            exact hpi) (le_trans htouch hcos)
  have hdata : sevenNineAngleLower[73]! = ((156952375972214773305 : Rat) / 100000000000000000000) := by native_decide
  have hdataR : (sevenNineAngleLower[73]! : ℝ) = ((156952375972214773305 : ℝ) / 100000000000000000000) := by
    have h := congrArg (fun q : Rat => (q : ℝ)) hdata
    convert h using 1 ; norm_num
  rw [hdataR]
  exact hangle

theorem sevenNineAngle_4_5_1_0 {a b : ℝ}
    (haL : (sevenNineRadial 4 1 0 : ℝ) ≤ a) (haU : a ≤ (sevenNineRadial 4 1 1 : ℝ))
    (hbL : (sevenNineRadial 5 0 0 : ℝ) ≤ b) (hbU : b ≤ (sevenNineRadial 5 0 1 : ℝ)) :
    (sevenNineAngleLower[74]! : ℝ) ≤ Real.arccos (touchCosine a b (Real.sqrt 8 + Real.sqrt 9)) := by
  let d : ℝ := Real.sqrt 8 + Real.sqrt 9
  have hd' : (((5828427124746190097603377448419396157139343750753896146353359475981464956924214077700775068 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) : ℝ) ≤ d := by
    dsimp [d]
    have h := rat_sum_sqrt_lower (q := ((5828427124746190097603377448419396157139343750753896146353359475981464956924214077700775068 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (qi := ((2828427124746190097603377448419396157139343750753896146353359475981464956924214077700775068655283145470027692461824594049 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (qj := ((3 : Rat) / 1))
      (ni := 8) (nj := 9)
      (by convert sqrt_lower_8 using 1 ; norm_num)
      (by convert sqrt_lower_9 using 1 ; norm_num)
      (by native_decide)
    convert h using 1 ; norm_num
  have hd : (((5828427124746190097603377448419396157139343750753896146353359475981464956924214077700775068 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) ≤ d := by exact hd'
  have hd2 : (((5828427124746190097603377448419396157139343750753896146353359475981464956924214077700775068 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))^2 ≤ d^2 := by
    have hq : (0 : ℝ) ≤ ((5828427124746190097603377448419396157139343750753896146353359475981464956924214077700775068 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) := by norm_num
    have hdn : 0 ≤ d := by positivity
    exact (sq_le_sq₀ hq hdn).mpr hd
  have hd2' : (sevenNineDistanceLower[18]! : ℝ)^2 ≤ d^2 := by
    convert hd2 using 1 ; norm_num [sevenNineDistanceLower]
  have h00 : (sevenNineRadial 4 1 0 : ℝ)^2 + (sevenNineRadial 5 0 0 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[74]! : ℝ) * (2 * (sevenNineRadial 4 1 0 : ℝ) * (sevenNineRadial 5 0 0 : ℝ)) := by
    have hq : (sevenNineRadial 4 1 0)^2 + (sevenNineRadial 5 0 0)^2 - sevenNineDistanceLower[18]!^2 ≤
        sevenNineCosUpper[74]! * (2 * sevenNineRadial 4 1 0 * sevenNineRadial 5 0 0) := by native_decide
    have hqR :
        (sevenNineRadial 4 1 0 : ℝ)^2 + (sevenNineRadial 5 0 0 : ℝ)^2 - (sevenNineDistanceLower[18]! : ℝ)^2 ≤
          (sevenNineCosUpper[74]! : ℝ) * (2 * (sevenNineRadial 4 1 0 : ℝ) * (sevenNineRadial 5 0 0 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 4 1 0 : ℝ)^2 + (sevenNineRadial 5 0 0 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 4 1 0 : ℝ)^2 + (sevenNineRadial 5 0 0 : ℝ)^2 - (sevenNineDistanceLower[18]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h01 : (sevenNineRadial 4 1 0 : ℝ)^2 + (sevenNineRadial 5 0 1 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[74]! : ℝ) * (2 * (sevenNineRadial 4 1 0 : ℝ) * (sevenNineRadial 5 0 1 : ℝ)) := by
    have hq : (sevenNineRadial 4 1 0)^2 + (sevenNineRadial 5 0 1)^2 - sevenNineDistanceLower[18]!^2 ≤
        sevenNineCosUpper[74]! * (2 * sevenNineRadial 4 1 0 * sevenNineRadial 5 0 1) := by native_decide
    have hqR :
        (sevenNineRadial 4 1 0 : ℝ)^2 + (sevenNineRadial 5 0 1 : ℝ)^2 - (sevenNineDistanceLower[18]! : ℝ)^2 ≤
          (sevenNineCosUpper[74]! : ℝ) * (2 * (sevenNineRadial 4 1 0 : ℝ) * (sevenNineRadial 5 0 1 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 4 1 0 : ℝ)^2 + (sevenNineRadial 5 0 1 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 4 1 0 : ℝ)^2 + (sevenNineRadial 5 0 1 : ℝ)^2 - (sevenNineDistanceLower[18]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h10 : (sevenNineRadial 4 1 1 : ℝ)^2 + (sevenNineRadial 5 0 0 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[74]! : ℝ) * (2 * (sevenNineRadial 4 1 1 : ℝ) * (sevenNineRadial 5 0 0 : ℝ)) := by
    have hq : (sevenNineRadial 4 1 1)^2 + (sevenNineRadial 5 0 0)^2 - sevenNineDistanceLower[18]!^2 ≤
        sevenNineCosUpper[74]! * (2 * sevenNineRadial 4 1 1 * sevenNineRadial 5 0 0) := by native_decide
    have hqR :
        (sevenNineRadial 4 1 1 : ℝ)^2 + (sevenNineRadial 5 0 0 : ℝ)^2 - (sevenNineDistanceLower[18]! : ℝ)^2 ≤
          (sevenNineCosUpper[74]! : ℝ) * (2 * (sevenNineRadial 4 1 1 : ℝ) * (sevenNineRadial 5 0 0 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 4 1 1 : ℝ)^2 + (sevenNineRadial 5 0 0 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 4 1 1 : ℝ)^2 + (sevenNineRadial 5 0 0 : ℝ)^2 - (sevenNineDistanceLower[18]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h11 : (sevenNineRadial 4 1 1 : ℝ)^2 + (sevenNineRadial 5 0 1 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[74]! : ℝ) * (2 * (sevenNineRadial 4 1 1 : ℝ) * (sevenNineRadial 5 0 1 : ℝ)) := by
    have hq : (sevenNineRadial 4 1 1)^2 + (sevenNineRadial 5 0 1)^2 - sevenNineDistanceLower[18]!^2 ≤
        sevenNineCosUpper[74]! * (2 * sevenNineRadial 4 1 1 * sevenNineRadial 5 0 1) := by native_decide
    have hqR :
        (sevenNineRadial 4 1 1 : ℝ)^2 + (sevenNineRadial 5 0 1 : ℝ)^2 - (sevenNineDistanceLower[18]! : ℝ)^2 ≤
          (sevenNineCosUpper[74]! : ℝ) * (2 * (sevenNineRadial 4 1 1 : ℝ) * (sevenNineRadial 5 0 1 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 4 1 1 : ℝ)^2 + (sevenNineRadial 5 0 1 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 4 1 1 : ℝ)^2 + (sevenNineRadial 5 0 1 : ℝ)^2 - (sevenNineDistanceLower[18]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have htouch := corner_touch_cosine_bound haL haU hbL hbU
    (by norm_num [sevenNineRadial, sevenNineRadialBounds])
    (by norm_num [sevenNineRadial, sevenNineRadialBounds]) h00 h01 h10 h11
  have hcos : (sevenNineCosUpper[74]! : ℝ) ≤ Real.cos ((151620133771560493114 : ℝ) / 100000000000000000000) := by
    apply lower_bound_of_taylor_error
      (cosine_taylor_ninety_six_remainder (a := 0) (b := 4) (x := ((151620133771560493114 : ℝ) / 100000000000000000000) )
        (by norm_num) (by constructor <;> norm_num [Real.pi_gt_d20, Real.pi_lt_four]))
    rw [cosine_taylor_ninety_six_at_zero (b := 4) (x := ((151620133771560493114 : ℝ) / 100000000000000000000)) (by norm_num)]
    have hp : (sevenNineCosUpper[74]! : Rat) + (((151620133771560493114 : Rat) / 100000000000000000000) : Rat)^97 / (Nat.factorial 96) ≤
        Finset.sum (Finset.range 49) (fun k => (-1 : Rat)^k * (((151620133771560493114 : Rat) / 100000000000000000000) : Rat)^(2*k) / Nat.factorial (2*k)) := by native_decide
    have hpR : (sevenNineCosUpper[74]! : ℝ) + ((151620133771560493114 : ℝ) / 100000000000000000000)^97 / (Nat.factorial 96) ≤
        Finset.sum (Finset.range 49) (fun k => (-1 : ℝ)^k * ((151620133771560493114 : ℝ) / 100000000000000000000)^(2*k) / Nat.factorial (2*k)) := by
      norm_num [sevenNineCosUpper, Finset.sum_range_succ]
    simpa [sub_zero] using hpR
  have hangle : ((151620133771560493114 : ℝ) / 100000000000000000000) ≤ Real.arccos (touchCosine a b (Real.sqrt 8 + Real.sqrt 9)) := by
    exact angle_lower_bound_of_cosine (by norm_num)
      (by
        calc
          ((151620133771560493114 : ℝ) / 100000000000000000000) ≤ (314159265358979323846 : ℝ) / 100000000000000000000 := by norm_num
          _ ≤ Real.pi := by
            have hpi := Real.pi_gt_d20.le
            norm_num at hpi ⊢
            exact hpi) (le_trans htouch hcos)
  have hdata : sevenNineAngleLower[74]! = ((151620133771560493114 : Rat) / 100000000000000000000) := by native_decide
  have hdataR : (sevenNineAngleLower[74]! : ℝ) = ((151620133771560493114 : ℝ) / 100000000000000000000) := by
    have h := congrArg (fun q : Rat => (q : ℝ)) hdata
    convert h using 1 ; norm_num
  rw [hdataR]
  exact hangle

theorem sevenNineAngle_4_5_1_1 {a b : ℝ}
    (haL : (sevenNineRadial 4 1 0 : ℝ) ≤ a) (haU : a ≤ (sevenNineRadial 4 1 1 : ℝ))
    (hbL : (sevenNineRadial 5 1 0 : ℝ) ≤ b) (hbU : b ≤ (sevenNineRadial 5 1 1 : ℝ)) :
    (sevenNineAngleLower[75]! : ℝ) ≤ Real.arccos (touchCosine a b (Real.sqrt 8 + Real.sqrt 9)) := by
  let d : ℝ := Real.sqrt 8 + Real.sqrt 9
  have hd' : (((5828427124746190097603377448419396157139343750753896146353359475981464956924214077700775068 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) : ℝ) ≤ d := by
    dsimp [d]
    have h := rat_sum_sqrt_lower (q := ((5828427124746190097603377448419396157139343750753896146353359475981464956924214077700775068 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (qi := ((2828427124746190097603377448419396157139343750753896146353359475981464956924214077700775068655283145470027692461824594049 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (qj := ((3 : Rat) / 1))
      (ni := 8) (nj := 9)
      (by convert sqrt_lower_8 using 1 ; norm_num)
      (by convert sqrt_lower_9 using 1 ; norm_num)
      (by native_decide)
    convert h using 1 ; norm_num
  have hd : (((5828427124746190097603377448419396157139343750753896146353359475981464956924214077700775068 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) ≤ d := by exact hd'
  have hd2 : (((5828427124746190097603377448419396157139343750753896146353359475981464956924214077700775068 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))^2 ≤ d^2 := by
    have hq : (0 : ℝ) ≤ ((5828427124746190097603377448419396157139343750753896146353359475981464956924214077700775068 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) := by norm_num
    have hdn : 0 ≤ d := by positivity
    exact (sq_le_sq₀ hq hdn).mpr hd
  have hd2' : (sevenNineDistanceLower[18]! : ℝ)^2 ≤ d^2 := by
    convert hd2 using 1 ; norm_num [sevenNineDistanceLower]
  have h00 : (sevenNineRadial 4 1 0 : ℝ)^2 + (sevenNineRadial 5 1 0 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[75]! : ℝ) * (2 * (sevenNineRadial 4 1 0 : ℝ) * (sevenNineRadial 5 1 0 : ℝ)) := by
    have hq : (sevenNineRadial 4 1 0)^2 + (sevenNineRadial 5 1 0)^2 - sevenNineDistanceLower[18]!^2 ≤
        sevenNineCosUpper[75]! * (2 * sevenNineRadial 4 1 0 * sevenNineRadial 5 1 0) := by native_decide
    have hqR :
        (sevenNineRadial 4 1 0 : ℝ)^2 + (sevenNineRadial 5 1 0 : ℝ)^2 - (sevenNineDistanceLower[18]! : ℝ)^2 ≤
          (sevenNineCosUpper[75]! : ℝ) * (2 * (sevenNineRadial 4 1 0 : ℝ) * (sevenNineRadial 5 1 0 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 4 1 0 : ℝ)^2 + (sevenNineRadial 5 1 0 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 4 1 0 : ℝ)^2 + (sevenNineRadial 5 1 0 : ℝ)^2 - (sevenNineDistanceLower[18]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h01 : (sevenNineRadial 4 1 0 : ℝ)^2 + (sevenNineRadial 5 1 1 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[75]! : ℝ) * (2 * (sevenNineRadial 4 1 0 : ℝ) * (sevenNineRadial 5 1 1 : ℝ)) := by
    have hq : (sevenNineRadial 4 1 0)^2 + (sevenNineRadial 5 1 1)^2 - sevenNineDistanceLower[18]!^2 ≤
        sevenNineCosUpper[75]! * (2 * sevenNineRadial 4 1 0 * sevenNineRadial 5 1 1) := by native_decide
    have hqR :
        (sevenNineRadial 4 1 0 : ℝ)^2 + (sevenNineRadial 5 1 1 : ℝ)^2 - (sevenNineDistanceLower[18]! : ℝ)^2 ≤
          (sevenNineCosUpper[75]! : ℝ) * (2 * (sevenNineRadial 4 1 0 : ℝ) * (sevenNineRadial 5 1 1 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 4 1 0 : ℝ)^2 + (sevenNineRadial 5 1 1 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 4 1 0 : ℝ)^2 + (sevenNineRadial 5 1 1 : ℝ)^2 - (sevenNineDistanceLower[18]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h10 : (sevenNineRadial 4 1 1 : ℝ)^2 + (sevenNineRadial 5 1 0 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[75]! : ℝ) * (2 * (sevenNineRadial 4 1 1 : ℝ) * (sevenNineRadial 5 1 0 : ℝ)) := by
    have hq : (sevenNineRadial 4 1 1)^2 + (sevenNineRadial 5 1 0)^2 - sevenNineDistanceLower[18]!^2 ≤
        sevenNineCosUpper[75]! * (2 * sevenNineRadial 4 1 1 * sevenNineRadial 5 1 0) := by native_decide
    have hqR :
        (sevenNineRadial 4 1 1 : ℝ)^2 + (sevenNineRadial 5 1 0 : ℝ)^2 - (sevenNineDistanceLower[18]! : ℝ)^2 ≤
          (sevenNineCosUpper[75]! : ℝ) * (2 * (sevenNineRadial 4 1 1 : ℝ) * (sevenNineRadial 5 1 0 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 4 1 1 : ℝ)^2 + (sevenNineRadial 5 1 0 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 4 1 1 : ℝ)^2 + (sevenNineRadial 5 1 0 : ℝ)^2 - (sevenNineDistanceLower[18]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h11 : (sevenNineRadial 4 1 1 : ℝ)^2 + (sevenNineRadial 5 1 1 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[75]! : ℝ) * (2 * (sevenNineRadial 4 1 1 : ℝ) * (sevenNineRadial 5 1 1 : ℝ)) := by
    have hq : (sevenNineRadial 4 1 1)^2 + (sevenNineRadial 5 1 1)^2 - sevenNineDistanceLower[18]!^2 ≤
        sevenNineCosUpper[75]! * (2 * sevenNineRadial 4 1 1 * sevenNineRadial 5 1 1) := by native_decide
    have hqR :
        (sevenNineRadial 4 1 1 : ℝ)^2 + (sevenNineRadial 5 1 1 : ℝ)^2 - (sevenNineDistanceLower[18]! : ℝ)^2 ≤
          (sevenNineCosUpper[75]! : ℝ) * (2 * (sevenNineRadial 4 1 1 : ℝ) * (sevenNineRadial 5 1 1 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 4 1 1 : ℝ)^2 + (sevenNineRadial 5 1 1 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 4 1 1 : ℝ)^2 + (sevenNineRadial 5 1 1 : ℝ)^2 - (sevenNineDistanceLower[18]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have htouch := corner_touch_cosine_bound haL haU hbL hbU
    (by norm_num [sevenNineRadial, sevenNineRadialBounds])
    (by norm_num [sevenNineRadial, sevenNineRadialBounds]) h00 h01 h10 h11
  have hcos : (sevenNineCosUpper[75]! : ℝ) ≤ Real.cos ((124812684724736064540 : ℝ) / 100000000000000000000) := by
    apply lower_bound_of_taylor_error
      (cosine_taylor_ninety_six_remainder (a := 0) (b := 4) (x := ((124812684724736064540 : ℝ) / 100000000000000000000) )
        (by norm_num) (by constructor <;> norm_num [Real.pi_gt_d20, Real.pi_lt_four]))
    rw [cosine_taylor_ninety_six_at_zero (b := 4) (x := ((124812684724736064540 : ℝ) / 100000000000000000000)) (by norm_num)]
    have hp : (sevenNineCosUpper[75]! : Rat) + (((124812684724736064540 : Rat) / 100000000000000000000) : Rat)^97 / (Nat.factorial 96) ≤
        Finset.sum (Finset.range 49) (fun k => (-1 : Rat)^k * (((124812684724736064540 : Rat) / 100000000000000000000) : Rat)^(2*k) / Nat.factorial (2*k)) := by native_decide
    have hpR : (sevenNineCosUpper[75]! : ℝ) + ((124812684724736064540 : ℝ) / 100000000000000000000)^97 / (Nat.factorial 96) ≤
        Finset.sum (Finset.range 49) (fun k => (-1 : ℝ)^k * ((124812684724736064540 : ℝ) / 100000000000000000000)^(2*k) / Nat.factorial (2*k)) := by
      norm_num [sevenNineCosUpper, Finset.sum_range_succ]
    simpa [sub_zero] using hpR
  have hangle : ((124812684724736064540 : ℝ) / 100000000000000000000) ≤ Real.arccos (touchCosine a b (Real.sqrt 8 + Real.sqrt 9)) := by
    exact angle_lower_bound_of_cosine (by norm_num)
      (by
        calc
          ((124812684724736064540 : ℝ) / 100000000000000000000) ≤ (314159265358979323846 : ℝ) / 100000000000000000000 := by norm_num
          _ ≤ Real.pi := by
            have hpi := Real.pi_gt_d20.le
            norm_num at hpi ⊢
            exact hpi) (le_trans htouch hcos)
  have hdata : sevenNineAngleLower[75]! = ((124812684724736064540 : Rat) / 100000000000000000000) := by native_decide
  have hdataR : (sevenNineAngleLower[75]! : ℝ) = ((124812684724736064540 : ℝ) / 100000000000000000000) := by
    have h := congrArg (fun q : Rat => (q : ℝ)) hdata
    convert h using 1 ; norm_num
  rw [hdataR]
  exact hangle

theorem sevenNineAngle_4_6_0_0 {a b : ℝ}
    (haL : (sevenNineRadial 4 0 0 : ℝ) ≤ a) (haU : a ≤ (sevenNineRadial 4 0 1 : ℝ))
    (hbL : (sevenNineRadial 6 0 0 : ℝ) ≤ b) (hbU : b ≤ (sevenNineRadial 6 0 1 : ℝ)) :
    (sevenNineAngleLower[76]! : ℝ) ≤ Real.arccos (touchCosine a b (Real.sqrt 8 + Real.sqrt 10)) := by
  let d : ℝ := Real.sqrt 8 + Real.sqrt 10
  have hd' : (((5990704784914569429602270992852114690858898890079112973210864328774059395563452299045023177 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) : ℝ) ≤ d := by
    dsimp [d]
    have h := rat_sum_sqrt_lower (q := ((5990704784914569429602270992852114690858898890079112973210864328774059395563452299045023177 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (qi := ((2828427124746190097603377448419396157139343750753896146353359475981464956924214077700775068655283145470027692461824594049 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (qj := ((3162277660168379331998893544432718533719555139325216826857504852792594438639238221344248108379300295187347284152840055148 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))
      (ni := 8) (nj := 10)
      (by convert sqrt_lower_8 using 1 ; norm_num)
      (by convert sqrt_lower_10 using 1 ; norm_num)
      (by native_decide)
    convert h using 1 ; norm_num
  have hd : (((5990704784914569429602270992852114690858898890079112973210864328774059395563452299045023177 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) ≤ d := by exact hd'
  have hd2 : (((5990704784914569429602270992852114690858898890079112973210864328774059395563452299045023177 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))^2 ≤ d^2 := by
    have hq : (0 : ℝ) ≤ ((5990704784914569429602270992852114690858898890079112973210864328774059395563452299045023177 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) := by norm_num
    have hdn : 0 ≤ d := by positivity
    exact (sq_le_sq₀ hq hdn).mpr hd
  have hd2' : (sevenNineDistanceLower[19]! : ℝ)^2 ≤ d^2 := by
    convert hd2 using 1 ; norm_num [sevenNineDistanceLower]
  have h00 : (sevenNineRadial 4 0 0 : ℝ)^2 + (sevenNineRadial 6 0 0 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[76]! : ℝ) * (2 * (sevenNineRadial 4 0 0 : ℝ) * (sevenNineRadial 6 0 0 : ℝ)) := by
    have hq : (sevenNineRadial 4 0 0)^2 + (sevenNineRadial 6 0 0)^2 - sevenNineDistanceLower[19]!^2 ≤
        sevenNineCosUpper[76]! * (2 * sevenNineRadial 4 0 0 * sevenNineRadial 6 0 0) := by native_decide
    have hqR :
        (sevenNineRadial 4 0 0 : ℝ)^2 + (sevenNineRadial 6 0 0 : ℝ)^2 - (sevenNineDistanceLower[19]! : ℝ)^2 ≤
          (sevenNineCosUpper[76]! : ℝ) * (2 * (sevenNineRadial 4 0 0 : ℝ) * (sevenNineRadial 6 0 0 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 4 0 0 : ℝ)^2 + (sevenNineRadial 6 0 0 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 4 0 0 : ℝ)^2 + (sevenNineRadial 6 0 0 : ℝ)^2 - (sevenNineDistanceLower[19]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h01 : (sevenNineRadial 4 0 0 : ℝ)^2 + (sevenNineRadial 6 0 1 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[76]! : ℝ) * (2 * (sevenNineRadial 4 0 0 : ℝ) * (sevenNineRadial 6 0 1 : ℝ)) := by
    have hq : (sevenNineRadial 4 0 0)^2 + (sevenNineRadial 6 0 1)^2 - sevenNineDistanceLower[19]!^2 ≤
        sevenNineCosUpper[76]! * (2 * sevenNineRadial 4 0 0 * sevenNineRadial 6 0 1) := by native_decide
    have hqR :
        (sevenNineRadial 4 0 0 : ℝ)^2 + (sevenNineRadial 6 0 1 : ℝ)^2 - (sevenNineDistanceLower[19]! : ℝ)^2 ≤
          (sevenNineCosUpper[76]! : ℝ) * (2 * (sevenNineRadial 4 0 0 : ℝ) * (sevenNineRadial 6 0 1 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 4 0 0 : ℝ)^2 + (sevenNineRadial 6 0 1 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 4 0 0 : ℝ)^2 + (sevenNineRadial 6 0 1 : ℝ)^2 - (sevenNineDistanceLower[19]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h10 : (sevenNineRadial 4 0 1 : ℝ)^2 + (sevenNineRadial 6 0 0 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[76]! : ℝ) * (2 * (sevenNineRadial 4 0 1 : ℝ) * (sevenNineRadial 6 0 0 : ℝ)) := by
    have hq : (sevenNineRadial 4 0 1)^2 + (sevenNineRadial 6 0 0)^2 - sevenNineDistanceLower[19]!^2 ≤
        sevenNineCosUpper[76]! * (2 * sevenNineRadial 4 0 1 * sevenNineRadial 6 0 0) := by native_decide
    have hqR :
        (sevenNineRadial 4 0 1 : ℝ)^2 + (sevenNineRadial 6 0 0 : ℝ)^2 - (sevenNineDistanceLower[19]! : ℝ)^2 ≤
          (sevenNineCosUpper[76]! : ℝ) * (2 * (sevenNineRadial 4 0 1 : ℝ) * (sevenNineRadial 6 0 0 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 4 0 1 : ℝ)^2 + (sevenNineRadial 6 0 0 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 4 0 1 : ℝ)^2 + (sevenNineRadial 6 0 0 : ℝ)^2 - (sevenNineDistanceLower[19]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h11 : (sevenNineRadial 4 0 1 : ℝ)^2 + (sevenNineRadial 6 0 1 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[76]! : ℝ) * (2 * (sevenNineRadial 4 0 1 : ℝ) * (sevenNineRadial 6 0 1 : ℝ)) := by
    have hq : (sevenNineRadial 4 0 1)^2 + (sevenNineRadial 6 0 1)^2 - sevenNineDistanceLower[19]!^2 ≤
        sevenNineCosUpper[76]! * (2 * sevenNineRadial 4 0 1 * sevenNineRadial 6 0 1) := by native_decide
    have hqR :
        (sevenNineRadial 4 0 1 : ℝ)^2 + (sevenNineRadial 6 0 1 : ℝ)^2 - (sevenNineDistanceLower[19]! : ℝ)^2 ≤
          (sevenNineCosUpper[76]! : ℝ) * (2 * (sevenNineRadial 4 0 1 : ℝ) * (sevenNineRadial 6 0 1 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 4 0 1 : ℝ)^2 + (sevenNineRadial 6 0 1 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 4 0 1 : ℝ)^2 + (sevenNineRadial 6 0 1 : ℝ)^2 - (sevenNineDistanceLower[19]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have htouch := corner_touch_cosine_bound haL haU hbL hbU
    (by norm_num [sevenNineRadial, sevenNineRadialBounds])
    (by norm_num [sevenNineRadial, sevenNineRadialBounds]) h00 h01 h10 h11
  have hcos : (sevenNineCosUpper[76]! : ℝ) ≤ Real.cos ((266837054522455336411 : ℝ) / 100000000000000000000) := by
    apply lower_bound_of_taylor_error
      (cosine_taylor_ninety_six_remainder (a := 0) (b := 4) (x := ((266837054522455336411 : ℝ) / 100000000000000000000) )
        (by norm_num) (by constructor <;> norm_num [Real.pi_gt_d20, Real.pi_lt_four]))
    rw [cosine_taylor_ninety_six_at_zero (b := 4) (x := ((266837054522455336411 : ℝ) / 100000000000000000000)) (by norm_num)]
    have hp : (sevenNineCosUpper[76]! : Rat) + (((266837054522455336411 : Rat) / 100000000000000000000) : Rat)^97 / (Nat.factorial 96) ≤
        Finset.sum (Finset.range 49) (fun k => (-1 : Rat)^k * (((266837054522455336411 : Rat) / 100000000000000000000) : Rat)^(2*k) / Nat.factorial (2*k)) := by native_decide
    have hpR : (sevenNineCosUpper[76]! : ℝ) + ((266837054522455336411 : ℝ) / 100000000000000000000)^97 / (Nat.factorial 96) ≤
        Finset.sum (Finset.range 49) (fun k => (-1 : ℝ)^k * ((266837054522455336411 : ℝ) / 100000000000000000000)^(2*k) / Nat.factorial (2*k)) := by
      norm_num [sevenNineCosUpper, Finset.sum_range_succ]
    simpa [sub_zero] using hpR
  have hangle : ((266837054522455336411 : ℝ) / 100000000000000000000) ≤ Real.arccos (touchCosine a b (Real.sqrt 8 + Real.sqrt 10)) := by
    exact angle_lower_bound_of_cosine (by norm_num)
      (by
        calc
          ((266837054522455336411 : ℝ) / 100000000000000000000) ≤ (314159265358979323846 : ℝ) / 100000000000000000000 := by norm_num
          _ ≤ Real.pi := by
            have hpi := Real.pi_gt_d20.le
            norm_num at hpi ⊢
            exact hpi) (le_trans htouch hcos)
  have hdata : sevenNineAngleLower[76]! = ((266837054522455336411 : Rat) / 100000000000000000000) := by native_decide
  have hdataR : (sevenNineAngleLower[76]! : ℝ) = ((266837054522455336411 : ℝ) / 100000000000000000000) := by
    have h := congrArg (fun q : Rat => (q : ℝ)) hdata
    convert h using 1 ; norm_num
  rw [hdataR]
  exact hangle

theorem sevenNineAngle_4_6_0_1 {a b : ℝ}
    (haL : (sevenNineRadial 4 0 0 : ℝ) ≤ a) (haU : a ≤ (sevenNineRadial 4 0 1 : ℝ))
    (hbL : (sevenNineRadial 6 1 0 : ℝ) ≤ b) (hbU : b ≤ (sevenNineRadial 6 1 1 : ℝ)) :
    (sevenNineAngleLower[77]! : ℝ) ≤ Real.arccos (touchCosine a b (Real.sqrt 8 + Real.sqrt 10)) := by
  let d : ℝ := Real.sqrt 8 + Real.sqrt 10
  have hd' : (((5990704784914569429602270992852114690858898890079112973210864328774059395563452299045023177 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) : ℝ) ≤ d := by
    dsimp [d]
    have h := rat_sum_sqrt_lower (q := ((5990704784914569429602270992852114690858898890079112973210864328774059395563452299045023177 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (qi := ((2828427124746190097603377448419396157139343750753896146353359475981464956924214077700775068655283145470027692461824594049 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (qj := ((3162277660168379331998893544432718533719555139325216826857504852792594438639238221344248108379300295187347284152840055148 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))
      (ni := 8) (nj := 10)
      (by convert sqrt_lower_8 using 1 ; norm_num)
      (by convert sqrt_lower_10 using 1 ; norm_num)
      (by native_decide)
    convert h using 1 ; norm_num
  have hd : (((5990704784914569429602270992852114690858898890079112973210864328774059395563452299045023177 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) ≤ d := by exact hd'
  have hd2 : (((5990704784914569429602270992852114690858898890079112973210864328774059395563452299045023177 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))^2 ≤ d^2 := by
    have hq : (0 : ℝ) ≤ ((5990704784914569429602270992852114690858898890079112973210864328774059395563452299045023177 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) := by norm_num
    have hdn : 0 ≤ d := by positivity
    exact (sq_le_sq₀ hq hdn).mpr hd
  have hd2' : (sevenNineDistanceLower[19]! : ℝ)^2 ≤ d^2 := by
    convert hd2 using 1 ; norm_num [sevenNineDistanceLower]
  have h00 : (sevenNineRadial 4 0 0 : ℝ)^2 + (sevenNineRadial 6 1 0 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[77]! : ℝ) * (2 * (sevenNineRadial 4 0 0 : ℝ) * (sevenNineRadial 6 1 0 : ℝ)) := by
    have hq : (sevenNineRadial 4 0 0)^2 + (sevenNineRadial 6 1 0)^2 - sevenNineDistanceLower[19]!^2 ≤
        sevenNineCosUpper[77]! * (2 * sevenNineRadial 4 0 0 * sevenNineRadial 6 1 0) := by native_decide
    have hqR :
        (sevenNineRadial 4 0 0 : ℝ)^2 + (sevenNineRadial 6 1 0 : ℝ)^2 - (sevenNineDistanceLower[19]! : ℝ)^2 ≤
          (sevenNineCosUpper[77]! : ℝ) * (2 * (sevenNineRadial 4 0 0 : ℝ) * (sevenNineRadial 6 1 0 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 4 0 0 : ℝ)^2 + (sevenNineRadial 6 1 0 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 4 0 0 : ℝ)^2 + (sevenNineRadial 6 1 0 : ℝ)^2 - (sevenNineDistanceLower[19]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h01 : (sevenNineRadial 4 0 0 : ℝ)^2 + (sevenNineRadial 6 1 1 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[77]! : ℝ) * (2 * (sevenNineRadial 4 0 0 : ℝ) * (sevenNineRadial 6 1 1 : ℝ)) := by
    have hq : (sevenNineRadial 4 0 0)^2 + (sevenNineRadial 6 1 1)^2 - sevenNineDistanceLower[19]!^2 ≤
        sevenNineCosUpper[77]! * (2 * sevenNineRadial 4 0 0 * sevenNineRadial 6 1 1) := by native_decide
    have hqR :
        (sevenNineRadial 4 0 0 : ℝ)^2 + (sevenNineRadial 6 1 1 : ℝ)^2 - (sevenNineDistanceLower[19]! : ℝ)^2 ≤
          (sevenNineCosUpper[77]! : ℝ) * (2 * (sevenNineRadial 4 0 0 : ℝ) * (sevenNineRadial 6 1 1 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 4 0 0 : ℝ)^2 + (sevenNineRadial 6 1 1 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 4 0 0 : ℝ)^2 + (sevenNineRadial 6 1 1 : ℝ)^2 - (sevenNineDistanceLower[19]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h10 : (sevenNineRadial 4 0 1 : ℝ)^2 + (sevenNineRadial 6 1 0 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[77]! : ℝ) * (2 * (sevenNineRadial 4 0 1 : ℝ) * (sevenNineRadial 6 1 0 : ℝ)) := by
    have hq : (sevenNineRadial 4 0 1)^2 + (sevenNineRadial 6 1 0)^2 - sevenNineDistanceLower[19]!^2 ≤
        sevenNineCosUpper[77]! * (2 * sevenNineRadial 4 0 1 * sevenNineRadial 6 1 0) := by native_decide
    have hqR :
        (sevenNineRadial 4 0 1 : ℝ)^2 + (sevenNineRadial 6 1 0 : ℝ)^2 - (sevenNineDistanceLower[19]! : ℝ)^2 ≤
          (sevenNineCosUpper[77]! : ℝ) * (2 * (sevenNineRadial 4 0 1 : ℝ) * (sevenNineRadial 6 1 0 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 4 0 1 : ℝ)^2 + (sevenNineRadial 6 1 0 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 4 0 1 : ℝ)^2 + (sevenNineRadial 6 1 0 : ℝ)^2 - (sevenNineDistanceLower[19]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h11 : (sevenNineRadial 4 0 1 : ℝ)^2 + (sevenNineRadial 6 1 1 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[77]! : ℝ) * (2 * (sevenNineRadial 4 0 1 : ℝ) * (sevenNineRadial 6 1 1 : ℝ)) := by
    have hq : (sevenNineRadial 4 0 1)^2 + (sevenNineRadial 6 1 1)^2 - sevenNineDistanceLower[19]!^2 ≤
        sevenNineCosUpper[77]! * (2 * sevenNineRadial 4 0 1 * sevenNineRadial 6 1 1) := by native_decide
    have hqR :
        (sevenNineRadial 4 0 1 : ℝ)^2 + (sevenNineRadial 6 1 1 : ℝ)^2 - (sevenNineDistanceLower[19]! : ℝ)^2 ≤
          (sevenNineCosUpper[77]! : ℝ) * (2 * (sevenNineRadial 4 0 1 : ℝ) * (sevenNineRadial 6 1 1 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 4 0 1 : ℝ)^2 + (sevenNineRadial 6 1 1 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 4 0 1 : ℝ)^2 + (sevenNineRadial 6 1 1 : ℝ)^2 - (sevenNineDistanceLower[19]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have htouch := corner_touch_cosine_bound haL haU hbL hbU
    (by norm_num [sevenNineRadial, sevenNineRadialBounds])
    (by norm_num [sevenNineRadial, sevenNineRadialBounds]) h00 h01 h10 h11
  have hcos : (sevenNineCosUpper[77]! : ℝ) ≤ Real.cos ((168593953022461709426 : ℝ) / 100000000000000000000) := by
    apply lower_bound_of_taylor_error
      (cosine_taylor_ninety_six_remainder (a := 0) (b := 4) (x := ((168593953022461709426 : ℝ) / 100000000000000000000) )
        (by norm_num) (by constructor <;> norm_num [Real.pi_gt_d20, Real.pi_lt_four]))
    rw [cosine_taylor_ninety_six_at_zero (b := 4) (x := ((168593953022461709426 : ℝ) / 100000000000000000000)) (by norm_num)]
    have hp : (sevenNineCosUpper[77]! : Rat) + (((168593953022461709426 : Rat) / 100000000000000000000) : Rat)^97 / (Nat.factorial 96) ≤
        Finset.sum (Finset.range 49) (fun k => (-1 : Rat)^k * (((168593953022461709426 : Rat) / 100000000000000000000) : Rat)^(2*k) / Nat.factorial (2*k)) := by native_decide
    have hpR : (sevenNineCosUpper[77]! : ℝ) + ((168593953022461709426 : ℝ) / 100000000000000000000)^97 / (Nat.factorial 96) ≤
        Finset.sum (Finset.range 49) (fun k => (-1 : ℝ)^k * ((168593953022461709426 : ℝ) / 100000000000000000000)^(2*k) / Nat.factorial (2*k)) := by
      norm_num [sevenNineCosUpper, Finset.sum_range_succ]
    simpa [sub_zero] using hpR
  have hangle : ((168593953022461709426 : ℝ) / 100000000000000000000) ≤ Real.arccos (touchCosine a b (Real.sqrt 8 + Real.sqrt 10)) := by
    exact angle_lower_bound_of_cosine (by norm_num)
      (by
        calc
          ((168593953022461709426 : ℝ) / 100000000000000000000) ≤ (314159265358979323846 : ℝ) / 100000000000000000000 := by norm_num
          _ ≤ Real.pi := by
            have hpi := Real.pi_gt_d20.le
            norm_num at hpi ⊢
            exact hpi) (le_trans htouch hcos)
  have hdata : sevenNineAngleLower[77]! = ((168593953022461709426 : Rat) / 100000000000000000000) := by native_decide
  have hdataR : (sevenNineAngleLower[77]! : ℝ) = ((168593953022461709426 : ℝ) / 100000000000000000000) := by
    have h := congrArg (fun q : Rat => (q : ℝ)) hdata
    convert h using 1 ; norm_num
  rw [hdataR]
  exact hangle

theorem sevenNineAngle_4_6_1_0 {a b : ℝ}
    (haL : (sevenNineRadial 4 1 0 : ℝ) ≤ a) (haU : a ≤ (sevenNineRadial 4 1 1 : ℝ))
    (hbL : (sevenNineRadial 6 0 0 : ℝ) ≤ b) (hbU : b ≤ (sevenNineRadial 6 0 1 : ℝ)) :
    (sevenNineAngleLower[78]! : ℝ) ≤ Real.arccos (touchCosine a b (Real.sqrt 8 + Real.sqrt 10)) := by
  let d : ℝ := Real.sqrt 8 + Real.sqrt 10
  have hd' : (((5990704784914569429602270992852114690858898890079112973210864328774059395563452299045023177 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) : ℝ) ≤ d := by
    dsimp [d]
    have h := rat_sum_sqrt_lower (q := ((5990704784914569429602270992852114690858898890079112973210864328774059395563452299045023177 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (qi := ((2828427124746190097603377448419396157139343750753896146353359475981464956924214077700775068655283145470027692461824594049 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (qj := ((3162277660168379331998893544432718533719555139325216826857504852792594438639238221344248108379300295187347284152840055148 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))
      (ni := 8) (nj := 10)
      (by convert sqrt_lower_8 using 1 ; norm_num)
      (by convert sqrt_lower_10 using 1 ; norm_num)
      (by native_decide)
    convert h using 1 ; norm_num
  have hd : (((5990704784914569429602270992852114690858898890079112973210864328774059395563452299045023177 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) ≤ d := by exact hd'
  have hd2 : (((5990704784914569429602270992852114690858898890079112973210864328774059395563452299045023177 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))^2 ≤ d^2 := by
    have hq : (0 : ℝ) ≤ ((5990704784914569429602270992852114690858898890079112973210864328774059395563452299045023177 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) := by norm_num
    have hdn : 0 ≤ d := by positivity
    exact (sq_le_sq₀ hq hdn).mpr hd
  have hd2' : (sevenNineDistanceLower[19]! : ℝ)^2 ≤ d^2 := by
    convert hd2 using 1 ; norm_num [sevenNineDistanceLower]
  have h00 : (sevenNineRadial 4 1 0 : ℝ)^2 + (sevenNineRadial 6 0 0 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[78]! : ℝ) * (2 * (sevenNineRadial 4 1 0 : ℝ) * (sevenNineRadial 6 0 0 : ℝ)) := by
    have hq : (sevenNineRadial 4 1 0)^2 + (sevenNineRadial 6 0 0)^2 - sevenNineDistanceLower[19]!^2 ≤
        sevenNineCosUpper[78]! * (2 * sevenNineRadial 4 1 0 * sevenNineRadial 6 0 0) := by native_decide
    have hqR :
        (sevenNineRadial 4 1 0 : ℝ)^2 + (sevenNineRadial 6 0 0 : ℝ)^2 - (sevenNineDistanceLower[19]! : ℝ)^2 ≤
          (sevenNineCosUpper[78]! : ℝ) * (2 * (sevenNineRadial 4 1 0 : ℝ) * (sevenNineRadial 6 0 0 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 4 1 0 : ℝ)^2 + (sevenNineRadial 6 0 0 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 4 1 0 : ℝ)^2 + (sevenNineRadial 6 0 0 : ℝ)^2 - (sevenNineDistanceLower[19]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h01 : (sevenNineRadial 4 1 0 : ℝ)^2 + (sevenNineRadial 6 0 1 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[78]! : ℝ) * (2 * (sevenNineRadial 4 1 0 : ℝ) * (sevenNineRadial 6 0 1 : ℝ)) := by
    have hq : (sevenNineRadial 4 1 0)^2 + (sevenNineRadial 6 0 1)^2 - sevenNineDistanceLower[19]!^2 ≤
        sevenNineCosUpper[78]! * (2 * sevenNineRadial 4 1 0 * sevenNineRadial 6 0 1) := by native_decide
    have hqR :
        (sevenNineRadial 4 1 0 : ℝ)^2 + (sevenNineRadial 6 0 1 : ℝ)^2 - (sevenNineDistanceLower[19]! : ℝ)^2 ≤
          (sevenNineCosUpper[78]! : ℝ) * (2 * (sevenNineRadial 4 1 0 : ℝ) * (sevenNineRadial 6 0 1 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 4 1 0 : ℝ)^2 + (sevenNineRadial 6 0 1 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 4 1 0 : ℝ)^2 + (sevenNineRadial 6 0 1 : ℝ)^2 - (sevenNineDistanceLower[19]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h10 : (sevenNineRadial 4 1 1 : ℝ)^2 + (sevenNineRadial 6 0 0 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[78]! : ℝ) * (2 * (sevenNineRadial 4 1 1 : ℝ) * (sevenNineRadial 6 0 0 : ℝ)) := by
    have hq : (sevenNineRadial 4 1 1)^2 + (sevenNineRadial 6 0 0)^2 - sevenNineDistanceLower[19]!^2 ≤
        sevenNineCosUpper[78]! * (2 * sevenNineRadial 4 1 1 * sevenNineRadial 6 0 0) := by native_decide
    have hqR :
        (sevenNineRadial 4 1 1 : ℝ)^2 + (sevenNineRadial 6 0 0 : ℝ)^2 - (sevenNineDistanceLower[19]! : ℝ)^2 ≤
          (sevenNineCosUpper[78]! : ℝ) * (2 * (sevenNineRadial 4 1 1 : ℝ) * (sevenNineRadial 6 0 0 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 4 1 1 : ℝ)^2 + (sevenNineRadial 6 0 0 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 4 1 1 : ℝ)^2 + (sevenNineRadial 6 0 0 : ℝ)^2 - (sevenNineDistanceLower[19]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h11 : (sevenNineRadial 4 1 1 : ℝ)^2 + (sevenNineRadial 6 0 1 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[78]! : ℝ) * (2 * (sevenNineRadial 4 1 1 : ℝ) * (sevenNineRadial 6 0 1 : ℝ)) := by
    have hq : (sevenNineRadial 4 1 1)^2 + (sevenNineRadial 6 0 1)^2 - sevenNineDistanceLower[19]!^2 ≤
        sevenNineCosUpper[78]! * (2 * sevenNineRadial 4 1 1 * sevenNineRadial 6 0 1) := by native_decide
    have hqR :
        (sevenNineRadial 4 1 1 : ℝ)^2 + (sevenNineRadial 6 0 1 : ℝ)^2 - (sevenNineDistanceLower[19]! : ℝ)^2 ≤
          (sevenNineCosUpper[78]! : ℝ) * (2 * (sevenNineRadial 4 1 1 : ℝ) * (sevenNineRadial 6 0 1 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 4 1 1 : ℝ)^2 + (sevenNineRadial 6 0 1 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 4 1 1 : ℝ)^2 + (sevenNineRadial 6 0 1 : ℝ)^2 - (sevenNineDistanceLower[19]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have htouch := corner_touch_cosine_bound haL haU hbL hbU
    (by norm_num [sevenNineRadial, sevenNineRadialBounds])
    (by norm_num [sevenNineRadial, sevenNineRadialBounds]) h00 h01 h10 h11
  have hcos : (sevenNineCosUpper[78]! : ℝ) ≤ Real.cos ((160917952631491276186 : ℝ) / 100000000000000000000) := by
    apply lower_bound_of_taylor_error
      (cosine_taylor_ninety_six_remainder (a := 0) (b := 4) (x := ((160917952631491276186 : ℝ) / 100000000000000000000) )
        (by norm_num) (by constructor <;> norm_num [Real.pi_gt_d20, Real.pi_lt_four]))
    rw [cosine_taylor_ninety_six_at_zero (b := 4) (x := ((160917952631491276186 : ℝ) / 100000000000000000000)) (by norm_num)]
    have hp : (sevenNineCosUpper[78]! : Rat) + (((160917952631491276186 : Rat) / 100000000000000000000) : Rat)^97 / (Nat.factorial 96) ≤
        Finset.sum (Finset.range 49) (fun k => (-1 : Rat)^k * (((160917952631491276186 : Rat) / 100000000000000000000) : Rat)^(2*k) / Nat.factorial (2*k)) := by native_decide
    have hpR : (sevenNineCosUpper[78]! : ℝ) + ((160917952631491276186 : ℝ) / 100000000000000000000)^97 / (Nat.factorial 96) ≤
        Finset.sum (Finset.range 49) (fun k => (-1 : ℝ)^k * ((160917952631491276186 : ℝ) / 100000000000000000000)^(2*k) / Nat.factorial (2*k)) := by
      norm_num [sevenNineCosUpper, Finset.sum_range_succ]
    simpa [sub_zero] using hpR
  have hangle : ((160917952631491276186 : ℝ) / 100000000000000000000) ≤ Real.arccos (touchCosine a b (Real.sqrt 8 + Real.sqrt 10)) := by
    exact angle_lower_bound_of_cosine (by norm_num)
      (by
        calc
          ((160917952631491276186 : ℝ) / 100000000000000000000) ≤ (314159265358979323846 : ℝ) / 100000000000000000000 := by norm_num
          _ ≤ Real.pi := by
            have hpi := Real.pi_gt_d20.le
            norm_num at hpi ⊢
            exact hpi) (le_trans htouch hcos)
  have hdata : sevenNineAngleLower[78]! = ((160917952631491276186 : Rat) / 100000000000000000000) := by native_decide
  have hdataR : (sevenNineAngleLower[78]! : ℝ) = ((160917952631491276186 : ℝ) / 100000000000000000000) := by
    have h := congrArg (fun q : Rat => (q : ℝ)) hdata
    convert h using 1 ; norm_num
  rw [hdataR]
  exact hangle

theorem sevenNineAngle_4_6_1_1 {a b : ℝ}
    (haL : (sevenNineRadial 4 1 0 : ℝ) ≤ a) (haU : a ≤ (sevenNineRadial 4 1 1 : ℝ))
    (hbL : (sevenNineRadial 6 1 0 : ℝ) ≤ b) (hbU : b ≤ (sevenNineRadial 6 1 1 : ℝ)) :
    (sevenNineAngleLower[79]! : ℝ) ≤ Real.arccos (touchCosine a b (Real.sqrt 8 + Real.sqrt 10)) := by
  let d : ℝ := Real.sqrt 8 + Real.sqrt 10
  have hd' : (((5990704784914569429602270992852114690858898890079112973210864328774059395563452299045023177 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) : ℝ) ≤ d := by
    dsimp [d]
    have h := rat_sum_sqrt_lower (q := ((5990704784914569429602270992852114690858898890079112973210864328774059395563452299045023177 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (qi := ((2828427124746190097603377448419396157139343750753896146353359475981464956924214077700775068655283145470027692461824594049 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (qj := ((3162277660168379331998893544432718533719555139325216826857504852792594438639238221344248108379300295187347284152840055148 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))
      (ni := 8) (nj := 10)
      (by convert sqrt_lower_8 using 1 ; norm_num)
      (by convert sqrt_lower_10 using 1 ; norm_num)
      (by native_decide)
    convert h using 1 ; norm_num
  have hd : (((5990704784914569429602270992852114690858898890079112973210864328774059395563452299045023177 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) ≤ d := by exact hd'
  have hd2 : (((5990704784914569429602270992852114690858898890079112973210864328774059395563452299045023177 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))^2 ≤ d^2 := by
    have hq : (0 : ℝ) ≤ ((5990704784914569429602270992852114690858898890079112973210864328774059395563452299045023177 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) := by norm_num
    have hdn : 0 ≤ d := by positivity
    exact (sq_le_sq₀ hq hdn).mpr hd
  have hd2' : (sevenNineDistanceLower[19]! : ℝ)^2 ≤ d^2 := by
    convert hd2 using 1 ; norm_num [sevenNineDistanceLower]
  have h00 : (sevenNineRadial 4 1 0 : ℝ)^2 + (sevenNineRadial 6 1 0 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[79]! : ℝ) * (2 * (sevenNineRadial 4 1 0 : ℝ) * (sevenNineRadial 6 1 0 : ℝ)) := by
    have hq : (sevenNineRadial 4 1 0)^2 + (sevenNineRadial 6 1 0)^2 - sevenNineDistanceLower[19]!^2 ≤
        sevenNineCosUpper[79]! * (2 * sevenNineRadial 4 1 0 * sevenNineRadial 6 1 0) := by native_decide
    have hqR :
        (sevenNineRadial 4 1 0 : ℝ)^2 + (sevenNineRadial 6 1 0 : ℝ)^2 - (sevenNineDistanceLower[19]! : ℝ)^2 ≤
          (sevenNineCosUpper[79]! : ℝ) * (2 * (sevenNineRadial 4 1 0 : ℝ) * (sevenNineRadial 6 1 0 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 4 1 0 : ℝ)^2 + (sevenNineRadial 6 1 0 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 4 1 0 : ℝ)^2 + (sevenNineRadial 6 1 0 : ℝ)^2 - (sevenNineDistanceLower[19]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h01 : (sevenNineRadial 4 1 0 : ℝ)^2 + (sevenNineRadial 6 1 1 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[79]! : ℝ) * (2 * (sevenNineRadial 4 1 0 : ℝ) * (sevenNineRadial 6 1 1 : ℝ)) := by
    have hq : (sevenNineRadial 4 1 0)^2 + (sevenNineRadial 6 1 1)^2 - sevenNineDistanceLower[19]!^2 ≤
        sevenNineCosUpper[79]! * (2 * sevenNineRadial 4 1 0 * sevenNineRadial 6 1 1) := by native_decide
    have hqR :
        (sevenNineRadial 4 1 0 : ℝ)^2 + (sevenNineRadial 6 1 1 : ℝ)^2 - (sevenNineDistanceLower[19]! : ℝ)^2 ≤
          (sevenNineCosUpper[79]! : ℝ) * (2 * (sevenNineRadial 4 1 0 : ℝ) * (sevenNineRadial 6 1 1 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 4 1 0 : ℝ)^2 + (sevenNineRadial 6 1 1 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 4 1 0 : ℝ)^2 + (sevenNineRadial 6 1 1 : ℝ)^2 - (sevenNineDistanceLower[19]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h10 : (sevenNineRadial 4 1 1 : ℝ)^2 + (sevenNineRadial 6 1 0 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[79]! : ℝ) * (2 * (sevenNineRadial 4 1 1 : ℝ) * (sevenNineRadial 6 1 0 : ℝ)) := by
    have hq : (sevenNineRadial 4 1 1)^2 + (sevenNineRadial 6 1 0)^2 - sevenNineDistanceLower[19]!^2 ≤
        sevenNineCosUpper[79]! * (2 * sevenNineRadial 4 1 1 * sevenNineRadial 6 1 0) := by native_decide
    have hqR :
        (sevenNineRadial 4 1 1 : ℝ)^2 + (sevenNineRadial 6 1 0 : ℝ)^2 - (sevenNineDistanceLower[19]! : ℝ)^2 ≤
          (sevenNineCosUpper[79]! : ℝ) * (2 * (sevenNineRadial 4 1 1 : ℝ) * (sevenNineRadial 6 1 0 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 4 1 1 : ℝ)^2 + (sevenNineRadial 6 1 0 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 4 1 1 : ℝ)^2 + (sevenNineRadial 6 1 0 : ℝ)^2 - (sevenNineDistanceLower[19]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h11 : (sevenNineRadial 4 1 1 : ℝ)^2 + (sevenNineRadial 6 1 1 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[79]! : ℝ) * (2 * (sevenNineRadial 4 1 1 : ℝ) * (sevenNineRadial 6 1 1 : ℝ)) := by
    have hq : (sevenNineRadial 4 1 1)^2 + (sevenNineRadial 6 1 1)^2 - sevenNineDistanceLower[19]!^2 ≤
        sevenNineCosUpper[79]! * (2 * sevenNineRadial 4 1 1 * sevenNineRadial 6 1 1) := by native_decide
    have hqR :
        (sevenNineRadial 4 1 1 : ℝ)^2 + (sevenNineRadial 6 1 1 : ℝ)^2 - (sevenNineDistanceLower[19]! : ℝ)^2 ≤
          (sevenNineCosUpper[79]! : ℝ) * (2 * (sevenNineRadial 4 1 1 : ℝ) * (sevenNineRadial 6 1 1 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 4 1 1 : ℝ)^2 + (sevenNineRadial 6 1 1 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 4 1 1 : ℝ)^2 + (sevenNineRadial 6 1 1 : ℝ)^2 - (sevenNineDistanceLower[19]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have htouch := corner_touch_cosine_bound haL haU hbL hbU
    (by norm_num [sevenNineRadial, sevenNineRadialBounds])
    (by norm_num [sevenNineRadial, sevenNineRadialBounds]) h00 h01 h10 h11
  have hcos : (sevenNineCosUpper[79]! : ℝ) ≤ Real.cos ((131242796857645825448 : ℝ) / 100000000000000000000) := by
    apply lower_bound_of_taylor_error
      (cosine_taylor_ninety_six_remainder (a := 0) (b := 4) (x := ((131242796857645825448 : ℝ) / 100000000000000000000) )
        (by norm_num) (by constructor <;> norm_num [Real.pi_gt_d20, Real.pi_lt_four]))
    rw [cosine_taylor_ninety_six_at_zero (b := 4) (x := ((131242796857645825448 : ℝ) / 100000000000000000000)) (by norm_num)]
    have hp : (sevenNineCosUpper[79]! : Rat) + (((131242796857645825448 : Rat) / 100000000000000000000) : Rat)^97 / (Nat.factorial 96) ≤
        Finset.sum (Finset.range 49) (fun k => (-1 : Rat)^k * (((131242796857645825448 : Rat) / 100000000000000000000) : Rat)^(2*k) / Nat.factorial (2*k)) := by native_decide
    have hpR : (sevenNineCosUpper[79]! : ℝ) + ((131242796857645825448 : ℝ) / 100000000000000000000)^97 / (Nat.factorial 96) ≤
        Finset.sum (Finset.range 49) (fun k => (-1 : ℝ)^k * ((131242796857645825448 : ℝ) / 100000000000000000000)^(2*k) / Nat.factorial (2*k)) := by
      norm_num [sevenNineCosUpper, Finset.sum_range_succ]
    simpa [sub_zero] using hpR
  have hangle : ((131242796857645825448 : ℝ) / 100000000000000000000) ≤ Real.arccos (touchCosine a b (Real.sqrt 8 + Real.sqrt 10)) := by
    exact angle_lower_bound_of_cosine (by norm_num)
      (by
        calc
          ((131242796857645825448 : ℝ) / 100000000000000000000) ≤ (314159265358979323846 : ℝ) / 100000000000000000000 := by norm_num
          _ ≤ Real.pi := by
            have hpi := Real.pi_gt_d20.le
            norm_num at hpi ⊢
            exact hpi) (le_trans htouch hcos)
  have hdata : sevenNineAngleLower[79]! = ((131242796857645825448 : Rat) / 100000000000000000000) := by native_decide
  have hdataR : (sevenNineAngleLower[79]! : ℝ) = ((131242796857645825448 : ℝ) / 100000000000000000000) := by
    have h := congrArg (fun q : Rat => (q : ℝ)) hdata
    convert h using 1 ; norm_num
  rw [hdataR]
  exact hangle

theorem sevenNineAngle_5_6_0_0 {a b : ℝ}
    (haL : (sevenNineRadial 5 0 0 : ℝ) ≤ a) (haU : a ≤ (sevenNineRadial 5 0 1 : ℝ))
    (hbL : (sevenNineRadial 6 0 0 : ℝ) ≤ b) (hbU : b ≤ (sevenNineRadial 6 0 1 : ℝ)) :
    (sevenNineAngleLower[80]! : ℝ) ≤ Real.arccos (touchCosine a b (Real.sqrt 9 + Real.sqrt 10)) := by
  let d : ℝ := Real.sqrt 9 + Real.sqrt 10
  have hd' : (((6162277660168379331998893544432718533719555139325216826857504852792594438639238221344248108 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) : ℝ) ≤ d := by
    dsimp [d]
    have h := rat_sum_sqrt_lower (q := ((6162277660168379331998893544432718533719555139325216826857504852792594438639238221344248108 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (qi := ((3 : Rat) / 1)) (qj := ((3162277660168379331998893544432718533719555139325216826857504852792594438639238221344248108379300295187347284152840055148 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))
      (ni := 9) (nj := 10)
      (by convert sqrt_lower_9 using 1 ; norm_num)
      (by convert sqrt_lower_10 using 1 ; norm_num)
      (by native_decide)
    convert h using 1 ; norm_num
  have hd : (((6162277660168379331998893544432718533719555139325216826857504852792594438639238221344248108 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) ≤ d := by exact hd'
  have hd2 : (((6162277660168379331998893544432718533719555139325216826857504852792594438639238221344248108 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))^2 ≤ d^2 := by
    have hq : (0 : ℝ) ≤ ((6162277660168379331998893544432718533719555139325216826857504852792594438639238221344248108 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) := by norm_num
    have hdn : 0 ≤ d := by positivity
    exact (sq_le_sq₀ hq hdn).mpr hd
  have hd2' : (sevenNineDistanceLower[20]! : ℝ)^2 ≤ d^2 := by
    convert hd2 using 1 ; norm_num [sevenNineDistanceLower]
  have h00 : (sevenNineRadial 5 0 0 : ℝ)^2 + (sevenNineRadial 6 0 0 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[80]! : ℝ) * (2 * (sevenNineRadial 5 0 0 : ℝ) * (sevenNineRadial 6 0 0 : ℝ)) := by
    have hq : (sevenNineRadial 5 0 0)^2 + (sevenNineRadial 6 0 0)^2 - sevenNineDistanceLower[20]!^2 ≤
        sevenNineCosUpper[80]! * (2 * sevenNineRadial 5 0 0 * sevenNineRadial 6 0 0) := by native_decide
    have hqR :
        (sevenNineRadial 5 0 0 : ℝ)^2 + (sevenNineRadial 6 0 0 : ℝ)^2 - (sevenNineDistanceLower[20]! : ℝ)^2 ≤
          (sevenNineCosUpper[80]! : ℝ) * (2 * (sevenNineRadial 5 0 0 : ℝ) * (sevenNineRadial 6 0 0 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 5 0 0 : ℝ)^2 + (sevenNineRadial 6 0 0 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 5 0 0 : ℝ)^2 + (sevenNineRadial 6 0 0 : ℝ)^2 - (sevenNineDistanceLower[20]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h01 : (sevenNineRadial 5 0 0 : ℝ)^2 + (sevenNineRadial 6 0 1 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[80]! : ℝ) * (2 * (sevenNineRadial 5 0 0 : ℝ) * (sevenNineRadial 6 0 1 : ℝ)) := by
    have hq : (sevenNineRadial 5 0 0)^2 + (sevenNineRadial 6 0 1)^2 - sevenNineDistanceLower[20]!^2 ≤
        sevenNineCosUpper[80]! * (2 * sevenNineRadial 5 0 0 * sevenNineRadial 6 0 1) := by native_decide
    have hqR :
        (sevenNineRadial 5 0 0 : ℝ)^2 + (sevenNineRadial 6 0 1 : ℝ)^2 - (sevenNineDistanceLower[20]! : ℝ)^2 ≤
          (sevenNineCosUpper[80]! : ℝ) * (2 * (sevenNineRadial 5 0 0 : ℝ) * (sevenNineRadial 6 0 1 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 5 0 0 : ℝ)^2 + (sevenNineRadial 6 0 1 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 5 0 0 : ℝ)^2 + (sevenNineRadial 6 0 1 : ℝ)^2 - (sevenNineDistanceLower[20]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h10 : (sevenNineRadial 5 0 1 : ℝ)^2 + (sevenNineRadial 6 0 0 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[80]! : ℝ) * (2 * (sevenNineRadial 5 0 1 : ℝ) * (sevenNineRadial 6 0 0 : ℝ)) := by
    have hq : (sevenNineRadial 5 0 1)^2 + (sevenNineRadial 6 0 0)^2 - sevenNineDistanceLower[20]!^2 ≤
        sevenNineCosUpper[80]! * (2 * sevenNineRadial 5 0 1 * sevenNineRadial 6 0 0) := by native_decide
    have hqR :
        (sevenNineRadial 5 0 1 : ℝ)^2 + (sevenNineRadial 6 0 0 : ℝ)^2 - (sevenNineDistanceLower[20]! : ℝ)^2 ≤
          (sevenNineCosUpper[80]! : ℝ) * (2 * (sevenNineRadial 5 0 1 : ℝ) * (sevenNineRadial 6 0 0 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 5 0 1 : ℝ)^2 + (sevenNineRadial 6 0 0 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 5 0 1 : ℝ)^2 + (sevenNineRadial 6 0 0 : ℝ)^2 - (sevenNineDistanceLower[20]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h11 : (sevenNineRadial 5 0 1 : ℝ)^2 + (sevenNineRadial 6 0 1 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[80]! : ℝ) * (2 * (sevenNineRadial 5 0 1 : ℝ) * (sevenNineRadial 6 0 1 : ℝ)) := by
    have hq : (sevenNineRadial 5 0 1)^2 + (sevenNineRadial 6 0 1)^2 - sevenNineDistanceLower[20]!^2 ≤
        sevenNineCosUpper[80]! * (2 * sevenNineRadial 5 0 1 * sevenNineRadial 6 0 1) := by native_decide
    have hqR :
        (sevenNineRadial 5 0 1 : ℝ)^2 + (sevenNineRadial 6 0 1 : ℝ)^2 - (sevenNineDistanceLower[20]! : ℝ)^2 ≤
          (sevenNineCosUpper[80]! : ℝ) * (2 * (sevenNineRadial 5 0 1 : ℝ) * (sevenNineRadial 6 0 1 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 5 0 1 : ℝ)^2 + (sevenNineRadial 6 0 1 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 5 0 1 : ℝ)^2 + (sevenNineRadial 6 0 1 : ℝ)^2 - (sevenNineDistanceLower[20]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have htouch := corner_touch_cosine_bound haL haU hbL hbU
    (by norm_num [sevenNineRadial, sevenNineRadialBounds])
    (by norm_num [sevenNineRadial, sevenNineRadialBounds]) h00 h01 h10 h11
  have hcos : (sevenNineCosUpper[80]! : ℝ) ≤ Real.cos ((314159265358979323846 : ℝ) / 100000000000000000000) := by
    apply lower_bound_of_taylor_error
      (cosine_taylor_ninety_six_remainder (a := 0) (b := 4) (x := ((314159265358979323846 : ℝ) / 100000000000000000000) )
        (by norm_num) (by constructor <;> norm_num [Real.pi_gt_d20, Real.pi_lt_four]))
    rw [cosine_taylor_ninety_six_at_zero (b := 4) (x := ((314159265358979323846 : ℝ) / 100000000000000000000)) (by norm_num)]
    have hp : (sevenNineCosUpper[80]! : Rat) + (((314159265358979323846 : Rat) / 100000000000000000000) : Rat)^97 / (Nat.factorial 96) ≤
        Finset.sum (Finset.range 49) (fun k => (-1 : Rat)^k * (((314159265358979323846 : Rat) / 100000000000000000000) : Rat)^(2*k) / Nat.factorial (2*k)) := by native_decide
    have hpR : (sevenNineCosUpper[80]! : ℝ) + ((314159265358979323846 : ℝ) / 100000000000000000000)^97 / (Nat.factorial 96) ≤
        Finset.sum (Finset.range 49) (fun k => (-1 : ℝ)^k * ((314159265358979323846 : ℝ) / 100000000000000000000)^(2*k) / Nat.factorial (2*k)) := by
      norm_num [sevenNineCosUpper, Finset.sum_range_succ]
    simpa [sub_zero] using hpR
  have hangle : ((314159265358979323846 : ℝ) / 100000000000000000000) ≤ Real.arccos (touchCosine a b (Real.sqrt 9 + Real.sqrt 10)) := by
    exact angle_lower_bound_of_cosine (by norm_num)
      (by
        calc
          ((314159265358979323846 : ℝ) / 100000000000000000000) ≤ (314159265358979323846 : ℝ) / 100000000000000000000 := by norm_num
          _ ≤ Real.pi := by
            have hpi := Real.pi_gt_d20.le
            norm_num at hpi ⊢
            exact hpi) (le_trans htouch hcos)
  have hdata : sevenNineAngleLower[80]! = ((314159265358979323846 : Rat) / 100000000000000000000) := by native_decide
  have hdataR : (sevenNineAngleLower[80]! : ℝ) = ((314159265358979323846 : ℝ) / 100000000000000000000) := by
    have h := congrArg (fun q : Rat => (q : ℝ)) hdata
    convert h using 1 ; norm_num
  rw [hdataR]
  exact hangle

theorem sevenNineAngle_5_6_0_1 {a b : ℝ}
    (haL : (sevenNineRadial 5 0 0 : ℝ) ≤ a) (haU : a ≤ (sevenNineRadial 5 0 1 : ℝ))
    (hbL : (sevenNineRadial 6 1 0 : ℝ) ≤ b) (hbU : b ≤ (sevenNineRadial 6 1 1 : ℝ)) :
    (sevenNineAngleLower[81]! : ℝ) ≤ Real.arccos (touchCosine a b (Real.sqrt 9 + Real.sqrt 10)) := by
  let d : ℝ := Real.sqrt 9 + Real.sqrt 10
  have hd' : (((6162277660168379331998893544432718533719555139325216826857504852792594438639238221344248108 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) : ℝ) ≤ d := by
    dsimp [d]
    have h := rat_sum_sqrt_lower (q := ((6162277660168379331998893544432718533719555139325216826857504852792594438639238221344248108 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (qi := ((3 : Rat) / 1)) (qj := ((3162277660168379331998893544432718533719555139325216826857504852792594438639238221344248108379300295187347284152840055148 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))
      (ni := 9) (nj := 10)
      (by convert sqrt_lower_9 using 1 ; norm_num)
      (by convert sqrt_lower_10 using 1 ; norm_num)
      (by native_decide)
    convert h using 1 ; norm_num
  have hd : (((6162277660168379331998893544432718533719555139325216826857504852792594438639238221344248108 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) ≤ d := by exact hd'
  have hd2 : (((6162277660168379331998893544432718533719555139325216826857504852792594438639238221344248108 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))^2 ≤ d^2 := by
    have hq : (0 : ℝ) ≤ ((6162277660168379331998893544432718533719555139325216826857504852792594438639238221344248108 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) := by norm_num
    have hdn : 0 ≤ d := by positivity
    exact (sq_le_sq₀ hq hdn).mpr hd
  have hd2' : (sevenNineDistanceLower[20]! : ℝ)^2 ≤ d^2 := by
    convert hd2 using 1 ; norm_num [sevenNineDistanceLower]
  have h00 : (sevenNineRadial 5 0 0 : ℝ)^2 + (sevenNineRadial 6 1 0 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[81]! : ℝ) * (2 * (sevenNineRadial 5 0 0 : ℝ) * (sevenNineRadial 6 1 0 : ℝ)) := by
    have hq : (sevenNineRadial 5 0 0)^2 + (sevenNineRadial 6 1 0)^2 - sevenNineDistanceLower[20]!^2 ≤
        sevenNineCosUpper[81]! * (2 * sevenNineRadial 5 0 0 * sevenNineRadial 6 1 0) := by native_decide
    have hqR :
        (sevenNineRadial 5 0 0 : ℝ)^2 + (sevenNineRadial 6 1 0 : ℝ)^2 - (sevenNineDistanceLower[20]! : ℝ)^2 ≤
          (sevenNineCosUpper[81]! : ℝ) * (2 * (sevenNineRadial 5 0 0 : ℝ) * (sevenNineRadial 6 1 0 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 5 0 0 : ℝ)^2 + (sevenNineRadial 6 1 0 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 5 0 0 : ℝ)^2 + (sevenNineRadial 6 1 0 : ℝ)^2 - (sevenNineDistanceLower[20]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h01 : (sevenNineRadial 5 0 0 : ℝ)^2 + (sevenNineRadial 6 1 1 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[81]! : ℝ) * (2 * (sevenNineRadial 5 0 0 : ℝ) * (sevenNineRadial 6 1 1 : ℝ)) := by
    have hq : (sevenNineRadial 5 0 0)^2 + (sevenNineRadial 6 1 1)^2 - sevenNineDistanceLower[20]!^2 ≤
        sevenNineCosUpper[81]! * (2 * sevenNineRadial 5 0 0 * sevenNineRadial 6 1 1) := by native_decide
    have hqR :
        (sevenNineRadial 5 0 0 : ℝ)^2 + (sevenNineRadial 6 1 1 : ℝ)^2 - (sevenNineDistanceLower[20]! : ℝ)^2 ≤
          (sevenNineCosUpper[81]! : ℝ) * (2 * (sevenNineRadial 5 0 0 : ℝ) * (sevenNineRadial 6 1 1 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 5 0 0 : ℝ)^2 + (sevenNineRadial 6 1 1 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 5 0 0 : ℝ)^2 + (sevenNineRadial 6 1 1 : ℝ)^2 - (sevenNineDistanceLower[20]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h10 : (sevenNineRadial 5 0 1 : ℝ)^2 + (sevenNineRadial 6 1 0 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[81]! : ℝ) * (2 * (sevenNineRadial 5 0 1 : ℝ) * (sevenNineRadial 6 1 0 : ℝ)) := by
    have hq : (sevenNineRadial 5 0 1)^2 + (sevenNineRadial 6 1 0)^2 - sevenNineDistanceLower[20]!^2 ≤
        sevenNineCosUpper[81]! * (2 * sevenNineRadial 5 0 1 * sevenNineRadial 6 1 0) := by native_decide
    have hqR :
        (sevenNineRadial 5 0 1 : ℝ)^2 + (sevenNineRadial 6 1 0 : ℝ)^2 - (sevenNineDistanceLower[20]! : ℝ)^2 ≤
          (sevenNineCosUpper[81]! : ℝ) * (2 * (sevenNineRadial 5 0 1 : ℝ) * (sevenNineRadial 6 1 0 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 5 0 1 : ℝ)^2 + (sevenNineRadial 6 1 0 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 5 0 1 : ℝ)^2 + (sevenNineRadial 6 1 0 : ℝ)^2 - (sevenNineDistanceLower[20]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h11 : (sevenNineRadial 5 0 1 : ℝ)^2 + (sevenNineRadial 6 1 1 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[81]! : ℝ) * (2 * (sevenNineRadial 5 0 1 : ℝ) * (sevenNineRadial 6 1 1 : ℝ)) := by
    have hq : (sevenNineRadial 5 0 1)^2 + (sevenNineRadial 6 1 1)^2 - sevenNineDistanceLower[20]!^2 ≤
        sevenNineCosUpper[81]! * (2 * sevenNineRadial 5 0 1 * sevenNineRadial 6 1 1) := by native_decide
    have hqR :
        (sevenNineRadial 5 0 1 : ℝ)^2 + (sevenNineRadial 6 1 1 : ℝ)^2 - (sevenNineDistanceLower[20]! : ℝ)^2 ≤
          (sevenNineCosUpper[81]! : ℝ) * (2 * (sevenNineRadial 5 0 1 : ℝ) * (sevenNineRadial 6 1 1 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 5 0 1 : ℝ)^2 + (sevenNineRadial 6 1 1 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 5 0 1 : ℝ)^2 + (sevenNineRadial 6 1 1 : ℝ)^2 - (sevenNineDistanceLower[20]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have htouch := corner_touch_cosine_bound haL haU hbL hbU
    (by norm_num [sevenNineRadial, sevenNineRadialBounds])
    (by norm_num [sevenNineRadial, sevenNineRadialBounds]) h00 h01 h10 h11
  have hcos : (sevenNineCosUpper[81]! : ℝ) ≤ Real.cos ((175633557293333229060 : ℝ) / 100000000000000000000) := by
    apply lower_bound_of_taylor_error
      (cosine_taylor_ninety_six_remainder (a := 0) (b := 4) (x := ((175633557293333229060 : ℝ) / 100000000000000000000) )
        (by norm_num) (by constructor <;> norm_num [Real.pi_gt_d20, Real.pi_lt_four]))
    rw [cosine_taylor_ninety_six_at_zero (b := 4) (x := ((175633557293333229060 : ℝ) / 100000000000000000000)) (by norm_num)]
    have hp : (sevenNineCosUpper[81]! : Rat) + (((175633557293333229060 : Rat) / 100000000000000000000) : Rat)^97 / (Nat.factorial 96) ≤
        Finset.sum (Finset.range 49) (fun k => (-1 : Rat)^k * (((175633557293333229060 : Rat) / 100000000000000000000) : Rat)^(2*k) / Nat.factorial (2*k)) := by native_decide
    have hpR : (sevenNineCosUpper[81]! : ℝ) + ((175633557293333229060 : ℝ) / 100000000000000000000)^97 / (Nat.factorial 96) ≤
        Finset.sum (Finset.range 49) (fun k => (-1 : ℝ)^k * ((175633557293333229060 : ℝ) / 100000000000000000000)^(2*k) / Nat.factorial (2*k)) := by
      norm_num [sevenNineCosUpper, Finset.sum_range_succ]
    simpa [sub_zero] using hpR
  have hangle : ((175633557293333229060 : ℝ) / 100000000000000000000) ≤ Real.arccos (touchCosine a b (Real.sqrt 9 + Real.sqrt 10)) := by
    exact angle_lower_bound_of_cosine (by norm_num)
      (by
        calc
          ((175633557293333229060 : ℝ) / 100000000000000000000) ≤ (314159265358979323846 : ℝ) / 100000000000000000000 := by norm_num
          _ ≤ Real.pi := by
            have hpi := Real.pi_gt_d20.le
            norm_num at hpi ⊢
            exact hpi) (le_trans htouch hcos)
  have hdata : sevenNineAngleLower[81]! = ((175633557293333229060 : Rat) / 100000000000000000000) := by native_decide
  have hdataR : (sevenNineAngleLower[81]! : ℝ) = ((175633557293333229060 : ℝ) / 100000000000000000000) := by
    have h := congrArg (fun q : Rat => (q : ℝ)) hdata
    convert h using 1 ; norm_num
  rw [hdataR]
  exact hangle

theorem sevenNineAngle_5_6_1_0 {a b : ℝ}
    (haL : (sevenNineRadial 5 1 0 : ℝ) ≤ a) (haU : a ≤ (sevenNineRadial 5 1 1 : ℝ))
    (hbL : (sevenNineRadial 6 0 0 : ℝ) ≤ b) (hbU : b ≤ (sevenNineRadial 6 0 1 : ℝ)) :
    (sevenNineAngleLower[82]! : ℝ) ≤ Real.arccos (touchCosine a b (Real.sqrt 9 + Real.sqrt 10)) := by
  let d : ℝ := Real.sqrt 9 + Real.sqrt 10
  have hd' : (((6162277660168379331998893544432718533719555139325216826857504852792594438639238221344248108 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) : ℝ) ≤ d := by
    dsimp [d]
    have h := rat_sum_sqrt_lower (q := ((6162277660168379331998893544432718533719555139325216826857504852792594438639238221344248108 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (qi := ((3 : Rat) / 1)) (qj := ((3162277660168379331998893544432718533719555139325216826857504852792594438639238221344248108379300295187347284152840055148 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))
      (ni := 9) (nj := 10)
      (by convert sqrt_lower_9 using 1 ; norm_num)
      (by convert sqrt_lower_10 using 1 ; norm_num)
      (by native_decide)
    convert h using 1 ; norm_num
  have hd : (((6162277660168379331998893544432718533719555139325216826857504852792594438639238221344248108 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) ≤ d := by exact hd'
  have hd2 : (((6162277660168379331998893544432718533719555139325216826857504852792594438639238221344248108 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))^2 ≤ d^2 := by
    have hq : (0 : ℝ) ≤ ((6162277660168379331998893544432718533719555139325216826857504852792594438639238221344248108 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) := by norm_num
    have hdn : 0 ≤ d := by positivity
    exact (sq_le_sq₀ hq hdn).mpr hd
  have hd2' : (sevenNineDistanceLower[20]! : ℝ)^2 ≤ d^2 := by
    convert hd2 using 1 ; norm_num [sevenNineDistanceLower]
  have h00 : (sevenNineRadial 5 1 0 : ℝ)^2 + (sevenNineRadial 6 0 0 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[82]! : ℝ) * (2 * (sevenNineRadial 5 1 0 : ℝ) * (sevenNineRadial 6 0 0 : ℝ)) := by
    have hq : (sevenNineRadial 5 1 0)^2 + (sevenNineRadial 6 0 0)^2 - sevenNineDistanceLower[20]!^2 ≤
        sevenNineCosUpper[82]! * (2 * sevenNineRadial 5 1 0 * sevenNineRadial 6 0 0) := by native_decide
    have hqR :
        (sevenNineRadial 5 1 0 : ℝ)^2 + (sevenNineRadial 6 0 0 : ℝ)^2 - (sevenNineDistanceLower[20]! : ℝ)^2 ≤
          (sevenNineCosUpper[82]! : ℝ) * (2 * (sevenNineRadial 5 1 0 : ℝ) * (sevenNineRadial 6 0 0 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 5 1 0 : ℝ)^2 + (sevenNineRadial 6 0 0 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 5 1 0 : ℝ)^2 + (sevenNineRadial 6 0 0 : ℝ)^2 - (sevenNineDistanceLower[20]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h01 : (sevenNineRadial 5 1 0 : ℝ)^2 + (sevenNineRadial 6 0 1 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[82]! : ℝ) * (2 * (sevenNineRadial 5 1 0 : ℝ) * (sevenNineRadial 6 0 1 : ℝ)) := by
    have hq : (sevenNineRadial 5 1 0)^2 + (sevenNineRadial 6 0 1)^2 - sevenNineDistanceLower[20]!^2 ≤
        sevenNineCosUpper[82]! * (2 * sevenNineRadial 5 1 0 * sevenNineRadial 6 0 1) := by native_decide
    have hqR :
        (sevenNineRadial 5 1 0 : ℝ)^2 + (sevenNineRadial 6 0 1 : ℝ)^2 - (sevenNineDistanceLower[20]! : ℝ)^2 ≤
          (sevenNineCosUpper[82]! : ℝ) * (2 * (sevenNineRadial 5 1 0 : ℝ) * (sevenNineRadial 6 0 1 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 5 1 0 : ℝ)^2 + (sevenNineRadial 6 0 1 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 5 1 0 : ℝ)^2 + (sevenNineRadial 6 0 1 : ℝ)^2 - (sevenNineDistanceLower[20]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h10 : (sevenNineRadial 5 1 1 : ℝ)^2 + (sevenNineRadial 6 0 0 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[82]! : ℝ) * (2 * (sevenNineRadial 5 1 1 : ℝ) * (sevenNineRadial 6 0 0 : ℝ)) := by
    have hq : (sevenNineRadial 5 1 1)^2 + (sevenNineRadial 6 0 0)^2 - sevenNineDistanceLower[20]!^2 ≤
        sevenNineCosUpper[82]! * (2 * sevenNineRadial 5 1 1 * sevenNineRadial 6 0 0) := by native_decide
    have hqR :
        (sevenNineRadial 5 1 1 : ℝ)^2 + (sevenNineRadial 6 0 0 : ℝ)^2 - (sevenNineDistanceLower[20]! : ℝ)^2 ≤
          (sevenNineCosUpper[82]! : ℝ) * (2 * (sevenNineRadial 5 1 1 : ℝ) * (sevenNineRadial 6 0 0 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 5 1 1 : ℝ)^2 + (sevenNineRadial 6 0 0 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 5 1 1 : ℝ)^2 + (sevenNineRadial 6 0 0 : ℝ)^2 - (sevenNineDistanceLower[20]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h11 : (sevenNineRadial 5 1 1 : ℝ)^2 + (sevenNineRadial 6 0 1 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[82]! : ℝ) * (2 * (sevenNineRadial 5 1 1 : ℝ) * (sevenNineRadial 6 0 1 : ℝ)) := by
    have hq : (sevenNineRadial 5 1 1)^2 + (sevenNineRadial 6 0 1)^2 - sevenNineDistanceLower[20]!^2 ≤
        sevenNineCosUpper[82]! * (2 * sevenNineRadial 5 1 1 * sevenNineRadial 6 0 1) := by native_decide
    have hqR :
        (sevenNineRadial 5 1 1 : ℝ)^2 + (sevenNineRadial 6 0 1 : ℝ)^2 - (sevenNineDistanceLower[20]! : ℝ)^2 ≤
          (sevenNineCosUpper[82]! : ℝ) * (2 * (sevenNineRadial 5 1 1 : ℝ) * (sevenNineRadial 6 0 1 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 5 1 1 : ℝ)^2 + (sevenNineRadial 6 0 1 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 5 1 1 : ℝ)^2 + (sevenNineRadial 6 0 1 : ℝ)^2 - (sevenNineDistanceLower[20]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have htouch := corner_touch_cosine_bound haL haU hbL hbU
    (by norm_num [sevenNineRadial, sevenNineRadialBounds])
    (by norm_num [sevenNineRadial, sevenNineRadialBounds]) h00 h01 h10 h11
  have hcos : (sevenNineCosUpper[82]! : ℝ) ≤ Real.cos ((174044104243594144883 : ℝ) / 100000000000000000000) := by
    apply lower_bound_of_taylor_error
      (cosine_taylor_ninety_six_remainder (a := 0) (b := 4) (x := ((174044104243594144883 : ℝ) / 100000000000000000000) )
        (by norm_num) (by constructor <;> norm_num [Real.pi_gt_d20, Real.pi_lt_four]))
    rw [cosine_taylor_ninety_six_at_zero (b := 4) (x := ((174044104243594144883 : ℝ) / 100000000000000000000)) (by norm_num)]
    have hp : (sevenNineCosUpper[82]! : Rat) + (((174044104243594144883 : Rat) / 100000000000000000000) : Rat)^97 / (Nat.factorial 96) ≤
        Finset.sum (Finset.range 49) (fun k => (-1 : Rat)^k * (((174044104243594144883 : Rat) / 100000000000000000000) : Rat)^(2*k) / Nat.factorial (2*k)) := by native_decide
    have hpR : (sevenNineCosUpper[82]! : ℝ) + ((174044104243594144883 : ℝ) / 100000000000000000000)^97 / (Nat.factorial 96) ≤
        Finset.sum (Finset.range 49) (fun k => (-1 : ℝ)^k * ((174044104243594144883 : ℝ) / 100000000000000000000)^(2*k) / Nat.factorial (2*k)) := by
      norm_num [sevenNineCosUpper, Finset.sum_range_succ]
    simpa [sub_zero] using hpR
  have hangle : ((174044104243594144883 : ℝ) / 100000000000000000000) ≤ Real.arccos (touchCosine a b (Real.sqrt 9 + Real.sqrt 10)) := by
    exact angle_lower_bound_of_cosine (by norm_num)
      (by
        calc
          ((174044104243594144883 : ℝ) / 100000000000000000000) ≤ (314159265358979323846 : ℝ) / 100000000000000000000 := by norm_num
          _ ≤ Real.pi := by
            have hpi := Real.pi_gt_d20.le
            norm_num at hpi ⊢
            exact hpi) (le_trans htouch hcos)
  have hdata : sevenNineAngleLower[82]! = ((174044104243594144883 : Rat) / 100000000000000000000) := by native_decide
  have hdataR : (sevenNineAngleLower[82]! : ℝ) = ((174044104243594144883 : ℝ) / 100000000000000000000) := by
    have h := congrArg (fun q : Rat => (q : ℝ)) hdata
    convert h using 1 ; norm_num
  rw [hdataR]
  exact hangle

theorem sevenNineAngle_5_6_1_1 {a b : ℝ}
    (haL : (sevenNineRadial 5 1 0 : ℝ) ≤ a) (haU : a ≤ (sevenNineRadial 5 1 1 : ℝ))
    (hbL : (sevenNineRadial 6 1 0 : ℝ) ≤ b) (hbU : b ≤ (sevenNineRadial 6 1 1 : ℝ)) :
    (sevenNineAngleLower[83]! : ℝ) ≤ Real.arccos (touchCosine a b (Real.sqrt 9 + Real.sqrt 10)) := by
  let d : ℝ := Real.sqrt 9 + Real.sqrt 10
  have hd' : (((6162277660168379331998893544432718533719555139325216826857504852792594438639238221344248108 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) : ℝ) ≤ d := by
    dsimp [d]
    have h := rat_sum_sqrt_lower (q := ((6162277660168379331998893544432718533719555139325216826857504852792594438639238221344248108 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (qi := ((3 : Rat) / 1)) (qj := ((3162277660168379331998893544432718533719555139325216826857504852792594438639238221344248108379300295187347284152840055148 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))
      (ni := 9) (nj := 10)
      (by convert sqrt_lower_9 using 1 ; norm_num)
      (by convert sqrt_lower_10 using 1 ; norm_num)
      (by native_decide)
    convert h using 1 ; norm_num
  have hd : (((6162277660168379331998893544432718533719555139325216826857504852792594438639238221344248108 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) ≤ d := by exact hd'
  have hd2 : (((6162277660168379331998893544432718533719555139325216826857504852792594438639238221344248108 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))^2 ≤ d^2 := by
    have hq : (0 : ℝ) ≤ ((6162277660168379331998893544432718533719555139325216826857504852792594438639238221344248108 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) := by norm_num
    have hdn : 0 ≤ d := by positivity
    exact (sq_le_sq₀ hq hdn).mpr hd
  have hd2' : (sevenNineDistanceLower[20]! : ℝ)^2 ≤ d^2 := by
    convert hd2 using 1 ; norm_num [sevenNineDistanceLower]
  have h00 : (sevenNineRadial 5 1 0 : ℝ)^2 + (sevenNineRadial 6 1 0 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[83]! : ℝ) * (2 * (sevenNineRadial 5 1 0 : ℝ) * (sevenNineRadial 6 1 0 : ℝ)) := by
    have hq : (sevenNineRadial 5 1 0)^2 + (sevenNineRadial 6 1 0)^2 - sevenNineDistanceLower[20]!^2 ≤
        sevenNineCosUpper[83]! * (2 * sevenNineRadial 5 1 0 * sevenNineRadial 6 1 0) := by native_decide
    have hqR :
        (sevenNineRadial 5 1 0 : ℝ)^2 + (sevenNineRadial 6 1 0 : ℝ)^2 - (sevenNineDistanceLower[20]! : ℝ)^2 ≤
          (sevenNineCosUpper[83]! : ℝ) * (2 * (sevenNineRadial 5 1 0 : ℝ) * (sevenNineRadial 6 1 0 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 5 1 0 : ℝ)^2 + (sevenNineRadial 6 1 0 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 5 1 0 : ℝ)^2 + (sevenNineRadial 6 1 0 : ℝ)^2 - (sevenNineDistanceLower[20]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h01 : (sevenNineRadial 5 1 0 : ℝ)^2 + (sevenNineRadial 6 1 1 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[83]! : ℝ) * (2 * (sevenNineRadial 5 1 0 : ℝ) * (sevenNineRadial 6 1 1 : ℝ)) := by
    have hq : (sevenNineRadial 5 1 0)^2 + (sevenNineRadial 6 1 1)^2 - sevenNineDistanceLower[20]!^2 ≤
        sevenNineCosUpper[83]! * (2 * sevenNineRadial 5 1 0 * sevenNineRadial 6 1 1) := by native_decide
    have hqR :
        (sevenNineRadial 5 1 0 : ℝ)^2 + (sevenNineRadial 6 1 1 : ℝ)^2 - (sevenNineDistanceLower[20]! : ℝ)^2 ≤
          (sevenNineCosUpper[83]! : ℝ) * (2 * (sevenNineRadial 5 1 0 : ℝ) * (sevenNineRadial 6 1 1 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 5 1 0 : ℝ)^2 + (sevenNineRadial 6 1 1 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 5 1 0 : ℝ)^2 + (sevenNineRadial 6 1 1 : ℝ)^2 - (sevenNineDistanceLower[20]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h10 : (sevenNineRadial 5 1 1 : ℝ)^2 + (sevenNineRadial 6 1 0 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[83]! : ℝ) * (2 * (sevenNineRadial 5 1 1 : ℝ) * (sevenNineRadial 6 1 0 : ℝ)) := by
    have hq : (sevenNineRadial 5 1 1)^2 + (sevenNineRadial 6 1 0)^2 - sevenNineDistanceLower[20]!^2 ≤
        sevenNineCosUpper[83]! * (2 * sevenNineRadial 5 1 1 * sevenNineRadial 6 1 0) := by native_decide
    have hqR :
        (sevenNineRadial 5 1 1 : ℝ)^2 + (sevenNineRadial 6 1 0 : ℝ)^2 - (sevenNineDistanceLower[20]! : ℝ)^2 ≤
          (sevenNineCosUpper[83]! : ℝ) * (2 * (sevenNineRadial 5 1 1 : ℝ) * (sevenNineRadial 6 1 0 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 5 1 1 : ℝ)^2 + (sevenNineRadial 6 1 0 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 5 1 1 : ℝ)^2 + (sevenNineRadial 6 1 0 : ℝ)^2 - (sevenNineDistanceLower[20]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have h11 : (sevenNineRadial 5 1 1 : ℝ)^2 + (sevenNineRadial 6 1 1 : ℝ)^2 - d^2 ≤
      (sevenNineCosUpper[83]! : ℝ) * (2 * (sevenNineRadial 5 1 1 : ℝ) * (sevenNineRadial 6 1 1 : ℝ)) := by
    have hq : (sevenNineRadial 5 1 1)^2 + (sevenNineRadial 6 1 1)^2 - sevenNineDistanceLower[20]!^2 ≤
        sevenNineCosUpper[83]! * (2 * sevenNineRadial 5 1 1 * sevenNineRadial 6 1 1) := by native_decide
    have hqR :
        (sevenNineRadial 5 1 1 : ℝ)^2 + (sevenNineRadial 6 1 1 : ℝ)^2 - (sevenNineDistanceLower[20]! : ℝ)^2 ≤
          (sevenNineCosUpper[83]! : ℝ) * (2 * (sevenNineRadial 5 1 1 : ℝ) * (sevenNineRadial 6 1 1 : ℝ)) := by
      exact_mod_cast hq
    have hmon : (sevenNineRadial 5 1 1 : ℝ)^2 + (sevenNineRadial 6 1 1 : ℝ)^2 - d^2 ≤
        (sevenNineRadial 5 1 1 : ℝ)^2 + (sevenNineRadial 6 1 1 : ℝ)^2 - (sevenNineDistanceLower[20]! : ℝ)^2 := by
      nlinarith [hd2']
    exact hmon.trans hqR
  have htouch := corner_touch_cosine_bound haL haU hbL hbU
    (by norm_num [sevenNineRadial, sevenNineRadialBounds])
    (by norm_num [sevenNineRadial, sevenNineRadialBounds]) h00 h01 h10 h11
  have hcos : (sevenNineCosUpper[83]! : ℝ) ≤ Real.cos ((138707213414389924204 : ℝ) / 100000000000000000000) := by
    apply lower_bound_of_taylor_error
      (cosine_taylor_ninety_six_remainder (a := 0) (b := 4) (x := ((138707213414389924204 : ℝ) / 100000000000000000000) )
        (by norm_num) (by constructor <;> norm_num [Real.pi_gt_d20, Real.pi_lt_four]))
    rw [cosine_taylor_ninety_six_at_zero (b := 4) (x := ((138707213414389924204 : ℝ) / 100000000000000000000)) (by norm_num)]
    have hp : (sevenNineCosUpper[83]! : Rat) + (((138707213414389924204 : Rat) / 100000000000000000000) : Rat)^97 / (Nat.factorial 96) ≤
        Finset.sum (Finset.range 49) (fun k => (-1 : Rat)^k * (((138707213414389924204 : Rat) / 100000000000000000000) : Rat)^(2*k) / Nat.factorial (2*k)) := by native_decide
    have hpR : (sevenNineCosUpper[83]! : ℝ) + ((138707213414389924204 : ℝ) / 100000000000000000000)^97 / (Nat.factorial 96) ≤
        Finset.sum (Finset.range 49) (fun k => (-1 : ℝ)^k * ((138707213414389924204 : ℝ) / 100000000000000000000)^(2*k) / Nat.factorial (2*k)) := by
      norm_num [sevenNineCosUpper, Finset.sum_range_succ]
    simpa [sub_zero] using hpR
  have hangle : ((138707213414389924204 : ℝ) / 100000000000000000000) ≤ Real.arccos (touchCosine a b (Real.sqrt 9 + Real.sqrt 10)) := by
    exact angle_lower_bound_of_cosine (by norm_num)
      (by
        calc
          ((138707213414389924204 : ℝ) / 100000000000000000000) ≤ (314159265358979323846 : ℝ) / 100000000000000000000 := by norm_num
          _ ≤ Real.pi := by
            have hpi := Real.pi_gt_d20.le
            norm_num at hpi ⊢
            exact hpi) (le_trans htouch hcos)
  have hdata : sevenNineAngleLower[83]! = ((138707213414389924204 : Rat) / 100000000000000000000) := by native_decide
  have hdataR : (sevenNineAngleLower[83]! : ℝ) = ((138707213414389924204 : ℝ) / 100000000000000000000) := by
    have h := congrArg (fun q : Rat => (q : ℝ)) hdata
    convert h using 1 ; norm_num
  rw [hdataR]
  exact hangle

end CirclePacking
