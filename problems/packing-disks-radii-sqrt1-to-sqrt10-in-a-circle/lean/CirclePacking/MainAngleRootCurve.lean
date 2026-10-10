import CirclePacking.MainAngleRootExistence
import CirclePacking.ArctanTaylor
import CirclePacking.MainAngleArctan
import Mathlib.Topology.Order.IntermediateValue

set_option maxHeartbeats 2000000

/-!
# Continuous dependence of a monotone root on a parameter

For each radius `R`, strict monotonicity and opposite signs at the two `t`
endpoints give a unique solution of `F t R = 0`. This file proves that those
solutions form a continuous curve when `F` is continuous in `R` for each fixed
`t`. For the concrete angle barriers, continuity is proved below from the
contact-angle formulas. The strict endpoint signs are left for the exact
interval certificate to supply.
-/

namespace CirclePacking

noncomputable section

/-- Choose the unique `t`-root of `F` for every parameter in `[rLo,rHi]`.
The strict endpoint signs and continuity in `t` supply existence by the
intermediate value theorem; strict monotonicity supplies uniqueness. -/
theorem exists_continuous_parametric_root
    {F : ℝ → ℝ → ℝ} {tLo tHi rLo rHi : ℝ}
    (ht : tLo < tHi)
    (hFcontT : ∀ R ∈ Set.Icc rLo rHi,
      ContinuousOn (fun t => F t R) (Set.Icc tLo tHi))
    (hFmono : ∀ R ∈ Set.Icc rLo rHi,
      StrictMonoOn (fun t => F t R) (Set.Icc tLo tHi))
    (hFcontR : ∀ t ∈ Set.Icc tLo tHi,
      ContinuousOn (fun R => F t R) (Set.Icc rLo rHi))
    (hFleft : ∀ R ∈ Set.Icc rLo rHi, F tLo R < 0)
    (hFright : ∀ R ∈ Set.Icc rLo rHi, 0 < F tHi R) :
    ∃ tcurve : ℝ → ℝ,
      ContinuousOn tcurve (Set.Icc rLo rHi) ∧
      ∀ R ∈ Set.Icc rLo rHi,
        tcurve R ∈ Set.Icc tLo tHi ∧ F (tcurve R) R = 0 := by
  have hrootExists : ∀ R ∈ Set.Icc rLo rHi,
      ∃ t, t ∈ Set.Icc tLo tHi ∧ F t R = 0 := by
    intro R hR
    have hzero : (0 : ℝ) ∈ Set.Icc (F tLo R) (F tHi R) :=
      ⟨(hFleft R hR).le, (hFright R hR).le⟩
    obtain ⟨t, htmem, hFt⟩ :=
      intermediate_value_Icc ht.le (hFcontT R hR) hzero
    exact ⟨t, htmem, hFt⟩
  let tcurve : ℝ → ℝ := fun R =>
    if hR : R ∈ Set.Icc rLo rHi then
      Classical.choose (hrootExists R hR)
    else tLo
  have tcurve_spec (R : ℝ) (hR : R ∈ Set.Icc rLo rHi) :
      tcurve R ∈ Set.Icc tLo tHi ∧ F (tcurve R) R = 0 := by
    simp only [tcurve, dite_eq_left hR]
    exact Classical.choose_spec (hrootExists R hR)
  have tcurve_interior (R : ℝ) (hR : R ∈ Set.Icc rLo rHi) :
      tLo < tcurve R ∧ tcurve R < tHi := by
    have hs := tcurve_spec R hR
    constructor
    · by_contra hnot
      have heq : tcurve R = tLo := le_antisymm
        (le_of_not_gt hnot) hs.1.1
      rw [heq] at hs
      linarith [hFleft R hR, hs.2]
    · by_contra hnot
      have heq : tcurve R = tHi := le_antisymm hs.1.2 (le_of_not_gt hnot)
      rw [heq] at hs
      linarith [hFright R hR, hs.2]
  have htcurve_cont : ContinuousOn tcurve (Set.Icc rLo rHi) := by
    rw [Metric.continuousOn_iff]
    intro R₀ hR₀ ε hε
    let t₀ := tcurve R₀
    have ht₀mem := (tcurve_spec R₀ hR₀).1
    have ht₀zero := (tcurve_spec R₀ hR₀).2
    have ht₀interior := tcurve_interior R₀ hR₀
    let η := min (ε / 2) (min ((t₀ - tLo) / 2) ((tHi - t₀) / 2))
    have hη : 0 < η := by
      dsimp [η]
      exact lt_min (by linarith [hε])
        (lt_min (by linarith [ht₀interior.1]) (by linarith [ht₀interior.2]))
    have hηε : η < ε := by
      dsimp [η]
      exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
    have hηleft : η < t₀ - tLo := by
      dsimp [η]
      have hηinner : η ≤ min ((t₀ - tLo) / 2) ((tHi - t₀) / 2) :=
        min_le_right _ _
      have hinnerleft : min ((t₀ - tLo) / 2) ((tHi - t₀) / 2) ≤
          (t₀ - tLo) / 2 := min_le_left _ _
      exact lt_of_le_of_lt (le_trans hηinner hinnerleft) (by linarith)
    have hηright : η < tHi - t₀ := by
      dsimp [η]
      have hηinner : η ≤ min ((t₀ - tLo) / 2) ((tHi - t₀) / 2) :=
        min_le_right _ _
      have hinnerright : min ((t₀ - tLo) / 2) ((tHi - t₀) / 2) ≤
          (tHi - t₀) / 2 := min_le_right _ _
      exact lt_of_le_of_lt (le_trans hηinner hinnerright) (by linarith)
    let tleft := t₀ - η
    let tright := t₀ + η
    have hleftMem : tleft ∈ Set.Icc tLo tHi := by
      constructor <;> dsimp [tleft] <;> linarith [ht₀mem.2]
    have hrightMem : tright ∈ Set.Icc tLo tHi := by
      constructor <;> dsimp [tright] <;> linarith [ht₀mem.1]
    have hleftRoot : tleft < t₀ := by
      dsimp [tleft]
      linarith
    have hrootRight : t₀ < tright := by
      dsimp [tright]
      linarith
    have hFleft₀ : F tleft R₀ < 0 := by
      have hmono := hFmono R₀ hR₀ hleftMem ht₀mem hleftRoot
      linarith
    have hFright₀ : 0 < F tright R₀ := by
      have hmono := hFmono R₀ hR₀ ht₀mem hrightMem hrootRight
      linarith
    obtain ⟨δleft, hδleft, hleftNear⟩ :=
      (Metric.continuousOn_iff.mp (hFcontR tleft hleftMem))
        R₀ hR₀ (-F tleft R₀ / 2) (by linarith)
    obtain ⟨δright, hδright, hrightNear⟩ :=
      (Metric.continuousOn_iff.mp (hFcontR tright hrightMem))
        R₀ hR₀ (F tright R₀ / 2) (by linarith)
    refine ⟨min δleft δright, lt_min hδleft hδright, ?_⟩
    intro R hR hdist
    have hleftSign : F tleft R < 0 := by
      have hclose := hleftNear R hR (lt_of_lt_of_le hdist (min_le_left _ _))
      have habs : |F tleft R - F tleft R₀| < -F tleft R₀ / 2 := by
        simpa [Real.dist_eq] using hclose
      linarith [(abs_lt.mp habs).2]
    have hrightSign : 0 < F tright R := by
      have hclose := hrightNear R hR (lt_of_lt_of_le hdist (min_le_right _ _))
      have habs : |F tright R - F tright R₀| < F tright R₀ / 2 := by
        simpa [Real.dist_eq] using hclose
      linarith [(abs_lt.mp habs).1]
    have hrootMem := (tcurve_spec R hR).1
    have hrootVal := (tcurve_spec R hR).2
    have hrootAbove : tleft < tcurve R := by
      by_contra hnot
      have hle : tcurve R ≤ tleft := le_of_not_gt hnot
      rcases lt_or_eq_of_le hle with hlt | heq
      · have hmono := hFmono R hR hrootMem hleftMem hlt
        linarith
      · rw [heq] at hrootVal
        linarith
    have hrootBelow : tcurve R < tright := by
      by_contra hnot
      have hle : tright ≤ tcurve R := le_of_not_gt hnot
      rcases lt_or_eq_of_le hle with hlt | heq
      · have hmono := hFmono R hR hrightMem hrootMem hlt
        linarith
      · rw [← heq] at hrootVal
        linarith
    have habs : |tcurve R - t₀| < ε := by
      rw [abs_lt]
      constructor
      · dsimp [tleft] at hrootAbove
        dsimp [t₀]
        linarith [hηε]
      · dsimp [tright] at hrootBelow
        dsimp [t₀]
        linarith [hηε]
    simpa [Real.dist_eq, t₀] using habs
  refine ⟨tcurve, htcurve_cont, ?_⟩
  intro R hR
  exact tcurve_spec R hR

/-- The law-of-cosines contact angle is continuous in both radii wherever
neither radius vanishes. Arccos is continuous on all reals, so no numerical
range restriction on the cosine is needed for this continuity statement. -/
private theorem touchAngle_comp_continuousOn
    {s : Set (ℝ × ℝ)} (a b : ℝ × ℝ → ℝ) (d : ℝ)
    (ha : ContinuousOn a s) (hb : ContinuousOn b s)
    (ha0 : ∀ p ∈ s, a p ≠ 0) (hb0 : ∀ p ∈ s, b p ≠ 0) :
    ContinuousOn (fun p => touchAngle (a p) (b p) d) s := by
  have hd2 : ContinuousOn (fun _ : ℝ × ℝ => d ^ 2) s := continuousOn_const
  have hnum : ContinuousOn (fun p => (a p) ^ 2 + (b p) ^ 2 - d ^ 2) s := by
    exact (ha.pow 2).add (hb.pow 2) |>.sub hd2
  have hden : ContinuousOn (fun p => 2 * a p * b p) s := by
    have htwo : ContinuousOn (fun _ : ℝ × ℝ => (2 : ℝ)) s := continuousOn_const
    exact (htwo.mul ha).mul hb
  have hden0 : ∀ p ∈ s, 2 * a p * b p ≠ 0 := by
    intro p hp
    exact mul_ne_zero (mul_ne_zero (by norm_num) (ha0 p hp)) (hb0 p hp)
  have hcos : ContinuousOn (fun p => touchCosine (a p) (b p) d) s := by
    change ContinuousOn (fun p =>
      ((a p) ^ 2 + (b p) ^ 2 - d ^ 2) / (2 * a p * b p)) s
    exact hnum.div hden hden0
  unfold touchAngle
  exact Real.continuous_arccos.continuousOn.comp hcos
    (by intro p hp; exact Set.mem_univ _)

private theorem sqrt_lt_eight_of_lt_sixty_four {n : ℝ}
    (hn0 : 0 ≤ n) (hn : n < 64) :
    Real.sqrt n < 8 := by
  have hs := Real.sq_sqrt hn0
  have hs0 := Real.sqrt_nonneg n
  nlinarith

private theorem angleRect_radius_sub_ne_zero
    {p : ℝ × ℝ} (hp : p ∈ mainBarrierTRange ×ˢ mainBarrierRadiusRange)
    {c : ℝ} (hc : c < 8) : p.2 - c ≠ 0 := by
  rcases hp with ⟨_, hR⟩
  have hRlo : (8.303 : ℝ) ≤ p.2 := hR.1
  exact ne_of_gt (by linarith)

private theorem angleRect_t_ne_zero
    {p : ℝ × ℝ} (hp : p ∈ mainBarrierTRange ×ˢ mainBarrierRadiusRange) :
    p.1 ≠ 0 := by
  rcases hp with ⟨ht, _⟩
  have htlo : (0.8588 : ℝ) ≤ p.1 := ht.1
  exact ne_of_gt (by linarith)

/-- The concrete angle barriers are jointly continuous on their rational
rectangle. This uses only continuity of arccos and nonvanishing of the two
radius arguments in each contact-angle formula. -/
theorem mainBarrier_continuousOn_pair :
    ContinuousOn (fun p : ℝ × ℝ => mainBarrierA p.1 p.2)
      (mainBarrierTRange ×ˢ mainBarrierRadiusRange) ∧
    ContinuousOn (fun p : ℝ × ℝ => mainBarrierB p.1 p.2)
      (mainBarrierTRange ×ˢ mainBarrierRadiusRange) := by
  let s := mainBarrierTRange ×ˢ mainBarrierRadiusRange
  have ht : ContinuousOn (fun p : ℝ × ℝ => p.1) s := continuousOn_fst
  have hR : ContinuousOn (fun p : ℝ × ℝ => p.2) s := continuousOn_snd
  have hsqrt2 : Real.sqrt 2 < 8 :=
    sqrt_lt_eight_of_lt_sixty_four (by norm_num) (by norm_num)
  have hsqrt5 : Real.sqrt 5 < 8 :=
    sqrt_lt_eight_of_lt_sixty_four (by norm_num) (by norm_num)
  have hsqrt6 : Real.sqrt 6 < 8 :=
    sqrt_lt_eight_of_lt_sixty_four (by norm_num) (by norm_num)
  have hsqrt7 : Real.sqrt 7 < 8 :=
    sqrt_lt_eight_of_lt_sixty_four (by norm_num) (by norm_num)
  have hsqrt8 : Real.sqrt 8 < 8 :=
    sqrt_lt_eight_of_lt_sixty_four (by norm_num) (by norm_num)
  have hsqrt9 : Real.sqrt 9 < 8 :=
    sqrt_lt_eight_of_lt_sixty_four (by norm_num) (by norm_num)
  have ht0 : ∀ p ∈ s, p.1 ≠ 0 := by
    intro p hp
    exact angleRect_t_ne_zero hp
  have hR2 : ∀ p ∈ s, p.2 - Real.sqrt 2 ≠ 0 := by
    intro p hp
    exact angleRect_radius_sub_ne_zero hp hsqrt2
  have hR5 : ∀ p ∈ s, p.2 - Real.sqrt 5 ≠ 0 := by
    intro p hp
    exact angleRect_radius_sub_ne_zero hp hsqrt5
  have hR6 : ∀ p ∈ s, p.2 - Real.sqrt 6 ≠ 0 := by
    intro p hp
    exact angleRect_radius_sub_ne_zero hp hsqrt6
  have hR7 : ∀ p ∈ s, p.2 - Real.sqrt 7 ≠ 0 := by
    intro p hp
    exact angleRect_radius_sub_ne_zero hp hsqrt7
  have hR8 : ∀ p ∈ s, p.2 - Real.sqrt 8 ≠ 0 := by
    intro p hp
    exact angleRect_radius_sub_ne_zero hp hsqrt8
  have hR9 : ∀ p ∈ s, p.2 - Real.sqrt 9 ≠ 0 := by
    intro p hp
    exact angleRect_radius_sub_ne_zero hp hsqrt9
  have hAlpha5 : ContinuousOn (fun p : ℝ × ℝ => mainAlpha5 p.1 p.2) s := by
    simpa only [mainAlpha5] using
      (touchAngle_comp_continuousOn (fun p : ℝ × ℝ => p.1)
        (fun p => p.2 - Real.sqrt 5) (Real.sqrt 10 + Real.sqrt 5)
        ht (hR.sub continuousOn_const) ht0 hR5)
  have hAlpha6 : ContinuousOn (fun p : ℝ × ℝ => mainAlpha6 p.1 p.2) s := by
    simpa only [mainAlpha6] using
      (touchAngle_comp_continuousOn (fun p : ℝ × ℝ => p.1)
        (fun p => p.2 - Real.sqrt 6) (Real.sqrt 10 + Real.sqrt 6)
        ht (hR.sub continuousOn_const) ht0 hR6)
  have hAlpha7 : ContinuousOn (fun p : ℝ × ℝ => mainAlpha7 p.1 p.2) s := by
    simpa only [mainAlpha7] using
      (touchAngle_comp_continuousOn (fun p : ℝ × ℝ => p.1)
        (fun p => p.2 - Real.sqrt 7) (Real.sqrt 10 + Real.sqrt 7)
        ht (hR.sub continuousOn_const) ht0 hR7)
  have hBeta57 : ContinuousOn (fun p : ℝ × ℝ => mainBeta57 p.2) s := by
    simpa only [mainBeta57] using
      (touchAngle_comp_continuousOn (fun p : ℝ × ℝ => p.2 - Real.sqrt 5)
        (fun p => p.2 - Real.sqrt 7) (Real.sqrt 5 + Real.sqrt 7)
        (hR.sub continuousOn_const) (hR.sub continuousOn_const) hR5 hR7)
  have hBeta79 : ContinuousOn (fun p : ℝ × ℝ => mainBeta79 p.2) s := by
    simpa only [mainBeta79] using
      (touchAngle_comp_continuousOn (fun p : ℝ × ℝ => p.2 - Real.sqrt 7)
        (fun p => p.2 - Real.sqrt 9) (Real.sqrt 7 + Real.sqrt 9)
        (hR.sub continuousOn_const) (hR.sub continuousOn_const) hR7 hR9)
  have hBeta92 : ContinuousOn (fun p : ℝ × ℝ => mainBeta92 p.2) s := by
    simpa only [mainBeta92] using
      (touchAngle_comp_continuousOn (fun p : ℝ × ℝ => p.2 - Real.sqrt 9)
        (fun p => p.2 - Real.sqrt 2) (Real.sqrt 9 + Real.sqrt 2)
        (hR.sub continuousOn_const) (hR.sub continuousOn_const) hR9 hR2)
  have hBeta28 : ContinuousOn (fun p : ℝ × ℝ => mainBeta28 p.2) s := by
    simpa only [mainBeta28] using
      (touchAngle_comp_continuousOn (fun p : ℝ × ℝ => p.2 - Real.sqrt 2)
        (fun p => p.2 - Real.sqrt 8) (Real.sqrt 2 + Real.sqrt 8)
        (hR.sub continuousOn_const) (hR.sub continuousOn_const) hR2 hR8)
  have hBeta86 : ContinuousOn (fun p : ℝ × ℝ => mainBeta86 p.2) s := by
    simpa only [mainBeta86] using
      (touchAngle_comp_continuousOn (fun p : ℝ × ℝ => p.2 - Real.sqrt 8)
        (fun p => p.2 - Real.sqrt 6) (Real.sqrt 8 + Real.sqrt 6)
        (hR.sub continuousOn_const) (hR.sub continuousOn_const) hR8 hR6)
  have hCommon : ContinuousOn (fun p : ℝ × ℝ => mainCommonWallAngles p.2) s := by
    convert (((hBeta79.add hBeta92).add hBeta28).add hBeta86) using 1
    ext p
    rfl
  constructor
  · convert (((hAlpha5.add hBeta57).add hCommon).add hAlpha6) using 1
    ext p
    rfl
  · convert ((hAlpha7.add hCommon).add hAlpha6) using 1
    ext p
    rfl

/-- Rational boxes used by the exact interval proof of the simultaneous
angle root. Their endpoints are exact decimal rationals in Lean. -/
def certifiedMainAngleTBox : Set ℝ :=
  Set.Icc 1.0037160860750841 1.0037160860750846

def certifiedMainAngleRadiusBox : Set ℝ :=
  Set.Icc 8.3034681221114890 8.3034681221114900

theorem certifiedMainAngleTBox_subset :
    certifiedMainAngleTBox ⊆ mainBarrierTRange := by
  intro t ht
  change 1.0037160860750841 ≤ t ∧ t ≤ 1.0037160860750846 at ht
  change 0.8588 ≤ t ∧ t ≤ 1.1265
  constructor <;> linarith

theorem certifiedMainAngleRadiusBox_subset :
    certifiedMainAngleRadiusBox ⊆ mainBarrierRadiusRange := by
  intro R hR
  change 8.3034681221114890 ≤ R ∧ R ≤ 8.3034681221114900 at hR
  change 8.303 ≤ R ∧ R ≤ 8.304
  constructor <;> linarith

/-- Assemble the monotone root-curve construction with the existing angle
barrier theorem. The strict increase of `A - B` is derived from the formal
weak increase of `A` and strict decrease of `B`. `ArctanTaylor` supplies the
exact conversion of contact `arccos` values to the quarter-angle arctangent
series and its first-omitted-term remainder; the four concrete edge-sign
inequalities are still analytic inputs awaiting finite-data replay. -/
theorem exists_main_angle_critical_pair_of_barrier_difference
    (hFcontT : ∀ R ∈ mainBarrierRadiusRange,
      ContinuousOn (fun t => mainBarrierA t R - mainBarrierB t R)
        mainBarrierTRange)
    (hFcontR : ∀ t ∈ mainBarrierTRange,
      ContinuousOn (fun R => mainBarrierA t R - mainBarrierB t R)
        mainBarrierRadiusRange)
    (hFleft : ∀ R ∈ mainBarrierRadiusRange,
      mainBarrierA 0.8588 R - mainBarrierB 0.8588 R < 0)
    (hFright : ∀ R ∈ mainBarrierRadiusRange,
      0 < mainBarrierA 1.1265 R - mainBarrierB 1.1265 R)
    (hBcont : ContinuousOn
      (fun p : ℝ × ℝ => mainBarrierB p.1 p.2)
      (mainBarrierTRange ×ˢ mainBarrierRadiusRange))
    (hBleft : ∀ t ∈ mainBarrierTRange,
      mainBarrierA t 8.303 - mainBarrierB t 8.303 = 0 →
        2 * Real.pi < mainBarrierB t 8.303)
    (hBright : ∀ t ∈ mainBarrierTRange,
      mainBarrierA t 8.304 - mainBarrierB t 8.304 = 0 →
        mainBarrierB t 8.304 < 2 * Real.pi) :
    ∃ t R, t ∈ mainBarrierTRange ∧ R ∈ mainBarrierRadiusRange ∧
      mainBarrierA t R = 2 * Real.pi ∧ mainBarrierB t R = 2 * Real.pi := by
  let F : ℝ → ℝ → ℝ := fun t R => mainBarrierA t R - mainBarrierB t R
  have hFmono : ∀ R ∈ mainBarrierRadiusRange,
      StrictMonoOn (fun t => F t R) mainBarrierTRange := by
    intro R hR t₁ ht₁ t₂ ht₂ h12
    have hA := mainBarrierA_mono_t_on_ranges hR ht₁ ht₂ h12.le
    have hB := mainBarrierB_strictAnti_t_on_ranges hR ht₁ ht₂ h12
    dsimp [F]
    linarith
  have htlohi : (0.8588 : ℝ) < 1.1265 := by norm_num
  obtain ⟨tcurve, htcurveCont, htcurveSpec⟩ :=
    exists_continuous_parametric_root
      (F := F) htlohi
      (by
        intro R hR
        simpa [F, mainBarrierTRange] using hFcontT R hR)
      hFmono
      (by
        intro t ht
        simpa [F, mainBarrierRadiusRange] using hFcontR t ht)
      (by
        intro R hR
        simpa [F] using hFleft R hR)
      (by
        intro R hR
        simpa [F] using hFright R hR)
  have htcurveMem : ∀ R ∈ mainBarrierRadiusRange,
      tcurve R ∈ mainBarrierTRange := by
    intro R hR
    simpa [mainBarrierTRange] using (htcurveSpec R hR).1
  have hFzero : ∀ R ∈ mainBarrierRadiusRange,
      mainBarrierA (tcurve R) R = mainBarrierB (tcurve R) R := by
    intro R hR
    have hz := (htcurveSpec R hR).2
    change mainBarrierA (tcurve R) R - mainBarrierB (tcurve R) R = 0 at hz
    linarith
  have hRleft : (8.303 : ℝ) ∈ mainBarrierRadiusRange := by
    norm_num [mainBarrierRadiusRange]
  have hRright : (8.304 : ℝ) ∈ mainBarrierRadiusRange := by
    norm_num [mainBarrierRadiusRange]
  have hBleft' : 2 * Real.pi < mainBarrierB (tcurve 8.303) 8.303 := by
    apply hBleft (tcurve 8.303) (htcurveMem 8.303 hRleft)
    rw [hFzero 8.303 hRleft]
    ring
  have hBright' : mainBarrierB (tcurve 8.304) 8.304 < 2 * Real.pi := by
    apply hBright (tcurve 8.304) (htcurveMem 8.304 hRright)
    rw [hFzero 8.304 hRright]
    ring
  exact exists_main_angle_critical_pair_of_continuous_root_curve
    htcurveCont htcurveMem hFzero hBcont hBleft' hBright'

/-- The barrier root argument needs only the four rigorous sign inputs once
the concrete continuity of the angle formulas and their `t`-monotonicity have
been replayed. -/
theorem exists_main_angle_critical_pair_of_barrier_signs
    (hFleft : ∀ R ∈ mainBarrierRadiusRange,
      mainBarrierA 0.8588 R - mainBarrierB 0.8588 R < 0)
    (hFright : ∀ R ∈ mainBarrierRadiusRange,
      0 < mainBarrierA 1.1265 R - mainBarrierB 1.1265 R)
    (hBleft : ∀ t ∈ mainBarrierTRange,
      mainBarrierA t 8.303 - mainBarrierB t 8.303 = 0 →
        2 * Real.pi < mainBarrierB t 8.303)
    (hBright : ∀ t ∈ mainBarrierTRange,
      mainBarrierA t 8.304 - mainBarrierB t 8.304 = 0 →
        mainBarrierB t 8.304 < 2 * Real.pi) :
    ∃ t R, t ∈ mainBarrierTRange ∧ R ∈ mainBarrierRadiusRange ∧
      mainBarrierA t R = 2 * Real.pi ∧ mainBarrierB t R = 2 * Real.pi := by
  let s := mainBarrierTRange ×ˢ mainBarrierRadiusRange
  have hAcont := mainBarrier_continuousOn_pair.1
  have hBcont := mainBarrier_continuousOn_pair.2
  have hFcont : ContinuousOn
      (fun p : ℝ × ℝ => mainBarrierA p.1 p.2 - mainBarrierB p.1 p.2) s := by
    exact hAcont.sub hBcont
  have hFcontT : ∀ R ∈ mainBarrierRadiusRange,
      ContinuousOn (fun t => mainBarrierA t R - mainBarrierB t R)
        mainBarrierTRange := by
    intro R hR
    have hmap : ContinuousOn (fun t : ℝ => (t, R)) mainBarrierTRange :=
      continuousOn_id.prodMk continuousOn_const
    have hmaps : Set.MapsTo (fun t : ℝ => (t, R)) mainBarrierTRange s := by
      intro t ht
      exact ⟨ht, hR⟩
    have hcomp := hFcont.comp hmap hmaps
    convert hcomp using 1
    ext t
    rfl
  have hFcontR : ∀ t ∈ mainBarrierTRange,
      ContinuousOn (fun R => mainBarrierA t R - mainBarrierB t R)
        mainBarrierRadiusRange := by
    intro t ht
    have hmap : ContinuousOn (fun R : ℝ => (t, R)) mainBarrierRadiusRange :=
      continuousOn_const.prodMk continuousOn_id
    have hmaps : Set.MapsTo (fun R : ℝ => (t, R)) mainBarrierRadiusRange s := by
      intro R hR
      exact ⟨ht, hR⟩
    have hcomp := hFcont.comp hmap hmaps
    convert hcomp using 1
    ext R
    rfl
  exact exists_main_angle_critical_pair_of_barrier_difference
    hFcontT hFcontR hFleft hFright hBcont hBleft hBright

/-- Localize the two nested intermediate-value arguments to a rational
subrectangle. This is the interface needed by the exact interval certificate:
the signs are checked only on its tiny root box, while monotonicity and joint
continuity are inherited from the already-certified larger rectangle. -/
theorem exists_main_angle_critical_pair_on_subrectangle
    {tLo tHi rLo rHi : ℝ}
    (ht : tLo < tHi) (hr : rLo < rHi)
    (htSub : Set.Icc tLo tHi ⊆ mainBarrierTRange)
    (hrSub : Set.Icc rLo rHi ⊆ mainBarrierRadiusRange)
    (hFleft : ∀ R ∈ Set.Icc rLo rHi,
      mainBarrierA tLo R - mainBarrierB tLo R < 0)
    (hFright : ∀ R ∈ Set.Icc rLo rHi,
      0 < mainBarrierA tHi R - mainBarrierB tHi R)
    (hBleft : ∀ t ∈ Set.Icc tLo tHi,
      mainBarrierA t rLo - mainBarrierB t rLo = 0 →
        2 * Real.pi < mainBarrierB t rLo)
    (hBright : ∀ t ∈ Set.Icc tLo tHi,
      mainBarrierA t rHi - mainBarrierB t rHi = 0 →
        mainBarrierB t rHi < 2 * Real.pi) :
    ∃ t R, t ∈ Set.Icc tLo tHi ∧ R ∈ Set.Icc rLo rHi ∧
      R < rHi ∧ mainBarrierA t R = 2 * Real.pi ∧
        mainBarrierB t R = 2 * Real.pi := by
  let s := mainBarrierTRange ×ˢ mainBarrierRadiusRange
  let F : ℝ → ℝ → ℝ := fun t R => mainBarrierA t R - mainBarrierB t R
  have hFglobal : ContinuousOn
      (fun p : ℝ × ℝ => mainBarrierA p.1 p.2 - mainBarrierB p.1 p.2) s := by
    exact mainBarrier_continuousOn_pair.1.sub mainBarrier_continuousOn_pair.2
  have hFcontT : ∀ R ∈ Set.Icc rLo rHi,
      ContinuousOn (fun t => F t R) (Set.Icc tLo tHi) := by
    intro R hR
    have hRglobal : R ∈ mainBarrierRadiusRange := hrSub hR
    have hmap : ContinuousOn (fun t : ℝ => (t, R)) (Set.Icc tLo tHi) :=
      continuousOn_id.prodMk continuousOn_const
    have hmaps : Set.MapsTo (fun t : ℝ => (t, R))
        (Set.Icc tLo tHi) s := by
      intro t ht
      exact ⟨htSub ht, hRglobal⟩
    have hcomp := hFglobal.comp hmap hmaps
    convert hcomp using 1
    ext t
    rfl
  have hFcontR : ∀ t ∈ Set.Icc tLo tHi,
      ContinuousOn (fun R => F t R) (Set.Icc rLo rHi) := by
    intro t ht
    have htglobal : t ∈ mainBarrierTRange := htSub ht
    have hmap : ContinuousOn (fun R : ℝ => (t, R)) (Set.Icc rLo rHi) :=
      continuousOn_const.prodMk continuousOn_id
    have hmaps : Set.MapsTo (fun R : ℝ => (t, R))
        (Set.Icc rLo rHi) s := by
      intro R hR
      exact ⟨htglobal, hrSub hR⟩
    have hcomp := hFglobal.comp hmap hmaps
    convert hcomp using 1
    ext R
    rfl
  have hFmono : ∀ R ∈ Set.Icc rLo rHi,
      StrictMonoOn (fun t => F t R) (Set.Icc tLo tHi) := by
    intro R hR t₁ ht₁ t₂ ht₂ h12
    have hRglobal : R ∈ mainBarrierRadiusRange := hrSub hR
    have hA := mainBarrierA_mono_t_on_ranges hRglobal
      (htSub ht₁) (htSub ht₂) h12.le
    have hB := mainBarrierB_strictAnti_t_on_ranges hRglobal
      (htSub ht₁) (htSub ht₂) h12
    dsimp [F]
    linarith
  obtain ⟨tcurve, htcurveCont, htcurveSpec⟩ :=
    exists_continuous_parametric_root (F := F) ht
      hFcontT hFmono hFcontR
      (by intro R hR; simpa [F] using hFleft R hR)
      (by intro R hR; simpa [F] using hFright R hR)
  have hFzero : ∀ R ∈ Set.Icc rLo rHi,
      mainBarrierA (tcurve R) R = mainBarrierB (tcurve R) R := by
    intro R hR
    have hz := (htcurveSpec R hR).2
    change mainBarrierA (tcurve R) R - mainBarrierB (tcurve R) R = 0 at hz
    linarith
  let H : ℝ → ℝ := fun R => mainBarrierB (tcurve R) R - 2 * Real.pi
  have hpairCont : ContinuousOn (fun R => (tcurve R, R))
      (Set.Icc rLo rHi) := htcurveCont.prodMk continuousOn_id
  have hpairMem : Set.MapsTo (fun R => (tcurve R, R))
      (Set.Icc rLo rHi) s := by
    intro R hR
    exact ⟨htSub (htcurveSpec R hR).1, hrSub hR⟩
  have hBcurve : ContinuousOn
      (fun R => mainBarrierB (tcurve R) R) (Set.Icc rLo rHi) := by
    have hcomp := mainBarrier_continuousOn_pair.2.comp hpairCont hpairMem
    convert hcomp using 1
    ext R
    rfl
  have hHcont : ContinuousOn H (Set.Icc rLo rHi) := by
    change ContinuousOn
      ((fun R => mainBarrierB (tcurve R) R) - fun _ => 2 * Real.pi)
      (Set.Icc rLo rHi)
    exact hBcurve.sub continuousOn_const
  have hrLoMem : rLo ∈ Set.Icc rLo rHi := ⟨le_rfl, hr.le⟩
  have hrHiMem : rHi ∈ Set.Icc rLo rHi := ⟨hr.le, le_rfl⟩
  have hBleft' : 2 * Real.pi < mainBarrierB (tcurve rLo) rLo := by
    apply hBleft (tcurve rLo) (htcurveSpec rLo hrLoMem).1
    rw [hFzero rLo hrLoMem]
    ring
  have hBright' : mainBarrierB (tcurve rHi) rHi < 2 * Real.pi := by
    apply hBright (tcurve rHi) (htcurveSpec rHi hrHiMem).1
    rw [hFzero rHi hrHiMem]
    ring
  have hzero : (0 : ℝ) ∈ Set.Icc (H rHi) (H rLo) := by
    constructor
    · dsimp [H]
      linarith
    · dsimp [H]
      linarith
  obtain ⟨R, hR, hHroot⟩ := intermediate_value_Icc' hr.le hHcont hzero
  have hBroot : mainBarrierB (tcurve R) R = 2 * Real.pi := by
    dsimp [H] at hHroot
    linarith
  have hRlt : R < rHi := by
    by_contra hnot
    have heq : R = rHi := le_antisymm hR.2 (le_of_not_gt hnot)
    rw [heq] at hBroot
    linarith
  exact ⟨tcurve R, R, (htcurveSpec R hR).1, hR, hRlt,
    by rw [hFzero R hR, hBroot], hBroot⟩

/-- Specialized sign-certificate interface for the exact rational root box.
Once its four strict boundary inequalities are replayed, this yields the
simultaneous angle solution without any further continuity assumptions. -/
theorem exists_certified_main_angle_critical_pair
    (hFleft : ∀ R ∈ certifiedMainAngleRadiusBox,
      mainBarrierA 1.0037160860750841 R -
        mainBarrierB 1.0037160860750841 R < 0)
    (hFright : ∀ R ∈ certifiedMainAngleRadiusBox,
      0 < mainBarrierA 1.0037160860750846 R -
        mainBarrierB 1.0037160860750846 R)
    (hBleft : ∀ t ∈ certifiedMainAngleTBox,
      mainBarrierA t 8.3034681221114890 -
        mainBarrierB t 8.3034681221114890 = 0 →
        2 * Real.pi < mainBarrierB t 8.3034681221114890)
    (hBright : ∀ t ∈ certifiedMainAngleTBox,
      mainBarrierA t 8.3034681221114900 -
        mainBarrierB t 8.3034681221114900 = 0 →
        mainBarrierB t 8.3034681221114900 < 2 * Real.pi) :
    ∃ t R, t ∈ certifiedMainAngleTBox ∧
      R ∈ certifiedMainAngleRadiusBox ∧
      R < 8.3034681221114900 ∧
      mainBarrierA t R = 2 * Real.pi ∧ mainBarrierB t R = 2 * Real.pi := by
  change ∃ t R, t ∈ Set.Icc 1.0037160860750841 1.0037160860750846 ∧
    R ∈ Set.Icc 8.3034681221114890 8.3034681221114900 ∧
    R < 8.3034681221114900 ∧
    mainBarrierA t R = 2 * Real.pi ∧ mainBarrierB t R = 2 * Real.pi
  exact exists_main_angle_critical_pair_on_subrectangle
    (by norm_num) (by norm_num)
    certifiedMainAngleTBox_subset certifiedMainAngleRadiusBox_subset
    hFleft hFright hBleft hBright

end
end CirclePacking
