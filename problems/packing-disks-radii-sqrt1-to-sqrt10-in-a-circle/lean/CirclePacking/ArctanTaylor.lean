import Mathlib.Analysis.SpecialFunctions.Complex.Arctan
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import CirclePacking.Angle

/-!
# Certified alternating-series bounds for `arctan`

The global angle-root certificate evaluates contact angles after a half-angle
substitution and uses the alternating power series for `arctan`.  These lemmas
give the analytic bridge from a finite rational Taylor sum to Mathlib's
`Real.arctan`; all remaining numeric work can therefore be checked as rational
arithmetic.
-/

namespace CirclePacking

noncomputable section

def arctanTaylorTerm (x : ℝ) (n : ℕ) : ℝ :=
  x ^ (2 * n + 1) / ((2 * n + 1 : ℕ) : ℝ)

def arctanTaylorPartial (x : ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range n, (-1 : ℝ) ^ i * arctanTaylorTerm x i

private theorem arctanTaylorTerm_nonneg {x : ℝ} (hx : 0 ≤ x) (n : ℕ) :
    0 ≤ arctanTaylorTerm x n := by
  unfold arctanTaylorTerm
  positivity

private theorem arctanTaylorTerm_step_le {x : ℝ}
    (hx0 : 0 ≤ x) (hxhalf : x ≤ 1 / 2) (n : ℕ) :
    arctanTaylorTerm x (n + 1) ≤ arctanTaylorTerm x n := by
  have hx2 : x ^ 2 ≤ 1 / 4 := by nlinarith [sq_nonneg (x - 1 / 2)]
  have hpow : x ^ (2 * (n + 1) + 1) =
      x ^ (2 * n + 1) * x ^ 2 := by
    rw [show 2 * (n + 1) + 1 = (2 * n + 1) + 2 by omega, pow_add]
  have hden₁ : (0 : ℝ) < ((2 * n + 1 : ℕ) : ℝ) := by positivity
  have hden₂ : (0 : ℝ) < ((2 * (n + 1) + 1 : ℕ) : ℝ) := by positivity
  rw [arctanTaylorTerm, arctanTaylorTerm, hpow]
  rw [div_le_div_iff₀ hden₂ hden₁]
  have hp : 0 ≤ x ^ (2 * n + 1) := pow_nonneg hx0 _
  have hcoeff : x ^ 2 * (2 * (n : ℝ) + 1) ≤ 2 * (n : ℝ) + 3 := by
    nlinarith [hx2]
  have hmul : x ^ (2 * n + 1) *
      (2 * (n : ℝ) + 3 - x ^ 2 * (2 * (n : ℝ) + 1)) ≥ 0 :=
    mul_nonneg hp (sub_nonneg.mpr hcoeff)
  have hcast₁ : ((2 * n + 1 : ℕ) : ℝ) = 2 * (n : ℝ) + 1 := by
    push_cast
    ring
  have hcast₂ : ((2 * (n + 1) + 1 : ℕ) : ℝ) = 2 * (n : ℝ) + 3 := by
    push_cast
    ring
  rw [hcast₁, hcast₂]
  nlinarith

private theorem arctanTaylorTerm_antitone {x : ℝ}
    (hx0 : 0 ≤ x) (hxhalf : x ≤ 1 / 2) :
    Antitone (arctanTaylorTerm x) := by
  apply antitone_nat_of_succ_le
  intro n
  exact arctanTaylorTerm_step_le hx0 hxhalf n

private theorem arctanTaylorTerm_le_half_pow {x : ℝ}
    (hx0 : 0 ≤ x) (hxhalf : x ≤ 1 / 2) (n : ℕ) :
    arctanTaylorTerm x n ≤ (1 / 2 : ℝ) ^ n := by
  have hden : (1 : ℝ) ≤ ((2 * n + 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 1 ≤ 2 * n + 1 by omega)
  have hpow₁ : x ^ (2 * n + 1) ≤ (1 / 2 : ℝ) ^ (2 * n + 1) := by
    gcongr
  have hpow₂ : (1 / 2 : ℝ) ^ (2 * n + 1) ≤ (1 / 2 : ℝ) ^ n := by
    rw [show 2 * n + 1 = n + (n + 1) by omega, pow_add]
    have hfactor : (1 / 2 : ℝ) ^ (n + 1) ≤ 1 := by
      exact pow_le_one₀ (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (1 / 2 : ℝ) ≤ 1)
    exact mul_le_of_le_one_right (pow_nonneg (by norm_num) _) hfactor
  unfold arctanTaylorTerm
  calc
    x ^ (2 * n + 1) / ((2 * n + 1 : ℕ) : ℝ) ≤ x ^ (2 * n + 1) :=
      div_le_self (pow_nonneg hx0 _) hden
    _ ≤ (1 / 2 : ℝ) ^ (2 * n + 1) := hpow₁
    _ ≤ (1 / 2 : ℝ) ^ n := hpow₂

private theorem arctanTaylorTerm_summable {x : ℝ}
    (hx0 : 0 ≤ x) (hxhalf : x ≤ 1 / 2) :
    Summable (arctanTaylorTerm x) := by
  have hgeom : Summable (fun n : ℕ => (1 / 2 : ℝ) ^ n) := by
    exact summable_geometric_of_lt_one (by norm_num) (by norm_num)
  apply hgeom.of_norm_bounded
  intro n
  rw [Real.norm_eq_abs, abs_of_nonneg (arctanTaylorTerm_nonneg hx0 n)]
  exact arctanTaylorTerm_le_half_pow hx0 hxhalf n

/-- The arctangent's degree-`n` alternating Taylor polynomial has error at most
the first omitted term, uniformly for `0 ≤ x ≤ 1/2`. -/
theorem arctanTaylor_error_bound {x : ℝ} (hx0 : 0 ≤ x)
    (hxhalf : x ≤ 1 / 2) (n : ℕ) :
    |Real.arctan x - arctanTaylorPartial x n| ≤ arctanTaylorTerm x n := by
  have hxnorm : ‖x‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hx0]
    linarith
  have hseries := Real.hasSum_arctan hxnorm
  have hseries' : HasSum (fun i : ℕ => (-1 : ℝ) ^ i * arctanTaylorTerm x i)
      (Real.arctan x) := by
    simpa [arctanTaylorTerm, mul_div_assoc] using hseries
  have herror := alternating_series_error_bound (arctanTaylorTerm x)
    (arctanTaylorTerm_antitone hx0 hxhalf)
    (arctanTaylorTerm_summable hx0 hxhalf) n
  rw [hseries'.tsum_eq] at herror
  simpa [arctanTaylorPartial] using herror

/-- The principal arccosine is twice the arctangent of the half-angle
parameter. This remains valid when the cosine is negative, which occurs for
some of the central-contact angles in the global certificate. -/
theorem arccos_eq_two_arctan_sqrt_fraction {c : ℝ}
    (hcLo : -1 < c) (hcHi : c < 1) :
    Real.arccos c =
      2 * Real.arctan (Real.sqrt ((1 - c) / (1 + c))) := by
  let q : ℝ := Real.sqrt ((1 - c) / (1 + c))
  have hden : 0 < 1 + c := by linarith
  have hratio : 0 ≤ (1 - c) / (1 + c) :=
    div_nonneg (by linarith) hden.le
  have hq0 : 0 ≤ q := by simp [q]
  have hq2 : q ^ 2 = (1 - c) / (1 + c) := by
    change (Real.sqrt ((1 - c) / (1 + c))) ^ 2 = _
    exact Real.sq_sqrt hratio
  have hratioId : (1 - q ^ 2) / (1 + q ^ 2) = c := by
    rw [hq2]
    field_simp [ne_of_gt hden]
    ring
  have hsqrtSq : (Real.sqrt (1 + q ^ 2)) ^ 2 = 1 + q ^ 2 :=
    Real.sq_sqrt (by positivity)
  have hcosSq : (1 / Real.sqrt (1 + q ^ 2)) ^ 2 =
      1 / (1 + q ^ 2) := by
    rw [one_div, inv_pow, hsqrtSq, one_div]
  have hsinSq : (q / Real.sqrt (1 + q ^ 2)) ^ 2 =
      q ^ 2 / (1 + q ^ 2) := by
    rw [div_pow, hsqrtSq]
  have hratioId' : 2 / (1 + q ^ 2) - 1 = c := by
    calc
      2 / (1 + q ^ 2) - 1 = (1 - q ^ 2) / (1 + q ^ 2) := by
        field_simp
        ring
      _ = c := hratioId
  have hcos : Real.cos (2 * Real.arctan q) = c := by
    rw [Real.cos_two_mul, Real.cos_arctan, hcosSq]
    calc
      2 * (1 / (1 + q ^ 2)) - 1 = 2 / (1 + q ^ 2) - 1 := by ring
      _ = c := hratioId'
  have hangleLo : 0 ≤ 2 * Real.arctan q := by
    have h := Real.arctan_nonneg.mpr hq0
    nlinarith
  have hangleHi : 2 * Real.arctan q ≤ Real.pi := by
    have h := Real.arctan_lt_pi_div_two q
    nlinarith
  calc
    Real.arccos c = Real.arccos (Real.cos (2 * Real.arctan q)) := by rw [hcos]
    _ = 2 * Real.arctan q := Real.arccos_cos hangleLo hangleHi

/-- Halving the arctangent argument via `tan(θ/2)` is the stable form used by
the certificate's Taylor evaluator. -/
theorem arctan_eq_two_arctan_half_quarter {v : ℝ} (hv : 0 ≤ v) :
    Real.arctan v =
      2 * Real.arctan (v / (1 + Real.sqrt (1 + v ^ 2))) := by
  let s : ℝ := Real.sqrt (1 + v ^ 2)
  let u : ℝ := v / (1 + s)
  have hs0 : 0 ≤ s := by simp [s]
  have hs2 : s ^ 2 = 1 + v ^ 2 := by
    change (Real.sqrt (1 + v ^ 2)) ^ 2 = 1 + v ^ 2
    exact Real.sq_sqrt (by positivity)
  have hsGt : v < s := by
    apply (sq_lt_sq₀ hv hs0).mp
    rw [hs2]
    nlinarith
  have hden : 0 < 1 + s := by linarith
  have hu0 : 0 ≤ u := by
    dsimp [u]
    exact div_nonneg hv hden.le
  have huLt : u < 1 := by
    apply (div_lt_one₀ hden).2
    linarith
  have huSqLt : u ^ 2 < 1 := by nlinarith
  have hdoubleDen : (1 + s) ^ 2 - v ^ 2 = 2 * (1 + s) := by
    nlinarith [hs2]
  have hdouble : 1 - u ^ 2 = 2 / (1 + s) := by
    dsimp [u]
    field_simp [ne_of_gt hden]
    nlinarith [hdoubleDen]
  have htanArgument : (u + u) / (1 - u * u) = v := by
    rw [show u * u = u ^ 2 by ring, hdouble]
    dsimp [u]
    field_simp [ne_of_gt hden]
    ring
  have hmul : u * u < 1 := by nlinarith [huSqLt]
  have hsum := Real.arctan_add (x := u) (y := u) hmul
  rw [htanArgument] at hsum
  calc
    Real.arctan v = Real.arctan u + Real.arctan u := hsum.symm
    _ = 2 * Real.arctan u := by ring
    _ = 2 * Real.arctan (v / (1 + Real.sqrt (1 + v ^ 2))) := by
      simp [u, s]

/-- Square of the quarter-angle tangent parameter, rationalized to one square
root. This identity is the basis for replaying rational enclosures of the
Python certificate's nested square-root expressions. -/
theorem arctanQuarterParameter_sq (v : ℝ) :
    (v / (1 + Real.sqrt (1 + v ^ 2))) ^ 2 =
      (Real.sqrt (1 + v ^ 2) - 1) / (Real.sqrt (1 + v ^ 2) + 1) := by
  have hs2 : (Real.sqrt (1 + v ^ 2)) ^ 2 = 1 + v ^ 2 :=
    Real.sq_sqrt (by positivity)
  have hden : (1 + Real.sqrt (1 + v ^ 2)) ≠ 0 := by positivity
  rw [div_pow]
  field_simp [hden]
  nlinarith [hs2]

/-- A rational upper bound on `v²` gives an upper bound on the quarter-angle
parameter, without approximating either square root. -/
theorem arctanQuarterParameter_le_of_sq_bound {v u : ℝ}
    (hv : 0 ≤ v) (hu : 0 ≤ u) (hu1 : u < 1)
    (hbound : 1 + v ^ 2 ≤ ((1 + u ^ 2) / (1 - u ^ 2)) ^ 2) :
    v / (1 + Real.sqrt (1 + v ^ 2)) ≤ u := by
  let s : ℝ := Real.sqrt (1 + v ^ 2)
  let q : ℝ := v / (1 + s)
  have hs0 : 0 ≤ s := by simp [s]
  have hs2 : s ^ 2 = 1 + v ^ 2 := by
    change (Real.sqrt (1 + v ^ 2)) ^ 2 = 1 + v ^ 2
    exact Real.sq_sqrt (by positivity)
  have hden : 0 < 1 - u ^ 2 := by nlinarith
  have htarget0 : 0 ≤ (1 + u ^ 2) / (1 - u ^ 2) :=
    div_nonneg (by positivity) hden.le
  have hsBound : s ≤ (1 + u ^ 2) / (1 - u ^ 2) := by
    apply (sq_le_sq₀ hs0 htarget0).mp
    nlinarith [hbound, hs2]
  have hcross : s * (1 - u ^ 2) ≤ 1 + u ^ 2 :=
    (le_div_iff₀ hden).mp hsBound
  have hq0 : 0 ≤ q := by
    dsimp [q]
    exact div_nonneg hv (by positivity)
  have hqSq : q ^ 2 = (s - 1) / (s + 1) := by
    simpa [q, s] using arctanQuarterParameter_sq v
  have hsden : 0 < s + 1 := by linarith
  have hqSqLe : q ^ 2 ≤ u ^ 2 := by
    rw [hqSq]
    apply (div_le_iff₀ hsden).2
    nlinarith [hcross]
  have hqu : q ≤ u := (sq_le_sq₀ hq0 hu).mp hqSqLe
  simpa [q, s] using hqu

/-- A rational lower bound on `v²` gives a lower bound on the quarter-angle
parameter. -/
theorem le_arctanQuarterParameter_of_sq_bound {v u : ℝ}
    (hv : 0 ≤ v) (hu : 0 ≤ u) (hu1 : u < 1)
    (hbound : ((1 + u ^ 2) / (1 - u ^ 2)) ^ 2 ≤ 1 + v ^ 2) :
    u ≤ v / (1 + Real.sqrt (1 + v ^ 2)) := by
  let s : ℝ := Real.sqrt (1 + v ^ 2)
  let q : ℝ := v / (1 + s)
  have hs0 : 0 ≤ s := by simp [s]
  have hs2 : s ^ 2 = 1 + v ^ 2 := by
    change (Real.sqrt (1 + v ^ 2)) ^ 2 = 1 + v ^ 2
    exact Real.sq_sqrt (by positivity)
  have hden : 0 < 1 - u ^ 2 := by nlinarith
  have htarget0 : 0 ≤ (1 + u ^ 2) / (1 - u ^ 2) :=
    div_nonneg (by positivity) hden.le
  have hsBound : (1 + u ^ 2) / (1 - u ^ 2) ≤ s := by
    apply (sq_le_sq₀ htarget0 hs0).mp
    nlinarith [hbound, hs2]
  have hcross : 1 + u ^ 2 ≤ s * (1 - u ^ 2) :=
    (div_le_iff₀ hden).mp hsBound
  have hq0 : 0 ≤ q := by
    dsimp [q]
    exact div_nonneg hv (by positivity)
  have hqSq : q ^ 2 = (s - 1) / (s + 1) := by
    simpa [q, s] using arctanQuarterParameter_sq v
  have hsden : 0 < s + 1 := by linarith
  have huSqLe : u ^ 2 ≤ q ^ 2 := by
    rw [hqSq]
    apply (le_div_iff₀ hsden).2
    nlinarith [hcross]
  have huq : u ≤ q := (sq_le_sq₀ hu hq0).mp huSqLe
  simpa [q, s] using huq

/-- Corollary specialized to the half-angle ratio arising from `arccos`. -/
def arccosQuarterParameter (c : ℝ) : ℝ :=
  Real.sqrt ((1 - c) / (1 + c)) /
    (1 + Real.sqrt (1 + (Real.sqrt ((1 - c) / (1 + c))) ^ 2))

theorem arccosQuarterParameter_le_of_ratio_bound {c u : ℝ}
    (hcLo : -1 < c) (hcHi : c < 1) (hu : 0 ≤ u) (hu1 : u < 1)
    (hbound : 1 + (1 - c) / (1 + c) ≤
      ((1 + u ^ 2) / (1 - u ^ 2)) ^ 2) :
    arccosQuarterParameter c ≤ u := by
  have hden : 0 < 1 + c := by linarith
  have hratio : 0 ≤ (1 - c) / (1 + c) :=
    div_nonneg (by linarith) hden.le
  have hrootSq : (Real.sqrt ((1 - c) / (1 + c))) ^ 2 =
      (1 - c) / (1 + c) := Real.sq_sqrt hratio
  have h := arctanQuarterParameter_le_of_sq_bound
    (Real.sqrt_nonneg _) hu hu1 (by rw [hrootSq]; exact hbound)
  simpa [arccosQuarterParameter] using h

theorem le_arccosQuarterParameter_of_ratio_bound {c u : ℝ}
    (hcLo : -1 < c) (hcHi : c < 1) (hu : 0 ≤ u) (hu1 : u < 1)
    (hbound : ((1 + u ^ 2) / (1 - u ^ 2)) ^ 2 ≤
      1 + (1 - c) / (1 + c)) :
    u ≤ arccosQuarterParameter c := by
  have hden : 0 < 1 + c := by linarith
  have hratio : 0 ≤ (1 - c) / (1 + c) :=
    div_nonneg (by linarith) hden.le
  have hrootSq : (Real.sqrt ((1 - c) / (1 + c))) ^ 2 =
      (1 - c) / (1 + c) := Real.sq_sqrt hratio
  have h := le_arctanQuarterParameter_of_sq_bound
    (Real.sqrt_nonneg _) hu hu1 (by rw [hrootSq]; exact hbound)
  simpa [arccosQuarterParameter] using h

/-- Exact bridge from `arccos` to the quarter-angle `arctan` used in the
rational angle certificate. -/
theorem arccos_eq_four_arctan_quarter_angle {c : ℝ}
    (hcLo : -1 < c) (hcHi : c < 1) :
    Real.arccos c =
      4 * Real.arctan
        (Real.sqrt ((1 - c) / (1 + c)) /
          (1 + Real.sqrt (1 + (Real.sqrt ((1 - c) / (1 + c))) ^ 2))) := by
  rw [arccos_eq_two_arctan_sqrt_fraction hcLo hcHi]
  rw [arctan_eq_two_arctan_half_quarter
    (v := Real.sqrt ((1 - c) / (1 + c))) (Real.sqrt_nonneg _)]
  ring

theorem arccos_eq_four_arctan_quarterParameter {c : ℝ}
    (hcLo : -1 < c) (hcHi : c < 1) :
    Real.arccos c = 4 * Real.arctan (arccosQuarterParameter c) := by
  simpa [arccosQuarterParameter] using
    arccos_eq_four_arctan_quarter_angle hcLo hcHi

theorem touchAngle_eq_four_arctan_quarterParameter {a b d : ℝ}
    (hcLo : -1 < touchCosine a b d)
    (hcHi : touchCosine a b d < 1) :
    touchAngle a b d = 4 * Real.arctan
      (arccosQuarterParameter (touchCosine a b d)) := by
  exact arccos_eq_four_arctan_quarterParameter hcLo hcHi

/-- Replacing an `arccos` value by the finite rational Taylor sum incurs at
most four times the first omitted alternating-series term. -/
theorem arccos_quarterTaylor_error_bound {c : ℝ}
    (hcLo : -1 < c) (hcHi : c < 1)
    (hq0 : 0 ≤ arccosQuarterParameter c)
    (hqhalf : arccosQuarterParameter c ≤ 1 / 2) (n : ℕ) :
    |Real.arccos c - 4 * arctanTaylorPartial
      (arccosQuarterParameter c) n| ≤
        4 * arctanTaylorTerm (arccosQuarterParameter c) n := by
  rw [arccos_eq_four_arctan_quarterParameter hcLo hcHi]
  have h := arctanTaylor_error_bound hq0 hqhalf n
  calc
    |4 * Real.arctan (arccosQuarterParameter c) -
        4 * arctanTaylorPartial (arccosQuarterParameter c) n| =
        4 * |Real.arctan (arccosQuarterParameter c) -
          arctanTaylorPartial (arccosQuarterParameter c) n| := by
            calc
              |4 * Real.arctan (arccosQuarterParameter c) -
                  4 * arctanTaylorPartial (arccosQuarterParameter c) n| =
                  |4 * (Real.arctan (arccosQuarterParameter c) -
                    arctanTaylorPartial (arccosQuarterParameter c) n)| := by
                      congr 1
                      ring
              _ = |4| * |Real.arctan (arccosQuarterParameter c) -
                    arctanTaylorPartial (arccosQuarterParameter c) n| := abs_mul _ _
              _ = 4 * |Real.arctan (arccosQuarterParameter c) -
                    arctanTaylorPartial (arccosQuarterParameter c) n| := by norm_num
    _ ≤ 4 * arctanTaylorTerm (arccosQuarterParameter c) n :=
      mul_le_mul_of_nonneg_left h (by norm_num)

theorem touchAngle_quarterTaylor_error_bound {a b d : ℝ}
    (hcLo : -1 < touchCosine a b d)
    (hcHi : touchCosine a b d < 1)
    (hq0 : 0 ≤ arccosQuarterParameter (touchCosine a b d))
    (hqhalf : arccosQuarterParameter (touchCosine a b d) ≤ 1 / 2)
    (n : ℕ) :
    |touchAngle a b d - 4 * arctanTaylorPartial
      (arccosQuarterParameter (touchCosine a b d)) n| ≤
        4 * arctanTaylorTerm
          (arccosQuarterParameter (touchCosine a b d)) n := by
  exact arccos_quarterTaylor_error_bound hcLo hcHi hq0 hqhalf n

end

end CirclePacking
