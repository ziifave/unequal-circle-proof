import CirclePacking.FifteenTouchAngleDerivatives
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! Smoothness of the cosine-rule angles along radius segments.  This module
isolates the only domain obligations: radii stay nonzero and the cosine-rule
argument avoids the two singular endpoints of `arccos`. -/

namespace CirclePacking

/-- The cosine-rule argument lies strictly between `-1` and `1` whenever the
two radii satisfy the strict triangle inequalities for a contact distance of
two. -/
theorem fifteenAngleCosineArgument_mem_Ioo
    {x y : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hsum : 2 < x + y) (hdiff : |x - y| < 2) :
    fifteenAngleCosineArgument x y ∈ Set.Ioo (-1) 1 := by
  have hden : 0 < 2 * x * y := by positivity
  change -1 < fifteenAngleCosineArgument x y ∧
    fifteenAngleCosineArgument x y < 1
  unfold fifteenAngleCosineArgument
  constructor
  · rw [lt_div_iff₀ hden]
    have hsumSq : (2 : ℝ) ^ 2 < (x + y) ^ 2 :=
      (sq_lt_sq₀ (by norm_num) (by linarith)).2 hsum
    nlinarith [hsumSq]
  · rw [div_lt_iff₀ hden]
    have hdiffSq : (x - y) ^ 2 < (2 : ℝ) ^ 2 := by
      have h := (sq_lt_sq₀ (abs_nonneg (x - y)) (by norm_num : (0 : ℝ) ≤ 2)).2 hdiff
      simpa [sq_abs] using h
    nlinarith [hdiffSq]

theorem fifteenTouchAngle_segment_contDiffOn
    {s : Set ℝ} (x y dx dy : ℝ)
    (hx : ∀ t ∈ s, x + t * dx ≠ 0)
    (hy : ∀ t ∈ s, y + t * dy ≠ 0)
    (hminus : ∀ t ∈ s,
      fifteenAngleCosineArgument (x + t * dx) (y + t * dy) ≠ -1)
    (hplus : ∀ t ∈ s,
      fifteenAngleCosineArgument (x + t * dx) (y + t * dy) ≠ 1) :
    ContDiffOn ℝ 2
      (fun t : ℝ => fifteenTouchAngle (x + t * dx) (y + t * dy)) s := by
  let X : ℝ → ℝ := fun t => x + t * dx
  let Y : ℝ → ℝ := fun t => y + t * dy
  let C : ℝ → ℝ := fun t => fifteenAngleCosineArgument (X t) (Y t)
  have hnum : ContDiffOn ℝ 2
      (fun t : ℝ => (X t) ^ 2 + (Y t) ^ 2 - 4) s := by
    fun_prop
  have hden : ContDiffOn ℝ 2 (fun t : ℝ => 2 * X t * Y t) s := by
    fun_prop
  have hden0 : ∀ t ∈ s, 2 * X t * Y t ≠ 0 := by
    intro t ht
    exact mul_ne_zero (mul_ne_zero (by norm_num) (hx t ht)) (hy t ht)
  have hC : ContDiffOn ℝ 2 C s := by
    dsimp [C]
    change ContDiffOn ℝ 2
      (fun t : ℝ => ((X t) ^ 2 + (Y t) ^ 2 - 4) / (2 * X t * Y t)) s
    exact hnum.div hden hden0
  have hmaps : Set.MapsTo C s ({-1, 1}ᶜ) := by
    intro t ht
    change C t ∉ ({-1, 1} : Set ℝ)
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    intro hbad
    rcases hbad with hbad | hbad
    · exact hminus t ht hbad
    · exact hplus t ht hbad
  have hangle := (Real.contDiffOn_arccos (n := 2)).comp hC hmaps
  change ContDiffOn ℝ 2 (fun t : ℝ => Real.arccos (C t)) s at hangle
  simpa [fifteenTouchAngle, C, X, Y] using hangle

theorem fifteenDetourAngle_segment_contDiffOn
    {s : Set ℝ} (b x y dx dy : ℝ)
    (hb : b ≠ 0)
    (hx : ∀ t ∈ s, x + t * dx ≠ 0)
    (hy : ∀ t ∈ s, y + t * dy ≠ 0)
    (hminusX : ∀ t ∈ s,
      fifteenAngleCosineArgument (x + t * dx) b ≠ -1)
    (hplusX : ∀ t ∈ s,
      fifteenAngleCosineArgument (x + t * dx) b ≠ 1)
    (hminusY : ∀ t ∈ s,
      fifteenAngleCosineArgument (y + t * dy) b ≠ -1)
    (hplusY : ∀ t ∈ s,
      fifteenAngleCosineArgument (y + t * dy) b ≠ 1) :
    ContDiffOn ℝ 2
      (fun t : ℝ => fifteenDetourAngleAlongSegment b x y dx dy t) s := by
  have hfirst := fifteenTouchAngle_segment_contDiffOn
    (s := s) x b dx 0
    (fun t ht => hx t ht)
    (fun t _ => by simpa using hb)
    (fun t ht => by simpa using hminusX t ht)
    (fun t ht => by simpa using hplusX t ht)
  have hsecond := fifteenTouchAngle_segment_contDiffOn
    (s := s) y b dy 0
    (fun t ht => hy t ht)
    (fun t _ => by simpa using hb)
    (fun t ht => by simpa using hminusY t ht)
    (fun t ht => by simpa using hplusY t ht)
  have hfirst' : ContDiffOn ℝ 2
      (fun t : ℝ => fifteenTouchAngle (x + t * dx) b) s := by
    simpa using hfirst
  have hsecond' : ContDiffOn ℝ 2
      (fun t : ℝ => fifteenTouchAngle (y + t * dy) b) s := by
    simpa using hsecond
  have hmiddle : ContDiffOn ℝ 2
      (fun _ : ℝ => fifteenTouchAngle b b) s := contDiffOn_const
  have hsum := (hfirst'.add hmiddle).add hsecond'
  change ContDiffOn ℝ 2
    (fun t : ℝ =>
      (fifteenTouchAngle (x + t * dx) b + fifteenTouchAngle b b) +
        fifteenTouchAngle (y + t * dy) b) s
  simpa [add_assoc] using hsum

/-- The exact second derivative of `arccos` on its smooth interval. -/
theorem fifteen_iteratedDeriv_two_arccos
    {x : ℝ} (hxlo : -1 < x) (hxhi : x < 1) :
    iteratedDeriv 2 Real.arccos x =
      -(x / Real.sqrt (1 - x ^ 2) ^ 3) := by
  have hleft : 0 < 1 - x := by linarith
  have hright : 0 < 1 + x := by linarith
  have hu : 0 < 1 - x ^ 2 := by
    nlinarith [mul_pos hleft hright]
  have hsqrt : Real.sqrt (1 - x ^ 2) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hu)
  have hpolyRaw := (hasDerivAt_id x).pow 2
  have hpoly : HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := by
    have hpolyRaw' := hpolyRaw.congr_deriv (by norm_num [id] :
      (2 : ℝ) * id x ^ (2 - 1) * 1 = 2 * x)
    exact hpolyRaw'.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun y => by simp [id])
  have hrad : HasDerivAt (fun y : ℝ => 1 - y ^ 2) (-2 * x) x := by
    convert (hasDerivAt_const x 1).sub hpoly using 1 <;> ring
  have hsqrt' := (Real.hasDerivAt_sqrt (ne_of_gt hu)).comp x hrad
  have hinv := hsqrt'.inv hsqrt
  have hsecond : HasDerivAt
      (fun y : ℝ => -(1 / Real.sqrt (1 - y ^ 2)))
      (-(x / Real.sqrt (1 - x ^ 2) ^ 3)) x := by
    convert hinv.neg using 1
    · ext y
      simp [Function.comp_apply, one_div]
    · simp only [Function.comp_apply]
      field_simp [hsqrt]
  calc
    iteratedDeriv 2 Real.arccos x = deriv (deriv Real.arccos) x := by
      rw [show (2 : ℕ) = 1 + 1 by norm_num, iteratedDeriv_succ]
      simp
    _ = deriv (fun y : ℝ => -(1 / Real.sqrt (1 - y ^ 2))) x := by
      rw [Real.deriv_arccos]
    _ = -(x / Real.sqrt (1 - x ^ 2) ^ 3) := hsecond.deriv

/-- Chain-rule form of the second derivative of a cosine-rule arccosine.
This is the exact expression whose rational interval enclosure supplies the
remaining Taylor-curvature estimate. -/
theorem fifteen_iteratedDeriv_two_arccos_comp
    (f : ℝ → ℝ) (x : ℝ)
    (hf : ContDiffAt ℝ 2 f x)
    (hflo : -1 < f x) (hfhi : f x < 1) :
    iteratedDeriv 2 (Real.arccos ∘ f) x =
      (deriv f x) ^ 2 *
          (-(f x / Real.sqrt (1 - (f x) ^ 2) ^ 3)) +
        iteratedDeriv 2 f x *
          (-(1 / Real.sqrt (1 - (f x) ^ 2))) := by
  have hg : ContDiffAt ℝ 2 Real.arccos (f x) :=
    Real.contDiffAt_arccos (ne_of_gt (by linarith [hflo]))
      (ne_of_lt (by linarith [hfhi]))
  rw [iteratedDeriv_scomp_two hg hf]
  rw [fifteen_iteratedDeriv_two_arccos hflo hfhi, Real.deriv_arccos]
  simp only [smul_eq_mul]

/-- Second derivative of a genuine contact-angle path, written entirely in
terms of the cosine-rule cap. This is the formula used for the forthcoming
rational curvature enclosure. -/
theorem fifteenTouchAngle_segment_iteratedDeriv_two
    (x y dx dy t : ℝ)
    (hx : x + t * dx ≠ 0) (hy : y + t * dy ≠ 0)
    (hlo : -1 < fifteenAngleCosineArgument (x + t * dx) (y + t * dy))
    (hhi : fifteenAngleCosineArgument (x + t * dx) (y + t * dy) < 1) :
    iteratedDeriv 2
        (fun u : ℝ => fifteenTouchAngle (x + u * dx) (y + u * dy)) t =
      (deriv (fun u : ℝ =>
          fifteenAngleCosineArgument (x + u * dx) (y + u * dy)) t) ^ 2 *
          (-(fifteenAngleCosineArgument (x + t * dx) (y + t * dy) /
            Real.sqrt (1 - fifteenAngleCosineArgument
              (x + t * dx) (y + t * dy) ^ 2) ^ 3)) +
        iteratedDeriv 2 (fun u : ℝ =>
          fifteenAngleCosineArgument (x + u * dx) (y + u * dy)) t *
          (-(1 / Real.sqrt (1 - fifteenAngleCosineArgument
            (x + t * dx) (y + t * dy) ^ 2))) := by
  let cap : ℝ → ℝ := fun u =>
    fifteenAngleCosineArgument (x + u * dx) (y + u * dy)
  have hcap : ContDiffAt ℝ 2 cap t := by
    have hnum : ContDiffAt ℝ 2
        (fun u : ℝ => (x + u * dx) ^ 2 + (y + u * dy) ^ 2 - 4) t := by
      fun_prop
    have hden : ContDiffAt ℝ 2
        (fun u : ℝ => 2 * (x + u * dx) * (y + u * dy)) t := by
      fun_prop
    have hden0 : 2 * (x + t * dx) * (y + t * dy) ≠ 0 :=
      mul_ne_zero (mul_ne_zero (by norm_num) hx) hy
    change ContDiffAt ℝ 2
      (fun u : ℝ =>
        ((x + u * dx) ^ 2 + (y + u * dy) ^ 2 - 4) /
          (2 * (x + u * dx) * (y + u * dy))) t
    exact hnum.div hden hden0
  have hformula := fifteen_iteratedDeriv_two_arccos_comp cap t hcap hlo hhi
  change iteratedDeriv 2 (Real.arccos ∘ cap) t = _
  exact hformula

/-- First derivative of the cosine-rule argument along an affine pair of
positive-radius paths.  Keeping this rational expression explicit is the
starting point for a certified second-derivative bound. -/
theorem fifteenAngleCosineArgument_segment_hasDerivAt
    (x y dx dy t : ℝ)
    (hx : x + t * dx ≠ 0) (hy : y + t * dy ≠ 0) :
    HasDerivAt
      (fun u : ℝ => fifteenAngleCosineArgument (x + u * dx) (y + u * dy))
      (((x + t * dx) ^ 2 - (y + t * dy) ^ 2 + 4) /
          (2 * (x + t * dx) ^ 2 * (y + t * dy)) * dx +
        ((y + t * dy) ^ 2 - (x + t * dx) ^ 2 + 4) /
          (2 * (x + t * dx) * (y + t * dy) ^ 2) * dy) t := by
  let X : ℝ → ℝ := fun u => x + u * dx
  let Y : ℝ → ℝ := fun u => y + u * dy
  have hX : HasDerivAt X dx t := by
    convert ((hasDerivAt_id t).const_mul dx).const_add x using 1
    · ext u
      simp [X]
      ring
    · simp
  have hY : HasDerivAt Y dy t := by
    convert ((hasDerivAt_id t).const_mul dy).const_add y using 1
    · ext u
      simp [Y]
      ring
    · simp
  have hnum : HasDerivAt (fun u : ℝ => X u ^ 2 + Y u ^ 2 - 4)
      (2 * X t * dx + 2 * Y t * dy) t := by
    have h := ((hX.pow 2).add (hY.pow 2)).sub_const 4
    convert h using 1 <;> simp [X, Y]
  have hden : HasDerivAt (fun u : ℝ => 2 * X u * Y u)
      (2 * (dx * Y t + X t * dy)) t := by
    have h := (hX.mul hY).const_mul 2
    convert h using 1
    · ext u
      simp [X, Y]
      ring
  have hden0 : 2 * X t * Y t ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) hx) hy
  have hquotient := hnum.div hden hden0
  have hquotientDeriv :
      ((2 * X t * dx + 2 * Y t * dy) * (2 * X t * Y t) -
        (X t ^ 2 + Y t ^ 2 - 4) * (2 * (dx * Y t + X t * dy))) /
          (2 * X t * Y t) ^ 2 =
        ((X t ^ 2 - Y t ^ 2 + 4) /
            (2 * X t ^ 2 * Y t) * dx +
          (Y t ^ 2 - X t ^ 2 + 4) /
            (2 * X t * Y t ^ 2) * dy) := by
    field_simp [hx, hy]
    ring
  have hquotient' := hquotient.congr_deriv hquotientDeriv
  have hquotientPoint : HasDerivAt
      (fun u : ℝ => (X u ^ 2 + Y u ^ 2 - 4) / (2 * X u * Y u))
      (((X t ^ 2 - Y t ^ 2 + 4) /
          (2 * X t ^ 2 * Y t) * dx) +
        ((Y t ^ 2 - X t ^ 2 + 4) /
          (2 * X t * Y t ^ 2) * dy)) t := by
    convert hquotient' using 1
  apply hquotientPoint.congr_of_eventuallyEq
  filter_upwards with u
  simp [fifteenAngleCosineArgument, X, Y]

/-- Along an affine pair of radii, the first partial derivative of the
cosine-rule cap also has an explicit derivative. -/
private theorem fifteenAngleCapGradientX_segment_hasDerivAt
    (x y dx dy t : ℝ)
    (hx : x + t * dx ≠ 0) (hy : y + t * dy ≠ 0) :
    HasDerivAt
      (fun u : ℝ =>
        ((x + u * dx) ^ 2 - (y + u * dy) ^ 2 + 4) /
          (2 * (x + u * dx) ^ 2 * (y + u * dy)))
      (((y + t * dy) ^ 2 - 4) /
          ((x + t * dx) ^ 3 * (y + t * dy)) * dx -
        ((x + t * dx) ^ 2 + (y + t * dy) ^ 2 + 4) /
          (2 * (x + t * dx) ^ 2 * (y + t * dy) ^ 2) * dy) t := by
  let X : ℝ → ℝ := fun u => x + u * dx
  let Y : ℝ → ℝ := fun u => y + u * dy
  have hX : HasDerivAt X dx t := by
    convert ((hasDerivAt_id t).const_mul dx).const_add x using 1
    · ext u
      simp [X]
      ring
    · simp
  have hY : HasDerivAt Y dy t := by
    convert ((hasDerivAt_id t).const_mul dy).const_add y using 1
    · ext u
      simp [Y]
      ring
    · simp
  have hnum : HasDerivAt (fun u : ℝ => X u ^ 2 - Y u ^ 2 + 4)
      (2 * X t * dx - 2 * Y t * dy) t := by
    have h := ((hX.pow 2).sub (hY.pow 2)).add_const 4
    convert h using 1 <;> simp [X, Y]
  have hden : HasDerivAt (fun u : ℝ => 2 * X u ^ 2 * Y u)
      (2 * (2 * X t * dx * Y t + X t ^ 2 * dy)) t := by
    have h := ((hX.pow 2).mul hY).const_mul 2
    convert h using 1
    · ext u
      simp [X, Y]
      ring
    · simp only [Nat.reduceSub, pow_one, pow_two, Pi.pow_apply]
      ring
  have hden0 : 2 * X t ^ 2 * Y t ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 2 hx)) hy
  have hquotient := hnum.div hden hden0
  have hquotientDeriv :
      ((2 * X t * dx - 2 * Y t * dy) * (2 * X t ^ 2 * Y t) -
        (X t ^ 2 - Y t ^ 2 + 4) *
          (2 * (2 * X t * dx * Y t + X t ^ 2 * dy))) /
          (2 * X t ^ 2 * Y t) ^ 2 =
        ((Y t ^ 2 - 4) / (X t ^ 3 * Y t) * dx -
          (X t ^ 2 + Y t ^ 2 + 4) / (2 * X t ^ 2 * Y t ^ 2) * dy) := by
    field_simp [hx, hy]
    ring_nf
  have hquotient' := hquotient.congr_deriv hquotientDeriv
  have hquotientPoint : HasDerivAt
      (fun u : ℝ => (X u ^ 2 - Y u ^ 2 + 4) / (2 * X u ^ 2 * Y u))
      ((Y t ^ 2 - 4) / (X t ^ 3 * Y t) * dx -
        (X t ^ 2 + Y t ^ 2 + 4) / (2 * X t ^ 2 * Y t ^ 2) * dy) t := by
    convert hquotient' using 1
  apply hquotientPoint.congr_of_eventuallyEq
  filter_upwards with u
  simp [X, Y]

/-- Exact Hessian of the cosine-rule cap along an affine radius segment.
The eventual nonvanishing hypothesis localizes the quotient derivative at the
evaluation point, including when that point is an endpoint of the candidate
segment. -/
theorem fifteenAngleCosineArgument_segment_iteratedDeriv_two
    (x y dx dy t : ℝ)
    (hvalid : ∀ᶠ u in nhds t,
      x + u * dx ≠ 0 ∧ y + u * dy ≠ 0) :
    iteratedDeriv 2
        (fun u : ℝ => fifteenAngleCosineArgument (x + u * dx) (y + u * dy)) t =
      ((y + t * dy) ^ 2 - 4) /
          ((x + t * dx) ^ 3 * (y + t * dy)) * dx ^ 2 -
        ((x + t * dx) ^ 2 + (y + t * dy) ^ 2 + 4) /
          ((x + t * dx) ^ 2 * (y + t * dy) ^ 2) * (dx * dy) +
        ((x + t * dx) ^ 2 - 4) /
          ((x + t * dx) * (y + t * dy) ^ 3) * dy ^ 2 := by
  let cap : ℝ → ℝ := fun u =>
    fifteenAngleCosineArgument (x + u * dx) (y + u * dy)
  let slope : ℝ → ℝ := fun u =>
    ((x + u * dx) ^ 2 - (y + u * dy) ^ 2 + 4) /
        (2 * (x + u * dx) ^ 2 * (y + u * dy)) * dx +
      ((y + u * dy) ^ 2 - (x + u * dx) ^ 2 + 4) /
        (2 * (x + u * dx) * (y + u * dy) ^ 2) * dy
  have hfirst : deriv cap =ᶠ[nhds t] slope := by
    filter_upwards [hvalid] with u hu
    have h := fifteenAngleCosineArgument_segment_hasDerivAt
      x y dx dy u hu.1 hu.2
    have hderiv := h.deriv
    simpa [cap, slope] using hderiv
  let X : ℝ → ℝ := fun u => x + u * dx
  let Y : ℝ → ℝ := fun u => y + u * dy
  have hx' : x + t * dx ≠ 0 ∧ y + t * dy ≠ 0 := by
    exact hvalid.self_of_nhds
  have hqx := fifteenAngleCapGradientX_segment_hasDerivAt
    x y dx dy t hx'.1 hx'.2
  have hqy := fifteenAngleCapGradientX_segment_hasDerivAt
    y x dy dx t hx'.2 hx'.1
  have hqx' : HasDerivAt
      (fun u : ℝ =>
        ((X u ^ 2 - Y u ^ 2 + 4) / (2 * X u ^ 2 * Y u)) * dx)
      (((Y t ^ 2 - 4) / (X t ^ 3 * Y t) * dx -
        (X t ^ 2 + Y t ^ 2 + 4) / (2 * X t ^ 2 * Y t ^ 2) * dy) * dx) t := by
    convert hqx.mul_const dx using 1
  have hqy' : HasDerivAt
      (fun u : ℝ =>
        ((Y u ^ 2 - X u ^ 2 + 4) / (2 * Y u ^ 2 * X u)) * dy)
      (((X t ^ 2 - 4) / (Y t ^ 3 * X t) * dy -
        (Y t ^ 2 + X t ^ 2 + 4) / (2 * Y t ^ 2 * X t ^ 2) * dx) * dy) t := by
    convert hqy.mul_const dy using 1
  have hslope : HasDerivAt slope
      (((Y t ^ 2 - 4) / (X t ^ 3 * Y t) * dx -
        (X t ^ 2 + Y t ^ 2 + 4) / (2 * X t ^ 2 * Y t ^ 2) * dy) * dx +
        ((X t ^ 2 - 4) / (Y t ^ 3 * X t) * dy -
        (Y t ^ 2 + X t ^ 2 + 4) / (2 * Y t ^ 2 * X t ^ 2) * dx) * dy) t := by
    have h := hqx'.add hqy'
    convert h using 1
    · ext u
      simp only [slope, X, Y]
      have hden : 2 * (x + u * dx) * (y + u * dy) ^ 2 =
          2 * (y + u * dy) ^ 2 * (x + u * dx) := by ring
      rw [hden]
      rfl
  have hsecond : HasDerivAt (deriv cap)
      (((Y t ^ 2 - 4) / (X t ^ 3 * Y t) * dx -
        (X t ^ 2 + Y t ^ 2 + 4) / (2 * X t ^ 2 * Y t ^ 2) * dy) * dx +
        ((X t ^ 2 - 4) / (Y t ^ 3 * X t) * dy -
        (Y t ^ 2 + X t ^ 2 + 4) / (2 * Y t ^ 2 * X t ^ 2) * dx) * dy) t :=
    hslope.congr_of_eventuallyEq hfirst
  have hiter : iteratedDeriv 2 cap t = deriv (deriv cap) t := by
    rw [show (2 : ℕ) = 1 + 1 by norm_num, iteratedDeriv_succ]
    simp
  have hX0 : X t ≠ 0 := hx'.1
  have hY0 : Y t ≠ 0 := hx'.2
  have hformula :
      (((Y t ^ 2 - 4) / (X t ^ 3 * Y t) * dx -
        (X t ^ 2 + Y t ^ 2 + 4) / (2 * X t ^ 2 * Y t ^ 2) * dy) * dx +
        ((X t ^ 2 - 4) / (Y t ^ 3 * X t) * dy -
        (Y t ^ 2 + X t ^ 2 + 4) / (2 * Y t ^ 2 * X t ^ 2) * dx) * dy) =
      (Y t ^ 2 - 4) / (X t ^ 3 * Y t) * dx ^ 2 -
        (X t ^ 2 + Y t ^ 2 + 4) / (X t ^ 2 * Y t ^ 2) * (dx * dy) +
        (X t ^ 2 - 4) / (X t * Y t ^ 3) * dy ^ 2 := by
    field_simp [hX0, hY0]
    ring_nf
  rw [hiter, hsecond.deriv]
  simpa [X, Y] using hformula

end CirclePacking
