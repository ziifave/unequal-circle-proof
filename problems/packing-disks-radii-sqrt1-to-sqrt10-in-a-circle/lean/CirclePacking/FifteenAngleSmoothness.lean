import CirclePacking.FifteenTouchAngleDerivatives
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! Smoothness of the cosine-rule angles along radius segments.  This module
isolates the only domain obligations: radii stay nonzero and the cosine-rule
argument avoids the two singular endpoints of `arccos`. -/

namespace CirclePacking

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

end CirclePacking
