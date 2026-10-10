import CirclePacking.FifteenTouchAngleDerivatives

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

end CirclePacking
