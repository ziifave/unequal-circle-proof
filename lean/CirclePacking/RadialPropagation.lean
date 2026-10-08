import CirclePacking.CertificateTree
import CirclePacking.GlobalAnchorRadius

namespace CirclePacking

/-!
# Soundness of radial lower-bound propagation

The Python radial contractor uses non-overlap to infer
`s_i ≥ r_i + r_j - upper_j`.  This file proves that implication from the
packing geometry and records it as a transformation of a rational box.  It is
the local soundness fact needed before replaying the full propagation pass at
every node of the global radial tree.
-/

theorem separated_implies_radial_sum_lower
    {c e : Circle} {s t : ℝ}
    (hsep : Separated c e)
    (hs : globalPointNorm c.center = s)
    (ht : globalPointNorm e.center = t) :
    c.radius + e.radius ≤ s + t := by
  have hdistSq : (c.radius + e.radius) ^ 2 ≤
      globalPointNorm (c.center.1 - e.center.1, c.center.2 - e.center.2) ^ 2 := by
    simpa [Separated, distSq, globalPointNorm_sq] using hsep
  have hdist : c.radius + e.radius ≤
      globalPointNorm (c.center.1 - e.center.1, c.center.2 - e.center.2) :=
    (sq_le_sq₀ (add_nonneg c.radius_nonneg e.radius_nonneg)
      (globalPointNorm_nonneg _)).mp hdistSq
  calc
    c.radius + e.radius ≤
        globalPointNorm (c.center.1 - e.center.1, c.center.2 - e.center.2) := hdist
    _ ≤ globalPointNorm c.center + globalPointNorm e.center :=
      globalPointNorm_triangle c.center e.center
    _ = s + t := by rw [hs, ht]

namespace RationalBox

def propagatePairLower (b : RationalBox d) (i j : Fin d)
    (riLower rjLower : ℚ) : RationalBox d :=
  b.setLo i (max (b.lo i) (riLower + rjLower - b.hi j))

def propagateOrderedPair (b : RationalBox d) (rootLower : Fin d → ℚ)
    (i j : Fin d) : RationalBox d :=
  if _h : i ≠ j then
    b.propagatePairLower i j (rootLower i) (rootLower j)
  else b

def propagatePairs (pairs : List (Fin d × Fin d))
    (rootLower : Fin d → ℚ) (b : RationalBox d) : RationalBox d :=
  pairs.foldl (fun current pair =>
    current.propagateOrderedPair rootLower pair.1 pair.2) b

def allDistinctOrderedPairs (d : ℕ) : List (Fin d × Fin d) :=
  (List.product (List.finRange d) (List.finRange d)).filter
    (fun pair => decide (pair.1 ≠ pair.2))

theorem mem_allDistinctOrderedPairs {d : ℕ} {i j : Fin d}
    (hij : i ≠ j) :
    (i, j) ∈ allDistinctOrderedPairs d := by
  simp [allDistinctOrderedPairs, hij]

theorem contains_after_pair_propagation
    {b : RationalBox d} {x : Fin d → ℝ} {i j : Fin d}
    (riLower rjLower : ℚ) (c e : Circle)
    (hx : Contains b x)
    (hsep : Separated c e)
    (hri : (riLower : ℝ) ≤ c.radius)
    (hrj : (rjLower : ℝ) ≤ e.radius)
    (hci : globalPointNorm c.center = x i)
    (hcj : globalPointNorm e.center = x j) :
    Contains (b.propagatePairLower i j riLower rjLower) x := by
  have hradial := separated_implies_radial_sum_lower hsep hci hcj
  have hderived :
      (riLower : ℝ) + (rjLower : ℝ) - (b.hi j : ℝ) ≤ x i := by
    have hxj := (hx j).2
    linarith
  have hcurrent : (b.lo i : ℝ) ≤ x i := (hx i).1
  have hderivedCast :
      ((riLower + rjLower - b.hi j : ℚ) : ℝ) ≤ x i := by
    exact_mod_cast hderived
  have hmax :
      max (b.lo i : ℝ) ((riLower + rjLower - b.hi j : ℚ) : ℝ) ≤ x i :=
    max_le_iff.mpr ⟨hcurrent, hderivedCast⟩
  have hcut :
      ((max (b.lo i) (riLower + rjLower - b.hi j) : ℚ) : ℝ) ≤ x i := by
    simpa only [Rat.cast_max] using hmax
  exact contains_setLo hx hcut

theorem packing_pair_propagation_sound
    {n : ℕ} {R : ℝ} (P : Packing n R)
    (b : RationalBox n) (i j : Fin n)
    (riLower rjLower : ℚ)
    (hx : Contains b (fun k => globalPointNorm (P.circles k).center))
    (hri : (riLower : ℝ) ≤ (P.circles i).radius)
    (hrj : (rjLower : ℝ) ≤ (P.circles j).radius)
    (hij : i ≠ j) :
    Contains (b.propagatePairLower i j riLower rjLower)
      (fun k => globalPointNorm (P.circles k).center) := by
  exact contains_after_pair_propagation riLower rjLower
    (P.circles i) (P.circles j) hx (P.separated hij)
    hri hrj rfl rfl

theorem packing_ordered_pair_propagation_sound
    {n : ℕ} {R : ℝ} (P : Packing n R)
    (b : RationalBox n) (rootLower : Fin n → ℚ)
    (i j : Fin n)
    (hx : Contains b (fun k => globalPointNorm (P.circles k).center))
    (hroots : ∀ k, (rootLower k : ℝ) ≤ (P.circles k).radius) :
    Contains (b.propagateOrderedPair rootLower i j)
      (fun k => globalPointNorm (P.circles k).center) := by
  by_cases hij : i ≠ j
  · simpa [propagateOrderedPair, hij] using
      packing_pair_propagation_sound P b i j
        (rootLower i) (rootLower j) hx (hroots i) (hroots j) hij
  · simp [propagateOrderedPair, hij]
    exact hx

theorem packing_propagatePairs_sound
    {n : ℕ} {R : ℝ} (P : Packing n R)
    (b : RationalBox n) (rootLower : Fin n → ℚ)
    (pairs : List (Fin n × Fin n))
    (hx : Contains b (fun k => globalPointNorm (P.circles k).center))
    (hroots : ∀ k, (rootLower k : ℝ) ≤ (P.circles k).radius) :
    Contains (b.propagatePairs pairs rootLower)
      (fun k => globalPointNorm (P.circles k).center) := by
  induction pairs generalizing b with
  | nil =>
      simpa [propagatePairs] using hx
  | cons pair pairs ih =>
      simp only [propagatePairs, List.foldl_cons]
      apply ih
      exact packing_ordered_pair_propagation_sound P b rootLower
        pair.1 pair.2 hx hroots

theorem packing_allPairPropagation_sound
    {n : ℕ} {R : ℝ} (P : Packing n R)
    (b : RationalBox n) (rootLower : Fin n → ℚ)
    (hx : Contains b (fun k => globalPointNorm (P.circles k).center))
    (hroots : ∀ k, (rootLower k : ℝ) ≤ (P.circles k).radius) :
    Contains (b.propagatePairs (allDistinctOrderedPairs n) rootLower)
      (fun k => globalPointNorm (P.circles k).center) := by
  exact packing_propagatePairs_sound P b rootLower
    (allDistinctOrderedPairs n) hx hroots

end RationalBox

end CirclePacking
