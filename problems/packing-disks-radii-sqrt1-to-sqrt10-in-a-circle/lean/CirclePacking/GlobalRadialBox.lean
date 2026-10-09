import CirclePacking.RadialPropagation
import CirclePacking.PropagatedSplitTree
import Mathlib.Analysis.SpecialFunctions.Sqrt

namespace CirclePacking

/-!
# Soundness of the global radial root box

The global radial search starts from an exact rational box derived from
downward square-root bounds for the disk radii and from containment and
pairwise non-overlap.  This file replays that derivation in Lean.  The
certificate's rational endpoints are data; their square-root inequalities
are checked by `norm_num` through `rat_le_sqrt`.
-/

def tenRootLower : Fin 10 → ℚ := fun i =>
  (![ 1,
      1414213562373 / 1000000000000,
      108253175473 / 62500000000,
      2,
      2236067977499 / 1000000000000,
      2449489742783 / 1000000000000,
      330718913883 / 125000000000,
      1414213562373 / 500000000000,
      3,
      395284707521 / 125000000000 ] : Fin 10 → ℚ) i

lemma rat_le_sqrt {q : ℚ} {n : ℕ}
    (hq : (0 : ℝ) ≤ q) (hsq : (q : ℝ) ^ 2 ≤ n) :
    (q : ℝ) ≤ Real.sqrt n := by
  have hn := Real.sq_sqrt (show (0 : ℝ) ≤ n by positivity)
  have hs := Real.sqrt_nonneg (n : ℝ)
  by_contra h
  have hlt : Real.sqrt (n : ℝ) < q := lt_of_not_ge h
  have hh := (sq_lt_sq₀ hs hq).mpr hlt
  nlinarith

theorem tenRootLower_le_sqrt (i : Fin 10) :
    (tenRootLower i : ℝ) ≤ Real.sqrt ((i.val + 1 : ℕ) : ℝ) := by
  fin_cases i <;>
    apply rat_le_sqrt <;> norm_num [tenRootLower]

lemma contained_radial_upper {U : ℝ} {c : Circle}
    (hc : Contained U c) :
    globalPointNorm c.center ≤ U - c.radius := by
  rcases hc with ⟨hcr, hdist⟩
  have hrad : 0 ≤ U - c.radius := sub_nonneg.mpr hcr
  have hsq : globalPointNorm c.center ^ 2 ≤ (U - c.radius) ^ 2 := by
    rw [globalPointNorm_sq]
    simpa [distSq] using hdist
  exact (sq_le_sq₀ (globalPointNorm_nonneg _) hrad).mp hsq

def radialInitialBox {d : ℕ} (U : ℚ) (rootLower : Fin d → ℚ) :
    RationalBox d where
  lo i := (List.finRange d).foldr
    (fun j acc => max (if i = j then 0 else
      rootLower i + 2 * rootLower j - U) acc) 0
  hi i := U - rootLower i

/-- The exact upper radius used in the global radial certificate. -/
def tenCircleGlobalRadiusUpper : ℚ := 830346812211149 / 100000000000000

/-- Root box after the certificate's complete distinct-pair radial pass. -/
def tenCircleGlobalRootBox : RationalBox 10 :=
  (radialInitialBox tenCircleGlobalRadiusUpper tenRootLower).propagatePairs
    (RationalBox.allDistinctOrderedPairs 10) tenRootLower

lemma foldr_max_le_real {xs : List ℚ} {s : ℝ}
    (hs : 0 ≤ s) (hall : ∀ q ∈ xs, (q : ℝ) ≤ s) :
    ((xs.foldr max 0 : ℚ) : ℝ) ≤ s := by
  induction xs with
  | nil => simpa using hs
  | cons a xs ih =>
      rw [List.foldr_cons, Rat.cast_max]
      apply max_le_iff.mpr
      refine ⟨hall a (by simp), ih ?_⟩
      intro q hq
      exact hall q (by simp [hq])

theorem radialInitialBox_contains
    {n : ℕ} {R : ℝ} (P : Packing n R)
    (U : ℚ) (rootLower : Fin n → ℚ) (hRU : R ≤ (U : ℝ))
    (hroots : ∀ i, (rootLower i : ℝ) ≤ (P.circles i).radius) :
    RationalBox.Contains
      (radialInitialBox (d := n) U rootLower)
      (fun i => globalPointNorm (P.circles i).center) := by
  have hcontained (i : Fin n) : Contained U (P.circles i) := by
    exact contained_mono hRU (P.contained i)
  intro i
  constructor
  · let candidates : List ℚ := (List.finRange n).map (fun j =>
      if i = j then 0 else rootLower i + 2 * rootLower j - U)
    have hzero : (0 : ℝ) ≤ globalPointNorm (P.circles i).center :=
      globalPointNorm_nonneg _
    have hcandidate : ∀ q ∈ candidates,
        (q : ℝ) ≤ globalPointNorm (P.circles i).center := by
      intro q hq
      have hex : ∃ j ∈ List.finRange n,
          (if i = j then 0 else rootLower i + 2 * rootLower j - U) = q := by
        simpa [candidates] using hq
      rcases hex with ⟨j, hj, hqeq⟩
      subst q
      by_cases hij : i = j
      · simpa [hij] using globalPointNorm_nonneg (P.circles i).center
      · have hsep := P.separated hij
        have hradial := separated_implies_radial_sum_lower hsep rfl rfl
        have huj := contained_radial_upper (hcontained j)
        have hrooti := hroots i
        have hrootj := hroots j
        simp [hij]
        have hbound :
            (rootLower i : ℝ) + 2 * (rootLower j : ℝ) - (U : ℝ) ≤
              globalPointNorm (P.circles i).center := by
          linarith
        linarith [hbound]
    have hfold :
        ((candidates.foldr max 0 : ℚ) : ℝ) ≤
          globalPointNorm (P.circles i).center :=
      foldr_max_le_real hzero hcandidate
    simpa [radialInitialBox, candidates, List.foldr_map] using hfold
  · have hu := contained_radial_upper (hcontained i)
    have hroot := hroots i
    have hbound :
        globalPointNorm (P.circles i).center ≤ (U : ℝ) - (rootLower i : ℝ) := by
      linarith
    have hcast :
        globalPointNorm (P.circles i).center ≤ ((U - rootLower i : ℚ) : ℝ) := by
      exact_mod_cast hbound
    simpa [radialInitialBox] using hcast

theorem tenCircle_radialInitialBox_contains
    {R : ℝ} (P : Packing 10 R)
    (U : ℚ) (hRU : R ≤ (U : ℝ))
    (hradius : ∀ i : Fin 10,
      (P.circles i).radius = Real.sqrt ((i.val + 1 : ℕ) : ℝ)) :
    RationalBox.Contains
      (radialInitialBox (d := 10) U tenRootLower)
      (fun i => globalPointNorm (P.circles i).center) := by
  apply radialInitialBox_contains P U tenRootLower hRU
  intro i
  rw [hradius i]
  exact tenRootLower_le_sqrt i

theorem tenCircle_globalRootBox_contains
    {R : ℝ} (P : Packing 10 R)
    (hRadius : ∀ i : Fin 10,
      (P.circles i).radius = Real.sqrt ((i.val + 1 : ℕ) : ℝ))
    (hR : R ≤ (tenCircleGlobalRadiusUpper : ℝ)) :
    RationalBox.Contains tenCircleGlobalRootBox
      (fun i => globalPointNorm (P.circles i).center) := by
  unfold tenCircleGlobalRootBox
  apply RationalBox.packing_allPairPropagation_sound P _ tenRootLower
  · exact tenCircle_radialInitialBox_contains P tenCircleGlobalRadiusUpper hR hRadius
  · intro i
    rw [hRadius i]
    exact tenRootLower_le_sqrt i

theorem tenCircle_globalTree_covers
    {R : ℝ} (P : Packing 10 R)
    (tree : RationalSplitTree 10 tenCircleGlobalRootBox)
    (hRadius : ∀ i : Fin 10,
      (P.circles i).radius = Real.sqrt ((i.val + 1 : ℕ) : ℝ))
    (hR : R ≤ (tenCircleGlobalRadiusUpper : ℝ)) :
    ∃ leaf ∈ tree.leafBoxes,
      RationalBox.Contains leaf
        (fun i => globalPointNorm (P.circles i).center) := by
  exact tree.covered _ (tenCircle_globalRootBox_contains P hRadius hR)

theorem tenCircle_propagatedGlobalTree_covers
    {R : ℝ} (P : Packing 10 R)
    (tree : PropagatedSplitTree tenRootLower
      (radialInitialBox tenCircleGlobalRadiusUpper tenRootLower))
    (hRadius : ∀ i : Fin 10,
      (P.circles i).radius = Real.sqrt ((i.val + 1 : ℕ) : ℝ))
    (hR : R ≤ (tenCircleGlobalRadiusUpper : ℝ)) :
    ∃ leaf ∈ tree.leafBoxes,
      RationalBox.Contains leaf
        (fun i => globalPointNorm (P.circles i).center) := by
  apply tree.covered _
  · exact tenCircle_radialInitialBox_contains P tenCircleGlobalRadiusUpper hR hRadius
  · intro b hb
    apply RationalBox.packing_allPairPropagation_sound P b tenRootLower hb
    intro i
    rw [hRadius i]
    exact tenRootLower_le_sqrt i

end CirclePacking
