import Mathlib.Data.Rat.Cast.Order
import Mathlib.Basic.Real.Basic

namespace CirclePacking

/-!
# Exact rational split-tree coverage

Search code may choose a sequence of rational bisections, but a proof must
check that the resulting leaves cover the original box.  `RationalSplitTree`
records a cut together with its two recursively certified subtrees.  Its
indices force the left and right boxes to agree with the parent at every
coordinate except the split coordinate.

The theorem `RationalSplitTree.covered` is the first Lean replay layer for the
radial partition used by the global certificate.  It checks coverage only;
leaf rejection claims are separate obligations.
-/

structure RationalBox (d : ℕ) where
  lo : Fin d → ℚ
  hi : Fin d → ℚ

namespace RationalBox

def setHi (b : RationalBox d) (i : Fin d) (q : ℚ) : RationalBox d :=
  { b with hi := Function.update b.hi i q }

def setLo (b : RationalBox d) (i : Fin d) (q : ℚ) : RationalBox d :=
  { b with lo := Function.update b.lo i q }

def Contains (b : RationalBox d) (x : Fin d → ℝ) : Prop :=
  ∀ i, (b.lo i : ℝ) ≤ x i ∧ x i ≤ (b.hi i : ℝ)

theorem contains_setHi
    {b : RationalBox d} {x : Fin d → ℝ} {i : Fin d} {q : ℚ}
    (hx : Contains b x) (hcut : x i ≤ (q : ℝ)) :
    Contains (b.setHi i q) x := by
  intro j
  by_cases hji : j = i
  · subst j
    simpa [setHi] using And.intro (hx i).1 hcut
  · simpa [setHi, hji] using hx j

theorem contains_setLo
    {b : RationalBox d} {x : Fin d → ℝ} {i : Fin d} {q : ℚ}
    (hx : Contains b x) (hcut : (q : ℝ) ≤ x i) :
    Contains (b.setLo i q) x := by
  intro j
  by_cases hji : j = i
  · subst j
    simpa [setLo] using And.intro hcut (hx i).2
  · simpa [setLo, hji] using hx j

theorem setHi_subset
    {b : RationalBox d} {x : Fin d → ℝ} {i : Fin d} {q : ℚ}
    (hcut : q ≤ b.hi i)
    (hx : Contains (b.setHi i q) x) : Contains b x := by
  have hcutReal : (q : ℝ) ≤ (b.hi i : ℝ) := by exact_mod_cast hcut
  intro j
  by_cases hji : j = i
  · subst j
    have hxj := hx i
    have hlo : (b.lo i : ℝ) ≤ x i := by simpa [setHi] using hxj.1
    have hupper : x i ≤ (q : ℝ) := by simpa [setHi] using hxj.2
    exact ⟨hlo, le_trans hupper hcutReal⟩
  · simpa [setHi, hji] using hx j

theorem setLo_subset
    {b : RationalBox d} {x : Fin d → ℝ} {i : Fin d} {q : ℚ}
    (hcut : b.lo i ≤ q)
    (hx : Contains (b.setLo i q) x) : Contains b x := by
  have hcutReal : (b.lo i : ℝ) ≤ (q : ℝ) := by exact_mod_cast hcut
  intro j
  by_cases hji : j = i
  · subst j
    have hxj := hx i
    have hlower : (q : ℝ) ≤ x i := by simpa [setLo] using hxj.1
    have hupper : x i ≤ (b.hi i : ℝ) := by simpa [setLo] using hxj.2
    exact ⟨le_trans hcutReal hlower, hupper⟩
  · simpa [setLo, hji] using hx j

end RationalBox

inductive RationalSplitTree (d : ℕ) : RationalBox d → Type
  | leaf {box : RationalBox d} : RationalSplitTree d box
  | split {box : RationalBox d} (axis : Fin d) (cut : ℚ)
      (cutLower : box.lo axis ≤ cut)
      (cutUpper : cut ≤ box.hi axis)
      (left : RationalSplitTree d (box.setHi axis cut))
      (right : RationalSplitTree d (box.setLo axis cut)) :
      RationalSplitTree d box

namespace RationalSplitTree

def leafBoxes : {box : RationalBox d} → RationalSplitTree d box → List (RationalBox d)
  | box, .leaf => [box]
  | _, .split _ _ _ _ left right => leafBoxes left ++ leafBoxes right

theorem covered {box : RationalBox d} (tree : RationalSplitTree d box)
    (x : Fin d → ℝ) (hx : RationalBox.Contains box x) :
    ∃ leaf ∈ tree.leafBoxes, RationalBox.Contains leaf x := by
  induction tree generalizing x with
  | leaf =>
      rename_i leafBox
      exact ⟨leafBox, by simp [leafBoxes], hx⟩
  | split axis cut cutLower cutUpper left right ihLeft ihRight =>
      rename_i parentBox
      by_cases hleft : x axis ≤ (cut : ℝ)
      · have hxLeft : RationalBox.Contains (parentBox.setHi axis cut) x :=
          RationalBox.contains_setHi hx hleft
        rcases ihLeft x hxLeft with ⟨leaf, hleaf, hcontains⟩
        exact ⟨leaf, by simp [leafBoxes, hleaf], hcontains⟩
      · have hright : (cut : ℝ) ≤ x axis := le_of_not_ge hleft
        have hxRight : RationalBox.Contains (parentBox.setLo axis cut) x :=
          RationalBox.contains_setLo hx hright
        rcases ihRight x hxRight with ⟨leaf, hleaf, hcontains⟩
        exact ⟨leaf, by simp [leafBoxes, hleaf], hcontains⟩

theorem leaf_subset_root {box : RationalBox d} (tree : RationalSplitTree d box)
    {leaf : RationalBox d} (hleaf : leaf ∈ tree.leafBoxes)
    (x : Fin d → ℝ) (hx : RationalBox.Contains leaf x) :
    RationalBox.Contains box x := by
  induction tree generalizing leaf x with
  | leaf =>
      rename_i rootBox
      have heq : leaf = rootBox := by simpa [leafBoxes] using hleaf
      subst leaf
      exact hx
  | split axis cut cutLower cutUpper left right ihLeft ihRight =>
      rename_i parentBox
      simp only [leafBoxes, List.mem_append] at hleaf
      rcases hleaf with hleft | hright
      · have hparent : RationalBox.Contains (parentBox.setHi axis cut) x :=
          ihLeft hleft x hx
        exact RationalBox.setHi_subset cutUpper hparent
      · have hparent : RationalBox.Contains (parentBox.setLo axis cut) x :=
          ihRight hright x hx
        exact RationalBox.setLo_subset cutLower hparent

end RationalSplitTree

end CirclePacking
