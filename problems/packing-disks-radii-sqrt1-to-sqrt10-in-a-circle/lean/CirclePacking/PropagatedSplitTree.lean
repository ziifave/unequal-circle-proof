import CirclePacking.RadialPropagation

namespace CirclePacking

/-!
# Split trees with a sound contractor at every node

The radial search contracts a box before testing it or splitting it.  Thus a
child is cut from the parent's contracted box, and the child is contracted
again when processed.  `PropagatedSplitTree` records that order in its type.
Its coverage theorem is generic in the soundness proof for the contractor.
-/

namespace RationalBox

def radialContract (b : RationalBox d) (rootLower : Fin d → ℚ) :
    RationalBox d :=
  b.propagatePairs (allDistinctOrderedPairs d) rootLower

end RationalBox

inductive PropagatedSplitTree {d : ℕ} (rootLower : Fin d → ℚ) :
    RationalBox d → Type
  | leaf {box : RationalBox d} : PropagatedSplitTree rootLower box
  | split {box : RationalBox d} (axis : Fin d) (cut : ℚ)
      (cutLower : (box.radialContract rootLower).lo axis ≤ cut)
      (cutUpper : cut ≤ (box.radialContract rootLower).hi axis)
      (left : PropagatedSplitTree rootLower
        ((box.radialContract rootLower).setHi axis cut))
      (right : PropagatedSplitTree rootLower
        ((box.radialContract rootLower).setLo axis cut)) :
      PropagatedSplitTree rootLower box

namespace PropagatedSplitTree

def leafBoxes : {box : RationalBox d} →
    PropagatedSplitTree (d := d) rootLower box → List (RationalBox d)
  | box, .leaf => [box.radialContract rootLower]
  | _, .split _ _ _ _ left right => leafBoxes left ++ leafBoxes right

theorem covered {box : RationalBox d}
    (tree : PropagatedSplitTree (d := d) rootLower box)
    (x : Fin d → ℝ) (hx : RationalBox.Contains box x)
    (contractorSound : ∀ b : RationalBox d,
      RationalBox.Contains b x →
        RationalBox.Contains (b.radialContract rootLower) x) :
    ∃ leaf ∈ tree.leafBoxes, RationalBox.Contains leaf x := by
  induction tree generalizing x with
  | leaf =>
      exact ⟨_, by simp [leafBoxes], contractorSound _ hx⟩
  | split axis cut cutLower cutUpper left right ihLeft ihRight =>
      rename_i parentBox
      have hxContracted :
          RationalBox.Contains (parentBox.radialContract rootLower) x :=
        contractorSound parentBox hx
      by_cases hleft : x axis ≤ (cut : ℝ)
      · have hxLeft : RationalBox.Contains
            ((parentBox.radialContract rootLower).setHi axis cut) x :=
          RationalBox.contains_setHi hxContracted hleft
        rcases ihLeft x hxLeft contractorSound with ⟨leaf, hleaf, hcontains⟩
        exact ⟨leaf, by simp [leafBoxes, hleaf], hcontains⟩
      · have hright : (cut : ℝ) ≤ x axis := le_of_not_ge hleft
        have hxRight : RationalBox.Contains
            ((parentBox.radialContract rootLower).setLo axis cut) x :=
          RationalBox.contains_setLo hxContracted hright
        rcases ihRight x hxRight contractorSound with ⟨leaf, hleaf, hcontains⟩
        exact ⟨leaf, by simp [leafBoxes, hleaf], hcontains⟩

end PropagatedSplitTree

end CirclePacking
