import Mathlib.Basic.Real.Basic
import CirclePacking.FifteenCertificate

/-! Semantic facts about the exact certificate's closed rational boxes.
These are the interval-covering lemmas needed to lift a checked subdivision
tree from rational endpoints to the real radii of a packing. -/

namespace CirclePacking

def fifteenRealIntervalContains (interval : FifteenInterval) (x : ℝ) : Prop :=
  (interval.1 : ℝ) ≤ x ∧ x ≤ (interval.2 : ℝ)

def fifteenRealBoxContains (box : FifteenBox) (radii : Fin 15 → ℝ) : Prop :=
  ∀ i : Fin 15, fifteenRealIntervalContains box[i.1]! (radii i)

/-- The split convention is closed on both sides, so a radius on the cut is
covered by either child (in fact, by both). -/
theorem fifteenRealIntervalSplitCovers (lo cut hi : Rat) (x : ℝ)
    (hx : fifteenRealIntervalContains (lo, hi) x) :
    fifteenRealIntervalContains (lo, cut) x ∨
      fifteenRealIntervalContains (cut, hi) x := by
  rcases hx with ⟨hlo, hhi⟩
  rcases le_total x (cut : ℝ) with hleft | hright
  · exact Or.inl ⟨hlo, hleft⟩
  · exact Or.inr ⟨hright, hhi⟩

theorem fifteenRealIntervalLeftChildSubset (lo cut hi : Rat) (x : ℝ)
    (hcut : (cut : ℝ) ≤ hi)
    (hx : fifteenRealIntervalContains (lo, cut) x) :
    fifteenRealIntervalContains (lo, hi) x := by
  rcases hx with ⟨hlo, hxcut⟩
  exact ⟨hlo, le_trans hxcut hcut⟩

theorem fifteenRealIntervalRightChildSubset (lo cut hi : Rat) (x : ℝ)
    (hcut : (lo : ℝ) ≤ cut)
    (hx : fifteenRealIntervalContains (cut, hi) x) :
    fifteenRealIntervalContains (lo, hi) x := by
  rcases hx with ⟨hcutx, hhi⟩
  exact ⟨le_trans hcut hcutx, hhi⟩

/-- Every real profile in a parent box remains in at least one of the two
array boxes produced by the checker at a legal split coordinate. -/
theorem fifteenRealBox_split_covers
    (box : FifteenBox) (radii : Fin 15 → ℝ) (axis : Nat) (cut : Rat)
    (hsize : box.size = 15) (haxis : axis < 15)
    (hparent : fifteenRealBoxContains box radii)
    (hcut : (box[axis]!).1 < cut ∧ cut < (box[axis]!).2) :
    fifteenRealBoxContains (box.set! axis ((box[axis]!).1, cut)) radii ∨
      fifteenRealBoxContains (box.set! axis (cut, (box[axis]!).2)) radii := by
  have haxisLtSize : axis < box.size := by omega
  have hparentAxis := hparent ⟨axis, by omega⟩
  have hcoord := fifteenRealIntervalSplitCovers (box[axis]!).1 cut
    (box[axis]!).2 (radii ⟨axis, by omega⟩) hparentAxis
  rcases hcoord with hleft | hright
  · left
    intro i
    by_cases hi : i.1 = axis
    · have heq : i = ⟨axis, by omega⟩ := Fin.ext hi
      subst i
      simpa only [fifteenRealIntervalContains, Array.set!_eq_setIfInBounds,
        Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?,
        Array.getElem?_setIfInBounds_self_of_lt haxisLtSize,
        Option.getD_some] using hleft
    · rw [Array.getElem!_set!_ne box axis i.1 ((box[axis]!).1, cut)
        (Ne.symm hi)]
      exact hparent i
  · right
    intro i
    by_cases hi : i.1 = axis
    · have heq : i = ⟨axis, by omega⟩ := Fin.ext hi
      subst i
      simpa only [fifteenRealIntervalContains, Array.set!_eq_setIfInBounds,
        Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?,
        Array.getElem?_setIfInBounds_self_of_lt haxisLtSize,
        Option.getD_some] using hright
    · rw [Array.getElem!_set!_ne box axis i.1 (cut, (box[axis]!).2)
        (Ne.symm hi)]
      exact hparent i

end CirclePacking
