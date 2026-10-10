import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Data.Fin.Rev
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic

/-! Reindex radius/type profiles by the same dihedral convention as Stage 0.
The permutation sends an old slot to its new slot; a transformed profile is
therefore pulled back by its inverse. These lemmas preserve population counts,
pointwise box bounds and pairwise separation, independently of certificate
data. The lifted-angle order and exact mask correspondence remain separate
obligations. -/

namespace CirclePacking

/-- Stage 0 reflects by `i ↦ 14 - i`, then rotates by the selected shift. -/
def fifteenStage0DihedralPermutation (reflected : Bool) (shift : Fin 15) :
    Equiv.Perm (Fin 15) :=
  if reflected then Fin.revPerm.trans (finCycle shift) else finCycle shift

def fifteenStage0TransformProfile {α : Type*} (profile : Fin 15 → α)
    (reflected : Bool) (shift : Fin 15) : Fin 15 → α :=
  fun i => profile ((fifteenStage0DihedralPermutation reflected shift).symm i)

theorem fifteenStage0DihedralPermutation_rotation_val (shift i : Fin 15) :
    (fifteenStage0DihedralPermutation false shift i).val =
      (i.val + shift.val) % 15 := by
  change (i + shift).val = _
  exact Fin.val_add i shift

theorem fifteenStage0DihedralPermutation_reflection_val (shift i : Fin 15) :
    (fifteenStage0DihedralPermutation true shift i).val =
      (14 - i.val + shift.val) % 15 := by
  change (i.rev + shift).val = _
  rw [Fin.val_add]
  have hrev : i.rev.val = 14 - i.val := by
    rw [Fin.val_rev]
    omega
  rw [hrev]

/-- Every radial population predicate has the same count after reindexing. -/
theorem fifteenStage0TransformProfile_population {α : Type*}
    (profile : Fin 15 → α) (predicate : α → Prop) [DecidablePred predicate]
    (reflected : Bool) (shift : Fin 15) :
    (Finset.univ.filter fun i : Fin 15 =>
      predicate (fifteenStage0TransformProfile profile reflected shift i)).card =
    (Finset.univ.filter fun i : Fin 15 => predicate (profile i)).card := by
  classical
  apply Finset.card_bijective
    (fifteenStage0DihedralPermutation reflected shift).symm
    (fifteenStage0DihedralPermutation reflected shift).symm.bijective
  intro i
  constructor
  · intro hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hi).2⟩
  · intro hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hi).2⟩

/-- Reindexing radii and their type labels together preserves every
per-position relation, in particular membership in the labelled radius box. -/
theorem fifteenStage0TransformProfile_pointwise {α β : Type*}
    (profile : Fin 15 → α) (labels : Fin 15 → β) (relation : α → β → Prop)
    (reflected : Bool) (shift : Fin 15)
    (h : ∀ i, relation (profile i) (labels i)) :
    ∀ i, relation (fifteenStage0TransformProfile profile reflected shift i)
      (fifteenStage0TransformProfile labels reflected shift i) := by
  intro i
  exact h ((fifteenStage0DihedralPermutation reflected shift).symm i)

/-- The reindexed values preserve a pairwise relation at distinct slots. -/
theorem fifteenStage0TransformProfile_pairwise {α : Type*}
    (profile : Fin 15 → α) (relation : α → α → Prop)
    (reflected : Bool) (shift : Fin 15)
    (h : ∀ i j, i ≠ j → relation (profile i) (profile j)) :
    ∀ i j, i ≠ j →
      relation (fifteenStage0TransformProfile profile reflected shift i)
        (fifteenStage0TransformProfile profile reflected shift j) := by
  intro i j hij
  apply h
  intro heq
  exact hij ((fifteenStage0DihedralPermutation reflected shift).symm.injective heq)

end CirclePacking
