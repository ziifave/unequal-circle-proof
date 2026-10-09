import CirclePacking.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Prod.Lex
import Mathlib.Data.Fintype.Card

/-! Reindex an arbitrary finite family by polar angle, breaking ties by its
original index. This gives the monotone `Fin 15` angle vector used by the
negative-cycle soundness lemmas. -/

namespace CirclePacking

private noncomputable def fifteenAngleOrderKey
    (theta : Fin 15 → ℝ) (i : Fin 15) : ℝ ×ₗ Fin 15 :=
  toLex (theta i, i)

private theorem fifteenAngleOrderKey_injective (theta : Fin 15 → ℝ) :
    Function.Injective (fifteenAngleOrderKey theta) := by
  intro i j hij
  have hpair := congrArg (fun z : ℝ ×ₗ Fin 15 => ofLex z) hij
  exact congrArg Prod.snd hpair

private abbrev fifteenAngleOrderLE (theta : Fin 15 → ℝ) (i j : Fin 15) : Prop :=
  fifteenAngleOrderKey theta i ≤ fifteenAngleOrderKey theta j

private theorem fifteenAngleOrderLE_trans (theta : Fin 15 → ℝ) :
    IsTrans (Fin 15) (fifteenAngleOrderLE theta) := by
  refine ⟨?_⟩
  intro a b c hab hbc
  exact le_trans hab hbc

private theorem fifteenAngleOrderLE_antisymm (theta : Fin 15 → ℝ) :
    Std.Antisymm (fifteenAngleOrderLE theta) := by
  refine ⟨?_⟩
  intro a b hab hba
  exact fifteenAngleOrderKey_injective theta (le_antisymm hab hba)

private theorem fifteenAngleOrderLE_total (theta : Fin 15 → ℝ) :
    Std.Total (fifteenAngleOrderLE theta) := by
  refine ⟨?_⟩
  intro a b
  exact le_total _ _

private noncomputable def fifteenAngleOrderSorted (theta : Fin 15 → ℝ) :
    List (Fin 15) := by
  classical
  letI : DecidableRel (fifteenAngleOrderLE theta) := Classical.decRel _
  letI : IsTrans (Fin 15) (fifteenAngleOrderLE theta) :=
    fifteenAngleOrderLE_trans theta
  letI : Std.Antisymm (fifteenAngleOrderLE theta) :=
    fifteenAngleOrderLE_antisymm theta
  letI : Std.Total (fifteenAngleOrderLE theta) :=
    fifteenAngleOrderLE_total theta
  exact Finset.univ.sort (fifteenAngleOrderLE theta)

private theorem fifteenAngleOrderList_length (theta : Fin 15 → ℝ) :
    (fifteenAngleOrderSorted theta).length = 15 := by
  classical
  letI : DecidableRel (fifteenAngleOrderLE theta) := Classical.decRel _
  letI : IsTrans (Fin 15) (fifteenAngleOrderLE theta) :=
    fifteenAngleOrderLE_trans theta
  letI : Std.Antisymm (fifteenAngleOrderLE theta) :=
    fifteenAngleOrderLE_antisymm theta
  letI : Std.Total (fifteenAngleOrderLE theta) :=
    fifteenAngleOrderLE_total theta
  change (Finset.univ.sort (fifteenAngleOrderLE theta)).length = 15
  have h := Finset.length_sort (s := (Finset.univ : Finset (Fin 15)))
    (fifteenAngleOrderLE theta)
  simpa using h

noncomputable def fifteenPackingAngleOrder
    (theta : Fin 15 → ℝ) : Fin 15 → Fin 15 := by
  classical
  letI : DecidableRel (fifteenAngleOrderLE theta) := Classical.decRel _
  letI : IsTrans (Fin 15) (fifteenAngleOrderLE theta) :=
    fifteenAngleOrderLE_trans theta
  letI : Std.Antisymm (fifteenAngleOrderLE theta) :=
    fifteenAngleOrderLE_antisymm theta
  letI : Std.Total (fifteenAngleOrderLE theta) :=
    fifteenAngleOrderLE_total theta
  let sorted : List (Fin 15) := fifteenAngleOrderSorted theta
  have hlen : sorted.length = 15 := by
    change (fifteenAngleOrderSorted theta).length = 15
    exact fifteenAngleOrderList_length theta
  exact fun k => sorted.get ⟨k.1, by rw [hlen]; exact k.2⟩

theorem fifteenPackingAngleOrder_injective (theta : Fin 15 → ℝ) :
    Function.Injective (fifteenPackingAngleOrder theta) := by
  classical
  intro i j hij
  letI : DecidableRel (fifteenAngleOrderLE theta) := Classical.decRel _
  letI : IsTrans (Fin 15) (fifteenAngleOrderLE theta) :=
    fifteenAngleOrderLE_trans theta
  letI : Std.Antisymm (fifteenAngleOrderLE theta) :=
    fifteenAngleOrderLE_antisymm theta
  letI : Std.Total (fifteenAngleOrderLE theta) :=
    fifteenAngleOrderLE_total theta
  let sorted : List (Fin 15) := fifteenAngleOrderSorted theta
  have hlen : sorted.length = 15 := by
    change (fifteenAngleOrderSorted theta).length = 15
    exact fifteenAngleOrderList_length theta
  have hnodup : sorted.Nodup := by
    change (Finset.univ.sort (fifteenAngleOrderLE theta)).Nodup
    exact Finset.sort_nodup Finset.univ (fifteenAngleOrderLE theta)
  have hget := hnodup.injective_get
  have hidx : (⟨i.1, by rw [hlen]; exact i.2⟩ : Fin sorted.length) =
      ⟨j.1, by rw [hlen]; exact j.2⟩ := by
    apply hget
    change (fifteenAngleOrderSorted theta).get ⟨i.1, by rw [hlen]; exact i.2⟩ =
      (fifteenAngleOrderSorted theta).get ⟨j.1, by rw [hlen]; exact j.2⟩
    exact hij
  have hval : i.1 = j.1 := by
    exact congrArg (fun x : Fin sorted.length => x.1) hidx
  exact Fin.ext hval

theorem fifteenPackingAngleOrder_surjective (theta : Fin 15 → ℝ) :
    Function.Surjective (fifteenPackingAngleOrder theta) :=
  Finite.injective_iff_surjective.mp (fifteenPackingAngleOrder_injective theta)

theorem fifteenPackingAngleOrder_bijective (theta : Fin 15 → ℝ) :
    Function.Bijective (fifteenPackingAngleOrder theta) :=
  ⟨fifteenPackingAngleOrder_injective theta,
    fifteenPackingAngleOrder_surjective theta⟩

theorem fifteenPackingAngleOrder_monotone (theta : Fin 15 → ℝ)
    {i j : Fin 15} (hij : i.1 < j.1) :
    theta (fifteenPackingAngleOrder theta i) ≤
      theta (fifteenPackingAngleOrder theta j) := by
  classical
  letI : DecidableRel (fifteenAngleOrderLE theta) := Classical.decRel _
  letI : IsTrans (Fin 15) (fifteenAngleOrderLE theta) :=
    fifteenAngleOrderLE_trans theta
  letI : Std.Antisymm (fifteenAngleOrderLE theta) :=
    fifteenAngleOrderLE_antisymm theta
  letI : Std.Total (fifteenAngleOrderLE theta) :=
    fifteenAngleOrderLE_total theta
  let sorted : List (Fin 15) := fifteenAngleOrderSorted theta
  have hsorted : List.Pairwise (fifteenAngleOrderLE theta) sorted := by
    change List.Pairwise (fifteenAngleOrderLE theta)
      (Finset.univ.sort (fifteenAngleOrderLE theta))
    exact Finset.pairwise_sort Finset.univ (r := fifteenAngleOrderLE theta)
  have hlen : sorted.length = 15 := by
    change (fifteenAngleOrderSorted theta).length = 15
    exact fifteenAngleOrderList_length theta
  let ki : Fin sorted.length := ⟨i.1, by rw [hlen]; exact i.2⟩
  let kj : Fin sorted.length := ⟨j.1, by rw [hlen]; exact j.2⟩
  have hpos : ki < kj := by
    exact Fin.mk_lt_mk.mpr hij
  have hle := hsorted.rel_get_of_lt hpos
  have hkey : fifteenAngleOrderKey theta (sorted.get ki) ≤
      fifteenAngleOrderKey theta (sorted.get kj) := hle
  have hangle := Prod.Lex.monotone_fst _ _ hkey
  change theta (sorted.get ki) ≤ theta (sorted.get kj)
  simpa [fifteenAngleOrderKey] using hangle

theorem fifteenPackingAngleOrder_preserves_radius_bounds
    (theta : Fin 15 → ℝ) (radius : Fin 15 → ℝ)
    (lower upper : Fin 15 → ℝ)
    (hbound : ∀ i, lower i ≤ radius i ∧ radius i ≤ upper i) :
    ∀ k, lower (fifteenPackingAngleOrder theta k) ≤
        radius (fifteenPackingAngleOrder theta k) ∧
      radius (fifteenPackingAngleOrder theta k) ≤
        upper (fifteenPackingAngleOrder theta k) := by
  intro k
  exact hbound (fifteenPackingAngleOrder theta k)

end CirclePacking
