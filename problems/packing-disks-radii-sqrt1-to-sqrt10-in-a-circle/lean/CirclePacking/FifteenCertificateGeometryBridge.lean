import CirclePacking.FifteenCertificateBins
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-! A geometric radius can be assigned to one of the exact certificate's
rational bins.  This is the first explicit bridge from the Stage 4 radial
profile to the root boxes used by the final subdivision certificate. -/

namespace CirclePacking

/-- Half-open ownership for the exact radial bins.  The value `13` is kept for
the exact origin, which is treated separately by the six-inner certificate. -/
noncomputable def fifteenExactRadialOwner (r : ℝ) : Nat :=
  if r = 0 then 13 else
  if r < 1 / 2 then 0 else
  if r < 1 then 1 else
  if r < 3 / 2 then 2 else
  if r < 8 / 5 then 3 else
  if r < 5 / 3 then 4 else
  if r < 17 / 10 then 5 else
  if r < 37 / 20 then 6 else
  if r < 2 then 7 else
  if r < 43 / 20 then 8 else
  if r < 23 / 10 then 9 else 10

def fifteenExactRadialOwnerSpec (label : Nat) (r : ℝ) : Prop :=
  match label with
  | 0 => 0 < r ∧ r < 1 / 2
  | 1 => 1 / 2 ≤ r ∧ r < 1
  | 2 => 1 ≤ r ∧ r < 3 / 2
  | 3 => 3 / 2 ≤ r ∧ r < 8 / 5
  | 4 => 8 / 5 ≤ r ∧ r < 5 / 3
  | 5 => 5 / 3 ≤ r ∧ r < 17 / 10
  | 6 => 17 / 10 ≤ r ∧ r < 37 / 20
  | 7 => 37 / 20 ≤ r ∧ r < 2
  | 8 => 2 ≤ r ∧ r < 43 / 20
  | 9 => 43 / 20 ≤ r ∧ r < 23 / 10
  | 10 => 23 / 10 ≤ r ∧ r < 2385432 / 1000000
  | 13 => r = 0
  | _ => False

theorem fifteenExactRadialOwner_spec
    {r : ℝ} (hr0 : 0 ≤ r)
    (hrL : r < 2385432 / 1000000) :
    fifteenExactRadialOwnerSpec (fifteenExactRadialOwner r) r := by
  by_cases hz : r = 0
  · simp [fifteenExactRadialOwner, hz, fifteenExactRadialOwnerSpec]
  have hrpos : 0 < r := lt_of_le_of_ne hr0 (Ne.symm hz)
  unfold fifteenExactRadialOwner
  rw [if_neg hz]
  split_ifs <;> simp only [fifteenExactRadialOwnerSpec] <;>
    constructor <;> linarith [hrpos, hrL]

theorem fifteenExactRadialOwnerSpec_label_le_ten
    {label : Nat} {r : ℝ}
    (howner : fifteenExactRadialOwnerSpec label r)
    (hnonzero : label ≠ 13) : label ≤ 10 := by
  have hcases : label = 0 ∨ label = 1 ∨ label = 2 ∨ label = 3 ∨
      label = 4 ∨ label = 5 ∨ label = 6 ∨ label = 7 ∨ label = 8 ∨
      label = 9 ∨ label = 10 ∨ label = 13 := by
    unfold fifteenExactRadialOwnerSpec at howner
    split at howner <;> simp_all
  rcases hcases with h | h | h | h | h | h | h | h | h | h | h | h <;>
    omega

/-- Each positive exact-bin owner is enclosed by the corresponding rational
interval consumed by `fifteenInitialBox?`. -/
theorem fifteenExactRadialOwnerSpec_certificate_interval
    {label : Nat} {r : ℝ}
    (howner : fifteenExactRadialOwnerSpec label r) :
    if label = 13 then r = 0 else
      ((fifteenBins[label]!).1 : ℝ) ≤ r ∧
        r ≤ ((fifteenBins[label]!).2 : ℝ) := by
  by_cases hzero : label = 13
  · simp [hzero] at howner ⊢
    exact howner
  have hlabel := fifteenExactRadialOwnerSpec_label_le_ten howner hzero
  have hcases : label = 0 ∨ label = 1 ∨ label = 2 ∨ label = 3 ∨
      label = 4 ∨ label = 5 ∨ label = 6 ∨ label = 7 ∨ label = 8 ∨
      label = 9 ∨ label = 10 := by
    unfold fifteenExactRadialOwnerSpec at howner
    split at howner <;> simp_all
  rcases hcases with h | h | h | h | h | h | h | h | h | h | h
  all_goals subst label
  all_goals
    norm_num [fifteenExactRadialOwnerSpec, fifteenBins, fifteenRational,
      Rat.normalize_eq_mkRat, Rat.cast_mkRat_of_ne_zero] at howner ⊢ <;>
      constructor <;> linarith

end CirclePacking
