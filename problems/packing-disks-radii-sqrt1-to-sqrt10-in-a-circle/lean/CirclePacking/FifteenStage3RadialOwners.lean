import CirclePacking.FifteenStage3Table
import CirclePacking.FifteenStageZeroHandoff
import CirclePacking.FifteenCertificateRadiusBounds

/-! Half-open ownership of the Stage 3 radius bins, distinct from their
closed rational enclosures.  Label 9 is the origin, label 8 remains reserved
for an unassigned search position, and label 7 denotes a wall center. -/

namespace CirclePacking

noncomputable def fifteenStage3RadialOwner (r : ℝ) : Nat :=
  if r = 0 then 9 else
  if r < 1 / 2 then 0 else
  if r < 1 then 1 else
  if r < 3 / 2 then 2 else
  if r < 8 / 5 then 3 else
  if r < 5 / 3 then 4 else
  if r < 2 then 5 else 6

noncomputable def fifteenStage3RadialLabel (r : ℝ) : Nat :=
  if r < fifteenCandidateInnerThreshold then fifteenStage3RadialOwner r else 7

def fifteenStage3OwnerSpec (label : Nat) (r : ℝ) : Prop :=
  match label with
  | 0 => 0 < r ∧ r < 1 / 2
  | 1 => 1 / 2 ≤ r ∧ r < 1
  | 2 => 1 ≤ r ∧ r < 3 / 2
  | 3 => 3 / 2 ≤ r ∧ r < 8 / 5
  | 4 => 8 / 5 ≤ r ∧ r < 5 / 3
  | 5 => 5 / 3 ≤ r ∧ r < 2
  | 6 => 2 ≤ r ∧ r < fifteenCandidateInnerThreshold
  | 7 => r = fifteenCandidateOuterRadius
  | 9 => r = 0
  | _ => False

theorem fifteenStage3RadialOwner_spec
    (r : ℝ) (hr0 : 0 ≤ r) (hrL : r < fifteenCandidateInnerThreshold) :
    fifteenStage3OwnerSpec (fifteenStage3RadialOwner r) r := by
  by_cases hz : r = 0
  · simp [fifteenStage3RadialOwner, hz, fifteenStage3OwnerSpec]
  have hrpos : 0 < r := lt_of_le_of_ne hr0 (Ne.symm hz)
  unfold fifteenStage3RadialOwner
  rw [ite_eq_right hz]
  split_ifs <;> simp only [fifteenStage3OwnerSpec] <;> constructor <;> linarith

theorem fifteenStage3RadialLabel_spec_of_classification
    (r : ℝ) (hr0 : 0 ≤ r)
    (hclass : r = fifteenCandidateOuterRadius ∨ r < fifteenCandidateInnerThreshold) :
    fifteenStage3OwnerSpec (fifteenStage3RadialLabel r) r := by
  unfold fifteenStage3RadialLabel
  split_ifs with hinner
  · exact fifteenStage3RadialOwner_spec r hr0 hinner
  · exact hclass.resolve_right hinner

/-- These are exactly the eight children of a Stage 3 inner-position split.
The wall label and the unassigned sentinel cannot own an inner center. -/
theorem fifteenStage3OwnerSpec_inner_choices
    {label : Nat} {r : ℝ} (howner : fifteenStage3OwnerSpec label r)
    (hinner : r < fifteenCandidateInnerThreshold) :
    label ∈ [0, 9, 1, 2, 3, 4, 5, 6] := by
  have hwall := fifteenCandidateInnerThreshold_lt_outerRadius
  unfold fifteenStage3OwnerSpec at howner
  split at howner <;> simp_all
  all_goals linarith

/-- Every rational cutpoint belongs to its right-hand owner; zero belongs
to its singleton owner rather than the positive first interval. -/
theorem fifteenStage3RadialOwner_cutpoints :
    fifteenStage3RadialOwner 0 = 9 ∧
      fifteenStage3RadialOwner (1 / 2) = 1 ∧
      fifteenStage3RadialOwner 1 = 2 ∧
      fifteenStage3RadialOwner (3 / 2) = 3 ∧
      fifteenStage3RadialOwner (8 / 5) = 4 ∧
      fifteenStage3RadialOwner (5 / 3) = 5 ∧
      fifteenStage3RadialOwner 2 = 6 := by
  norm_num [fifteenStage3RadialOwner]

/-- Every owner is enclosed by the certificate's closed rational bin.  The
origin has its own singleton enclosure, rather than the positive first bin. -/
theorem fifteenStage3OwnerSpec_closed_hull
    {label : Nat} {r : ℝ} (howner : fifteenStage3OwnerSpec label r) :
    if label = 9 then r = 0 else
      ((fifteenStage3Bins[label]!).1 : ℝ) ≤ r ∧
        r ≤ ((fifteenStage3Bins[label]!).2 : ℝ) := by
  have hthreshold : fifteenCandidateInnerThreshold < (2385432 : ℝ) / 1000000 := by
    simpa only [fifteenCandidateInnerThreshold] using
      fifteenCandidateInnerThreshold_lt_2385432_1e6
  have hwall := fifteenCandidateOuterRadius_mem_certificate_interval
  have hlabel : label = 0 ∨ label = 1 ∨ label = 2 ∨ label = 3 ∨
      label = 4 ∨ label = 5 ∨ label = 6 ∨ label = 7 ∨ label = 9 := by
    unfold fifteenStage3OwnerSpec at howner
    split at howner <;> simp_all
  rcases hlabel with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    norm_num [fifteenStage3Bins, fifteenRational, Rat.normalize_eq_mkRat,
      Rat.cast_mkRat_of_ne_zero, fifteenStage3OwnerSpec] at howner ⊢ <;>
    first | exact howner | constructor <;> linarith [hwall.1, hwall.2]

theorem fifteenStage3OwnerSpec_small_iff
    {label : Nat} {r : ℝ} (howner : fifteenStage3OwnerSpec label r) :
    (label ≤ 1 ∨ label = 9) ↔ r < 1 := by
  have hwall := fifteenCandidateOuterRadius_gt_one
  unfold fifteenStage3OwnerSpec at howner
  split at howner <;> simp_all <;> linarith

theorem fifteenStage3OwnerSpec_high_iff
    {label : Nat} {r : ℝ} (howner : fifteenStage3OwnerSpec label r)
    (hinner : r < fifteenCandidateInnerThreshold) :
    (5 ≤ label ∧ label ≤ 6) ↔ 5 / 3 ≤ r := by
  have hwall := fifteenCandidateInnerThreshold_lt_outerRadius
  unfold fifteenStage3OwnerSpec at howner
  split at howner <;> simp_all <;> linarith

theorem fifteenStage3OwnerSpec_high2_iff
    {label : Nat} {r : ℝ} (howner : fifteenStage3OwnerSpec label r)
    (hinner : r < fifteenCandidateInnerThreshold) :
    label = 6 ↔ 2 ≤ r := by
  have hwall := fifteenCandidateInnerThreshold_lt_outerRadius
  unfold fifteenStage3OwnerSpec at howner
  split at howner <;> simp_all <;> linarith

/-- The actual wall-pushed packing has an owner at every sorted slot; in
particular, no feasible radius is lost at a rational cutpoint or the origin. -/
theorem fifteen_unit_packing_wall_push_stage3_owner_profile
    {R : ℝ} (P : Packing 15 R)
    (hunit : ∀ i, (P.circles i).radius = 1)
    (hR : R ≤ fifteenCandidateOuterRadius + 1) :
    let Q := fifteen_unit_packing_wall_push P hunit hR
    ∀ i : Fin 15, fifteenStage3OwnerSpec
      (fifteenStage3RadialLabel (fifteenPackingSortedRadius Q i))
      (fifteenPackingSortedRadius Q i) := by
  dsimp only
  intro i
  apply fifteenStage3RadialLabel_spec_of_classification
  · exact pointNorm_nonneg _
  · exact fifteen_unit_packing_wall_push_sorted_radial_classification P hunit hR i

end CirclePacking
