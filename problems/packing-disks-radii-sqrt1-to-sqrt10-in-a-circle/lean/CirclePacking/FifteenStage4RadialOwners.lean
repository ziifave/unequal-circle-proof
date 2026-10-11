import CirclePacking.FifteenStage4Table
import CirclePacking.FifteenWallPush
import CirclePacking.FifteenCandidateDetourCurvature
import CirclePacking.FifteenCertificateRadiusBounds

/-! Half-open geometric owners for the finer Stage 4 radius partition.
Labels 0--10 are the inner bins, 11 is the wall, 13 is the singleton
origin, and 12 remains the checker's unassigned sentinel. -/

namespace CirclePacking

noncomputable def fifteenStage4RadialOwner (r : ℝ) : Nat :=
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

noncomputable def fifteenStage4RadialLabel (r : ℝ) : Nat :=
  if r < fifteenCandidateInnerThreshold then fifteenStage4RadialOwner r else 11

def fifteenStage4OwnerSpec (label : Nat) (r : ℝ) : Prop :=
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
  | 10 => 23 / 10 ≤ r ∧ r < fifteenCandidateInnerThreshold
  | 11 => r = fifteenCandidateOuterRadius
  | 13 => r = 0
  | _ => False

theorem fifteenCandidateInnerThreshold_gt_23_10 :
    (23 : ℝ) / 10 < fifteenCandidateInnerThreshold := by
  have hb := fifteenCandidateOuterRadius_mem_certificate_interval
  have hbpos := fifteenCandidateOuterRadius_pos
  have hrecip : 4 / fifteenCandidateOuterRadius < 4 / ((352 : ℝ) / 100) := by
    apply (div_lt_div_iff₀ hbpos (by norm_num : (0 : ℝ) < 352 / 100)).2
    nlinarith [hb.1]
  dsimp [fifteenCandidateInnerThreshold]
  nlinarith [hb.1, hrecip]

theorem fifteenStage4RadialOwner_spec
    (r : ℝ) (hr0 : 0 ≤ r) (hrL : r < fifteenCandidateInnerThreshold) :
    fifteenStage4OwnerSpec (fifteenStage4RadialOwner r) r := by
  by_cases hz : r = 0
  · simp [fifteenStage4RadialOwner, hz, fifteenStage4OwnerSpec]
  have hrpos : 0 < r := lt_of_le_of_ne hr0 (Ne.symm hz)
  unfold fifteenStage4RadialOwner
  rw [ite_eq_right hz]
  split_ifs <;> simp only [fifteenStage4OwnerSpec] <;> constructor <;>
    linarith

theorem fifteenStage4RadialLabel_spec_of_classification
    (r : ℝ) (hr0 : 0 ≤ r)
    (hclass : r = fifteenCandidateOuterRadius ∨
      r < fifteenCandidateInnerThreshold) :
    fifteenStage4OwnerSpec (fifteenStage4RadialLabel r) r := by
  unfold fifteenStage4RadialLabel
  split_ifs with hinner
  · exact fifteenStage4RadialOwner_spec r hr0 hinner
  · exact hclass.resolve_right hinner

theorem fifteenStage4OwnerSpec_closed_hull
    {label : Nat} {r : ℝ} (howner : fifteenStage4OwnerSpec label r) :
    if label = 13 then r = 0 else
      ((fifteenStage4Bins[label]!).1 : ℝ) ≤ r ∧
        r ≤ ((fifteenStage4Bins[label]!).2 : ℝ) := by
  have hthreshold : fifteenCandidateInnerThreshold <
      (2385432 : ℝ) / 1000000 := by
    simpa only [fifteenCandidateInnerThreshold] using
      fifteenCandidateInnerThreshold_lt_2385432_1e6
  have hwall := fifteenCandidateOuterRadius_mem_certificate_interval
  have hlabel : label = 0 ∨ label = 1 ∨ label = 2 ∨ label = 3 ∨
      label = 4 ∨ label = 5 ∨ label = 6 ∨ label = 7 ∨
      label = 8 ∨ label = 9 ∨ label = 10 ∨ label = 11 ∨ label = 13 := by
    unfold fifteenStage4OwnerSpec at howner
    split at howner <;> simp_all
  rcases hlabel with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl <;>
    norm_num [fifteenStage4Bins, fifteenRational,
      Rat.normalize_eq_mkRat, Rat.cast_mkRat_of_ne_zero,
      fifteenStage4OwnerSpec] at howner ⊢ <;>
    first | exact howner | constructor <;> linarith [hwall.1, hwall.2, hthreshold]

end CirclePacking
