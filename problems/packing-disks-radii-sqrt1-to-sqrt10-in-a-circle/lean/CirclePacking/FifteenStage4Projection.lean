import CirclePacking.FifteenStage4StreamSoundness
import CirclePacking.FifteenStage3PathStructural

/-! The finer Stage 4 labels admit a quotient to the Stage 3 owner classes.
The quotient preserves every counter and structural-pruning predicate, so
Stage 4 structural leaves can reuse the already established Stage 3 geometry
argument. -/

namespace CirclePacking

/-- Forget the extra radial subdivisions while preserving the exceptional
origin, wall, and unassigned labels. -/
def s4ToS3Label (label : Nat) : Nat :=
  if label = 13 then 9 else
  if label ≤ 4 then label else
  if label ≤ 7 then 5 else
  if label ≤ 10 then 6 else
  if label = 11 then 7 else 8

private theorem s4ToS3Label_eq_eight {label : Nat} (h : 14 ≤ label) :
    s4ToS3Label label = 8 := by
  have h13 : label ≠ 13 := by omega
  have h4 : ¬ label ≤ 4 := by omega
  have h7 : ¬ label ≤ 7 := by omega
  have h10 : ¬ label ≤ 10 := by omega
  have h11 : label ≠ 11 := by omega
  simp [s4ToS3Label, h13, h4, h7, h10, h11]

theorem s4ToS3_smallPredicate (label : Nat) :
    (label ≤ 1 || label == 13) =
      (s4ToS3Label label ≤ 1 || s4ToS3Label label == 9) := by
  by_cases h : label ≤ 13
  · interval_cases label <;> decide
  · have h14 : 14 ≤ label := by omega
    rw [s4ToS3Label_eq_eight h14]
    simp <;> omega

@[simp] theorem s4ToS3_smallCondition (label : Nat) :
    (label ≤ 1 ∨ label = 13) ↔
      (s4ToS3Label label ≤ 1 ∨ s4ToS3Label label = 9) := by
  by_cases h : label ≤ 13
  · interval_cases label <;> simp [s4ToS3Label]
  · have h14 : 14 ≤ label := by omega
    rw [s4ToS3Label_eq_eight h14]
    simp <;> omega

theorem s4ToS3_highPredicate (label : Nat) :
    (label ≥ 5 && label ≤ 10) =
      (s4ToS3Label label ≥ 5 && s4ToS3Label label ≤ 6) := by
  by_cases h : label ≤ 13
  · interval_cases label <;> decide
  · have h14 : 14 ≤ label := by omega
    rw [s4ToS3Label_eq_eight h14]
    simp <;> omega

@[simp] theorem s4ToS3_highCondition (label : Nat) :
    (5 ≤ label ∧ label ≤ 10) ↔
      (5 ≤ s4ToS3Label label ∧ s4ToS3Label label ≤ 6) := by
  by_cases h : label ≤ 13
  · interval_cases label <;> simp [s4ToS3Label]
  · have h14 : 14 ≤ label := by omega
    rw [s4ToS3Label_eq_eight h14]
    simp <;> omega

theorem s4ToS3_high2Predicate (label : Nat) :
    (label ≥ 8 && label ≤ 10) = (s4ToS3Label label == 6) := by
  by_cases h : label ≤ 13
  · interval_cases label <;> decide
  · have h14 : 14 ≤ label := by omega
    rw [s4ToS3Label_eq_eight h14]
    simp <;> omega

@[simp] theorem s4ToS3_high2Condition (label : Nat) :
    (8 ≤ label ∧ label ≤ 10) ↔ s4ToS3Label label = 6 := by
  by_cases h : label ≤ 13
  · interval_cases label <;> simp [s4ToS3Label]
  · have h14 : 14 ≤ label := by omega
    rw [s4ToS3Label_eq_eight h14]
    simp <;> omega

theorem s4ToS3_originPredicate (label : Nat) :
    (label == 13) = (s4ToS3Label label == 9) := by
  by_cases h : label ≤ 13
  · interval_cases label <;> decide
  · have h14 : 14 ≤ label := by omega
    rw [s4ToS3Label_eq_eight h14]
    simp <;> omega

theorem s4ToS3_lowOriginPredicate (label : Nat) :
    (label < 8 && label != 13) =
      (s4ToS3Label label < 6 && s4ToS3Label label != 9) := by
  by_cases h : label ≤ 13
  · interval_cases label <;> decide
  · have h14 : 14 ≤ label := by omega
    rw [s4ToS3Label_eq_eight h14]
    simp <;> omega

theorem s4ToS3_mixedZeroPredicate (label : Nat) :
    (label == 0 || label == 13) =
      (s4ToS3Label label == 0 || s4ToS3Label label == 9) := by
  by_cases h : label ≤ 13
  · interval_cases label <;> decide
  · have h14 : 14 ≤ label := by omega
    rw [s4ToS3Label_eq_eight h14]
    simp <;> omega

theorem s4ToS3_mixedTwoPredicate (label : Nat) :
    (label == 2) = (s4ToS3Label label == 2) := by
  by_cases h : label ≤ 13
  · interval_cases label <;> decide
  · have h14 : 14 ≤ label := by omega
    rw [s4ToS3Label_eq_eight h14]
    simp <;> omega

def s4ToS3State (s : S4State) : S3State :=
  ⟨s.labels.map s4ToS3Label, s.depth, s.small, s.high, s.high2⟩

theorem s4InnerPositions_eq_s3 (pattern : String) :
    s4InnerPositions pattern = s3InnerPositions pattern := rfl

theorem s4ToS3State_initial (pattern : String) :
    s4ToS3State (s4Initial pattern) = s3Initial pattern := by
  simp only [s4ToS3State, s4Initial, s3Initial, s4N, s3N]
  congr 1
  apply Array.ext
  · simp
  · intro i hi₁ hi₂
    simp only [Array.getElem_map]
    by_cases hb : pattern.toList[i]? = some '1'
    · simp [hb, s4ToS3Label]
    · simp [hb, s4ToS3Label]

theorem s4ToS3State_next (inner : Array Nat) (s : S4State) (label : Nat) :
    s4ToS3State (s4Next inner s label) =
      s3Next inner (s4ToS3State s) (s4ToS3Label label) := by
  cases s
  simp [s4ToS3State, s4Next, s3Next]

private theorem s4ToS3_get! (labels : Array Nat) (p : Nat) :
    (labels.map s4ToS3Label)[p]! = s4ToS3Label (labels[p]!) := by
  by_cases hp : p < labels.size
  · rw [getElem!_pos labels p hp,
      getElem!_pos (labels.map s4ToS3Label) p (by simpa using hp)]
    exact Array.getElem_map s4ToS3Label (by simpa using hp)
  · have hp' : ¬ p < (labels.map s4ToS3Label).size := by simpa using hp
    rw [getElem!_neg labels p hp, getElem!_neg (labels.map s4ToS3Label) p hp']
    simp [s4ToS3Label]

private theorem s4OriginReason_project (inner labels : Array Nat) :
    s4OriginReason inner ⟨labels, 0, 0, 0, 0⟩ =
      s3OriginReason inner (⟨labels.map s4ToS3Label, 0, 0, 0, 0⟩ : S3State) := by
  simp only [s4OriginReason, s3OriginReason, s4ToS3_get!,
    s4ToS3_originPredicate, s4ToS3_lowOriginPredicate]

private theorem s4MixedReason_project (labels : Array Nat) (small : Nat) :
    s4MixedReason ⟨labels, 0, small, 0, 0⟩ =
      s3MixedReason (⟨labels.map s4ToS3Label, 0, small, 0, 0⟩ : S3State) := by
  have hzero : labels.toList.any (fun t => t == 0 || t == 13) =
      (labels.map s4ToS3Label).toList.any (fun t => t == 0 || t == 9) := by
    rw [Array.toList_map]
    induction labels.toList with
    | nil => rfl
    | cons x xs ih =>
        simp only [List.any_cons, List.map_cons]
        rw [s4ToS3_mixedZeroPredicate x, ih]
  have htwo : labels.toList.any (fun t => t == 2) =
      (labels.map s4ToS3Label).toList.any (fun t => t == 2) := by
    rw [Array.toList_map]
    induction labels.toList with
    | nil => rfl
    | cons x xs ih =>
        simp only [List.any_cons, List.map_cons]
        rw [s4ToS3_mixedTwoPredicate x, ih]
  by_cases hs : small = 1
  · simp only [s4MixedReason, s3MixedReason, hs]
    rw [hzero, htwo]
  · simp [s4MixedReason, s3MixedReason, hs]

theorem s4StructurallyPruned_project (inner : Array Nat) (s : S4State) :
    s4StructurallyPruned inner s =
      s3StructurallyPruned inner (s4ToS3State s) := by
  have hsmall : s4SmallReason s = s3SmallReason (s4ToS3State s) := by
    cases s
    rfl
  have horigin : s4OriginReason inner s =
      s3OriginReason inner (s4ToS3State s) := by
    cases s with
    | mk labels depth small high high2 =>
        exact s4OriginReason_project inner labels
  have hrank : s4RankReason inner s =
      s3RankReason inner (s4ToS3State s) := by
    cases s
    rfl
  have hmixed : s4MixedReason s = s3MixedReason (s4ToS3State s) := by
    cases s with
    | mk labels depth small high high2 =>
        exact s4MixedReason_project labels small
  unfold s4StructurallyPruned s3StructurallyPruned
  rw [hsmall, horigin, hrank, hmixed]

theorem FifteenStage4TargetPath.project
    (pattern : String) (target : Array Nat) {s : S4State}
    (hpath : FifteenStage4TargetPath pattern target s) :
    FifteenStage3TargetPath pattern (target.map s4ToS3Label) (s4ToS3State s) := by
  induction hpath with
  | initial =>
      rw [s4ToS3State_initial]
      exact .initial
  | @step s hpath hdepth ih =>
      rw [s4ToS3State_next]
      have hinner := s4InnerPositions_eq_s3 pattern
      let pos := (s4InnerPositions pattern)[s.depth]!
      rw [← s4ToS3_get! target pos]
      apply FifteenStage3TargetPath.step ih
      simpa [s4ToS3State, hinner] using hdepth

/-- A Stage 4 structural prune transfers to the identical Stage 3 prune on
the projected path, where the packing-level exclusion theorem applies. -/
theorem fifteenStage4TargetPath_structuralPrune_excluded_of_geometry
    (radii : Fin 15 → ℝ) (labels : Fin 15 → Nat)
    (hgeometry : FifteenStage3GeometricConditions radii labels)
    (profile : Fin 15 → Bool)
    (hprofile : ∀ i, profile i = true ↔
      radii i < fifteenCandidateInnerThreshold)
    (target : Array Nat) {s : S4State}
    (hpath : FifteenStage4TargetPath (fifteenStage0ProfileWord profile)
      target s)
    (hprojectedTarget : target.map s4ToS3Label =
      fifteenStage3OwnerLabelArray labels)
    (hreason : s4StructurallyPruned
      (s4InnerPositions (fifteenStage0ProfileWord profile)) s = true) : False := by
  have hprojectedPath := hpath.project
  rw [hprojectedTarget] at hprojectedPath
  have hprojectedReason : s3StructurallyPruned
      (s3InnerPositions (fifteenStage0ProfileWord profile))
      (s4ToS3State s) = true := by
    rw [← s4StructurallyPruned_project]
    simpa [s4InnerPositions_eq_s3] using hreason
  have hreason' :
      s3SmallReason (s4ToS3State s) = true ∨
      s3OriginReason (s3InnerPositions (fifteenStage0ProfileWord profile))
        (s4ToS3State s) = true ∨
      s3RankReason (s3InnerPositions (fifteenStage0ProfileWord profile))
        (s4ToS3State s) = true ∨
      s3MixedReason (s4ToS3State s) = true := by
    simpa [s3StructurallyPruned, or_assoc] using hprojectedReason
  exact fifteenStage3TargetPath_structuralReasons_excluded_of_geometry
    radii labels hgeometry profile hprofile hprojectedPath hreason'

set_option maxHeartbeats 0
/-- The finer Stage 4 half-open radial partition projects exactly to the
coarser Stage 3 partition, including the wall and singleton origin. -/
theorem s4ToS3RadialLabel_eq_stage3 (r : ℝ) :
    s4ToS3Label (fifteenStage4RadialLabel r) =
      fifteenStage3RadialLabel r := by
  by_cases hinner : r < fifteenCandidateInnerThreshold
  · simp only [fifteenStage4RadialLabel, fifteenStage3RadialLabel, if_pos hinner]
    unfold fifteenStage4RadialOwner fifteenStage3RadialOwner
    split_ifs <;> norm_num [s4ToS3Label] <;>
      linarith [fifteenCandidateInnerThreshold_gt_23_10]
  · simp [fifteenStage4RadialLabel, fifteenStage3RadialLabel,
      hinner, s4ToS3Label]

end CirclePacking
