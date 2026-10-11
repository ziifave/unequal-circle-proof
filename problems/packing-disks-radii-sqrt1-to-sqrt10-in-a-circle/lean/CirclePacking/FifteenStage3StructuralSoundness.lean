import CirclePacking.FifteenStage3RadialOwners
import CirclePacking.FifteenSixRadiusCount

/-! Population bounds and structural soundness of Stage 3 leaf reasons,
including the generic partial-assignment rank inequality.  The path-level
rank theorem is in `FifteenStage3PathStructural`; connecting its sequence
counts to the geometric Finset populations and proving cycle/stream soundness
remain separate obligations. -/

namespace CirclePacking

private theorem fifteenStage3_radial_rank_population
    (radii : Fin 15 → ℝ) (threshold : ℝ) (n : Nat) (S : Finset (Fin 15))
    (hbound : (Finset.univ.filter fun i : Fin 15 => radii i < threshold).card ≤ n) :
    S.card - n ≤ (S.filter fun i => threshold ≤ radii i).card := by
  classical
  have hsub : (S.filter fun i => ¬ threshold ≤ radii i) ⊆
      Finset.univ.filter fun i : Fin 15 => radii i < threshold := by
    intro i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, lt_of_not_ge (Finset.mem_filter.mp hi).2⟩
  have hlow := (Finset.card_le_card hsub).trans hbound
  have hpartition := Finset.card_filter_add_card_filter_not
    (s := S) (p := fun i => threshold ≤ radii i)
  omega

theorem fifteenStage3RadialAssignment_population
    (radii : Fin 15 → ℝ) (labels : Fin 15 → Nat)
    (howners : ∀ i, fifteenStage3OwnerSpec (labels i) (radii i))
    (hsmall : (Finset.univ.filter fun i : Fin 15 => radii i < 1).card ≤ 1)
    (hfifth : (Finset.univ.filter fun i : Fin 15 => radii i ≤ 5 / 3).card ≤ 4)
    (hsixth : (Finset.univ.filter fun i : Fin 15 => radii i < 2).card ≤ 5)
    (inner : Finset (Fin 15)) (hinner : ∀ i ∈ inner, radii i < fifteenCandidateInnerThreshold) :
    (inner.filter fun i => labels i ≤ 1 ∨ labels i = 9).card ≤ 1 ∧
      inner.card - 4 ≤ (inner.filter fun i => 5 ≤ labels i ∧ labels i ≤ 6).card ∧
      inner.card - 5 ≤ (inner.filter fun i => labels i = 6).card := by
  classical
  have hsmallSub : (inner.filter fun i => labels i ≤ 1 ∨ labels i = 9) ⊆
      Finset.univ.filter fun i : Fin 15 => radii i < 1 := by
    intro i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (fifteenStage3OwnerSpec_small_iff (howners i)).mp (Finset.mem_filter.mp hi).2⟩
  have hfifthSub : (Finset.univ.filter fun i : Fin 15 => radii i < 5 / 3) ⊆
      Finset.univ.filter fun i : Fin 15 => radii i ≤ 5 / 3 := by
    intro i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hi).2.le⟩
  have hhighEq : (inner.filter fun i => 5 ≤ labels i ∧ labels i ≤ 6) =
      inner.filter (fun i => 5 / 3 ≤ radii i) := by
    apply Finset.filter_congr
    intro i hi
    exact fifteenStage3OwnerSpec_high_iff (howners i) (hinner i hi)
  have hhigh2Eq : (inner.filter fun i => labels i = 6) =
      inner.filter (fun i => 2 ≤ radii i) := by
    apply Finset.filter_congr
    intro i hi
    exact fifteenStage3OwnerSpec_high2_iff (howners i) (hinner i hi)
  refine ⟨(Finset.card_le_card hsmallSub).trans hsmall, ?_, ?_⟩
  · rw [hhighEq]
    exact fifteenStage3_radial_rank_population radii (5 / 3) 4 inner
      ((Finset.card_le_card hfifthSub).trans hfifth)
  · rw [hhigh2Eq]
    exact fifteenStage3_radial_rank_population radii 2 5 inner hsixth

/-- A partial assignment cannot repair a violated rank bound: even if every
unassigned center becomes high, its total cannot exceed this expression. -/
theorem fifteenStage3_partial_rank_bound
    (inner assigned : Finset (Fin 15)) (hsub : assigned ⊆ inner)
    (predicate : Fin 15 → Prop) [DecidablePred predicate]
    (n : Nat) (hpopulation : inner.card - n ≤ (inner.filter predicate).card) :
    inner.card - n ≤ (assigned.filter predicate).card + (inner.card - assigned.card) := by
  classical
  have hcover : inner.filter predicate ⊆ (assigned.filter predicate) ∪ (inner \ assigned) := by
    intro i hi
    have hiInner := (Finset.mem_filter.mp hi).1
    by_cases hiAssigned : i ∈ assigned
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hiAssigned, (Finset.mem_filter.mp hi).2⟩)
    · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hiInner, hiAssigned⟩)
  calc
    inner.card - n ≤ (inner.filter predicate).card := hpopulation
    _ ≤ ((assigned.filter predicate) ∪ (inner \ assigned)).card := Finset.card_le_card hcover
    _ ≤ (assigned.filter predicate).card + (inner \ assigned).card := Finset.card_union_le _ _
    _ = (assigned.filter predicate).card + (inner.card - assigned.card) := by
      rw [Finset.card_sdiff_of_subset hsub]

theorem fifteenStage3Owners_exclude_small_leaf
    (inner assigned : Finset (Fin 15)) (hsub : assigned ⊆ inner)
    (labels : Fin 15 → Nat)
    (hpopulation : (inner.filter fun i => labels i ≤ 1 ∨ labels i = 9).card ≤ 1)
    (hleaf : 1 < (assigned.filter fun i => labels i ≤ 1 ∨ labels i = 9).card) : False := by
  have hbound := (Finset.card_le_card (Finset.filter_subset_filter _ hsub)).trans hpopulation
  omega

theorem fifteenStage3Owners_exclude_rank_leaf
    (inner assigned : Finset (Fin 15)) (hsub : assigned ⊆ inner)
    (labels : Fin 15 → Nat)
    (hhigh : inner.card - 4 ≤ (inner.filter fun i => 5 ≤ labels i ∧ labels i ≤ 6).card)
    (hhigh2 : inner.card - 5 ≤ (inner.filter fun i => labels i = 6).card)
    (hleaf : (assigned.filter fun i => 5 ≤ labels i ∧ labels i ≤ 6).card +
        (inner.card - assigned.card) < inner.card - 4 ∨
      (assigned.filter fun i => labels i = 6).card +
        (inner.card - assigned.card) < inner.card - 5) : False := by
  have hbound := fifteenStage3_partial_rank_bound inner assigned hsub _ 4 hhigh
  have hbound2 := fifteenStage3_partial_rank_bound inner assigned hsub _ 5 hhigh2
  omega

theorem fifteenStage3Owners_exclude_origin_leaf
    (radii : Fin 15 → ℝ) (labels : Fin 15 → Nat)
    (howners : ∀ i, fifteenStage3OwnerSpec (labels i) (radii i))
    (hsum : ∀ i j, i ≠ j → 2 ≤ radii i + radii j)
    (i j : Fin 15) (hi : labels i = 9) (hj : labels j < 6) : False := by
  have hne : i ≠ j := by intro heq; subst j; omega
  have hi0 : radii i = 0 := by simpa only [hi, fifteenStage3OwnerSpec] using howners i
  have hj2 : radii j < 2 := by
    have howner := howners j
    unfold fifteenStage3OwnerSpec at howner
    split at howner <;> simp_all <;> first | omega | linarith
  have hbound := hsum i j hne
  linarith

theorem fifteenStage3Owners_exclude_mixed_leaf
    (radii : Fin 15 → ℝ) (labels : Fin 15 → Nat)
    (howners : ∀ i, fifteenStage3OwnerSpec (labels i) (radii i))
    (hsum : ∀ i j, i ≠ j → 2 ≤ radii i + radii j)
    (i j : Fin 15) (hi : labels i = 0 ∨ labels i = 9) (hj : labels j = 2) : False := by
  have hne : i ≠ j := by intro heq; subst j; omega
  have hiHalf : radii i < 1 / 2 := by
    rcases hi with hi | hi
    · have howner : 0 < radii i ∧ radii i < 1 / 2 := by
        simpa only [hi, fifteenStage3OwnerSpec] using howners i
      exact howner.2
    · have hz : radii i = 0 := by simpa only [hi, fifteenStage3OwnerSpec] using howners i
      linarith
  have hjOwner : 1 ≤ radii j ∧ radii j < 3 / 2 := by
    simpa only [hj, fifteenStage3OwnerSpec] using howners j
  have hjThreeHalves : radii j < 3 / 2 := hjOwner.2
  have hbound := hsum i j hne
  linarith

/-- Canonical reindexing preserves all actual owner, pair-sum and population
hypotheses needed by the four structural Stage 3 leaf families. -/
theorem fifteen_unit_packing_wall_push_stage3_structural_profile
    {R : ℝ} (P : Packing 15 R)
    (hunit : ∀ i, (P.circles i).radius = 1)
    (hR : R ≤ fifteenCandidateOuterRadius + 1) (reflected : Bool) (shift : Fin 15) :
    let Q := fifteen_unit_packing_wall_push P hunit hR
    let radii := fifteenStage0TransformProfile (fifteenPackingSortedRadius Q) reflected shift
    let labels := fun i => fifteenStage3RadialLabel (radii i)
    let inner := Finset.univ.filter fun i : Fin 15 => radii i < fifteenCandidateInnerThreshold
    (∀ i, fifteenStage3OwnerSpec (labels i) (radii i)) ∧
      (∀ i j, i ≠ j → 2 ≤ radii i + radii j) ∧
      (inner.filter fun i => labels i ≤ 1 ∨ labels i = 9).card ≤ 1 ∧
      inner.card - 4 ≤ (inner.filter fun i => 5 ≤ labels i ∧ labels i ≤ 6).card ∧
      inner.card - 5 ≤ (inner.filter fun i => labels i = 6).card := by
  classical
  dsimp only
  let Q := fifteen_unit_packing_wall_push P hunit hR
  let original := fifteenPackingSortedRadius Q
  let radii := fifteenStage0TransformProfile original reflected shift
  let labels := fun i => fifteenStage3RadialLabel (radii i)
  let inner := Finset.univ.filter fun i : Fin 15 => radii i < fifteenCandidateInnerThreshold
  have hunitQ := fifteen_unit_packing_wall_push_preserves_unit_radii P hunit hR
  have howners : ∀ i, fifteenStage3OwnerSpec (labels i) (radii i) :=
    fun i => fifteen_unit_packing_wall_push_stage3_owner_profile P hunit hR
      ((fifteenStage0DihedralPermutation reflected shift).symm i)
  have hsumOriginal : ∀ i j : Fin 15, i ≠ j → 2 ≤ original i + original j := by
    intro i j hij
    have hindices : fifteenPackingSortedIndex Q i ≠ fifteenPackingSortedIndex Q j := by
      intro heq
      exact hij ((fifteenPackingSortedIndex_bijective Q).1 heq)
    exact fifteen_unit_packing_pair_radial_sum_ge_two Q hunitQ hindices
  have hsum := fifteenStage0TransformProfile_pairwise original
    (fun a b => 2 ≤ a + b) reflected shift hsumOriginal
  have hsmall : (Finset.univ.filter fun i : Fin 15 => radii i < 1).card ≤ 1 := by
    change (Finset.univ.filter fun i : Fin 15 =>
      fifteenStage0TransformProfile original reflected shift i < 1).card ≤ 1
    rw [fifteenStage0TransformProfile_population original (fun r => r < 1) reflected shift]
    exact fifteen_unit_packing_subunit_sorted_count_le_one Q hunitQ
  have hfifth : (Finset.univ.filter fun i : Fin 15 => radii i ≤ 5 / 3).card ≤ 4 := by
    change (Finset.univ.filter fun i : Fin 15 =>
      fifteenStage0TransformProfile original reflected shift i ≤ 5 / 3).card ≤ 4
    rw [fifteenStage0TransformProfile_population original (fun r => r ≤ 5 / 3) reflected shift]
    exact fifteen_unit_packing_small_radius_count_le_four Q hunitQ
  have hsixth : (Finset.univ.filter fun i : Fin 15 => radii i < 2).card ≤ 5 := by
    change (Finset.univ.filter fun i : Fin 15 =>
      fifteenStage0TransformProfile original reflected shift i < 2).card ≤ 5
    rw [fifteenStage0TransformProfile_population original (fun r => r < 2) reflected shift]
    exact fifteen_unit_packing_radius_two_count_le_five Q hunitQ
  have hpopulation := fifteenStage3RadialAssignment_population radii labels howners
    hsmall hfifth hsixth inner (fun i hi => (Finset.mem_filter.mp hi).2)
  exact ⟨howners, hsum, hpopulation⟩

end CirclePacking
