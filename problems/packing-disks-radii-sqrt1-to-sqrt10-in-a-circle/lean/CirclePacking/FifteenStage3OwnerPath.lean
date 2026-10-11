import CirclePacking.FifteenStage3GeometricHandoff
import CirclePacking.FifteenStage3Certificate
import CirclePacking.FifteenStageZero

/-! The Stage 3 profile word, radial owners, and checker branch choices are
identified at the same positional slots. -/

namespace CirclePacking

private theorem fifteenStage3ProfileWord_toList (profile : Fin 15 → Bool) :
    (fifteenStage0ProfileWord profile).toList =
      List.ofFn (fun i => if profile i then '1' else '0') := by
  change (String.ofList ((List.range 15).map fun i =>
    if Nat.testBit (fifteenStage0ProfileMask profile) (14 - i) then '1' else '0')).toList = _
  rw [String.toList_ofList]
  apply List.ext_getElem
  · simp
  · intro i hi _
    have hi' : i < 15 := by simpa using hi
    simp only [List.getElem_map, List.getElem_range, List.getElem_ofFn]
    rw [fifteenStage0ProfileMask_testBit profile ⟨i, hi'⟩]

/-- The positional `1` bits selected by `s3InnerPositions` are exactly the
true entries of the profile used to construct the Stage 0 word. -/
theorem fifteenStage3ProfileWord_inner_iff (profile : Fin 15 → Bool) (i : Fin 15) :
    i.val ∈ (s3InnerPositions (fifteenStage0ProfileWord profile)).toList ↔
      profile i = true := by
  rw [s3InnerPositions_mem_iff_char]
  constructor
  · rintro ⟨_, hchar⟩
    have hword :
        (fifteenStage0ProfileWord profile).toList[i.val]? =
          some (if profile i then '1' else '0') := by
      rw [fifteenStage3ProfileWord_toList]
      change (List.ofFn (fun j : Fin 15 => if profile j then '1' else '0'))[i.val]? = _
      rw [List.getElem?_ofFn, dif_pos i.isLt]
    rw [hword] at hchar
    cases hprofile : profile i <;> simp_all
  · intro hprofile
    constructor
    · exact i.isLt
    · rw [fifteenStage3ProfileWord_toList]
      change (List.ofFn (fun j : Fin 15 => if profile j then '1' else '0'))[i.val]? = _
      rw [List.getElem?_ofFn, dif_pos i.isLt]
      simp [hprofile]

def fifteenStage3OwnerLabelArray (labels : Fin 15 → Nat) : Array Nat :=
  Array.ofFn labels

theorem fifteenStage3OwnerLabelArray_get (labels : Fin 15 → Nat) (i : Nat)
    (hi : i < 15) :
    (fifteenStage3OwnerLabelArray labels)[i]! = labels ⟨i, hi⟩ := by
  unfold fifteenStage3OwnerLabelArray
  rw [getElem!_pos _ _ (by simpa using hi)]
  rw [Array.getElem_ofFn (by simpa using hi)]

/-- A real inner owner belongs to one of precisely the eight labels split by
the certificate. This names the geometric side of the branch choice. -/
theorem fifteenStage3GeometricInnerOwner_is_branch
    (radii : Fin 15 → ℝ) (labels : Fin 15 → Nat)
    (howners : ∀ i, fifteenStage3OwnerSpec (labels i) (radii i))
    (profile : Fin 15 → Bool)
    (hprofile : ∀ i, profile i = true → radii i < fifteenCandidateInnerThreshold)
    (i : Fin 15) (hi : profile i = true) :
    labels i ∈ [0, 9, 1, 2, 3, 4, 5, 6] := by
  exact fifteenStage3OwnerSpec_inner_choices (howners i) (hprofile i hi)

/-- For a complete geometric owner profile, every index the checker splits
has a target label among the corresponding eight children. -/
theorem fifteenStage3GeometricProfile_nextLabel_allowed
    (radii : Fin 15 → ℝ) (labels : Fin 15 → Nat)
    (howners : ∀ i, fifteenStage3OwnerSpec (labels i) (radii i))
    (profile : Fin 15 → Bool)
    (hprofile : ∀ i, profile i = true → radii i < fifteenCandidateInnerThreshold)
    (k : Nat)
    (hk : k < (s3InnerPositions (fifteenStage0ProfileWord profile)).size) :
    let ownerArray := fifteenStage3OwnerLabelArray labels
    ownerArray[(s3InnerPositions (fifteenStage0ProfileWord profile))[k]!]! ∈
        [0, 9, 1, 2, 3, 4, 5, 6] := by
  let p := (s3InnerPositions (fifteenStage0ProfileWord profile))[k]!
  have hp : p < 15 := by
    dsimp [p]
    exact fifteenStage3InnerPosition_get_bound
      (fifteenStage0ProfileWord profile) hk
  have hmemOrdinary :
      (s3InnerPositions (fifteenStage0ProfileWord profile))[k] ∈
        (s3InnerPositions (fifteenStage0ProfileWord profile)).toList :=
    Array.getElem_mem_toList hk
  have hmem : p ∈ (s3InnerPositions (fifteenStage0ProfileWord profile)).toList := by
    dsimp [p]
    rw [getElem!_pos (s3InnerPositions (fifteenStage0ProfileWord profile)) k hk]
    exact hmemOrdinary
  have htrue : profile ⟨p, hp⟩ = true := by
    have hiff := fifteenStage3ProfileWord_inner_iff profile ⟨p, hp⟩
    exact hiff.mp hmem
  change (fifteenStage3OwnerLabelArray labels)[p]! ∈ _
  rw [fifteenStage3OwnerLabelArray_get labels p hp]
  exact fifteenStage3GeometricInnerOwner_is_branch radii labels howners profile
    hprofile ⟨p, hp⟩ htrue

/-- A complete radial profile therefore selects one complete Stage 3 path;
at every split, its label is one of the certificate's eight children, and
the resulting state agrees with the actual owner array on all split slots. -/
theorem fifteenStage3GeometricProfile_targetPath
    (radii : Fin 15 → ℝ) (labels : Fin 15 → Nat)
    (howners : ∀ i, fifteenStage3OwnerSpec (labels i) (radii i))
    (profile : Fin 15 → Bool)
    (hprofile : ∀ i, profile i = true → radii i < fifteenCandidateInnerThreshold) :
    ∃ s : S3State,
      FifteenStage3TargetPath (fifteenStage0ProfileWord profile)
        (fifteenStage3OwnerLabelArray labels) s ∧
      s.depth = (s3InnerPositions (fifteenStage0ProfileWord profile)).size ∧
      (∀ k, k < s.depth →
        s.labels[(s3InnerPositions (fifteenStage0ProfileWord profile))[k]!]! =
          getElem! (fifteenStage3OwnerLabelArray labels)
            ((s3InnerPositions (fifteenStage0ProfileWord profile))[k]!)) ∧
      (∀ k, k < (s3InnerPositions (fifteenStage0ProfileWord profile)).size →
        getElem! (fifteenStage3OwnerLabelArray labels)
          ((s3InnerPositions (fifteenStage0ProfileWord profile))[k]!) ∈
            [0, 9, 1, 2, 3, 4, 5, 6]) := by
  obtain ⟨s, hpath, hdepth⟩ := fifteenStage3TargetPath_full
    (fifteenStage0ProfileWord profile) (fifteenStage3OwnerLabelArray labels)
  refine ⟨s, hpath, hdepth, ?_, ?_⟩
  · exact fifteenStage3TargetPath_prefix_agrees
      (fifteenStage0ProfileWord profile) (fifteenStage3OwnerLabelArray labels) hpath
  · intro k hk
    exact fifteenStage3GeometricProfile_nextLabel_allowed radii labels howners profile
      hprofile k hk

/-- A non-sentinel label observed at an inner position on a target path has
already been assigned, and therefore equals the corresponding geometric
owner label. -/
private theorem fifteenStage3TargetPath_label_agrees_at_inner
    (labels : Fin 15 → Nat) (profile : Fin 15 → Bool) {s : S3State}
    (hpath : FifteenStage3TargetPath (fifteenStage0ProfileWord profile)
      (fifteenStage3OwnerLabelArray labels) s)
    (k : Nat) (hk : k < (s3InnerPositions (fifteenStage0ProfileWord profile)).size)
    (hsentinel : s.labels[(s3InnerPositions
      (fifteenStage0ProfileWord profile))[k]!]! ≠ 8) :
    s.labels[(s3InnerPositions (fifteenStage0ProfileWord profile))[k]!]! =
      labels ⟨(s3InnerPositions (fifteenStage0ProfileWord profile))[k]!,
        fifteenStage3InnerPosition_get_bound
          (fifteenStage0ProfileWord profile) hk⟩ := by
  let pattern := fifteenStage0ProfileWord profile
  let inner := s3InnerPositions pattern
  have hsem := fifteenStage3TargetPath_slot_semantics pattern
    (fifteenStage3OwnerLabelArray labels) hpath k (by simpa [inner] using hk)
  have hsem' : s.labels[inner[k]!]! = if k < s.depth then
      (fifteenStage3OwnerLabelArray labels)[inner[k]!]! else 8 := by
    simpa [inner] using hsem
  have hassigned : k < s.depth := by
    by_contra hnot
    have hkge : s.depth ≤ k := by omega
    have hnot' : ¬ k < s.depth := not_lt.mpr hkge
    have hsem8 : s.labels[inner[k]!]! = 8 := by
      simpa [hnot'] using hsem'
    exact hsentinel hsem8
  have htarget : s.labels[inner[k]!]! =
      (fifteenStage3OwnerLabelArray labels)[inner[k]!]! := by
    simpa [hassigned] using hsem'
  have hpositionBound : inner[k]! < 15 := by
    exact fifteenStage3InnerPosition_get_bound pattern hk
  rw [fifteenStage3OwnerLabelArray_get labels inner[k]! hpositionBound] at htarget
  exact htarget

/-- The checker’s origin-conflict leaf cannot occur on a geometrically valid
owner path: both labels it detects have already been assigned, so they
would give two actual centers whose radii sum to less than two. -/
theorem fifteenStage3TargetPath_originReason_excluded
    (radii : Fin 15 → ℝ) (labels : Fin 15 → Nat)
    (howners : ∀ i, fifteenStage3OwnerSpec (labels i) (radii i))
    (hsum : ∀ i j, i ≠ j → 2 ≤ radii i + radii j)
    (profile : Fin 15 → Bool) {s : S3State}
    (hpath : FifteenStage3TargetPath (fifteenStage0ProfileWord profile)
      (fifteenStage3OwnerLabelArray labels) s)
    (hreason : s3OriginReason
      (s3InnerPositions (fifteenStage0ProfileWord profile)) s = true) : False := by
  let inner := s3InnerPositions (fifteenStage0ProfileWord profile)
  have hparts :
      (∃ k, ∃ hk : k < inner.size, s.labels[inner[k]]! = 9) ∧
      (∃ k, ∃ hk : k < inner.size,
        s.labels[inner[k]]! < 6 ∧ ¬ s.labels[inner[k]]! = 9) := by
    simpa [s3OriginReason, List.any_eq_true, Bool.and_eq_true] using hreason
  obtain ⟨⟨i, hi, hi9⟩, ⟨j, hj, hjLow, _⟩⟩ := hparts
  have hi9Array : s.labels[inner[i]!]! = 9 := by
    simpa only [getElem!_pos inner i hi] using hi9
  have hjLowArray : s.labels[inner[j]!]! < 6 := by
    simpa only [getElem!_pos inner j hj] using hjLow
  have hiSentinel : s.labels[inner[i]!]! ≠ 8 := by
    rw [hi9Array]
    decide
  have hjSentinel : s.labels[inner[j]!]! ≠ 8 := by omega
  have hiLabel := fifteenStage3TargetPath_label_agrees_at_inner labels profile
    hpath i hi hiSentinel
  have hjLabel := fifteenStage3TargetPath_label_agrees_at_inner labels profile
    hpath j hj hjSentinel
  have hi9' : labels ⟨inner[i]!, fifteenStage3InnerPosition_get_bound _ hi⟩ = 9 := by
    rw [← hiLabel]
    exact hi9Array
  have hjLow' : labels ⟨inner[j]!, fifteenStage3InnerPosition_get_bound _ hj⟩ < 6 := by
    rw [← hjLabel]
    exact hjLowArray
  exact fifteenStage3Owners_exclude_origin_leaf radii labels howners hsum
    ⟨inner[i]!, fifteenStage3InnerPosition_get_bound _ hi⟩
    ⟨inner[j]!, fifteenStage3InnerPosition_get_bound _ hj⟩ hi9' hjLow'

/-- The mixed-bin structural prune also contradicts an actual packing. Its
two witness labels are below the fixed wall sentinel, so the outer-slot
invariant first identifies them as inner centers, after which pairwise
separation rules out the radii combination. -/
theorem fifteenStage3TargetPath_mixedReason_excluded
    (radii : Fin 15 → ℝ) (labels : Fin 15 → Nat)
    (howners : ∀ i, fifteenStage3OwnerSpec (labels i) (radii i))
    (hsum : ∀ i j, i ≠ j → 2 ≤ radii i + radii j)
    (profile : Fin 15 → Bool) {s : S3State}
    (hpath : FifteenStage3TargetPath (fifteenStage0ProfileWord profile)
      (fifteenStage3OwnerLabelArray labels) s)
    (hreason : s3MixedReason s = true) : False := by
  have hsize := (fifteenStage3ReachableState_semantics
    (fifteenStage0ProfileWord profile)
    (fifteenStage3TargetPath_reachable _ _ hpath)).2.1
  have hsize15 : s.labels.size = 15 := by simpa using hsize
  have hsmall : s.small = 1 := by
    by_contra hne
    simp [s3MixedReason, hne] at hreason
  have hflags :
      ((s.labels.toList.any fun t => t == 0 || t == 9) &&
        (s.labels.toList.any fun t => t == 2)) = true := by
    simpa [s3MixedReason, hsmall] using hreason
  have hflagPair := Bool.and_eq_true_iff.mp hflags
  have hlist :
      (∃ p ∈ s.labels.toList, p = 0 ∨ p = 9) ∧
      (∃ q ∈ s.labels.toList, q = 2) := by
    constructor
    · have hp := (List.any_eq_true.mp hflagPair.1)
      rcases hp with ⟨p, hp, hpLabel⟩
      have hpLabel' : (p == 0) = true ∨ (p == 9) = true := by
        simpa only [Bool.or_eq_true] using hpLabel
      rcases hpLabel' with hp0 | hp9
      · exact ⟨p, hp, Or.inl (by simpa using hp0)⟩
      · exact ⟨p, hp, Or.inr (by simpa using hp9)⟩
    · have hq := (List.any_eq_true.mp hflagPair.2)
      rcases hq with ⟨q, hq, hqLabel⟩
      exact ⟨q, hq, by simpa using hqLabel⟩
  obtain ⟨⟨pv, hpv, hpVal⟩, ⟨qv, hqv, hqVal⟩⟩ := hlist
  obtain ⟨p, hp, hpEq⟩ := List.mem_iff_getElem.mp hpv
  obtain ⟨q, hq, hqEq⟩ := List.mem_iff_getElem.mp hqv
  have hpLabel : s.labels[p]! = 0 ∨ s.labels[p]! = 9 := by
    have hget : s.labels[p]! = pv := by
      calc
        s.labels[p]! = s.labels.toList[p]! := by rw [Array.getElem!_toList]
        _ = s.labels.toList[p] := getElem!_pos s.labels.toList p hp
        _ = pv := hpEq
    rw [hget]
    exact hpVal
  have hqLabel : s.labels[q]! = 2 := by
    have hget : s.labels[q]! = qv := by
      calc
        s.labels[q]! = s.labels.toList[q]! := by rw [Array.getElem!_toList]
        _ = s.labels.toList[q] := getElem!_pos s.labels.toList q hq
        _ = qv := hqEq
    rw [hget]
    exact hqVal
  let pattern := fifteenStage0ProfileWord profile
  let inner := s3InnerPositions pattern
  have hpBound : p < 15 := by simpa [hsize15] using hp
  have hqBound : q < 15 := by simpa [hsize15] using hq
  have hpInner : p ∈ inner.toList := by
    by_contra houter
    have hwall := fifteenStage3TargetPath_outerSlot_seven pattern
      (fifteenStage3OwnerLabelArray labels) hpath p hpBound houter
    rw [hwall] at hpLabel
    omega
  have hqInner : q ∈ inner.toList := by
    by_contra houter
    have hwall := fifteenStage3TargetPath_outerSlot_seven pattern
      (fifteenStage3OwnerLabelArray labels) hpath q hqBound houter
    rw [hwall] at hqLabel
    omega
  obtain ⟨i, hi, hip⟩ := List.mem_iff_getElem.mp hpInner
  obtain ⟨j, hj, hjq⟩ := List.mem_iff_getElem.mp hqInner
  have hposI : inner[i]! = p := by
    calc
      inner[i]! = inner.toList[i]! := by rw [Array.getElem!_toList]
      _ = inner.toList[i] := getElem!_pos inner.toList i hi
      _ = p := hip
  have hposJ : inner[j]! = q := by
    calc
      inner[j]! = inner.toList[j]! := by rw [Array.getElem!_toList]
      _ = inner.toList[j] := getElem!_pos inner.toList j hj
      _ = q := hjq
  have hpState : s.labels[inner[i]!]! = 0 ∨ s.labels[inner[i]!]! = 9 := by
    rw [hposI]
    exact hpLabel
  have hqState : s.labels[inner[j]!]! = 2 := by
    rw [hposJ]
    exact hqLabel
  have hpSentinel : s.labels[inner[i]!]! ≠ 8 := by
    rcases hpState with h | h <;> rw [h] <;> decide
  have hqSentinel : s.labels[inner[j]!]! ≠ 8 := by
    rw [hqState]
    decide
  have hpActual := fifteenStage3TargetPath_label_agrees_at_inner labels profile
    hpath i (by simpa [inner] using hi) hpSentinel
  have hqActual := fifteenStage3TargetPath_label_agrees_at_inner labels profile
    hpath j (by simpa [inner] using hj) hqSentinel
  have hpLabels : labels ⟨inner[i]!, fifteenStage3InnerPosition_get_bound _ hi⟩ =
      0 ∨ labels ⟨inner[i]!, fifteenStage3InnerPosition_get_bound _ hi⟩ = 9 := by
    rw [← hpActual]
    exact hpState
  have hqLabelActual : labels ⟨inner[j]!, fifteenStage3InnerPosition_get_bound _ hj⟩ =
      2 := by
    rw [← hqActual]
    exact hqState
  exact fifteenStage3Owners_exclude_mixed_leaf radii labels howners hsum
    ⟨inner[i]!, fifteenStage3InnerPosition_get_bound _ hi⟩
    ⟨inner[j]!, fifteenStage3InnerPosition_get_bound _ hj⟩ hpLabels hqLabelActual

/-- An arbitrary packing below the candidate radius reaches the same
owner-selected Stage 3 branch after wall replacement and Stage 0 dihedral
normalization.  This is the concrete geometry-to-search-tree handoff; the
certificate stream still needs a soundness theorem showing that this branch
is pruned. -/
theorem fifteen_unit_packing_wall_push_stage3_target_path
    {R : ℝ} (P : Packing 15 R)
    (hunit : ∀ i, (P.circles i).radius = 1)
    (hR : R ≤ fifteenCandidateOuterRadius + 1) :
    ∃ reflected : Bool, ∃ shift : Fin 15,
      let radii := fifteenStage0TransformProfile
        (fifteenPackingSortedRadius (fifteen_unit_packing_wall_push P hunit hR))
        reflected shift
      let labels := fun i : Fin 15 => fifteenStage3RadialLabel (radii i)
      let profile := fun i : Fin 15 => decide
        (radii i < fifteenCandidateInnerThreshold)
      fifteenStage0ProfileWord profile ∈ fifteenStage0SurvivorPatterns ∧
      ∃ s : S3State,
        FifteenStage3TargetPath (fifteenStage0ProfileWord profile)
          (fifteenStage3OwnerLabelArray labels) s ∧
        s.depth = (s3InnerPositions (fifteenStage0ProfileWord profile)).size ∧
        (∀ k, k < s.depth →
          s.labels[(s3InnerPositions (fifteenStage0ProfileWord profile))[k]!]! =
            getElem! (fifteenStage3OwnerLabelArray labels)
              ((s3InnerPositions (fifteenStage0ProfileWord profile))[k]!)) ∧
        (∀ k, k < (s3InnerPositions (fifteenStage0ProfileWord profile)).size →
          getElem! (fifteenStage3OwnerLabelArray labels)
            ((s3InnerPositions (fifteenStage0ProfileWord profile))[k]!) ∈
              [0, 9, 1, 2, 3, 4, 5, 6]) := by
  dsimp only
  obtain ⟨reflected, shift, hsurvivor, hconditions, _, _, _⟩ :=
    fifteen_unit_packing_wall_push_stage3_geometric_handoff P hunit hR
  refine ⟨reflected, shift, hsurvivor, ?_⟩
  let radii := fifteenStage0TransformProfile
    (fifteenPackingSortedRadius (fifteen_unit_packing_wall_push P hunit hR))
    reflected shift
  let labels := fun i : Fin 15 => fifteenStage3RadialLabel (radii i)
  let profile := fun i : Fin 15 => decide (radii i < fifteenCandidateInnerThreshold)
  have hprofile : ∀ i, profile i = true →
      radii i < fifteenCandidateInnerThreshold := by
    intro i hi
    exact of_decide_eq_true hi
  obtain ⟨s, hpath, hdepth, hagree, hchoices⟩ :=
    fifteenStage3GeometricProfile_targetPath radii labels hconditions.owners
      profile hprofile
  exact ⟨s, hpath, hdepth, hagree, hchoices⟩

end CirclePacking
