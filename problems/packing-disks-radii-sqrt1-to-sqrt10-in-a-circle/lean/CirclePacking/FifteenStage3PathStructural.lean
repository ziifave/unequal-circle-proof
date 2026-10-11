import CirclePacking.FifteenStage3OwnerPath

/-! Geometric soundness for the small-count Stage 3 leaf, along the concrete
owner-selected branch. -/

namespace CirclePacking

private def s3SmallLabelPredicate (label : Nat) : Bool :=
  label ≤ 1 || label == 9

def s3FilterRangeCount (n : Nat) (predicate : Nat → Bool) : Nat :=
  ((List.range n).filter predicate).length

private theorem s3FilterRangeCount_step (n : Nat) (predicate : Nat → Bool) :
    s3FilterRangeCount (n + 1) predicate =
      s3FilterRangeCount n predicate + (if predicate n then 1 else 0) := by
  by_cases hp : predicate n = true <;>
    simp [s3FilterRangeCount, List.range_succ, List.filter_append, hp]

private theorem s3FilterRangeCount_le_prefix_add_remaining
    (predicate : Nat → Bool) :
    ∀ n depth, depth ≤ n →
      s3FilterRangeCount n predicate ≤
        s3FilterRangeCount depth predicate + (n - depth) := by
  intro n
  induction n with
  | zero =>
      intro depth hdepth
      have : depth = 0 := by omega
      subst depth
      simp [s3FilterRangeCount]
  | succ n ih =>
      intro depth hdepth
      by_cases hdepth' : depth ≤ n
      · have hstep := s3FilterRangeCount_step n predicate
        have hprev := ih depth hdepth'
        rw [hstep]
        have hsub : n + 1 - depth = n - depth + 1 := by omega
        rw [hsub]
        by_cases hp : predicate n <;> simp [hp] <;> omega
      · have hEq : depth = n + 1 := by omega
        subst depth
        simp [s3FilterRangeCount]

def fifteenStage3ProfileOwnerPosition (profile : Fin 15 → Bool) (k : Nat) : Fin 15 :=
  let position :=
    (s3InnerPositions (fifteenStage0ProfileWord profile))[k]!
  ⟨position % 15, Nat.mod_lt _ (by decide)⟩

/-- Counting owner labels along the array of inner positions is the same as
counting them in the finite set selected by the profile word. This is the
reindexing bridge from geometric Finset population bounds to checker slots. -/
theorem fifteenStage3ProfileOwnerLabelCount
    (profile : Fin 15 → Bool) (labels : Fin 15 → Nat)
    (predicate : Nat → Bool) :
    s3FilterRangeCount
        (s3InnerPositions (fifteenStage0ProfileWord profile)).size
        (fun k => predicate (labels (fifteenStage3ProfileOwnerPosition profile k))) =
      ((Finset.univ.filter fun i : Fin 15 => profile i = true).filter
        fun i => predicate (labels i) = true).card := by
  classical
  let pattern := fifteenStage0ProfileWord profile
  let positions := s3InnerPositions pattern
  let ownerAt (k : Nat) : Nat := labels (fifteenStage3ProfileOwnerPosition profile k)
  let source := (Finset.range positions.size).filter fun k => predicate (ownerAt k) = true
  let profileSet := Finset.univ.filter fun i : Fin 15 => profile i = true
  let target := profileSet.filter fun i => predicate (labels i) = true
  have hfilteredNodup :
      ((List.range positions.size).filter fun k => predicate (ownerAt k)).Nodup :=
    List.nodup_range.filter _
  have hlistSet :
      ((List.range positions.size).filter fun k => predicate (ownerAt k)).toFinset = source := by
    ext k
    simp [source, List.mem_range]
  have hcountSource : source.card = s3FilterRangeCount positions.size
      (fun k => predicate (ownerAt k)) := by
    calc
      source.card =
          ((List.range positions.size).filter fun k => predicate (ownerAt k)).toFinset.card := by
        rw [hlistSet]
      _ = ((List.range positions.size).filter fun k => predicate (ownerAt k)).length :=
        List.toFinset_card_of_nodup hfilteredNodup
      _ = s3FilterRangeCount positions.size (fun k => predicate (ownerAt k)) := by
        rfl
  let hmap (k : Nat) (_hk : k ∈ source) : Fin 15 :=
    fifteenStage3ProfileOwnerPosition profile k
  have hmap_mem (k : Nat) (hk : k ∈ source) : hmap k hk ∈ target := by
    have hklt := Finset.mem_range.mp (Finset.mem_filter.mp hk).1
    have hmod : positions[k]! % 15 = positions[k]! :=
      Nat.mod_eq_of_lt (fifteenStage3InnerPosition_get_bound pattern hklt)
    have hmemOrdinary : positions[k] ∈ positions.toList := Array.getElem_mem_toList hklt
    have hmem : positions[k]! ∈ positions.toList := by
      rw [getElem!_pos positions k hklt]
      exact hmemOrdinary
    have hprofileMem : (hmap k hk).val ∈ positions.toList := by
      change positions[k]! % 15 ∈ positions.toList
      rw [hmod]
      exact hmem
    have hprofile : profile (hmap k hk) = true := by
      exact (fifteenStage3ProfileWord_inner_iff profile (hmap k hk)).mp
        (by simpa only [pattern] using hprofileMem)
    have hpredicate : predicate (labels (hmap k hk)) = true := by
      simpa [hmap, ownerAt] using (Finset.mem_filter.mp hk).2
    exact Finset.mem_filter.mpr ⟨
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hprofile⟩, hpredicate⟩
  have hmap_injective : ∀ k₁ hk₁ k₂ hk₂, hmap k₁ hk₁ = hmap k₂ hk₂ → k₁ = k₂ := by
    intro k₁ hk₁ k₂ hk₂ heq
    have hk₁lt := Finset.mem_range.mp (Finset.mem_filter.mp hk₁).1
    have hk₂lt := Finset.mem_range.mp (Finset.mem_filter.mp hk₂).1
    have hk₁mod : positions[k₁]! % 15 = positions[k₁]! :=
      Nat.mod_eq_of_lt (fifteenStage3InnerPosition_get_bound pattern hk₁lt)
    have hk₂mod : positions[k₂]! % 15 = positions[k₂]! :=
      Nat.mod_eq_of_lt (fifteenStage3InnerPosition_get_bound pattern hk₂lt)
    have hvalMod : positions[k₁]! % 15 = positions[k₂]! % 15 := by
      simpa [hmap, fifteenStage3ProfileOwnerPosition] using congrArg Fin.val heq
    have hval : positions[k₁]! = positions[k₂]! := by
      calc
        positions[k₁]! = positions[k₁]! % 15 := hk₁mod.symm
        _ = positions[k₂]! % 15 := hvalMod
        _ = positions[k₂]! := hk₂mod
    have hlist₁ : k₁ < positions.toList.length := by simpa using hk₁lt
    have hlist₂ : k₂ < positions.toList.length := by simpa using hk₂lt
    apply (fifteenStage3InnerPositions_nodup pattern).getElem!_inj hlist₁ hlist₂ |>.mp
    calc
      positions.toList[k₁]! = positions[k₁]! := by rw [Array.getElem!_toList]
      _ = positions[k₂]! := hval
      _ = positions.toList[k₂]! := by rw [Array.getElem!_toList]
  have hmap_surjective : ∀ i, i ∈ target → ∃ k hk, hmap k hk = i := by
    intro i hi
    have hiProfile : profile i = true :=
      (Finset.mem_filter.mp (Finset.mem_filter.mp hi).1).2
    have hmem : i.val ∈ positions.toList :=
      (fifteenStage3ProfileWord_inner_iff profile i).mpr hiProfile
    obtain ⟨k, hk, hget⟩ := List.mem_iff_getElem.mp hmem
    have hklt : k < positions.size := by simpa using hk
    have hgetBang : positions.toList[k]! = i.val := by
      rw [getElem!_pos positions.toList k hk]
      exact hget
    have harray : positions[k]! = i.val := by
      calc
        positions[k]! = positions.toList[k]! := by rw [Array.getElem!_toList]
        _ = i.val := hgetBang
    have hsource : k ∈ source := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_range.mpr hklt, ?_⟩
      have hmod : positions[k]! % 15 = positions[k]! :=
        Nat.mod_eq_of_lt (fifteenStage3InnerPosition_get_bound pattern hklt)
      have hcenter : fifteenStage3ProfileOwnerPosition profile k = i := by
        apply Fin.ext
        calc
          positions[k]! % 15 = positions[k]! := hmod
          _ = i.val := harray
      have howner : ownerAt k = labels i := by
        simpa [ownerAt] using congrArg labels hcenter
      rw [howner]
      exact (Finset.mem_filter.mp hi).2
    have hcenter : fifteenStage3ProfileOwnerPosition profile k = i := by
      apply Fin.ext
      have hmod : positions[k]! % 15 = positions[k]! :=
        Nat.mod_eq_of_lt (fifteenStage3InnerPosition_get_bound pattern hklt)
      calc
        positions[k]! % 15 = positions[k]! := hmod
        _ = i.val := harray
    exact ⟨k, hsource, by simpa [hmap] using hcenter⟩
  have hbij := Finset.card_bij hmap hmap_mem hmap_injective hmap_surjective
  calc
    s3FilterRangeCount positions.size (fun k => predicate (ownerAt k)) = source.card :=
      hcountSource.symm
    _ = target.card := hbij
    _ = ((Finset.univ.filter fun i : Fin 15 => profile i = true).filter
        fun i => predicate (labels i) = true).card := by
      rfl

/-- A state on a geometrically valid target path cannot trigger the
small-count prune.  The counter records exactly the assigned-prefix labels;
two such labels would be two distinct centers of radii below one, contrary
to their required separation. -/
theorem fifteenStage3TargetPath_smallReason_excluded
    (radii : Fin 15 → ℝ) (labels : Fin 15 → Nat)
    (howners : ∀ i, fifteenStage3OwnerSpec (labels i) (radii i))
    (hsum : ∀ i j, i ≠ j → 2 ≤ radii i + radii j)
    (profile : Fin 15 → Bool) {s : S3State}
    (hpath : FifteenStage3TargetPath (fifteenStage0ProfileWord profile)
      (fifteenStage3OwnerLabelArray labels) s)
    (hsmall : 1 < s.small) : False := by
  let pattern := fifteenStage0ProfileWord profile
  let inner := s3InnerPositions pattern
  let slots := (List.range s.depth).filter fun k =>
    s3SmallLabelPredicate s.labels[inner[k]!]!
  have hreachable := fifteenStage3TargetPath_reachable pattern
    (fifteenStage3OwnerLabelArray labels) hpath
  have hsem := fifteenStage3ReachableState_semantics pattern hreachable
  have hcounter : s.small = slots.length := by
    simpa [slots, s3SmallLabelPredicate, fifteenStage3PrefixCount] using
      hsem.1.1
  have hlen : 1 < slots.length := by omega
  have hnodup : slots.Nodup := by
    rw [List.nodup_iff_pairwise_ne]
    exact List.Pairwise.filter _
      (List.nodup_iff_pairwise_ne.mp List.nodup_range)
  cases hslots : slots with
  | nil => simp [hslots] at hlen
  | cons first tail =>
      cases htail : tail with
      | nil => simp [hslots, htail] at hlen
      | cons second rest =>
          have hfullNodup : (first :: second :: rest).Nodup := by
            simpa [hslots, htail] using hnodup
          have hfirstNot : first ∉ second :: rest :=
            (List.nodup_cons.mp hfullNodup).1
          have hdistinct : first ≠ second := by
            intro heq
            apply hfirstNot
            simp [heq]
          have hfirstMem : first ∈ slots := by simp [hslots]
          have hsecondMem : second ∈ slots := by simp [hslots, htail]
          have hfirstData := List.mem_filter.mp hfirstMem
          have hsecondData := List.mem_filter.mp hsecondMem
          have hfirstDepth : first < s.depth := List.mem_range.mp hfirstData.1
          have hsecondDepth : second < s.depth := List.mem_range.mp hsecondData.1
          have hdepthBound : s.depth ≤ inner.size := by
            simpa [inner] using hsem.2.2
          have hfirstInner : first < inner.size := by omega
          have hsecondInner : second < inner.size := by omega
          have hfirstActualIndex : inner[first]! < 15 :=
            fifteenStage3InnerPosition_get_bound pattern hfirstInner
          have hsecondActualIndex : inner[second]! < 15 :=
            fifteenStage3InnerPosition_get_bound pattern hsecondInner
          let i : Fin 15 := ⟨inner[first]!, hfirstActualIndex⟩
          let j : Fin 15 := ⟨inner[second]!, hsecondActualIndex⟩
          have hfirstAgree := fifteenStage3TargetPath_prefix_agrees pattern
            (fifteenStage3OwnerLabelArray labels) hpath first hfirstDepth
          have hsecondAgree := fifteenStage3TargetPath_prefix_agrees pattern
            (fifteenStage3OwnerLabelArray labels) hpath second hsecondDepth
          have hfirstOwner : s.labels[inner[first]!]! = labels i := by
            calc
              s.labels[inner[first]!]! =
                  (fifteenStage3OwnerLabelArray labels)[inner[first]!]! := hfirstAgree
              _ = labels i := by
                simp [i, fifteenStage3OwnerLabelArray_get, hfirstActualIndex]
          have hsecondOwner : s.labels[inner[second]!]! = labels j := by
            calc
              s.labels[inner[second]!]! =
                  (fifteenStage3OwnerLabelArray labels)[inner[second]!]! := hsecondAgree
              _ = labels j := by
                simp [j, fifteenStage3OwnerLabelArray_get, hsecondActualIndex]
          have hfirstPred : s3SmallLabelPredicate (labels i) = true := by
            rw [← hfirstOwner]
            exact hfirstData.2
          have hsecondPred : s3SmallLabelPredicate (labels j) = true := by
            rw [← hsecondOwner]
            exact hsecondData.2
          have hfirstSmall : radii i < 1 := by
            apply (fifteenStage3OwnerSpec_small_iff (howners i)).mp
            simpa [s3SmallLabelPredicate, Bool.or_eq_true, beq_iff_eq] using hfirstPred
          have hsecondSmall : radii j < 1 := by
            apply (fifteenStage3OwnerSpec_small_iff (howners j)).mp
            simpa [s3SmallLabelPredicate, Bool.or_eq_true, beq_iff_eq] using hsecondPred
          have hpositionNe : inner[first]! ≠ inner[second]! := by
            intro heq
            have hfirstList : first < inner.toList.length := by simpa using hfirstInner
            have hsecondList : second < inner.toList.length := by simpa using hsecondInner
            have hindexEq : first = second :=
              (fifteenStage3InnerPositions_nodup pattern).getElem!_inj
                hfirstList hsecondList |>.mp (by
                  calc
                    inner.toList[first]! = inner[first]! := by rw [Array.getElem!_toList]
                    _ = inner[second]! := heq
                    _ = inner.toList[second]! := by rw [Array.getElem!_toList])
            exact hdistinct hindexEq
          have hij : i ≠ j := by
            intro heq
            exact hpositionNe (congrArg Fin.val heq)
          have hsep := hsum i j hij
          linarith

/-- Rank pruning is sound on a target path once the full owner word satisfies
the two global high-bin population bounds. The checker counters count only
the assigned prefix; every remaining slot can contribute at most one, which
is exactly the optimistic completion bound used by the prune. -/
theorem fifteenStage3TargetPath_rankReason_excluded_of_population
    (profile : Fin 15 → Bool) (target : Array Nat) {s : S3State}
    (hpath : FifteenStage3TargetPath (fifteenStage0ProfileWord profile) target s)
    (hhighPopulation :
      (s3InnerPositions (fifteenStage0ProfileWord profile)).size - 4 ≤
        s3FilterRangeCount
          (s3InnerPositions (fifteenStage0ProfileWord profile)).size
          (fun k =>
            5 ≤ target[(s3InnerPositions
              (fifteenStage0ProfileWord profile))[k]!]! &&
              target[(s3InnerPositions
                (fifteenStage0ProfileWord profile))[k]!]! ≤ 6))
    (hhigh2Population :
      (s3InnerPositions (fifteenStage0ProfileWord profile)).size - 5 ≤
        s3FilterRangeCount
          (s3InnerPositions (fifteenStage0ProfileWord profile)).size
          (fun k => target[(s3InnerPositions
            (fifteenStage0ProfileWord profile))[k]!]! == 6))
    (hreason : s3RankReason
      (s3InnerPositions (fifteenStage0ProfileWord profile)) s = true) : False := by
  let pattern := fifteenStage0ProfileWord profile
  let inner := s3InnerPositions pattern
  have hreachable := fifteenStage3TargetPath_reachable pattern target hpath
  have hsem := fifteenStage3ReachableState_semantics pattern hreachable
  have hdepth : s.depth ≤ inner.size := by simpa [inner] using hsem.2.2
  rcases hsem.1 with ⟨_, hhighCounter, hhigh2Counter⟩
  have hhighPrefix :
      s3FilterRangeCount s.depth (fun k =>
        5 ≤ target[inner[k]!]! && target[inner[k]!]! ≤ 6) = s.high := by
    rw [hhighCounter]
    unfold fifteenStage3PrefixCount s3FilterRangeCount
    congr 1
    apply List.filter_congr
    intro k hk
    have hk' : k < s.depth := List.mem_range.mp hk
    rw [fifteenStage3TargetPath_prefix_agrees pattern target hpath k hk']
  have hhigh2Prefix :
      s3FilterRangeCount s.depth (fun k => target[inner[k]!]! == 6) = s.high2 := by
    rw [hhigh2Counter]
    unfold fifteenStage3PrefixCount s3FilterRangeCount
    congr 1
    apply List.filter_congr
    intro k hk
    have hk' : k < s.depth := List.mem_range.mp hk
    rw [fifteenStage3TargetPath_prefix_agrees pattern target hpath k hk']
  have hhighBound :
      inner.size - 4 ≤ s.high + (inner.size - s.depth) := by
    have hcount := s3FilterRangeCount_le_prefix_add_remaining
      (fun k => 5 ≤ target[inner[k]!]! && target[inner[k]!]! ≤ 6)
      inner.size s.depth hdepth
    simpa [inner, hhighPrefix] using hhighPopulation.trans hcount
  have hhigh2Bound :
      inner.size - 5 ≤ s.high2 + (inner.size - s.depth) := by
    have hcount := s3FilterRangeCount_le_prefix_add_remaining
      (fun k => target[inner[k]!]! == 6) inner.size s.depth hdepth
    simpa [inner, hhigh2Prefix] using hhigh2Population.trans hcount
  have hreason' :
      s.high + (inner.size - s.depth) < inner.size - 4 ∨
        s.high2 + (inner.size - s.depth) < max 0 (inner.size - 5) := by
    simpa [s3RankReason, inner, Bool.or_eq_true] using hreason
  rcases hreason' with hbad | hbad
  · omega
  · have hmax : max 0 (inner.size - 5) = inner.size - 5 := by omega
    rw [hmax] at hbad
    omega

/-- The positional count consumed by the checker is the same as the
geometric owner-label count, now expressed through the concrete label array. -/
theorem fifteenStage3ProfileOwnerArrayLabelCount
    (profile : Fin 15 → Bool) (labels : Fin 15 → Nat)
    (predicate : Nat → Bool) :
    s3FilterRangeCount
        (s3InnerPositions (fifteenStage0ProfileWord profile)).size
        (fun k => predicate
          ((fifteenStage3OwnerLabelArray labels)[
            ((s3InnerPositions (fifteenStage0ProfileWord profile))[k]!)]!)) =
      ((Finset.univ.filter fun i : Fin 15 => profile i = true).filter
        fun i => predicate (labels i) = true).card := by
  let positions := s3InnerPositions (fifteenStage0ProfileWord profile)
  have hfilters :
      ((List.range positions.size).filter fun k =>
        predicate ((fifteenStage3OwnerLabelArray labels)[positions[k]!]!)) =
      ((List.range positions.size).filter fun k =>
        predicate (labels (fifteenStage3ProfileOwnerPosition profile k))) := by
    apply List.filter_congr
    intro k hk
    have hklt : k < positions.size := List.mem_range.mp hk
    have hpBound := fifteenStage3InnerPosition_get_bound
      (fifteenStage0ProfileWord profile) hklt
    have howner : fifteenStage3ProfileOwnerPosition profile k =
        ⟨positions[k]!, hpBound⟩ := by
      apply Fin.ext
      simp [fifteenStage3ProfileOwnerPosition, positions,
        Nat.mod_eq_of_lt hpBound]
    have harray := fifteenStage3OwnerLabelArray_get labels positions[k]! hpBound
    rw [harray, howner]
  calc
    s3FilterRangeCount positions.size
        (fun k => predicate ((fifteenStage3OwnerLabelArray labels)[positions[k]!]!)) =
      ((List.range positions.size).filter fun k =>
        predicate ((fifteenStage3OwnerLabelArray labels)[positions[k]!]!)).length := rfl
    _ = ((List.range positions.size).filter fun k =>
        predicate (labels (fifteenStage3ProfileOwnerPosition profile k))).length := by
      rw [hfilters]
    _ = s3FilterRangeCount positions.size
        (fun k => predicate (labels (fifteenStage3ProfileOwnerPosition profile k))) := rfl
    _ = _ := fifteenStage3ProfileOwnerLabelCount profile labels predicate

/-- The global high-bin population hypotheses from actual geometry rule out
the Stage 3 rank-prune leaf on its owner-selected target path. -/
theorem fifteenStage3TargetPath_rankReason_excluded_of_geometry
    (radii : Fin 15 → ℝ) (labels : Fin 15 → Nat)
    (hgeometry : FifteenStage3GeometricConditions radii labels)
    (profile : Fin 15 → Bool)
    (hprofile : ∀ i, profile i = true ↔
      radii i < fifteenCandidateInnerThreshold)
    {s : S3State}
    (hpath : FifteenStage3TargetPath (fifteenStage0ProfileWord profile)
      (fifteenStage3OwnerLabelArray labels) s)
    (hreason : s3RankReason
      (s3InnerPositions (fifteenStage0ProfileWord profile)) s = true) : False := by
  let positions := s3InnerPositions (fifteenStage0ProfileWord profile)
  let profileSet := Finset.univ.filter fun i : Fin 15 => profile i = true
  let geometricSet := Finset.univ.filter fun i : Fin 15 =>
    radii i < fifteenCandidateInnerThreshold
  let profileHighSet := profileSet.filter fun i => 5 ≤ labels i ∧ labels i ≤ 6
  let geometricHighSet := geometricSet.filter fun i => 5 ≤ labels i ∧ labels i ≤ 6
  let profileHigh2Set := profileSet.filter fun i => labels i = 6
  let geometricHigh2Set := geometricSet.filter fun i => labels i = 6
  have hsets : profileSet = geometricSet := by
    ext i
    simp [profileSet, geometricSet, hprofile i]
  have hhighSets : profileHighSet = geometricHighSet := by
    simp [profileHighSet, geometricHighSet, hsets]
  have hhigh2Sets : profileHigh2Set = geometricHigh2Set := by
    simp [profileHigh2Set, geometricHigh2Set, hsets]
  have hsize : positions.size = profileSet.card := by
    have hcount := fifteenStage3ProfileOwnerLabelCount profile labels (fun _ => true)
    simpa [positions, profileSet, s3FilterRangeCount] using hcount
  have hhighCount :
      s3FilterRangeCount positions.size (fun k =>
        5 ≤ (fifteenStage3OwnerLabelArray labels)[positions[k]!]! &&
          (fifteenStage3OwnerLabelArray labels)[positions[k]!]! ≤ 6) =
        profileHighSet.card := by
    have hcount := fifteenStage3ProfileOwnerArrayLabelCount profile labels
      (fun l => 5 ≤ l && l ≤ 6)
    simpa [positions, profileHighSet, s3FilterRangeCount] using hcount
  have hhigh2Count :
      s3FilterRangeCount positions.size (fun k =>
        (fifteenStage3OwnerLabelArray labels)[positions[k]!]! == 6) =
        profileHigh2Set.card := by
    have hcount := fifteenStage3ProfileOwnerArrayLabelCount profile labels
      (fun l => l == 6)
    simpa [positions, profileHigh2Set, s3FilterRangeCount] using hcount
  have hhighPopulation : positions.size - 4 ≤
      s3FilterRangeCount positions.size (fun k =>
        5 ≤ (fifteenStage3OwnerLabelArray labels)[positions[k]!]! &&
          (fifteenStage3OwnerLabelArray labels)[positions[k]!]! ≤ 6) := by
    calc
      positions.size - 4 = profileSet.card - 4 := by rw [hsize]
      _ ≤ profileHighSet.card := by
        calc
          profileSet.card - 4 = geometricSet.card - 4 := by rw [hsets]
          _ ≤ geometricHighSet.card := hgeometry.highCount
          _ = profileHighSet.card := by rw [← hhighSets]
      _ = s3FilterRangeCount positions.size (fun k =>
          5 ≤ (fifteenStage3OwnerLabelArray labels)[positions[k]!]! &&
            (fifteenStage3OwnerLabelArray labels)[positions[k]!]! ≤ 6) := hhighCount.symm
  have hhigh2Population : positions.size - 5 ≤
      s3FilterRangeCount positions.size (fun k =>
        (fifteenStage3OwnerLabelArray labels)[positions[k]!]! == 6) := by
    calc
      positions.size - 5 = profileSet.card - 5 := by rw [hsize]
      _ ≤ profileHigh2Set.card := by
        calc
          profileSet.card - 5 = geometricSet.card - 5 := by rw [hsets]
          _ ≤ geometricHigh2Set.card := hgeometry.high2Count
          _ = profileHigh2Set.card := by rw [← hhigh2Sets]
      _ = s3FilterRangeCount positions.size (fun k =>
          (fifteenStage3OwnerLabelArray labels)[positions[k]!]! == 6) := hhigh2Count.symm
  exact fifteenStage3TargetPath_rankReason_excluded_of_population
    profile (fifteenStage3OwnerLabelArray labels) hpath hhighPopulation
    hhigh2Population hreason

/-- None of the four structural leaf reasons can occur on a target path
selected by a geometrically valid radial owner assignment. -/
theorem fifteenStage3TargetPath_structuralReasons_excluded_of_geometry
    (radii : Fin 15 → ℝ) (labels : Fin 15 → Nat)
    (hgeometry : FifteenStage3GeometricConditions radii labels)
    (profile : Fin 15 → Bool)
    (hprofile : ∀ i, profile i = true ↔
      radii i < fifteenCandidateInnerThreshold)
    {s : S3State}
    (hpath : FifteenStage3TargetPath (fifteenStage0ProfileWord profile)
      (fifteenStage3OwnerLabelArray labels) s)
    (hreason : s3SmallReason s = true ∨
      s3OriginReason (s3InnerPositions (fifteenStage0ProfileWord profile)) s = true ∨
      s3RankReason (s3InnerPositions (fifteenStage0ProfileWord profile)) s = true ∨
      s3MixedReason s = true) : False := by
  rcases hreason with hsmall | horigin | hrank | hmixed
  · have hsmall' : 1 < s.small := by simpa [s3SmallReason] using hsmall
    exact fifteenStage3TargetPath_smallReason_excluded radii labels
      hgeometry.owners hgeometry.pairSum profile hpath hsmall'
  · exact fifteenStage3TargetPath_originReason_excluded radii labels
      hgeometry.owners hgeometry.pairSum profile hpath horigin
  · exact fifteenStage3TargetPath_rankReason_excluded_of_geometry radii labels
      hgeometry profile hprofile hpath hrank
  · exact fifteenStage3TargetPath_mixedReason_excluded radii labels
      hgeometry.owners hgeometry.pairSum profile hpath hmixed

/-- Every candidate packing below the proposed radius has a Stage 3
owner-selected path on which none of the four structural leaf rules applies.
This isolates the remaining certificate and cycle-leaf soundness obligations. -/
theorem fifteen_unit_packing_wall_push_stage3_structural_path
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
        ¬ (s3SmallReason s = true ∨
          s3OriginReason (s3InnerPositions (fifteenStage0ProfileWord profile)) s = true ∨
          s3RankReason (s3InnerPositions (fifteenStage0ProfileWord profile)) s = true ∨
          s3MixedReason s = true) := by
  dsimp only
  obtain ⟨reflected, shift, hsurvivor,
    ⟨s, hpath, _hdepth, _hagrees, _hchoices⟩⟩ :=
      fifteen_unit_packing_wall_push_stage3_target_path P hunit hR
  refine ⟨reflected, shift, hsurvivor, ⟨s, hpath, ?_⟩⟩
  let radii := fifteenStage0TransformProfile
    (fifteenPackingSortedRadius (fifteen_unit_packing_wall_push P hunit hR))
    reflected shift
  let labels := fun i : Fin 15 => fifteenStage3RadialLabel (radii i)
  let profile := fun i : Fin 15 => decide
    (radii i < fifteenCandidateInnerThreshold)
  have hgeometry : FifteenStage3GeometricConditions radii labels :=
    fifteen_unit_packing_wall_push_stage3_geometric_conditions P hunit hR reflected shift
  have hprofile : ∀ i, profile i = true ↔
      radii i < fifteenCandidateInnerThreshold := by
    intro i
    simp [profile]
  intro hreason
  exact fifteenStage3TargetPath_structuralReasons_excluded_of_geometry
    radii labels hgeometry profile hprofile hpath hreason

end CirclePacking
