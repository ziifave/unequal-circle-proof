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

end CirclePacking
