import CirclePacking.FifteenStage3CycleHandoff
import CirclePacking.FifteenStage3PathStructural

/-! A successful finite Stage 3 stream cannot survive along a geometrically
valid owner-selected branch: structural leaves contradict geometry, split
nodes contain the selected child, and cycle leaves contradict angular
feasibility. -/

namespace CirclePacking

/-- No successful certificate stream can cover a target path when every
structural leaf is geometrically impossible and every valid cycle leaf
contradicts the target geometry. The recursion follows the one child selected
by the target owner labels; the other children remain checked by the stream
replay. -/
theorem s3CheckStream_targetPath_no_success
    (pattern : String) (target : Array Nat)
    (cycles : Array (List S3CertEdge))
    (hallowed : ∀ {s : S3State},
      FifteenStage3TargetPath pattern target s →
      s.depth < (s3InnerPositions pattern).size →
      target[(s3InnerPositions pattern)[s.depth]!]! ∈ s3BranchLabels)
    (hstruct : ∀ {s : S3State},
      FifteenStage3TargetPath pattern target s →
      s3StructurallyPruned (s3InnerPositions pattern) s = false)
    (hcycle : ∀ {s : S3State},
      FifteenStage3TargetPath pattern target s →
      ∀ edges, s3CycleValid s.labels edges = true → False) :
    ∀ fuel {s : S3State}, FifteenStage3TargetPath pattern target s →
      s.depth + fuel = (s3InnerPositions pattern).size →
      ∀ input output,
        s3CheckStream fuel (s3InnerPositions pattern) cycles s input = some output →
        False := by
  intro fuel
  induction fuel using Nat.strong_induction_on with
  | h fuel ih =>
      intro s hpath hremaining input output hsuccess
      have hparts :
          s3SmallReason s = false ∧
          s3OriginReason (s3InnerPositions pattern) s = false ∧
          s3RankReason (s3InnerPositions pattern) s = false ∧
          s3MixedReason s = false := by
        simpa [s3StructurallyPruned, and_assoc] using hstruct hpath
      cases input with
      | nil =>
          simp [s3CheckStream] at hsuccess
      | cons token rest =>
          by_cases hB : token = 'B'
          · subst token
            cases fuel with
            | zero =>
                simp [s3CheckStream] at hsuccess
            | succ n =>
                have hdepth : s.depth < (s3InnerPositions pattern).size := by
                  omega
                let label := target[(s3InnerPositions pattern)[s.depth]!]!
                have hlabel : label ∈ s3BranchLabels := by
                  simpa [label] using hallowed hpath hdepth
                have hchildPath : FifteenStage3TargetPath pattern target
                    (s3Next (s3InnerPositions pattern) s label) := by
                  simpa [label] using
                    (FifteenStage3TargetPath.step hpath hdepth)
                obtain ⟨before, after, hchild⟩ :=
                  s3CheckStream_split_has_successful_child n
                    (s3InnerPositions pattern) cycles s rest output label
                    (by simpa using hsuccess) hdepth (hstruct hpath) hlabel
                have hchildRemaining :
                    (s3Next (s3InnerPositions pattern) s label).depth + n =
                      (s3InnerPositions pattern).size := by
                  simp only [s3Next]
                  omega
                exact ih n (by omega) hchildPath hchildRemaining before after hchild
          · by_cases hS : token = 'S'
            · subst token
              have hleaf :
                  (if s3SmallReason s then some rest else none) = some output := by
                simpa [s3CheckStream] using hsuccess
              have hreason : s3SmallReason s = true := by
                by_cases hr : s3SmallReason s = true
                · exact hr
                · simp [hr] at hleaf
              have hbad : false = true := hparts.1.symm.trans hreason
              cases hbad
            · by_cases hO : token = 'O'
              · subst token
                have hleaf :
                    (if s3OriginReason (s3InnerPositions pattern) s
                      then some rest else none) = some output := by
                  simpa [s3CheckStream] using hsuccess
                have hreason :
                    s3OriginReason (s3InnerPositions pattern) s = true := by
                  by_cases hr : s3OriginReason (s3InnerPositions pattern) s = true
                  · exact hr
                  · simp [hr] at hleaf
                have hbad : false = true := hparts.2.1.symm.trans hreason
                cases hbad
              · by_cases hR : token = 'R'
                · subst token
                  have hleaf :
                      (if s3RankReason (s3InnerPositions pattern) s
                        then some rest else none) = some output := by
                    simpa [s3CheckStream] using hsuccess
                  have hreason :
                      s3RankReason (s3InnerPositions pattern) s = true := by
                    by_cases hr : s3RankReason (s3InnerPositions pattern) s = true
                    · exact hr
                    · simp [hr] at hleaf
                  have hbad : false = true := hparts.2.2.1.symm.trans hreason
                  cases hbad
                · by_cases hM : token = 'M'
                  · subst token
                    have hleaf :
                        (if s3MixedReason s then some rest else none) = some output := by
                      simpa [s3CheckStream] using hsuccess
                    have hreason : s3MixedReason s = true := by
                      by_cases hr : s3MixedReason s = true
                      · exact hr
                      · simp [hr] at hleaf
                    have hbad : false = true := hparts.2.2.2.symm.trans hreason
                    cases hbad
                  · by_cases hC : token = 'C'
                    · subst token
                      cases rest with
                      | nil => simp [s3CheckStream] at hsuccess
                      | cons refHi rest =>
                          cases rest with
                          | nil => simp [s3CheckStream] at hsuccess
                          | cons refLo rest =>
                              obtain ⟨_id, _tail, edges, _hparse, _hedges,
                                _hdepth, _hnotPruned, hvalid⟩ :=
                                  s3CheckStream_cycle_success_specs fuel
                                    (s3InnerPositions pattern) cycles s refHi refLo
                                    rest output hsuccess
                              exact hcycle hpath edges hvalid
                    · simp [s3CheckStream, hB, hS, hO, hR, hM, hC] at hsuccess

/-- The abstract stream contradiction applies directly to a real owner
profile, once the ordered angles and wall labels are supplied. -/
theorem fifteenStage3GeometricTargetPath_stream_no_success
    (radii : Fin 15 → ℝ) (labels : Fin 15 → Nat)
    (profile : Fin 15 → Bool) (theta : Fin 15 → ℝ)
    (hgeometry : FifteenStage3GeometricConditions radii labels)
    (hprofile : ∀ i, profile i = true ↔
      radii i < fifteenCandidateInnerThreshold)
    (houterLabel : ∀ i, profile i = false → labels i = 7)
    (hsorted : ∀ i j : Fin 15, i.1 < j.1 → theta i ≤ theta j)
    (hthetaRange : ∀ i, 0 ≤ theta i ∧ theta i ≤ 2 * Real.pi)
    (hsep : ∀ i j : Fin 15, i ≠ j →
      4 ≤ pointNorm
        ((polarPoint (radii i) (theta i)).1 - (polarPoint (radii j) (theta j)).1,
         (polarPoint (radii i) (theta i)).2 - (polarPoint (radii j) (theta j)).2) ^ 2)
    (cycles : Array (List S3CertEdge)) (stream : List Char)
    (hstream : s3CheckStream
      (s3InnerPositions (fifteenStage0ProfileWord profile)).size
      (s3InnerPositions (fifteenStage0ProfileWord profile)) cycles
      (s3Initial (fifteenStage0ProfileWord profile)) stream = some []) :
    False := by
  let pattern := fifteenStage0ProfileWord profile
  let target := fifteenStage3OwnerLabelArray labels
  have hallowed : ∀ {s : S3State},
      FifteenStage3TargetPath pattern target s →
      s.depth < (s3InnerPositions pattern).size →
      target[(s3InnerPositions pattern)[s.depth]!]! ∈ s3BranchLabels := by
    intro s _hpath hdepth
    have hchoice := fifteenStage3GeometricProfile_nextLabel_allowed
      radii labels hgeometry.owners profile
      (fun i hi => (hprofile i).mp hi) s.depth hdepth
    simpa [pattern, target, s3BranchLabels, fifteenStage3OwnerLabelArray] using hchoice
  have hstruct : ∀ {s : S3State},
      FifteenStage3TargetPath pattern target s →
      s3StructurallyPruned (s3InnerPositions pattern) s = false := by
    intro s hpath
    apply Bool.eq_false_of_not_eq_true
    intro hpruned
    have hreason :
        s3SmallReason s = true ∨
        s3OriginReason (s3InnerPositions pattern) s = true ∨
        s3RankReason (s3InnerPositions pattern) s = true ∨
        s3MixedReason s = true := by
      simpa [s3StructurallyPruned, or_assoc] using hpruned
    exact fifteenStage3TargetPath_structuralReasons_excluded_of_geometry
      radii labels hgeometry profile hprofile hpath hreason
  have hcycle : ∀ {s : S3State},
      FifteenStage3TargetPath pattern target s →
      ∀ edges, s3CycleValid s.labels edges = true → False := by
    intro s hpath edges hvalid
    exact fifteenStage3TargetPath_cycleLeaf_excluded radii labels
      hgeometry.owners hgeometry.pairSum theta hsorted
      (fun i => (hthetaRange i).1) (fun i => (hthetaRange i).2)
      hsep profile houterLabel hpath edges hvalid
  have hroot : FifteenStage3TargetPath pattern target (s3Initial pattern) := .initial
  have hrootDepth : (s3Initial pattern).depth +
      (s3InnerPositions pattern).size = (s3InnerPositions pattern).size := by
    simp [s3Initial]
  exact s3CheckStream_targetPath_no_success pattern target cycles hallowed hstruct hcycle
    (s3InnerPositions pattern).size hroot hrootDepth stream [] (by
      simpa [pattern] using hstream)

end CirclePacking
