import CirclePacking.FifteenStage4Certificate
import CirclePacking.FifteenStage4CycleGeometry

/-! A successful finite Stage 3 stream cannot survive along a geometrically
valid owner-selected branch: structural leaves contradict geometry, split
nodes contain the selected child, and cycle leaves contradict angular
feasibility. -/

namespace CirclePacking

/-- The checker path selected by a proposed Stage 4 owner label at each
inner slot. -/
inductive FifteenStage4TargetPath (pattern : String) (target : Array Nat) :
    S4State → Prop where
  | initial : FifteenStage4TargetPath pattern target (s4Initial pattern)
  | step {s : S4State} :
      FifteenStage4TargetPath pattern target s →
      s.depth < (s4InnerPositions pattern).size →
      FifteenStage4TargetPath pattern target
        (s4Next (s4InnerPositions pattern) s
          target[(s4InnerPositions pattern)[s.depth]!]!)

/-- No successful certificate stream can cover a target path when every
structural leaf is geometrically impossible and every valid cycle leaf
contradicts the target geometry. The recursion follows the one child selected
by the target owner labels; the other children remain checked by the stream
replay. -/
theorem s4CheckStream_targetPath_no_success
    (pattern : String) (target : Array Nat)
    (cycles : Array (List S4CertEdge))
    (hallowed : ∀ {s : S4State},
      FifteenStage4TargetPath pattern target s →
      s.depth < (s4InnerPositions pattern).size →
      target[(s4InnerPositions pattern)[s.depth]!]! ∈ s4BranchLabels)
    (hstruct : ∀ {s : S4State},
      FifteenStage4TargetPath pattern target s →
      s4StructurallyPruned (s4InnerPositions pattern) s = false)
    (hcycle : ∀ {s : S4State},
      FifteenStage4TargetPath pattern target s →
      ∀ edges, s4CycleValid s.labels edges = true → False) :
    ∀ fuel {s : S4State}, FifteenStage4TargetPath pattern target s →
      s.depth + fuel = (s4InnerPositions pattern).size →
      ∀ input output,
        s4CheckStream fuel (s4InnerPositions pattern) cycles s input = some output →
        False := by
  intro fuel
  induction fuel using Nat.strong_induction_on with
  | h fuel ih =>
      intro s hpath hremaining input output hsuccess
      have hparts :
          s4SmallReason s = false ∧
          s4OriginReason (s4InnerPositions pattern) s = false ∧
          s4RankReason (s4InnerPositions pattern) s = false ∧
          s4MixedReason s = false := by
        simpa [s4StructurallyPruned, and_assoc] using hstruct hpath
      cases input with
      | nil =>
          simp [s4CheckStream] at hsuccess
      | cons token rest =>
          by_cases hB : token = 'B'
          · subst token
            cases fuel with
            | zero =>
                simp [s4CheckStream] at hsuccess
            | succ n =>
                have hdepth : s.depth < (s4InnerPositions pattern).size := by
                  omega
                let label := target[(s4InnerPositions pattern)[s.depth]!]!
                have hlabel : label ∈ s4BranchLabels := by
                  simpa [label] using hallowed hpath hdepth
                have hchildPath : FifteenStage4TargetPath pattern target
                    (s4Next (s4InnerPositions pattern) s label) := by
                  simpa [label] using
                    (FifteenStage4TargetPath.step hpath hdepth)
                obtain ⟨before, after, hchild⟩ :=
                  s4CheckStream_split_has_successful_child n
                    (s4InnerPositions pattern) cycles s rest output label
                    (by simpa using hsuccess) hdepth (hstruct hpath) hlabel
                have hchildRemaining :
                    (s4Next (s4InnerPositions pattern) s label).depth + n =
                      (s4InnerPositions pattern).size := by
                  simp [s4Next]
                  omega
                exact ih n (by omega) hchildPath hchildRemaining before after hchild
          · by_cases hS : token = 'S'
            · subst token
              have hleaf :
                  (if s4SmallReason s then some rest else none) = some output := by
                simpa [s4CheckStream] using hsuccess
              have hreason : s4SmallReason s = true := by
                by_cases hr : s4SmallReason s = true
                · exact hr
                · simp [hr] at hleaf
              have hbad : false = true := hparts.1.symm.trans hreason
              cases hbad
            · by_cases hO : token = 'O'
              · subst token
                have hleaf :
                    (if s4OriginReason (s4InnerPositions pattern) s
                      then some rest else none) = some output := by
                  simpa [s4CheckStream] using hsuccess
                have hreason :
                    s4OriginReason (s4InnerPositions pattern) s = true := by
                  by_cases hr : s4OriginReason (s4InnerPositions pattern) s = true
                  · exact hr
                  · simp [hr] at hleaf
                have hbad : false = true := hparts.2.1.symm.trans hreason
                cases hbad
              · by_cases hR : token = 'R'
                · subst token
                  have hleaf :
                      (if s4RankReason (s4InnerPositions pattern) s
                        then some rest else none) = some output := by
                    simpa [s4CheckStream] using hsuccess
                  have hreason :
                      s4RankReason (s4InnerPositions pattern) s = true := by
                    by_cases hr : s4RankReason (s4InnerPositions pattern) s = true
                    · exact hr
                    · simp [hr] at hleaf
                  have hbad : false = true := hparts.2.2.1.symm.trans hreason
                  cases hbad
                · by_cases hM : token = 'M'
                  · subst token
                    have hleaf :
                        (if s4MixedReason s then some rest else none) = some output := by
                      simpa [s4CheckStream] using hsuccess
                    have hreason : s4MixedReason s = true := by
                      by_cases hr : s4MixedReason s = true
                      · exact hr
                      · simp [hr] at hleaf
                    have hbad : false = true := hparts.2.2.2.symm.trans hreason
                    cases hbad
                  · by_cases hC : token = 'C'
                    · subst token
                      cases rest with
                      | nil => simp [s4CheckStream] at hsuccess
                      | cons refHi rest =>
                          cases rest with
                          | nil => simp [s4CheckStream] at hsuccess
                          | cons refLo rest =>
                              obtain ⟨_id, _tail, edges, _hparse, _hedges,
                                _hdepth, _hnotPruned, hvalid⟩ :=
                                  s4CheckStream_cycle_success_specs fuel
                                    (s4InnerPositions pattern) cycles s refHi refLo
                                    rest output hsuccess
                              exact hcycle hpath edges hvalid
                    · simp [s4CheckStream, hB, hS, hO, hR, hM, hC] at hsuccess

end CirclePacking
