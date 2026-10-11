import CirclePacking.FifteenStage4CoverageCertificate
import CirclePacking.FifteenStage4PathGeometry

/-! A checked coverage tree follows every geometrically possible owner word.
Since structural and negative-cycle leaves are geometrically impossible, the
selected path must terminate at an accepted full assignment. -/

namespace CirclePacking

def s4CoverageTargetAssignment (inner target : Array Nat) : Array Nat :=
  inner.map (fun p => s4CoverageDigit target[p]!)

theorem s4CoverageAssignment_eq_target_of_path_full
    (pattern : String) (inner target : Array Nat) {s : S4State}
    (hpath : FifteenStage4TargetPath pattern target s)
    (hinner : inner = s4InnerPositions pattern)
    (hfull : s.depth = inner.size) :
    s4CoverageAssignment inner s = s4CoverageTargetAssignment inner target := by
  subst inner
  unfold s4CoverageAssignment s4CoverageTargetAssignment
  apply Array.ext
  · simp
  · intro k hk₁ hk₂
    have hk : k < (s4InnerPositions pattern).size := by simpa using hk₁
    have hslot := fifteenStage4TargetPath_slot_semantics pattern target hpath k hk
    have hassigned : k < s.depth := by omega
    have hslot' : s.labels[(s4InnerPositions pattern)[k]!]! =
        target[(s4InnerPositions pattern)[k]!]! := by
      simpa [hassigned] using hslot
    have hslot'' := hslot'
    rw [getElem!_pos (s4InnerPositions pattern) k hk] at hslot''
    simp only [Array.getElem_map]
    rw [hslot'']

theorem s4CoverageStream_cycle_success_specs
    (fuel : Nat) (inner : Array Nat) (cycles : Array (List S4CertEdge))
    (allowed : List (Array Nat)) (s : S4State) (refHi refLo : Char)
    (rest output : List Char)
    (hsuccess : s4CoverageStream fuel inner cycles allowed s
      ('C' :: refHi :: refLo :: rest) = some output) :
    ∃ edges, s4CycleValid s.labels edges = true := by
  have hordinary : s4CheckStream fuel inner cycles s
      ('C' :: refHi :: refLo :: rest) = some output := by
    simpa [s4CheckStream, s4CoverageStream] using hsuccess
  obtain ⟨_id, _tail, edges, _hparse, _hedges, _hdepth, _hnotPruned, hvalid⟩ :=
    s4CheckStream_cycle_success_specs fuel inner cycles s refHi refLo rest output
      hordinary
  exact ⟨edges, hvalid⟩

theorem s4CoverageStream_targetPath_assignment_mem
    (pattern : String) (target : Array Nat)
    (cycles : Array (List S4CertEdge)) (allowed : List (Array Nat))
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
        s4CoverageStream fuel (s4InnerPositions pattern) cycles allowed s input =
          some output →
        s4CoverageTargetAssignment (s4InnerPositions pattern) target ∈ allowed := by
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
      | nil => simp [s4CoverageStream] at hsuccess
      | cons token rest =>
          by_cases hB : token = 'B'
          · subst token
            cases fuel with
            | zero => simp [s4CoverageStream] at hsuccess
            | succ n =>
                have hdepth : s.depth < (s4InnerPositions pattern).size := by omega
                let label := target[(s4InnerPositions pattern)[s.depth]!]!
                have hlabel : label ∈ s4BranchLabels := by
                  simpa [label] using hallowed hpath hdepth
                have hchildPath : FifteenStage4TargetPath pattern target
                    (s4Next (s4InnerPositions pattern) s label) := by
                  simpa [label] using (FifteenStage4TargetPath.step hpath hdepth)
                obtain ⟨before, after, hchild⟩ :=
                  s4CoverageStream_split_has_successful_child n
                    (s4InnerPositions pattern) cycles allowed s rest output label
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
                simpa [s4CoverageStream] using hsuccess
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
                  simpa [s4CoverageStream] using hsuccess
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
                    simpa [s4CoverageStream] using hsuccess
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
                      simpa [s4CoverageStream] using hsuccess
                    have hreason : s4MixedReason s = true := by
                      by_cases hr : s4MixedReason s = true
                      · exact hr
                      · simp [hr] at hleaf
                    have hbad : false = true := hparts.2.2.2.symm.trans hreason
                    cases hbad
                  · by_cases hC : token = 'C'
                    · subst token
                      cases rest with
                      | nil => simp [s4CoverageStream] at hsuccess
                      | cons refHi rest =>
                          cases rest with
                          | nil => simp [s4CoverageStream] at hsuccess
                          | cons refLo rest =>
                              obtain ⟨edges, hvalid⟩ :=
                                s4CoverageStream_cycle_success_specs fuel
                                  (s4InnerPositions pattern) cycles allowed s
                                  refHi refLo rest output hsuccess
                              exact False.elim (hcycle hpath edges hvalid)
                    · by_cases hA : token = 'A'
                      · subst token
                        have haccepted :
                            (s.depth == (s4InnerPositions pattern).size &&
                              !s4StructurallyPruned (s4InnerPositions pattern) s &&
                              decide (s4CoverageAssignment
                                (s4InnerPositions pattern) s ∈ allowed)) = true := by
                          by_cases hc :
                              (s.depth == (s4InnerPositions pattern).size &&
                                !s4StructurallyPruned (s4InnerPositions pattern) s &&
                                decide (s4CoverageAssignment
                                  (s4InnerPositions pattern) s ∈ allowed)) = true
                          · exact hc
                          · simp [s4CoverageStream, hc] at hsuccess
                        have hparts' := Bool.and_eq_true_iff.mp haccepted
                        have hdepth : s.depth = (s4InnerPositions pattern).size :=
                          of_decide_eq_true (Bool.and_eq_true_iff.mp hparts'.1).1
                        have hmem : s4CoverageAssignment
                            (s4InnerPositions pattern) s ∈ allowed :=
                          of_decide_eq_true hparts'.2
                        have hassign := s4CoverageAssignment_eq_target_of_path_full
                          pattern (s4InnerPositions pattern) target hpath rfl hdepth
                        rw [← hassign]
                        exact hmem
                      · simp [s4CoverageStream, hB, hS, hO, hR, hM, hC, hA]
                          at hsuccess

private theorem s4RadialOwner_mem_branchLabels (r : ℝ) :
    fifteenStage4RadialOwner r ∈ s4BranchLabels := by
  unfold fifteenStage4RadialOwner
  split_ifs <;> simp [s4BranchLabels]

/-- The accepted leaf selected by a real packing carries exactly the radial
owner word in angular order.  The cycle and structural leaves are excluded
using the same Stage 4 geometric lemmas used for the closed-pattern proof. -/
theorem fifteenStage4CoverageGeometricTargetAssignment_mem
    (radii : Fin 15 → ℝ) (labels : Fin 15 → Nat)
    (hlabels : ∀ i, labels i = fifteenStage3RadialLabel (radii i))
    (hgeometry : FifteenStage3GeometricConditions radii labels)
    (profile : Fin 15 → Bool)
    (hprofile : ∀ i, profile i = true ↔
      radii i < fifteenCandidateInnerThreshold)
    (hnonneg : ∀ i, 0 ≤ radii i)
    (hclassification : ∀ i, radii i = fifteenCandidateOuterRadius ∨
      radii i < fifteenCandidateInnerThreshold)
    (theta : Fin 15 → ℝ)
    (hsorted : ∀ i j : Fin 15, i.1 < j.1 → theta i ≤ theta j)
    (hthetaLo : ∀ i, 0 ≤ theta i)
    (hthetaHi : ∀ i, theta i ≤ 2 * Real.pi)
    (hsep : ∀ i j : Fin 15, i ≠ j →
      4 ≤ pointNorm
        ((polarPoint (radii i) (theta i)).1 - (polarPoint (radii j) (theta j)).1,
         (polarPoint (radii i) (theta i)).2 - (polarPoint (radii j) (theta j)).2) ^ 2)
    (allowed : List (Array Nat)) (cycles : Array (List S4CertEdge))
    (stream : List Char)
    (hstream : s4CoverageStream
      (s4InnerPositions (fifteenStage0ProfileWord profile)).size
      (s4InnerPositions (fifteenStage0ProfileWord profile)) cycles allowed
      (s4Initial (fifteenStage0ProfileWord profile)) stream = some []) :
    s4CoverageTargetAssignment
      (s4InnerPositions (fifteenStage0ProfileWord profile))
      (fifteenStage4OwnerLabelArray (fun i =>
        fifteenStage4RadialLabel (radii i))) ∈ allowed := by
  let pattern := fifteenStage0ProfileWord profile
  let labels4 : Fin 15 → Nat := fun i => fifteenStage4RadialLabel (radii i)
  let target := fifteenStage4OwnerLabelArray labels4
  have howners4 : ∀ i, fifteenStage4OwnerSpec (labels4 i) (radii i) := by
    intro i
    exact fifteenStage4RadialLabel_spec_of_classification (radii i)
      (hnonneg i) (hclassification i)
  have houter4 : ∀ i, profile i = false → labels4 i = 11 := by
    intro i hfalse
    have hnot : ¬ radii i < fifteenCandidateInnerThreshold := by
      intro hlt
      have htrue := (hprofile i).2 hlt
      rw [hfalse] at htrue
      cases htrue
    simp [labels4, fifteenStage4RadialLabel, hnot]
  have hprojectedTarget : target.map s4ToS3Label =
      fifteenStage3OwnerLabelArray labels := by
    apply Array.ext
    · simp [target, labels4, fifteenStage4OwnerLabelArray,
        fifteenStage3OwnerLabelArray]
    · intro p hp₁ hp₂
      have hp : p < 15 := by
        simpa [target, labels4, fifteenStage4OwnerLabelArray] using hp₁
      simp [target, labels4, fifteenStage4OwnerLabelArray,
        fifteenStage3OwnerLabelArray, hlabels,
        s4ToS3RadialLabel_eq_stage3]
  have hallowed : ∀ {s : S4State},
      FifteenStage4TargetPath pattern target s →
      s.depth < (s4InnerPositions pattern).size →
      target[(s4InnerPositions pattern)[s.depth]!]! ∈ s4BranchLabels := by
    intro s _hpath hdepth
    let inner := s4InnerPositions pattern
    let p := inner[s.depth]!
    have hmemOrdinary : inner[s.depth] ∈ inner.toList :=
      Array.getElem_mem_toList hdepth
    have hmem : p ∈ inner.toList := by
      dsimp [p]
      rw [getElem!_pos inner s.depth hdepth]
      exact hmemOrdinary
    have hp : p < 15 := by
      dsimp [p]
      have hdepth' : s.depth < (s3InnerPositions pattern).size := by
        simpa [inner, s4InnerPositions_eq_s3] using hdepth
      exact fifteenStage3InnerPosition_get_bound pattern hdepth'
    have hprofileTrue : profile ⟨p, hp⟩ = true := by
      apply (fifteenStage3ProfileWord_inner_iff profile ⟨p, hp⟩).mp
      simpa [pattern, inner, p, s4InnerPositions_eq_s3] using hmem
    have hradiusInner : radii ⟨p, hp⟩ < fifteenCandidateInnerThreshold :=
      (hprofile ⟨p, hp⟩).mp hprofileTrue
    have htargetLabel : target[p]! = labels4 ⟨p, hp⟩ := by
      change (fifteenStage4OwnerLabelArray labels4)[p]! = labels4 ⟨p, hp⟩
      exact fifteenStage4OwnerLabelArray_get labels4 p hp
    change target[p]! ∈ s4BranchLabels
    rw [htargetLabel]
    have hradialLabel : labels4 ⟨p, hp⟩ =
        fifteenStage4RadialOwner (radii ⟨p, hp⟩) := by
      simp [labels4, fifteenStage4RadialLabel, hradiusInner]
    rw [hradialLabel]
    exact s4RadialOwner_mem_branchLabels _
  have hstruct : ∀ {s : S4State},
      FifteenStage4TargetPath pattern target s →
      s4StructurallyPruned (s4InnerPositions pattern) s = false := by
    intro s hpath
    apply Bool.eq_false_of_not_eq_true
    intro hpruned
    exact fifteenStage4TargetPath_structuralPrune_excluded_of_geometry
      radii labels hgeometry profile hprofile target hpath
      (by simpa [pattern] using hprojectedTarget) hpruned
  have hcycle : ∀ {s : S4State},
      FifteenStage4TargetPath pattern target s →
      ∀ edges, s4CycleValid s.labels edges = true → False := by
    intro s hpath edges hvalid
    exact fifteenStage4TargetPath_cycleLeaf_excluded radii labels4 howners4
      hgeometry.pairSum theta hsorted hthetaLo hthetaHi hsep profile houter4
      hpath edges hvalid
  have hroot : FifteenStage4TargetPath pattern target (s4Initial pattern) := .initial
  have hremaining : (s4Initial pattern).depth +
      (s4InnerPositions pattern).size = (s4InnerPositions pattern).size := by
    simp [s4Initial]
  exact s4CoverageStream_targetPath_assignment_mem pattern target cycles allowed
    hallowed hstruct hcycle (s4InnerPositions pattern).size hroot hremaining
    stream [] (by simpa [pattern] using hstream)

end CirclePacking
