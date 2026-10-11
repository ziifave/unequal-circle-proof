import CirclePacking.FifteenStage4CoverageCertificate
import CirclePacking.FifteenCertificate

/-! Data-level bridge from residual Stage 4 assignments to the exact
subdivision certificate's normal root records.  Each root is filtered through
the same pattern/bin validation used by the exact certificate replay. -/

namespace CirclePacking

open Lean

def s4CoverageNormalPatterns : List String :=
  ["000100100010101", "000100100100101", "001001001001001"]

def s4CoverageRootBoxes? : Option (List (String × Array Nat × FifteenBox)) := do
  let document ← (Json.parse fifteenCertificateSource).toOption
  let rootsJson ← fifteenJsonField? document "roots"
  let roots ← fifteenJsonArray? rootsJson
  roots.toList.mapM fun root => do
    guard (fifteenRootValid root)
    let pattern ← fifteenFieldString? root "pattern"
    let text ← fifteenFieldString? root "assignment"
    let assignment ← s4CoverageAssignment? text
    let box ← fifteenInitialBox? pattern text
    some (pattern, assignment, box)

def s4CoverageRootPairs? : Option (List (String × Array Nat)) := do
  let roots ← s4CoverageRootBoxes?
  some (roots.map (fun (pattern, assignment, _box) => (pattern, assignment)))

def s4CoverageRootBoxDataCorrect
    (row : String × Array Nat × FifteenBox) : Prop :=
  ∀ k, k < (s4InnerPositions row.1).size →
    row.2.2[(s4InnerPositions row.1)[k]!]! =
      fifteenBins[row.2.1[k]!]!

def s4CoverageRootBoxDataCheck
    (row : String × Array Nat × FifteenBox) : Bool :=
  (List.range (s4InnerPositions row.1).size).all (fun k =>
    decide (row.2.2[(s4InnerPositions row.1)[k]!]! =
      fifteenBins[row.2.1[k]!]!)) &&
  (List.range 15).all (fun p =>
    decide (p ∈ (s4InnerPositions row.1).toList ∨
      row.2.2[p]! = fifteenBins[11]!))

def s4CoverageAllRootBoxesGood : Bool :=
  match s4CoverageRootBoxes? with
  | none => false
  | some roots => roots.all s4CoverageRootBoxDataCheck

def s4CoverageResidualRootPairsValid : Bool :=
  match s4CoverageRootPairs? with
  | none => false
  | some roots => s4CoverageNormalPatterns.all (fun pattern =>
      match s4ResidualAssignments? pattern with
      | none => false
      | some assignments => assignments.all (fun assignment =>
          decide ((pattern, assignment) ∈ roots)))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem s4CoverageResidualRootPairs_replay :
    s4CoverageResidualRootPairsValid = true := by
  native_decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem s4CoverageAllRootBoxesGood_replay :
    s4CoverageAllRootBoxesGood = true := by
  native_decide

theorem s4CoverageResidualAssignment_has_root
    {pattern : String} {assignment : Array Nat}
    (hpattern : pattern ∈ s4CoverageNormalPatterns)
    (hassignment : ∃ assignments,
      s4ResidualAssignments? pattern = some assignments ∧
        assignment ∈ assignments) :
    ∃ roots, s4CoverageRootPairs? = some roots ∧
      (pattern, assignment) ∈ roots := by
  have hvalid := s4CoverageResidualRootPairs_replay
  unfold s4CoverageResidualRootPairsValid at hvalid
  cases hroots : s4CoverageRootPairs? with
  | none => simp [hroots] at hvalid
  | some roots =>
      simp only [hroots] at hvalid
      have hpatterns := List.all_eq_true.mp hvalid pattern hpattern
      obtain ⟨assignments, hparse, hmem⟩ := hassignment
      rw [hparse] at hpatterns
      have hmember := List.all_eq_true.mp hpatterns assignment hmem
      exact ⟨roots, rfl, of_decide_eq_true hmember⟩

theorem s4CoverageResidualAssignment_has_root_box
    {pattern : String} {assignment : Array Nat}
    (hpattern : pattern ∈ s4CoverageNormalPatterns)
    (hassignment : ∃ assignments,
      s4ResidualAssignments? pattern = some assignments ∧
        assignment ∈ assignments) :
    ∃ roots, s4CoverageRootBoxes? = some roots ∧
      ∃ box, (pattern, assignment, box) ∈ roots := by
  obtain ⟨pairs, hpairs, hmem⟩ :=
    s4CoverageResidualAssignment_has_root hpattern hassignment
  cases hroots : s4CoverageRootBoxes? with
  | none =>
      simp [s4CoverageRootPairs?, hroots] at hpairs
  | some roots =>
      have hpairs' : roots.map (fun (pattern, assignment, _box) =>
          (pattern, assignment)) = pairs := by
        simpa [s4CoverageRootPairs?, hroots] using hpairs
      have hmap :
          (pattern, assignment) ∈
            roots.map (fun (pattern, assignment, _box) =>
              (pattern, assignment)) := by
        rw [hpairs']
        exact hmem
      obtain ⟨⟨rootPattern, rootAssignment, box⟩, hroot, hpair⟩ :=
        List.mem_map.mp hmap
      have hrootPair : rootPattern = pattern ∧ rootAssignment = assignment := by
        simpa using hpair
      refine ⟨roots, rfl, box, ?_⟩
      rw [← hrootPair.1, ← hrootPair.2]
      exact hroot

theorem s4CoverageRootBoxDataCorrect_of_mem
    {roots : List (String × Array Nat × FifteenBox)}
    {row : String × Array Nat × FifteenBox}
    (hroots : s4CoverageRootBoxes? = some roots)
    (hrow : row ∈ roots) :
    ∀ k, k < (s4InnerPositions row.1).size →
      row.2.2[(s4InnerPositions row.1)[k]!]! =
        fifteenBins[row.2.1[k]!]! := by
  have hvalid := s4CoverageAllRootBoxesGood_replay
  have hrows : roots.all s4CoverageRootBoxDataCheck = true := by
    simpa [s4CoverageAllRootBoxesGood, hroots] using hvalid
  have hrowValid := List.all_eq_true.mp hrows row hrow
  have hinnerValid := (Bool.and_eq_true_iff.mp hrowValid).1
  change (List.range (s4InnerPositions row.1).size).all
    (fun k => decide (row.2.2[(s4InnerPositions row.1)[k]!]! =
      fifteenBins[row.2.1[k]!]!)) = true at hinnerValid
  intro k hk
  have hk' := List.all_eq_true.mp hinnerValid k (List.mem_range.mpr hk)
  exact of_decide_eq_true hk'

theorem s4CoverageRootOutsideBoxDataCorrect_of_mem
    {roots : List (String × Array Nat × FifteenBox)}
    {row : String × Array Nat × FifteenBox}
    (hroots : s4CoverageRootBoxes? = some roots)
    (hrow : row ∈ roots) :
    ∀ p, p < 15 → p ∉ (s4InnerPositions row.1).toList →
      row.2.2[p]! = fifteenBins[11]! := by
  have hvalid := s4CoverageAllRootBoxesGood_replay
  have hrows : roots.all s4CoverageRootBoxDataCheck = true := by
    simpa [s4CoverageAllRootBoxesGood, hroots] using hvalid
  have hrowValid := List.all_eq_true.mp hrows row hrow
  have houtsideValid := (Bool.and_eq_true_iff.mp hrowValid).2
  intro p hp hnotInner
  have hbool := List.all_eq_true.mp houtsideValid p (List.mem_range.mpr hp)
  have hdisj : p ∈ (s4InnerPositions row.1).toList ∨
      row.2.2[p]! = fifteenBins[11]! := of_decide_eq_true hbool
  exact hdisj.resolve_left hnotInner

end CirclePacking
