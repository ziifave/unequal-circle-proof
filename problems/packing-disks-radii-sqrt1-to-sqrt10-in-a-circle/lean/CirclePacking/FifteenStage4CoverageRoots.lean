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

end CirclePacking
