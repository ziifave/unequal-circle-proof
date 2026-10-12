import CirclePacking.FifteenStage4CoverageHandoff

/-! Replay the nine origin-special terminals independently from the main
root work list, while reusing its exact leaf validator. -/

namespace CirclePacking

open Lean

def s4CoverageSpecialCases? : Option (Array Json) := do
  let document ← (Json.parse fifteenCertificateSource).toOption
  let casesJson ← fifteenJsonField? document "special_cases"
  fifteenJsonArray? casesJson

def s4CoverageSpecialLookup? (cases : Array Json)
    (assignment mode : String) : Option (FifteenBox × Json) := do
  let item ← cases.toList.find? (fun item =>
    fifteenFieldString? item "pattern" == some fifteenSpecialPattern &&
    fifteenFieldString? item "assignment" == some assignment &&
    fifteenFieldString? item "mode" == some mode &&
    fifteenFieldNat? item "vertex" == some 13)
  let box ← fifteenSpecialBox? assignment mode 13
  let leaf ← fifteenJsonField? item "leaf"
  some (box, leaf)

def s4CoverageSpecialLeafValid (cases : Array Json)
    (assignment mode : String) : Bool :=
  match s4CoverageSpecialLookup? cases assignment mode with
  | none => false
  | some (box, leaf) =>
      let expectedTag := if mode == "POSITIVE_HIGH" then "CYCLE" else "SUM"
      let positiveZero := if mode == "POSITIVE_LOW" then [13] else []
      let exactZero := if mode == "EXACT_ZERO" then [13] else []
      decide (fifteenJsonAt? leaf 0 >>= fifteenJsonString? = some expectedTag) &&
      fifteenTerminalValid box (fifteenInnerPositions fifteenSpecialPattern)
        leaf false positiveZero exactZero

def s4CoverageSpecialLeafReplayCases (cases : Array Json) : Bool :=
  let assignments := ["636808", "646808", "656808"]
  let modes := ["POSITIVE_LOW", "POSITIVE_HIGH", "EXACT_ZERO"]
  assignments.all (fun assignment =>
    modes.all (s4CoverageSpecialLeafValid cases assignment))

def s4CoverageSpecialLeafReplay : Bool :=
  match s4CoverageSpecialCases? with
  | none => false
  | some cases => s4CoverageSpecialLeafReplayCases cases

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem s4CoverageSpecialLeafReplay_replays :
    s4CoverageSpecialLeafReplay = true := by
  native_decide

theorem s4CoverageSpecialResidualAssignments_exact :
    s4ResidualAssignments? fifteenSpecialPattern =
      some [#[6, 3, 6, 8, 0, 8], #[6, 4, 6, 8, 0, 8],
        #[6, 5, 6, 8, 0, 8]] := by
  native_decide

theorem s4CoverageSpecialLeafData
    {assignment mode : String}
    (hassignment : assignment ∈ ["636808", "646808", "656808"])
    (hmode : mode ∈ ["POSITIVE_LOW", "POSITIVE_HIGH", "EXACT_ZERO"]) :
    ∃ cases box leaf,
      s4CoverageSpecialCases? = some cases ∧
      s4CoverageSpecialLookup? cases assignment mode = some (box, leaf) ∧
      fifteenJsonAt? leaf 0 >>= fifteenJsonString? =
        some (if mode == "POSITIVE_HIGH" then "CYCLE" else "SUM") ∧
      fifteenTerminalValid box (fifteenInnerPositions fifteenSpecialPattern)
        leaf false (if mode == "POSITIVE_LOW" then [13] else [])
          (if mode == "EXACT_ZERO" then [13] else []) = true := by
  have hReplay := s4CoverageSpecialLeafReplay_replays
  cases hcases : s4CoverageSpecialCases? with
  | none =>
      rw [s4CoverageSpecialLeafReplay, hcases] at hReplay
      contradiction
  | some cases =>
      have hcasesReplay : s4CoverageSpecialLeafReplayCases cases = true := by
        simpa only [s4CoverageSpecialLeafReplay, hcases] using hReplay
      change ([ ("636808" : String), "646808", "656808" ].all
        (fun assignment =>
          ["POSITIVE_LOW", "POSITIVE_HIGH", "EXACT_ZERO"].all
            (s4CoverageSpecialLeafValid cases assignment))) = true at hcasesReplay
      have hassignments := List.all_eq_true.mp hcasesReplay assignment hassignment
      change ["POSITIVE_LOW", "POSITIVE_HIGH", "EXACT_ZERO"].all
        (s4CoverageSpecialLeafValid cases assignment) = true at hassignments
      have hmodes := List.all_eq_true.mp hassignments mode hmode
      unfold s4CoverageSpecialLeafValid at hmodes
      cases hlookup : s4CoverageSpecialLookup? cases assignment mode with
      | none => simp [hlookup] at hmodes
      | some pair =>
          cases pair with
          | mk box leaf =>
              simp only [hlookup] at hmodes
              have hparts := Bool.and_eq_true_iff.mp hmodes
              refine ⟨cases, box, leaf, rfl, hlookup, ?_, hparts.2⟩
              exact of_decide_eq_true hparts.1

end CirclePacking
