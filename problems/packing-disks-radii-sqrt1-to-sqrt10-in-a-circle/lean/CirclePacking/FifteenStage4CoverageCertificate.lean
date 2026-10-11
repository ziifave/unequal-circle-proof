import CirclePacking.FifteenStage4Certificate

/-! A Stage 4 coverage stream closes impossible radial-bin branches and marks
the surviving leaves with `A`.  Unlike the closed-pattern checker, an `A`
leaf is accepted only when its complete inner-bin word occurs in the
independently serialized residual assignment list. -/

namespace CirclePacking

def s4CoverageDigit (label : Nat) : Nat := if label == 13 then 0 else label

def s4CoverageAssignment (inner : Array Nat) (s : S4State) : Array Nat :=
  inner.map (fun p => s4CoverageDigit s.labels[p]!)

def s4CoverageAssignment? (text : String) : Option (Array Nat) := do
  let digits ← text.toList.mapM s4Digit?
  some digits.toArray

private def s4ResidualSource : String :=
  include_str "../../../../problems/packing-15-equal-disks-in-a-circle/candidate_bundle/full_residuals.txt"

private def s4ResidualLine? (pattern line : String) : Option (List String) := do
  let fields := line.splitOn "\t"
  guard (fields[0]? == some "UNKNOWN")
  guard (fields[2]? == some pattern)
  let encoded ← fields[5]?
  some ((encoded.splitOn ",").filter (· != ""))

private def s4ResidualAssignmentTexts? (pattern : String) : Option (List String) := do
  match (s4ResidualSource.splitOn "\n").filterMap (s4ResidualLine? pattern) with
  | [assignments] => some assignments
  | _ => none

def s4ResidualAssignments? (pattern : String) : Option (List (Array Nat)) := do
  let texts ← s4ResidualAssignmentTexts? pattern
  texts.mapM s4CoverageAssignment?

def s4CoverageStream : Nat → Array Nat → Array (List S4CertEdge) →
    List (Array Nat) → S4State → List Char → Option (List Char)
  | 0, _, _, _, _, 'B' :: _ => none
  | _, _, _, _, s, 'S' :: rest => if s4SmallReason s then some rest else none
  | _, inner, _, _, s, 'O' :: rest =>
      if s4OriginReason inner s then some rest else none
  | _, inner, _, _, s, 'R' :: rest =>
      if s4RankReason inner s then some rest else none
  | _, _, _, _, s, 'M' :: rest => if s4MixedReason s then some rest else none
  | _, inner, cycles, _, s, 'C' :: refHi :: refLo :: rest => do
      let (id, tail) ← s4ParseCycleId? (refHi :: refLo :: rest)
      let edges ← cycles[id]?
      if s.depth ≥ 3 && !s4StructurallyPruned inner s &&
          s4CycleValid s.labels edges then some tail else none
  | _, inner, _, allowed, s, 'A' :: rest =>
      if s.depth == inner.size && !s4StructurallyPruned inner s &&
          decide (s4CoverageAssignment inner s ∈ allowed) then some rest else none
  | fuel + 1, inner, cycles, allowed, s, 'B' :: rest => do
      if s.depth >= inner.size || s4StructurallyPruned inner s then none else do
        let tail ← s4CoverageStream fuel inner cycles allowed (s4Next inner s 0) rest
        let tail ← s4CoverageStream fuel inner cycles allowed (s4Next inner s 13) tail
        let tail ← s4CoverageStream fuel inner cycles allowed (s4Next inner s 1) tail
        let tail ← s4CoverageStream fuel inner cycles allowed (s4Next inner s 2) tail
        let tail ← s4CoverageStream fuel inner cycles allowed (s4Next inner s 3) tail
        let tail ← s4CoverageStream fuel inner cycles allowed (s4Next inner s 4) tail
        let tail ← s4CoverageStream fuel inner cycles allowed (s4Next inner s 5) tail
        let tail ← s4CoverageStream fuel inner cycles allowed (s4Next inner s 6) tail
        let tail ← s4CoverageStream fuel inner cycles allowed (s4Next inner s 7) tail
        let tail ← s4CoverageStream fuel inner cycles allowed (s4Next inner s 8) tail
        let tail ← s4CoverageStream fuel inner cycles allowed (s4Next inner s 9) tail
        s4CoverageStream fuel inner cycles allowed (s4Next inner s 10) tail
  | _, _, _, _, _, _ => none
termination_by fuel _ _ _ _ _ => fuel

def s4CoverageRecordValid (pattern : String)
    (cycles : Array (List S4CertEdge)) (stream : String) : Bool := Id.run do
  let some allowed := s4ResidualAssignments? pattern | return false
  match s4CoverageStream (s4InnerPositions pattern).size
      (s4InnerPositions pattern) cycles allowed (s4Initial pattern) stream.toList with
  | some [] => return true
  | _ => return false

def s4ParseCoverageRecord? (source : String) : Option S4CertificateRecord := do
  let lines := (source.splitOn "\n").filter (· != "")
  guard (lines.length == 1)
  let record ← s4ParseRecord? lines.head!
  some record

def s4CoverageSourceValid (source pattern : String) : Bool :=
  match s4ParseCoverageRecord? source with
  | some record => record.pattern == pattern &&
      s4CoverageRecordValid record.pattern record.cycles record.stream
  | none => false

theorem s4CoverageSourceValid_record {source pattern : String}
    (hvalid : s4CoverageSourceValid source pattern = true) :
    ∃ record, s4ParseCoverageRecord? source = some record ∧
      record.pattern = pattern ∧
      s4CoverageRecordValid record.pattern record.cycles record.stream = true := by
  unfold s4CoverageSourceValid at hvalid
  cases hparse : s4ParseCoverageRecord? source with
  | none => simp [hparse] at hvalid
  | some record =>
      simp only [hparse, Bool.and_eq_true_iff] at hvalid
      exact ⟨record, rfl, beq_iff_eq.mp hvalid.1, hvalid.2⟩

theorem s4CoverageRecordValid_stream {record : S4CertificateRecord}
    (hvalid : s4CoverageRecordValid record.pattern record.cycles record.stream =
      true) :
    ∃ allowed, s4ResidualAssignments? record.pattern = some allowed ∧
      s4CoverageStream (s4InnerPositions record.pattern).size
        (s4InnerPositions record.pattern) record.cycles allowed
        (s4Initial record.pattern) record.stream.toList = some [] := by
  unfold s4CoverageRecordValid at hvalid
  cases hallowed : s4ResidualAssignments? record.pattern with
  | none => simp [hallowed] at hvalid
  | some allowed =>
      cases hstream : s4CoverageStream (s4InnerPositions record.pattern).size
          (s4InnerPositions record.pattern) record.cycles allowed
          (s4Initial record.pattern) record.stream.toList with
      | none => simp [hallowed, hstream] at hvalid
      | some suffix =>
          cases suffix with
          | nil => exact ⟨allowed, rfl, by simpa [hstream]⟩
          | cons c rest => simp [hallowed, hstream] at hvalid

def s4RunCoverageChildren (fuel : Nat) (inner : Array Nat)
    (cycles : Array (List S4CertEdge)) (allowed : List (Array Nat))
    (s : S4State) : List Nat → List Char → Option (List Char)
  | [], input => some input
  | label :: rest, input =>
      (s4CoverageStream fuel inner cycles allowed (s4Next inner s label) input).bind
        (s4RunCoverageChildren fuel inner cycles allowed s rest)

theorem s4RunCoverageChildren_success_for_mem
    (fuel : Nat) (inner : Array Nat) (cycles : Array (List S4CertEdge))
    (allowed : List (Array Nat)) (s : S4State) (labels : List Nat)
    (input output : List Char)
    (hcheck : s4RunCoverageChildren fuel inner cycles allowed s labels input =
      some output)
    (label : Nat) (hmem : label ∈ labels) :
    ∃ before after,
      s4CoverageStream fuel inner cycles allowed (s4Next inner s label)
        before = some after := by
  induction labels generalizing input output with
  | nil => simp at hmem
  | cons first rest ih =>
      simp only [s4RunCoverageChildren, Option.bind_eq_some_iff] at hcheck
      obtain ⟨middle, hfirst, hrest⟩ := hcheck
      rcases List.mem_cons.mp hmem with heq | htail
      · subst label
        exact ⟨input, middle, hfirst⟩
      · exact ih middle output hrest htail

theorem s4CoverageStream_split_has_successful_child
    (fuel : Nat) (inner : Array Nat) (cycles : Array (List S4CertEdge))
    (allowed : List (Array Nat)) (s : S4State) (input output : List Char)
    (label : Nat)
    (hsuccess : s4CoverageStream (fuel + 1) inner cycles allowed s
      ('B' :: input) = some output)
    (hdepth : s.depth < inner.size)
    (hnotpruned : s4StructurallyPruned inner s = false)
    (hlabel : label ∈ s4BranchLabels) :
    ∃ before after,
      s4CoverageStream fuel inner cycles allowed (s4Next inner s label)
        before = some after := by
  have hchildren :
      s4RunCoverageChildren fuel inner cycles allowed s s4BranchLabels input =
        some output := by
    simpa [s4CoverageStream, s4BranchLabels, s4RunCoverageChildren,
      Nat.not_le_of_gt hdepth, hnotpruned] using hsuccess
  exact s4RunCoverageChildren_success_for_mem fuel inner cycles allowed s
    s4BranchLabels input output hchildren label hlabel

end CirclePacking
