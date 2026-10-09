import Lean

/-!
# Lean replay of the 15-disk rational subdivision certificate

This is the first Lean-facing replay layer for the 15-equal-disk candidate.
It parses the repository's exact JSON certificate at compile time, checks the
rational bisection tree, and verifies the integer sum and topology of each
recorded angular negative cycle.  The cycle edge's integer angle tick is
certificate data at this stage; proving that the tick is a valid geometric
angle lower bound is the next layer of the formalization.

The tree replayer deliberately uses a work list rather than recursively
expanding the large JSON value.  The resulting Boolean theorem is checked with
`native_decide`, following the existing finite-certificate convention in this
Lean project.
-/

namespace CirclePacking

open Lean

abbrev FifteenInterval := Rat × Rat
abbrev FifteenBox := Array FifteenInterval
abbrev FifteenTask := FifteenBox × List Nat × Json

def fifteenIntervalContains (interval : FifteenInterval) (x : Rat) : Prop :=
  interval.1 ≤ x ∧ x ≤ interval.2

theorem fifteenIntervalSplitCovers (lo cut hi x : Rat)
    (hx : fifteenIntervalContains (lo, hi) x) :
    fifteenIntervalContains (lo, cut) x ∨ fifteenIntervalContains (cut, hi) x := by
  rcases hx with ⟨hlo, hhi⟩
  rcases Rat.le_total (a := x) (b := cut) with hleft | hright
  · exact Or.inl ⟨hlo, hleft⟩
  · exact Or.inr ⟨hright, hhi⟩

theorem fifteenIntervalLeftChildSubset (lo cut hi x : Rat)
    (hcut : cut ≤ hi) (hx : fifteenIntervalContains (lo, cut) x) :
    fifteenIntervalContains (lo, hi) x := by
  rcases hx with ⟨hlo, hxcut⟩
  exact ⟨hlo, Rat.le_trans hxcut hcut⟩

theorem fifteenIntervalRightChildSubset (lo cut hi x : Rat)
    (hcut : lo ≤ cut) (hx : fifteenIntervalContains (cut, hi) x) :
    fifteenIntervalContains (lo, hi) x := by
  rcases hx with ⟨hcutx, hhi⟩
  exact ⟨Rat.le_trans hcut hcutx, hhi⟩

def fifteenRational (n d : Nat) : Rat :=
  if hd : d = 0 then 0 else Rat.normalize (Int.ofNat n) d hd

def fifteenBins : Array FifteenInterval := #[
  (fifteenRational 0 1, fifteenRational 1 2),
  (fifteenRational 1 2, fifteenRational 1 1),
  (fifteenRational 1 1, fifteenRational 3 2),
  (fifteenRational 3 2, fifteenRational 8 5),
  (fifteenRational 8 5, fifteenRational 5 3),
  (fifteenRational 5 3, fifteenRational 17 10),
  (fifteenRational 17 10, fifteenRational 37 20),
  (fifteenRational 37 20, fifteenRational 2 1),
  (fifteenRational 2 1, fifteenRational 43 20),
  (fifteenRational 43 20, fifteenRational 23 10),
  (fifteenRational 23 10, fifteenRational 2385432 1000000),
  (fifteenRational 35213569647 10000000000,
    fifteenRational 35213569648 10000000000)
]

def fifteenCertificateSource : String :=
  include_str "../../../../research/fifteen_equal_completion/candidate_bundle/exact_subdivision_certificate.json"

def fifteenResidualSource : String :=
  include_str "../../../../research/fifteen_equal_completion/candidate_bundle/full_residuals.txt"

def fifteenJsonArray? (j : Json) : Option (Array Json) :=
  match j with
  | .arr values => some values
  | _ => none

def fifteenJsonField? (j : Json) (key : String) : Option Json :=
  (j.getObjVal? key).toOption

def fifteenJsonAt? (j : Json) (index : Nat) : Option Json := do
  let values ← fifteenJsonArray? j
  values[index]?

def fifteenJsonNat? (j : Json) : Option Nat := (j.getNat?).toOption

def fifteenJsonString? (j : Json) : Option String := (j.getStr?).toOption

def fifteenFieldNat? (j : Json) (key : String) : Option Nat := do
  let value ← fifteenJsonField? j key
  fifteenJsonNat? value

def fifteenFieldString? (j : Json) (key : String) : Option String := do
  let value ← fifteenJsonField? j key
  fifteenJsonString? value

def fifteenResidualLine? (pattern line : String) : Option (List String) := do
  let fields := line.splitOn "\t"
  guard (fields[0]? == some "UNKNOWN")
  guard (fields[2]? == some pattern)
  let encoded ← fields[5]?
  some ((encoded.splitOn ",").filter (· != ""))

def fifteenResidualAssignments? (pattern : String) : Option (List String) := do
  match (fifteenResidualSource.splitOn "\n").filterMap (fifteenResidualLine? pattern) with
  | [assignments] => some assignments
  | _ => none

def fifteenSameMembers (xs ys : List String) : Bool :=
  xs.length == ys.length && xs.length == xs.eraseDups.length &&
    ys.length == ys.eraseDups.length && xs.all ys.contains && ys.all xs.contains

def fifteenParseRat (text : String) : Option Rat := do
  match text.splitOn "/" with
  | [numerator, denominator] => do
      let n ← numerator.toNat?
      let d ← denominator.toNat?
      guard (d != 0)
      some (fifteenRational n d)
  | [numerator] => do
      let n ← numerator.toNat?
      some (fifteenRational n 1)
  | _ => none

def fifteenInnerPositionsAux : Nat → List Char → List Nat
  | _, [] => []
  | i, c :: rest =>
      (if c == '1' then [i] else []) ++ fifteenInnerPositionsAux (i + 1) rest

def fifteenInnerPositions (pattern : String) : List Nat :=
  fifteenInnerPositionsAux 0 pattern.toList

def fifteenDigit? (c : Char) : Option Nat :=
  if 48 ≤ c.toNat && c.toNat ≤ 57 then some (c.toNat - 48) else none

def fifteenIsBinaryPattern (pattern : String) : Bool :=
  pattern.length == 15 && pattern.toList.all (fun c => c == '0' || c == '1')

def fifteenInitialBox? (pattern assignment : String) : Option FifteenBox := do
  guard (fifteenIsBinaryPattern pattern)
  let positions := fifteenInnerPositions pattern
  let digits ← assignment.toList.mapM fifteenDigit?
  guard (positions.length == digits.length)
  let box ← (List.zip positions digits).foldlM (fun box (position, digit) => do
    guard (digit != 0 && digit ≤ 10)
    let interval ← fifteenBins[digit]?
    pure (box.set! position interval)) (Array.replicate 15 fifteenBins[11]!)
  some box

structure FifteenCycleEdge where
  source : Nat
  target : Nat
  kind : String
  ticks : Nat
  deriving DecidableEq, Repr

def fifteenParseCycleEdge? (j : Json) : Option FifteenCycleEdge := do
  let values ← fifteenJsonArray? j
  if values.size != 4 then none
  let source ← fifteenJsonNat? values[0]!
  let target ← fifteenJsonNat? values[1]!
  let kind ← fifteenJsonString? values[2]!
  let ticks ← fifteenJsonNat? values[3]!
  some ⟨source, target, kind, ticks⟩

def fifteenCycleEdgeShape (edge : FifteenCycleEdge) : Bool :=
  decide (edge.source < 15) && decide (edge.target < 15) && decide (edge.ticks ≤ 8790) &&
  (if edge.kind == "O" then
    edge.source == edge.target + 1 && edge.target < 14 && edge.ticks == 0
   else if edge.kind == "L" then
    edge.source > edge.target
   else if edge.kind == "U" then
    edge.source < edge.target
   else false)

def fifteenCycleEdgeWeight (edge : FifteenCycleEdge) : Int :=
  if edge.kind == "O" then 0
  else if edge.kind == "L" then -(Int.ofNat edge.ticks)
  else Int.ofNat (17600 - edge.ticks)

def fifteenCycleLinkValid : List FifteenCycleEdge → Bool
  | [] => true
  | [_] => true
  | first :: second :: rest =>
      first.target == second.source && fifteenCycleLinkValid (second :: rest)

def fifteenCycleValid (j : Json) : Bool := Id.run do
  let some rawEdges := fifteenJsonArray? j | return false
  let some edges := rawEdges.toList.mapM fifteenParseCycleEdge? | return false
  if edges.length < 2 || edges.length > 15 then return false
  if !edges.all fifteenCycleEdgeShape then return false
  let some first := edges.head? | return false
  let some last := edges.getLast? | return false
  if !fifteenCycleLinkValid edges then return false
  if last.target != first.source then return false
  let weight := edges.foldl (fun sum edge => sum + fifteenCycleEdgeWeight edge) (0 : Int)
  return decide (weight < 0)

def fifteenLocalLo : Rat := fifteenRational 42 25
def fifteenLocalHi : Rat := fifteenRational 43 25

def fifteenInLocalBox (box : FifteenBox) (inner : List Nat) : Bool :=
  inner.all (fun p =>
    decide (fifteenLocalLo ≤ box[p]!.1) && decide (box[p]!.2 ≤ fifteenLocalHi))

def fifteenTerminalValid (box : FifteenBox) (inner : List Nat)
    (node : Json) (allowLocal : Bool) : Bool := Id.run do
  let some values := fifteenJsonArray? node | return false
  let some tag := values[0]? >>= fifteenJsonString? | return false
  if tag == "CYCLE" then
    if values.size != 2 then return false
    let some edges := values[1]? | return false
    return fifteenCycleValid edges
  if tag == "SUM" then
    if values.size != 3 then return false
    let some i := values[1]? >>= fifteenJsonNat? | return false
    let some j := values[2]? >>= fifteenJsonNat? | return false
    if i >= j || j >= 15 || !inner.contains i || !inner.contains j then return false
    return decide (box[i]!.2 + box[j]!.2 < 2)
  if tag == "LOCAL" && allowLocal then
    return values.size == 1 && inner == fifteenInnerPositions "001001001001001" &&
      fifteenInLocalBox box inner
  return false

def fifteenSplitParts? (node : Json) : Option (Nat × Rat × Json × Json) := do
  let values ← fifteenJsonArray? node
  if values.size != 5 then none
  let tag ← fifteenJsonString? values[0]!
  if tag != "SPLIT" then none
  let axis ← fifteenJsonNat? values[1]!
  let cutText ← fifteenJsonString? values[2]!
  let cut ← fifteenParseRat cutText
  let left ← values[3]?
  let right ← values[4]?
  some (axis, cut, left, right)

structure FifteenTreeCounts where
  nodes : Nat := 0
  cycles : Nat := 0
  sums : Nat := 0
  localLeaves : Nat := 0
  deriving Repr

def fifteenCheckTasks : Nat → List FifteenTask → FifteenTreeCounts → Option FifteenTreeCounts
  | 0, [] , counts => some counts
  | 0, _ :: _, _ => none
  | _ + 1, [], counts => some counts
  | fuel + 1, (box, inner, node) :: rest, counts => Id.run do
      let counts := { counts with nodes := counts.nodes + 1 }
      let some tag := fifteenJsonAt? node 0 >>= fifteenJsonString? | return none
      if tag == "SPLIT" then
        let some (axis, cut, left, right) := fifteenSplitParts? node | return none
        let some (lo, hi) := box[axis]? | return none
        if decide (axis >= 15) || !inner.contains axis || !(decide (lo < cut)) ||
            !(decide (cut < hi)) || cut != (lo + hi) / 2 then
          return none
        let leftBox := box.set! axis (lo, cut)
        let rightBox := box.set! axis (cut, hi)
        return fifteenCheckTasks fuel ((leftBox, inner, left) :: (rightBox, inner, right) :: rest) counts
      if tag == "CYCLE" then
        if !fifteenTerminalValid box inner node false then return none
        return fifteenCheckTasks fuel rest { counts with cycles := counts.cycles + 1 }
      if tag == "SUM" then
        if !fifteenTerminalValid box inner node false then return none
        return fifteenCheckTasks fuel rest { counts with sums := counts.sums + 1 }
      if tag == "LOCAL" then
        if !fifteenTerminalValid box inner node true then return none
        return fifteenCheckTasks fuel rest { counts with localLeaves := counts.localLeaves + 1 }
      return none

def fifteenExpectedRoots (pattern : String) : Nat :=
  if pattern == "000100100010101" then 47
  else if pattern == "000100100100101" then 38
  else if pattern == "001001001001001" then 1181
  else 0

def fifteenRootKey? (root : Json) : Option (String × String) := do
  let pattern ← fifteenFieldString? root "pattern"
  let assignment ← fifteenFieldString? root "assignment"
  some (pattern, assignment)

def fifteenUniqueKeys : List (String × String) → Bool
  | [] => true
  | key :: rest => !(rest.contains key) && fifteenUniqueKeys rest

def fifteenRootValid (root : Json) : Bool := Id.run do
  let some pattern := fifteenFieldString? root "pattern" | return false
  let some assignment := fifteenFieldString? root "assignment" | return false
  if fifteenExpectedRoots pattern == 0 then return false
  if (fifteenInitialBox? pattern assignment).isNone then return false
  let some _tree := fifteenJsonField? root "tree" | return false
  return true

def fifteenRootCount (roots : Array Json) (pattern : String) : Nat :=
  roots.foldl (fun count root =>
    if fifteenFieldString? root "pattern" == some pattern then count + 1 else count) 0

def fifteenRootAssignmentsMatchResidual (roots : Array Json) (pattern : String) : Bool :=
  match fifteenResidualAssignments? pattern with
  | none => false
  | some expected =>
      let observed := roots.toList.filterMap (fun root =>
        if fifteenFieldString? root "pattern" == some pattern
        then fifteenFieldString? root "assignment"
        else none)
      fifteenSameMembers expected observed

def fifteenRootTasksAux : List Json → Option (List FifteenTask)
  | [] => some []
  | root :: rest => do
      let pattern ← fifteenFieldString? root "pattern"
      let assignment ← fifteenFieldString? root "assignment"
      let box ← fifteenInitialBox? pattern assignment
      let tree ← fifteenJsonField? root "tree"
      let tasks ← fifteenRootTasksAux rest
      some ((box, fifteenInnerPositions pattern, tree) :: tasks)

def fifteenSpecialPattern : String := "001001001001011"

def fifteenSpecialBox? (assignment mode : String) (vertex : Nat) : Option FifteenBox := do
  let positions := fifteenInnerPositions fifteenSpecialPattern
  let digits ← assignment.toList.mapM fifteenDigit?
  guard (digits.length == positions.length)
  let zeros := (List.zip positions digits).filterMap (fun (p, d) =>
    if d == 0 then some p else none)
  guard (zeros.length == 1 && zeros.head? == some vertex)
  let box ← (List.zip positions digits).foldlM (fun box (position, digit) => do
    if digit == 0 then
      let interval? :=
        if mode == "POSITIVE_LOW" then (fifteenRational 0 1, fifteenRational 1 4)
        else if mode == "POSITIVE_HIGH" then (fifteenRational 1 4, fifteenRational 1 2)
        else if mode == "EXACT_ZERO" then (fifteenRational 0 1, fifteenRational 0 1)
        else (fifteenRational 0 1, fifteenRational 0 1)
      if mode != "POSITIVE_LOW" && mode != "POSITIVE_HIGH" && mode != "EXACT_ZERO" then
        none
      else pure (box.set! position interval?)
    else
      guard (digit ≤ 10)
      let interval ← fifteenBins[digit]?
      pure (box.set! position interval)) (Array.replicate 15 fifteenBins[11]!)
  some box

def fifteenSpecialCaseValid (item : Json) : Bool := Id.run do
  let some pattern := fifteenFieldString? item "pattern" | return false
  let some assignment := fifteenFieldString? item "assignment" | return false
  let some mode := fifteenFieldString? item "mode" | return false
  let some vertex := fifteenFieldNat? item "vertex" | return false
  if pattern != fifteenSpecialPattern then return false
  let some box := fifteenSpecialBox? assignment mode vertex | return false
  let some leaf := fifteenJsonField? item "leaf" | return false
  return fifteenTerminalValid box (fifteenInnerPositions pattern) leaf false

def fifteenSpecialModeCount (cases : Array Json) (assignment mode : String) : Nat :=
  cases.foldl (fun count item =>
    if fifteenFieldString? item "assignment" == some assignment &&
        fifteenFieldString? item "mode" == some mode then count + 1 else count) 0

def fifteenSpecialAssignments (cases : Array Json) : List String :=
  cases.toList.filterMap (fun item => fifteenFieldString? item "assignment")

def fifteenSpecialAssignmentsMatchResidual (cases : Array Json) : Bool :=
  match fifteenResidualAssignments? fifteenSpecialPattern with
  | none => false
  | some expected => fifteenSameMembers expected (fifteenSpecialAssignments cases).eraseDups

def fifteenSpecialCasesValid (cases : Array Json) : Bool := Id.run do
  if cases.size != 9 || !cases.all fifteenSpecialCaseValid then return false
  let assignments := fifteenSpecialAssignments cases
  if assignments.length != 9 then return false
  let unique := assignments.eraseDups
  if unique.length != 3 then return false
  if !fifteenSpecialAssignmentsMatchResidual cases then return false
  return unique.all (fun assignment =>
    fifteenSpecialModeCount cases assignment "POSITIVE_LOW" == 1 &&
    fifteenSpecialModeCount cases assignment "POSITIVE_HIGH" == 1 &&
    fifteenSpecialModeCount cases assignment "EXACT_ZERO" == 1)

def fifteenExactCertificateReplay : Bool := Id.run do
  let .ok document := Json.parse fifteenCertificateSource | return false
  if fifteenFieldString? document "format" != some "unequal-circle-exact-subdivision-v1" then
    return false
  let some rootsJson := fifteenJsonField? document "roots" | return false
  let some roots := fifteenJsonArray? rootsJson | return false
  if roots.size != 1266 || !roots.all fifteenRootValid then return false
  let keys := roots.toList.filterMap fifteenRootKey?
  if keys.length != roots.size || !fifteenUniqueKeys keys then return false
  if fifteenRootCount roots "000100100010101" != 47 then return false
  if fifteenRootCount roots "000100100100101" != 38 then return false
  if fifteenRootCount roots "001001001001001" != 1181 then return false
  if !fifteenRootAssignmentsMatchResidual roots "000100100010101" then return false
  if !fifteenRootAssignmentsMatchResidual roots "000100100100101" then return false
  if !fifteenRootAssignmentsMatchResidual roots "001001001001001" then return false
  let some tasks := fifteenRootTasksAux roots.toList | return false
  let some counts := fifteenCheckTasks 60000 tasks {} | return false
  if counts.nodes != 58860 || counts.cycles != 30032 || counts.sums != 0 || counts.localLeaves != 31 then
    return false
  let some specialsJson := fifteenJsonField? document "special_cases" | return false
  let some specials := fifteenJsonArray? specialsJson | return false
  return fifteenSpecialCasesValid specials

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem fifteenExactCertificate_replays : fifteenExactCertificateReplay = true := by
  native_decide

end CirclePacking
