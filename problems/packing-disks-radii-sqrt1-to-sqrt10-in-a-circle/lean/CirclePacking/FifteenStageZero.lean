import Lean
import CirclePacking.FifteenTickBounds

/-!
# Exact replay of the 760 dihedral patterns

This module independently checks the first finite layer of the 15-disk
certificate.  It generates the 15-bit dihedral representatives inside Lean,
reconstructs the complete admissible radial-type assignment list for every
representative, and checks an integer negative-cycle witness for every
assignment on each of the 382 excluded representatives.  The other 378
representatives carry a feasible assignment together with a potential for the
coarse difference-constraint graph, so their status as survivors is also
checked without trusting the C++ search.

The input files are compact exports of `stage0_certificate.json.gz`; their
exporter is not trusted by the proof.  Lean checks all records and cycle
weights directly with exact finite arithmetic.
-/

namespace CirclePacking

private def stage0N : Nat := 15
private def stage0TwoPiUpper : Nat := 17600

def fifteenStage0CoarseQ (i j : Nat) : Nat :=
  if i == 0 then
    if j == 0 then 1610 else if j == 3 then 840 else 0
  else if i == 1 then 0
  else if i == 2 then
    if j == 2 then 3360 else if j == 3 then 2408 else 0
  else if i == 3 then
    if j == 0 then 840 else if j == 2 || j == 3 then 2408 else 0
  else 0

private def stage0Boxes : Array FifteenInterval := #[
  (fifteenRational 2385 1000, fifteenRational 3522 1000),
  (fifteenRational 0 1, fifteenRational 1 1),
  (fifteenRational 1 1, fifteenRational 5 3),
  (fifteenRational 5 3, fifteenRational 2385432 1000000)
]

private def stage0CoarsePairValid (i j q : Nat) : Bool := Id.run do
  let some x := stage0Boxes[i]? | return false
  let some y := stage0Boxes[j]? | return false
  if q == 0 then return false
  if !(decide (0 < x.1)) || !(decide (0 < y.1)) then return false
  if !(decide (2 ≤ x.1 + y.1)) then return false
  if !(decide (x.2 - y.1 < 2)) || !(decide (y.2 - x.1 < 2)) then return false
  let cap := fifteenBoxCosineCap x y
  if !(decide (-1 < cap)) || !(decide (cap < 1)) then return false
  return fifteenTickCertificateValid x y false false q

private def stage0CoarseTableReplay : Bool :=
  (List.range 4).all fun i =>
    (List.range 4).all fun j =>
      let q := fifteenStage0CoarseQ i j
      if q == 0 then true else stage0CoarsePairValid i j q

def fifteenStage0CoarseTypeBox (typeIndex : Fin 4) : FifteenInterval :=
  stage0Boxes[typeIndex.1]!

def fifteenStage0CoarseAngleTick (typeI typeJ : Fin 4) : Nat :=
  fifteenStage0CoarseQ typeI.1 typeJ.1

def fifteenStage0CoarsePairChecker (typeI typeJ : Fin 4) : Bool :=
  let q := fifteenStage0CoarseAngleTick typeI typeJ
  if q == 0 then true
  else stage0CoarsePairValid typeI.1 typeJ.1 q

def fifteenStage0CoarseAngleTableReplay : Bool := stage0CoarseTableReplay

private def stage0MaskWeight (mask : Nat) : Nat :=
  (List.range stage0N).foldl
    (fun count i => if Nat.testBit mask (14 - i) then count + 1 else count) 0

private def stage0RotateMask (mask shift : Nat) : Nat :=
  (List.range stage0N).foldl (fun result i =>
    if Nat.testBit mask (14 - i) then
      result + 2 ^ (14 - ((i + shift) % stage0N))
    else result) 0

private def stage0ReverseMask (mask : Nat) : Nat :=
  (List.range stage0N).foldl (fun result i =>
    if Nat.testBit mask (14 - i) then result + 2 ^ i else result) 0

private def stage0CanonicalMask (mask : Nat) : Nat := Id.run do
  let reflected := stage0ReverseMask mask
  let rotations := (List.range stage0N).flatMap fun shift =>
    [stage0RotateMask mask shift, stage0RotateMask reflected shift]
  return rotations.foldl Nat.min mask

private def stage0MaskWord (mask : Nat) : String :=
  String.ofList ((List.range stage0N).map fun i =>
    if Nat.testBit mask (14 - i) then '1' else '0')

private def stage0CanonicalWords : List String :=
  ((List.range 32768).filter fun mask =>
    let weight := stage0MaskWeight mask
    5 ≤ weight && weight ≤ 8 && stage0CanonicalMask mask == mask).map
      stage0MaskWord

def fifteenStage0OrbitWords : List String := stage0CanonicalWords

private def stage0InnerPositionsAux : Nat → List Char → List Nat
  | _, [] => []
  | index, bit :: rest =>
      (if bit == '1' then [index] else []) ++
        stage0InnerPositionsAux (index + 1) rest

private def stage0InnerPositions (pattern : String) : List Nat :=
  stage0InnerPositionsAux 0 pattern.toList

private def stage0PatternValid (pattern : String) : Bool :=
  pattern.length == stage0N &&
    pattern.toList.all (fun bit => bit == '0' || bit == '1')

private def stage0Digits? (assignment : String) : Option (List Nat) :=
  assignment.toList.mapM fun digit =>
    if '1' ≤ digit && digit ≤ '3' then some (digit.toNat - 48) else none

private def stage0AssignmentAdmissible (k : Nat) (assignment : String) : Bool :=
  match stage0Digits? assignment with
  | none => false
  | some digits =>
      digits.length == k &&
      (digits.filter (· == 1)).length ≤ 1 &&
      (digits.filter (· == 3)).length ≥ k - 4

private def stage0AssignmentsAux : Nat → List (List Nat)
  | 0 => [[]]
  | n + 1 => (stage0AssignmentsAux n).flatMap fun rest =>
      [1, 2, 3].map (fun digit => digit :: rest)

private def stage0DigitsString (digits : List Nat) : String :=
  String.ofList (digits.map fun digit => Char.ofNat (48 + digit))

private def stage0ExpectedAssignments (k : Nat) : List String :=
  ((stage0AssignmentsAux k).filter fun digits =>
    (digits.filter (· == 1)).length ≤ 1 &&
      (digits.filter (· == 3)).length ≥ k - 4).map stage0DigitsString

private def stage0SameMembers (xs ys : List String) : Bool :=
  xs.length == ys.length &&
    xs.length == xs.eraseDups.length &&
    ys.length == ys.eraseDups.length &&
    xs.all ys.contains && ys.all xs.contains

private def stage0DecodeVertex (c : Char) : Option Nat :=
  if '0' ≤ c && c ≤ '9' then some (c.toNat - 48)
  else if 'A' ≤ c && c ≤ 'E' then some (10 + c.toNat - 65)
  else none

private structure Stage0Edge where
  source : Nat
  target : Nat
  kind : Nat
  deriving DecidableEq, BEq, Repr

private def stage0ParseEdges : List Char → Option (List Stage0Edge)
  | [] => some []
  | source :: target :: kind :: rest => do
      let u ← stage0DecodeVertex source
      let v ← stage0DecodeVertex target
      let k ← if kind == 'O' then some 0
        else if kind == 'L' then some 1
        else if kind == 'U' then some 2
        else none
      let tail ← stage0ParseEdges rest
      some (⟨u, v, k⟩ :: tail)
  | _ => none

private def stage0CycleLinesSource : String :=
  include_str "../../../../research/fifteen_equal_completion/candidate_bundle/stage0_cycles.txt"

private def stage0OrbitLinesSource : String :=
  include_str "../../../../research/fifteen_equal_completion/candidate_bundle/stage0_orbits.txt"

private def stage0NonemptyLines (source : String) : List String :=
  (source.splitOn "\n").filter (· != "")

private def stage0Cycles? : Option (Array (List Stage0Edge)) := do
  let cycles ← (stage0NonemptyLines stage0CycleLinesSource).mapM fun line => do
    let edges ← stage0ParseEdges line.toList
    guard (!edges.isEmpty && edges.length ≤ stage0N)
    pure edges
  return cycles.toArray

private def stage0ParseCase? (text : String) : Option (String × Nat) := do
  match text.splitOn ":" with
  | [assignment, cycleId] => do
      let id ← cycleId.toNat?
      some (assignment, id)
  | _ => none

private def stage0ParseCases? (text : String) : Option (List (String × Nat)) :=
  (text.splitOn ",").mapM stage0ParseCase?

private def stage0ParsePotential? (text : String) : Option (List Nat) :=
  (text.splitOn ",").mapM String.toNat?

private structure Stage0Orbit where
  pattern : String
  excluded : Bool
  cases : List (String × Nat)
  witness : String
  potential : List Nat
  deriving Repr

private def stage0ParseOrbit? (line : String) : Option Stage0Orbit := do
  match line.splitOn "|" with
  | [pattern, "E", encoded] => do
      let cases ← stage0ParseCases? encoded
      some ⟨pattern, true, cases, "", []⟩
  | [pattern, "U", witness, encodedPotential] => do
      let potential ← stage0ParsePotential? encodedPotential
      some ⟨pattern, false, [], witness, potential⟩
  | _ => none

private def stage0Orbits? : Option (List Stage0Orbit) := do
  (stage0NonemptyLines stage0OrbitLinesSource).mapM stage0ParseOrbit?

private def stage0Labels (pattern assignment : String) : Array Nat := Id.run do
  let positions := stage0InnerPositions pattern
  let digits := (stage0Digits? assignment).getD []
  let mut labels := Array.replicate stage0N 0
  for (position, digit) in List.zip positions digits do
    labels := labels.set! position digit
  return labels

private def stage0EdgeWeight (labels : Array Nat) (edge : Stage0Edge) : Int :=
  if edge.kind == 0 then 0
  else if edge.kind == 1 then
    -(Int.ofNat (fifteenStage0CoarseQ labels[edge.target]! labels[edge.source]!))
  else
    Int.ofNat (stage0TwoPiUpper -
      fifteenStage0CoarseQ labels[edge.source]! labels[edge.target]!)

private def stage0EdgeShape (edge : Stage0Edge) : Bool :=
  edge.source < stage0N && edge.target < stage0N &&
    (if edge.kind == 0 then edge.source == edge.target + 1 && edge.target < 14
     else if edge.kind == 1 then edge.source > edge.target
     else if edge.kind == 2 then edge.source < edge.target
     else false)

private def stage0CycleValid (pattern assignment : String)
    (edges : List Stage0Edge) : Bool := Id.run do
  if !stage0PatternValid pattern || !(stage0AssignmentAdmissible
      (stage0InnerPositions pattern).length assignment) then return false
  if edges.isEmpty || edges.length > stage0N then return false
  if !edges.all stage0EdgeShape then return false
  if !(List.zip edges (edges.drop 1)).all
      (fun (left, right) => left.target == right.source) then return false
  let some first := edges.head? | return false
  let some last := edges.getLast? | return false
  if last.target != first.source then return false
  let labels := stage0Labels pattern assignment
  let weight := edges.foldl (fun sum edge => sum + stage0EdgeWeight labels edge) 0
  return weight < 0

structure FifteenStage0GraphEdge where
  source : Nat
  target : Nat
  weight : Int
  deriving DecidableEq, Repr

private def stage0GraphEdges (labels : Array Nat) : List FifteenStage0GraphEdge :=
  let orderEdges := (List.range 14).map fun index => ⟨index + 1, index, 0⟩
  let pairEdges := (List.range stage0N).flatMap fun i =>
    (List.range (14 - i)).flatMap fun offset =>
      let j := i + offset + 1
      let q := fifteenStage0CoarseQ labels[i]! labels[j]!
      [⟨j, i, -(Int.ofNat q)⟩,
       ⟨i, j, Int.ofNat (stage0TwoPiUpper - q)⟩]
  orderEdges ++ pairEdges

private def stage0PotentialValid (pattern witness : String)
    (potential : List Nat) : Bool := Id.run do
  if !stage0PatternValid pattern || !(stage0AssignmentAdmissible
      (stage0InnerPositions pattern).length witness) then return false
  if potential.length != stage0N then return false
  let labels := stage0Labels pattern witness
  let values := potential.toArray
  return (stage0GraphEdges labels).all fun edge =>
    decide (Int.ofNat values[edge.target]! ≤
      Int.ofNat values[edge.source]! + edge.weight)

private def stage0OrbitValid (cycles : Array (List Stage0Edge))
    (orbit : Stage0Orbit) : Bool := Id.run do
  if !stage0PatternValid orbit.pattern then return false
  let k := (stage0InnerPositions orbit.pattern).length
  if orbit.excluded then
    let assignments := orbit.cases.map Prod.fst
    if !stage0SameMembers (stage0ExpectedAssignments k) assignments then return false
    return orbit.cases.all fun (assignment, cycleId) =>
      match cycles[cycleId]? with
      | none => false
      | some edges => stage0CycleValid orbit.pattern assignment edges
  else
    if !orbit.cases.isEmpty then return false
    return stage0PotentialValid orbit.pattern orbit.witness orbit.potential

private def stage0CertificateReplay : Bool := Id.run do
  let some cycles := stage0Cycles? | return false
  let some orbits := stage0Orbits? | return false
  if cycles.size != 10832 || orbits.length != 760 then return false
  if (cycles.toList.eraseDups.length != cycles.size) then return false
  if orbits.map Stage0Orbit.pattern != stage0CanonicalWords then return false
  if !stage0CoarseTableReplay then return false
  if !(orbits.all (stage0OrbitValid cycles)) then return false
  let excluded := (orbits.filter Stage0Orbit.excluded).length
  let survivors := (orbits.filter (fun orbit => !orbit.excluded)).length
  if excluded != 382 || survivors != 378 then return false
  let counts := [5, 6, 7, 8].map fun k =>
    (orbits.filter fun orbit => (stage0InnerPositions orbit.pattern).length == k).length
  return counts == [111, 185, 232, 232]

def fifteenStage0CertificateReplay : Bool := stage0CertificateReplay

def fifteenStage0OrbitCountByWeight : List Nat :=
  [5, 6, 7, 8].map fun k =>
    (fifteenStage0OrbitWords.filter fun word =>
      (stage0InnerPositions word).length == k).length

def FifteenStage0GraphChain (start : Nat) :
    List FifteenStage0GraphEdge → Nat → Prop
  | [], finish => finish = start
  | edge :: rest, finish =>
      edge.source = start ∧ FifteenStage0GraphChain edge.target rest finish

private def stage0PotentialDifference (potential : Nat → Int)
    (edge : FifteenStage0GraphEdge) : Int :=
  potential edge.target - potential edge.source

theorem fifteenStage0ListSumMapLe {α : Type} (items : List α)
    (f g : α → Int) (h : ∀ item ∈ items, f item ≤ g item) :
    (items.map f).sum ≤ (items.map g).sum := by
  induction items with
  | nil => simp
  | cons item rest ih =>
      simp only [List.map_cons, List.sum_cons]
      exact Int.add_le_add (h item (by simp))
        (ih (fun next hnext => h next (by simp [hnext])))

theorem fifteenStage0GraphChain_telescope
    (potential : Nat → Int) (start finish : Nat)
    (edges : List FifteenStage0GraphEdge)
    (hchain : FifteenStage0GraphChain start edges finish) :
    (edges.map (stage0PotentialDifference potential)).sum =
      potential finish - potential start := by
  induction edges generalizing start finish with
  | nil =>
      simp only [FifteenStage0GraphChain] at hchain
      subst finish
      simp
  | cons edge rest ih =>
      simp only [FifteenStage0GraphChain] at hchain
      rcases hchain with ⟨hsource, hrest⟩
      subst start
      simp only [List.map_cons, List.sum_cons]
      rw [ih edge.target finish hrest]
      simp only [stage0PotentialDifference]
      omega

theorem fifteenStage0Potential_cycle_nonnegative
    (potential : Nat → Int) (start : Nat)
    (edges : List FifteenStage0GraphEdge)
    (hchain : FifteenStage0GraphChain start edges start)
    (hpotential : ∀ edge ∈ edges,
      potential edge.target ≤ potential edge.source + edge.weight) :
    0 ≤ (edges.map (fun edge => edge.weight)).sum := by
  have hterm : ∀ edge ∈ edges,
      stage0PotentialDifference potential edge ≤ edge.weight := by
    intro edge hedge
    have h := hpotential edge hedge
    dsimp [stage0PotentialDifference]
    omega
  have hsum := fifteenStage0ListSumMapLe edges
    (stage0PotentialDifference potential) (fun edge => edge.weight) hterm
  have htelescope := fifteenStage0GraphChain_telescope potential start start edges hchain
  rw [Int.sub_self] at htelescope
  rw [htelescope] at hsum
  exact hsum

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem fifteenStage0Certificate_replays : fifteenStage0CertificateReplay = true := by
  native_decide

theorem fifteenStage0CoarseAngleTable_replays :
    fifteenStage0CoarseAngleTableReplay = true := by
  native_decide

theorem fifteenStage0DihedralClassCounts :
    fifteenStage0OrbitWords.length = 760 ∧
      fifteenStage0OrbitCountByWeight = [111, 185, 232, 232] := by
  native_decide

end CirclePacking
