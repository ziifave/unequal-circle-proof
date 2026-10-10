import Lean
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
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
def fifteenStage0TwoPiUpper : Nat := 17600

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

theorem fifteenStage0OuterTypeBox_rat_bounds :
    (fifteenStage0CoarseTypeBox (0 : Fin 4)).1 =
        fifteenRational 2385 1000 ∧
      (fifteenStage0CoarseTypeBox (0 : Fin 4)).2 =
        fifteenRational 3522 1000 := by
  decide

theorem fifteenStage0InnerTypeBox_rat_bounds :
    ((fifteenStage0CoarseTypeBox (1 : Fin 4)).1 = fifteenRational 0 1 ∧
      (fifteenStage0CoarseTypeBox (1 : Fin 4)).2 = fifteenRational 1 1) ∧
    ((fifteenStage0CoarseTypeBox (2 : Fin 4)).1 = fifteenRational 1 1 ∧
      (fifteenStage0CoarseTypeBox (2 : Fin 4)).2 = fifteenRational 5 3) ∧
    ((fifteenStage0CoarseTypeBox (3 : Fin 4)).1 = fifteenRational 5 3 ∧
      (fifteenStage0CoarseTypeBox (3 : Fin 4)).2 =
        fifteenRational 2385432 1000000) := by
  decide

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

/-! The search certificate below records the canonical representative of each
dihedral orbit.  This finite check makes the coverage direction explicit too:
every 15-bit mask of weight 5 through 8 canonicalizes to a word in the
enumerated list. -/
private def stage0CanonicalCoverageCheck : Bool :=
  (List.range 32768).all fun mask =>
    let weight := stage0MaskWeight mask
    let canonical := stage0CanonicalMask mask
    if _hweight : 5 ≤ weight ∧ weight ≤ 8 then
      (canonical < 32768) &&
        (stage0MaskWeight canonical == weight) &&
        (stage0CanonicalMask canonical == canonical)
    else true

def fifteenStage0CanonicalCoverageReplay : Bool :=
  stage0CanonicalCoverageCheck

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

structure FifteenStage0CycleStep where
  source : Nat
  target : Nat
  kind : Nat
  deriving DecidableEq, BEq, Repr

private abbrev Stage0Edge := FifteenStage0CycleStep

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
  include_str "../../../../problems/packing-15-equal-disks-in-a-circle/candidate_bundle/stage0_cycles.txt"

private def stage0OrbitLinesSource : String :=
  include_str "../../../../problems/packing-15-equal-disks-in-a-circle/candidate_bundle/stage0_orbits.txt"

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

/-- Patterns not eliminated by the certified first-stage assignment table. -/
def fifteenStage0SurvivorPatterns : List String :=
  match stage0Orbits? with
  | none => []
  | some orbits => orbits.filterMap fun orbit =>
      if orbit.excluded then none else some orbit.pattern

private def stage0Labels (pattern assignment : String) : Array Nat := Id.run do
  let positions := stage0InnerPositions pattern
  let digits := (stage0Digits? assignment).getD []
  let mut labels := Array.replicate stage0N 0
  for (position, digit) in List.zip positions digits do
    labels := labels.set! position digit
  return labels

def fifteenStage0EdgeWeight
    (labels : Array Nat) (edge : FifteenStage0CycleStep) : Int :=
  if edge.kind == 0 then 0
  else if edge.kind == 1 then
    -(Int.ofNat (fifteenStage0CoarseQ labels[edge.target]! labels[edge.source]!))
  else
    Int.ofNat (fifteenStage0TwoPiUpper -
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
  let weight := edges.foldl
    (fun sum edge => sum + fifteenStage0EdgeWeight labels edge) 0
  return weight < 0

structure FifteenStage0GraphEdge where
  source : Nat
  target : Nat
  weight : Int
  deriving DecidableEq, Repr

/-- One finite negative-cycle witness from the Stage 0 certificate.  Each
step stores its source, target, and kind (`0` for radial order, `1` for a
lower pair bound, and `2` for an upper pair bound).  The weights are
reconstructed from the pattern and assignment by Lean. -/
structure FifteenStage0CycleWitness where
  pattern : String
  assignment : String
  steps : List (Nat × Nat × Nat)
  deriving DecidableEq, Repr

private def stage0GraphEdges (labels : Array Nat) : List FifteenStage0GraphEdge :=
  let orderEdges := (List.range 14).map fun index => ⟨index + 1, index, 0⟩
  let pairEdges := (List.range stage0N).flatMap fun i =>
    (List.range (14 - i)).flatMap fun offset =>
      let j := i + offset + 1
      let q := fifteenStage0CoarseQ labels[i]! labels[j]!
      [⟨j, i, -(Int.ofNat q)⟩,
       ⟨i, j, Int.ofNat (fifteenStage0TwoPiUpper - q)⟩]
  orderEdges ++ pairEdges

def fifteenStage0StepGraphEdge (labels : Array Nat)
    (step : Nat × Nat × Nat) : FifteenStage0GraphEdge :=
  let edge : Stage0Edge := ⟨step.1, step.2.1, step.2.2⟩
  ⟨edge.source, edge.target, fifteenStage0EdgeWeight labels edge⟩

/-- Reconstruct the graph edge represented by one encoded certificate step. -/
def fifteenStage0CycleWitnessStepEdge
    (witness : FifteenStage0CycleWitness)
    (step : Nat × Nat × Nat) : FifteenStage0GraphEdge :=
  fifteenStage0StepGraphEdge
    (stage0Labels witness.pattern witness.assignment) step

/-- Reconstruct the weighted graph walk encoded by a Stage 0 witness. -/
def fifteenStage0CycleWitnessEdges
    (witness : FifteenStage0CycleWitness) : List FifteenStage0GraphEdge :=
  witness.steps.map (fifteenStage0CycleWitnessStepEdge witness)

private def stage0CycleWitnesses? : Option (List FifteenStage0CycleWitness) := do
  let cycles ← stage0Cycles?
  let orbits ← stage0Orbits?
  let groups ← orbits.mapM fun orbit =>
    if orbit.excluded then
      orbit.cases.mapM fun (assignment, cycleId) => do
        let edges ← cycles[cycleId]?
        pure {
          pattern := orbit.pattern
          assignment := assignment
          steps := edges.map fun edge =>
            (edge.source, edge.target, edge.kind)
        }
    else
      pure []
  pure groups.flatten

/-- The assignment-specific Stage 0 negative-cycle witnesses decoded from the
checked source bundle.  They reference the 10,832 shared cycle encodings. -/
def fifteenStage0NegativeCycleWitnesses : List FifteenStage0CycleWitness :=
  (stage0CycleWitnesses?).getD []

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

private def stage0OrbitCertificateReplay : Bool := Id.run do
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

def FifteenStage0GraphChain (start : Nat) :
    List FifteenStage0GraphEdge → Nat → Prop
  | [], finish => finish = start
  | edge :: rest, finish =>
      edge.source = start ∧ FifteenStage0GraphChain edge.target rest finish

def FifteenStage0CycleStepWellFormed (step : Nat × Nat × Nat) : Prop :=
  step.1 < 15 ∧ step.2.1 < 15 ∧
    ((step.2.2 = 0 ∧ step.1 = step.2.1 + 1 ∧ step.2.1 < 14) ∨
      (step.2.2 = 1 ∧ step.1 > step.2.1) ∨
      (step.2.2 = 2 ∧ step.1 < step.2.1))

private def stage0CycleStepCheck (step : Nat × Nat × Nat) : Bool :=
  decide (step.1 < 15 ∧ step.2.1 < 15 ∧
    ((step.2.2 = 0 ∧ step.1 = step.2.1 + 1 ∧ step.2.1 < 14) ∨
      (step.2.2 = 1 ∧ step.1 > step.2.1) ∨
      (step.2.2 = 2 ∧ step.1 < step.2.1)))

private theorem stage0CycleStepCheck_sound
    (step : Nat × Nat × Nat)
    (hcheck : stage0CycleStepCheck step = true) :
    FifteenStage0CycleStepWellFormed step := by
  change (step.1 < 15 ∧ step.2.1 < 15 ∧
    ((step.2.2 = 0 ∧ step.1 = step.2.1 + 1 ∧ step.2.1 < 14) ∨
      (step.2.2 = 1 ∧ step.1 > step.2.1) ∨
      (step.2.2 = 2 ∧ step.1 < step.2.1)))
  exact of_decide_eq_true hcheck

private def stage0CycleWitnessStepsCheck
    (witness : FifteenStage0CycleWitness) : Bool :=
  witness.steps.all stage0CycleStepCheck

private def stage0CycleWitnessLabelsCheck
    (witness : FifteenStage0CycleWitness) : Bool :=
  let labels := stage0Labels witness.pattern witness.assignment
  decide (∀ i : Fin 15, labels[i.1]! < 4)

/-- The finite radial-type label attached to a sorted center by a Stage 0
pattern/assignment.  The modulo makes this a total `Fin 4`-valued function;
certificate soundness separately proves that the unwrapped label is below 4. -/
def fifteenStage0CycleWitnessLabel
    (witness : FifteenStage0CycleWitness) (i : Fin 15) : Nat :=
  (stage0Labels witness.pattern witness.assignment)[i.1]!

private def stage0CycleWitnessShapeCheck
    (witness : FifteenStage0CycleWitness) : Bool :=
  stage0CycleWitnessStepsCheck witness &&
    stage0CycleWitnessLabelsCheck witness

def FifteenStage0CycleWitnessShapeCertified
    (witness : FifteenStage0CycleWitness) : Prop :=
  (∀ step ∈ witness.steps, FifteenStage0CycleStepWellFormed step) ∧
    (∀ i : Fin 15, fifteenStage0CycleWitnessLabel witness i < 4)

private theorem stage0CycleWitnessShapeCheck_sound
    (witness : FifteenStage0CycleWitness)
    (hcheck : stage0CycleWitnessShapeCheck witness = true) :
    FifteenStage0CycleWitnessShapeCertified witness := by
  simp only [stage0CycleWitnessShapeCheck, Bool.and_eq_true] at hcheck
  constructor
  · intro step hstep
    have hs := (List.all_eq_true.mp hcheck.1) step hstep
    exact stage0CycleStepCheck_sound step hs
  · intro i
    have hlabels := of_decide_eq_true hcheck.2
    simpa [fifteenStage0CycleWitnessLabel] using hlabels i

def fifteenStage0CycleWitnessTypeIndex
    (witness : FifteenStage0CycleWitness) (i : Fin 15) : Fin 4 :=
  let label := fifteenStage0CycleWitnessLabel witness i
  ⟨label % 4, Nat.mod_lt label (by omega)⟩

def FifteenStage0GraphChainCheck (start : Nat) :
    List FifteenStage0GraphEdge → Nat → Bool
  | [], finish => decide (finish = start)
  | edge :: rest, finish =>
      decide (edge.source = start) &&
        FifteenStage0GraphChainCheck edge.target rest finish

theorem fifteenStage0GraphChainCheck_correct (start finish : Nat)
    (edges : List FifteenStage0GraphEdge) :
    FifteenStage0GraphChainCheck start edges finish = true ↔
      FifteenStage0GraphChain start edges finish := by
  induction edges generalizing start finish with
  | nil => simp [FifteenStage0GraphChainCheck, FifteenStage0GraphChain]
  | cons edge rest ih =>
      simp [FifteenStage0GraphChainCheck, FifteenStage0GraphChain, ih]

def fifteenStage0CycleWitnessCheck
    (witness : FifteenStage0CycleWitness) : Bool :=
  let edges := fifteenStage0CycleWitnessEdges witness
  let start := (edges.headD ⟨0, 0, 0⟩).source
  decide (edges ≠ []) &&
    FifteenStage0GraphChainCheck start edges start &&
    decide ((edges.map fun edge => edge.weight).sum < 0)

def FifteenStage0NegativeCycleWitnessCertified
    (witness : FifteenStage0CycleWitness) : Prop :=
  fifteenStage0CycleWitnessCheck witness = true

theorem fifteenStage0CycleWitnessCheck_sound
    (witness : FifteenStage0CycleWitness)
    (hcheck : fifteenStage0CycleWitnessCheck witness = true) :
    let edges := fifteenStage0CycleWitnessEdges witness
    let start := (edges.headD ⟨0, 0, 0⟩).source
    edges ≠ [] ∧ FifteenStage0GraphChain start edges start ∧
      (edges.map fun edge => edge.weight).sum < 0 := by
  simp only [fifteenStage0CycleWitnessCheck, Bool.and_eq_true] at hcheck
  constructor
  · exact of_decide_eq_true hcheck.1.1
  constructor
  · exact (fifteenStage0GraphChainCheck_correct _ _ _).mp hcheck.1.2
  · exact of_decide_eq_true hcheck.2

private def stage0CycleWitnessCertificateReplay : Bool :=
  fifteenStage0NegativeCycleWitnesses.all fifteenStage0CycleWitnessCheck

private def stage0CycleWitnessShapeReplay : Bool :=
  fifteenStage0NegativeCycleWitnesses.all stage0CycleWitnessShapeCheck

private def stage0CertificateReplay : Bool :=
  stage0OrbitCertificateReplay &&
    (stage0CycleWitnessCertificateReplay && stage0CycleWitnessShapeReplay)

def fifteenStage0CertificateReplay : Bool := stage0CertificateReplay

def fifteenStage0OrbitCountByWeight : List Nat :=
  [5, 6, 7, 8].map fun k =>
    (fifteenStage0OrbitWords.filter fun word =>
      (stage0InnerPositions word).length == k).length

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

theorem fifteenStage0ListSumMapLeReal {α : Type} (items : List α)
    (f g : α → ℝ) (h : ∀ item ∈ items, f item ≤ g item) :
    (items.map f).sum ≤ (items.map g).sum := by
  induction items with
  | nil => simp
  | cons item rest ih =>
      simp only [List.map_cons, List.sum_cons]
      exact add_le_add (h item (by simp))
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

private def stage0RealPotentialDifference (potential : Nat → ℝ)
    (edge : FifteenStage0GraphEdge) : ℝ :=
  potential edge.target - potential edge.source

theorem fifteenStage0GraphChain_real_telescope
    (potential : Nat → ℝ) (start finish : Nat)
    (edges : List FifteenStage0GraphEdge)
    (hchain : FifteenStage0GraphChain start edges finish) :
    (edges.map (stage0RealPotentialDifference potential)).sum =
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
      simp only [stage0RealPotentialDifference]
      ring

/-- A real-valued angle assignment satisfying every weighted edge inequality
cannot realize a negative closed walk.  The edge weights may be integer ticks
cast to `ℝ`; the only semantic input is the per-edge upper bound. -/
theorem fifteenStage0GraphChain_real_potential_excludes
    (potential : Nat → ℝ) (start : Nat)
    (edges : List FifteenStage0GraphEdge)
    (hchain : FifteenStage0GraphChain start edges start)
    (hnegative : (edges.map fun edge => (edge.weight : ℝ)).sum < 0)
    (hpotential : ∀ edge ∈ edges,
      potential edge.target ≤ potential edge.source + (edge.weight : ℝ)) :
    False := by
  have hterm : ∀ edge ∈ edges,
      stage0RealPotentialDifference potential edge ≤ (edge.weight : ℝ) := by
    intro edge hedge
    have h := hpotential edge hedge
    dsimp [stage0RealPotentialDifference]
    linarith
  have hsum := fifteenStage0ListSumMapLeReal edges
    (stage0RealPotentialDifference potential)
    (fun edge => (edge.weight : ℝ)) hterm
  have htelescope := fifteenStage0GraphChain_real_telescope
    potential start start edges hchain
  rw [htelescope] at hsum
  simp at hsum
  linarith

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem fifteenStage0Certificate_replays : fifteenStage0CertificateReplay = true := by
  native_decide

/-- Every excluded assignment in the Stage 0 table has an explicit, Lean-
reconstructed negative closed walk; this is the Prop-level interface consumed
by the geometric soundness theorem in `FifteenStageZeroGeometry`. -/
theorem fifteenStage0NegativeCycleWitnesses_certified :
    ∀ witness ∈ fifteenStage0NegativeCycleWitnesses,
      FifteenStage0NegativeCycleWitnessCertified witness := by
  have h := fifteenStage0Certificate_replays
  unfold fifteenStage0CertificateReplay stage0CertificateReplay
    stage0CycleWitnessCertificateReplay at h
  simp only [Bool.and_eq_true] at h
  intro witness hw
  have hcheck := (List.all_eq_true.mp h.2.1) witness hw
  simpa [FifteenStage0NegativeCycleWitnessCertified] using hcheck

theorem fifteenStage0NegativeCycleWitnesses_shape_certified :
    ∀ witness ∈ fifteenStage0NegativeCycleWitnesses,
      FifteenStage0CycleWitnessShapeCertified witness := by
  have h := fifteenStage0Certificate_replays
  unfold fifteenStage0CertificateReplay stage0CertificateReplay at h
  simp only [Bool.and_eq_true] at h
  intro witness hw
  have hcheck := (List.all_eq_true.mp h.2.2) witness hw
  exact stage0CycleWitnessShapeCheck_sound witness hcheck

/-- A checked Stage 0 negative cycle rules out every real angle potential
satisfying its reconstructed difference constraints. -/
theorem fifteenStage0NegativeCycleWitness_no_real_potential
    (witness : FifteenStage0CycleWitness)
    (hwitness : witness ∈ fifteenStage0NegativeCycleWitnesses)
    (potential : Nat → ℝ)
    (hpotential : ∀ edge ∈ fifteenStage0CycleWitnessEdges witness,
      potential edge.target ≤ potential edge.source + (edge.weight : ℝ)) :
    False := by
  have hcert := fifteenStage0NegativeCycleWitnesses_certified witness hwitness
  rcases fifteenStage0CycleWitnessCheck_sound witness hcert with
    ⟨_hne, hchain, hnegative⟩
  have hnegativeReal :
      ((fifteenStage0CycleWitnessEdges witness).map
        (fun edge => (edge.weight : ℝ))).sum < 0 := by
    let edges := fifteenStage0CycleWitnessEdges witness
    have hnegativeInt :
        (edges.map fun edge => edge.weight).sum < 0 := by
      simpa [edges] using hnegative
    have hcast :
        (edges.map fun edge => (edge.weight : ℝ)).sum =
          (((edges.map fun edge => edge.weight).sum : Int) : ℝ) := by
      induction edges with
      | nil => simp
      | cons edge rest ih => simp [ih]
    calc
      (edges.map fun edge => (edge.weight : ℝ)).sum =
          (((edges.map fun edge => edge.weight).sum : Int) : ℝ) := hcast
      _ < 0 := by exact_mod_cast hnegativeInt
  exact fifteenStage0GraphChain_real_potential_excludes potential
    ((fifteenStage0CycleWitnessEdges witness).headD ⟨0, 0, 0⟩).source
    (fifteenStage0CycleWitnessEdges witness) hchain hnegativeReal hpotential

theorem fifteenStage0CoarseAngleTable_replays :
    fifteenStage0CoarseAngleTableReplay = true := by
  native_decide

theorem fifteenStage0DihedralClassCounts :
    fifteenStage0OrbitWords.length = 760 ∧
      fifteenStage0OrbitCountByWeight = [111, 185, 232, 232] := by
  native_decide

theorem fifteenStage0CanonicalCoverage_replays :
    fifteenStage0CanonicalCoverageReplay = true := by
  native_decide

theorem fifteenStage0CanonicalWord_mem_orbitWords
    (mask : Nat) (hmask : mask < 32768)
    (hweight : 5 ≤ stage0MaskWeight mask ∧ stage0MaskWeight mask ≤ 8) :
    stage0MaskWord (stage0CanonicalMask mask) ∈ fifteenStage0OrbitWords := by
  have hmem : mask ∈ List.range 32768 := by simp; omega
  have hcoverage := (List.all_eq_true.mp
    fifteenStage0CanonicalCoverage_replays) mask hmem
  let canonical := stage0CanonicalMask mask
  have hproperties : canonical < 32768 ∧
    stage0MaskWeight canonical = stage0MaskWeight mask ∧
      stage0CanonicalMask canonical = canonical := by
    have hparts :
        (decide (canonical < 32768) = true ∧
          (stage0MaskWeight canonical == stage0MaskWeight mask) = true) ∧
        (stage0CanonicalMask canonical == canonical) = true := by
      simpa [hweight, canonical, Bool.and_eq_true, beq_iff_eq] using hcoverage
    rcases hparts with ⟨⟨hcanonical, hweightEq⟩, hfixed⟩
    refine ⟨of_decide_eq_true hcanonical, ?_, ?_⟩
    · simpa [beq_iff_eq] using hweightEq
    · simpa [beq_iff_eq] using hfixed
  have hcanonicalWeight :
      5 ≤ stage0MaskWeight canonical ∧ stage0MaskWeight canonical ≤ 8 := by
    rw [hproperties.2.1]
    exact hweight
  have hcanonicalMem : canonical ∈ List.range 32768 := by
    simp only [List.mem_range]
    exact hproperties.1
  have hfiltered : canonical ∈ List.filter (fun candidate =>
      let weight := stage0MaskWeight candidate
      5 ≤ weight && weight ≤ 8 &&
        stage0CanonicalMask candidate == candidate) (List.range 32768) := by
    apply List.mem_filter.mpr
    refine ⟨hcanonicalMem, ?_⟩
    simp [hcanonicalWeight, hproperties.2.2]
  change stage0MaskWord canonical ∈
    List.map stage0MaskWord (List.filter (fun candidate =>
      let weight := stage0MaskWeight candidate
      5 ≤ weight && weight ≤ 8 &&
        stage0CanonicalMask candidate == candidate) (List.range 32768))
  exact List.mem_map.mpr ⟨canonical, hfiltered, rfl⟩

end CirclePacking
