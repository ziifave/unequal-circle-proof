import CirclePacking.FifteenStageZero
import CirclePacking.FifteenTickSoundness

/-!
# Independent Lean replay of the 378 → 23 → 4 radial-pattern stages

The C++ search is not imported or called here. Lean reconstructs both radial
type systems, enumerates every type assignment with the published necessary
prunings, and runs the integer difference-constraint test itself. The resulting
classification is compared against the checked-in stage tables. The rational
angle-tick tables used by those searches are also replayed here.

This closes the finite *classification computation* in Lean. The geometric
interpretation of every branch-pruning condition remains part of the paper's
separate geometric reduction.
-/

namespace CirclePacking

private def stage34N : Nat := 15
private def stage34TwoPiUpper : Nat := 17600

private def stage34Bins3 : Array FifteenInterval := #[
  (fifteenRational 0 1, fifteenRational 1 2),
  (fifteenRational 1 2, fifteenRational 1 1),
  (fifteenRational 1 1, fifteenRational 3 2),
  (fifteenRational 3 2, fifteenRational 8 5),
  (fifteenRational 8 5, fifteenRational 5 3),
  (fifteenRational 5 3, fifteenRational 2 1),
  (fifteenRational 2 1, fifteenRational 2385432 1000000),
  (fifteenRational 35213569647 10000000000,
    fifteenRational 35213569648 10000000000)
]

private def stage34Bins4 : Array FifteenInterval := #[
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

private def stage34Q3 : Array (Array Nat) := #[
  #[8700,8700,8700,6746,6142,4047,0,0],
  #[8700,8700,5105,4784,4585,3690,1738,0],
  #[8700,5105,4086,3923,3818,3321,2720,0],
  #[6746,4784,3923,3780,3688,3245,2744,0],
  #[6142,4585,3818,3688,3603,3194,2727,656],
  #[4047,3690,3321,3245,3194,2932,2609,868],
  #[0,1738,2720,2744,2727,2609,2422,1383],
  #[0,0,0,0,656,868,1383,1612]
]

private def stage34Q4 : Array (Array Nat) := #[
  #[8700,8700,8700,6746,6142,5883,4896,4047,0,0,0,0],
  #[8700,8700,5105,4784,4585,4488,4077,3690,3228,2344,1738,0],
  #[8700,5105,4086,3923,3818,3767,3541,3321,3105,2889,2720,0],
  #[6746,4784,3923,3780,3688,3642,3442,3245,3051,2856,2744,0],
  #[6142,4585,3818,3688,3603,3561,3376,3194,3014,2832,2727,656],
  #[5883,4488,3767,3642,3561,3521,3344,3169,2994,2819,2717,868],
  #[4896,4077,3541,3442,3376,3344,3198,3051,2904,2754,2668,950],
  #[4047,3690,3321,3245,3194,3169,3051,2932,2809,2682,2609,1214],
  #[0,3228,3105,3051,3014,2994,2904,2809,2709,2604,2541,1383],
  #[0,2344,2889,2856,2832,2819,2754,2682,2604,2518,2467,1499],
  #[0,1738,2720,2744,2727,2717,2668,2609,2541,2467,2422,1579],
  #[0,0,0,0,656,868,950,1214,1383,1499,1579,1612]
]

private structure Stage34Config where
  bins : Array FifteenInterval
  q : Array (Array Nat)
  typeCount : Nat
  outerLabel : Nat
  unassignedLabel : Nat
  exactZeroLabel : Nat
  highThreshold : Nat
  high2Threshold : Nat
  exactConflictThreshold : Nat
  deriving Inhabited

private def stage34Config3 : Stage34Config :=
  ⟨stage34Bins3, stage34Q3, 7, 7, 8, 9, 5, 6, 6⟩

private def stage34Config4 : Stage34Config :=
  ⟨stage34Bins4, stage34Q4, 11, 11, 12, 13, 5, 8, 8⟩

private def stage34PositionsAux : Nat → List Char → List Nat
  | _, [] => []
  | i, c :: rest =>
      (if c == '1' then [i] else []) ++ stage34PositionsAux (i + 1) rest

private def stage34Positions (pattern : String) : List Nat :=
  stage34PositionsAux 0 pattern.toList

private structure Stage34Edge where
  source : Nat
  target : Nat
  weight : Int32
  deriving Repr

private def stage34PairQ (config : Stage34Config) (labels : Array Nat)
    (i j : Nat) : Nat := Id.run do
  let a := labels[i]!
  let b := labels[j]!
  if a >= config.bins.size || b >= config.bins.size then return 0
  return (config.q[a]!)[b]!

private def stage34GraphEdges (config : Stage34Config)
    (labels : Array Nat) : Array Stage34Edge := Id.run do
  let mut edges : Array Stage34Edge := #[]
  for i in [:14] do
    edges := edges.push ⟨i + 1, i, 0⟩
  for i in [:stage34N] do
    for offset in [:14 - i] do
      let j := i + offset + 1
      let q := stage34PairQ config labels i j
      edges := edges.push ⟨j, i, -(Int32.ofNat q)⟩
      edges := edges.push ⟨i, j, Int32.ofNat (stage34TwoPiUpper - q)⟩
  return edges

private def stage34RelaxToPotential (config : Stage34Config)
    (labels : Array Nat) (seed : Array Int32) : Option (Array Int32) := Id.run do
  let edges := stage34GraphEdges config labels
  let mut distances := seed
  let mut stable := false
  for _pass in [:stage34N] do
    if !stable then
      let mut changed := false
      for edge in edges do
        let candidate := distances[edge.source]! + edge.weight
        if candidate < distances[edge.target]! then
          distances := distances.set! edge.target candidate
          changed := true
      if !changed then stable := true
  if stable then return some distances
  return none

private structure Stage34State where
  labels : Array Nat
  small : Nat
  high : Nat
  high2 : Nat

private def stage34StructurallyPruned (config : Stage34Config) (inner remaining : List Nat)
    (state : Stage34State) : Bool := Id.run do
  let k := inner.length
  let originConflict := inner.any (fun p => state.labels[p]! == config.exactZeroLabel) &&
    inner.any (fun p => state.labels[p]! < config.exactConflictThreshold &&
      state.labels[p]! != config.exactZeroLabel)
  if originConflict then return true
  if state.small > 1 then return true
  if state.high + remaining.length < k - 4 then return true
  if state.high2 + remaining.length < max 0 (k - 5) then return true
  if state.small == 1 then
    let zero := (List.range stage34N).any (fun i =>
      state.labels[i]! == 0 || state.labels[i]! == config.exactZeroLabel)
    let mone := (List.range stage34N).any (fun i => state.labels[i]! == 2)
    if zero && mone then return true
  return false

private def stage34NextState (config : Stage34Config) (state : Stage34State)
    (position label : Nat) : Stage34State :=
  { labels := state.labels.set! position label,
    small := state.small + (if label == config.exactZeroLabel || label <= 1 then 1 else 0),
    high := state.high + (if label >= config.highThreshold && label < config.typeCount then 1 else 0),
    high2 := state.high2 + (if label >= config.high2Threshold && label < config.typeCount then 1 else 0) }

private def stage34Choices (config : Stage34Config) : List Nat :=
  [0, config.exactZeroLabel] ++ (List.range (config.typeCount - 1)).map (· + 1)

private def stage34Search (config : Stage34Config) (inner remaining : List Nat)
    (state : Stage34State) (potential : Array Int32) : Bool := Id.run do
  if stage34StructurallyPruned config inner remaining state then return false
  let depth := inner.length - remaining.length
  let feasiblePotential :=
    if depth >= 3 then stage34RelaxToPotential config state.labels potential
    else some potential
  match feasiblePotential with
  | none => return false
  | some nextPotential =>
      match remaining with
      | [] => return true
      | position :: rest =>
          return (stage34Choices config).any fun label =>
            stage34Search config inner rest
              (stage34NextState config state position label) nextPotential
termination_by remaining.length
decreasing_by simp_wf

private def stage34HasFeasibleAssignment (config : Stage34Config)
    (pattern : String) : Bool := Id.run do
  let inner := stage34Positions pattern
  let state : Stage34State :=
    ⟨Array.replicate stage34N config.outerLabel, 0, 0, 0⟩
  let mut labels := state.labels
  for p in inner do
    labels := labels.set! p config.unassignedLabel
  return stage34Search config inner inner { state with labels := labels }
    (Array.replicate stage34N (Int32.ofNat 0))

private def stage34ParseRows (source : String) : List (String × Bool) :=
  (source.splitOn "\n").filterMap fun line =>
    match line.splitOn "\t" with
    | status :: _k :: pattern :: _ =>
        if status == "UNKNOWN" then some (pattern, true)
        else if status == "CLOSED" then some (pattern, false)
        else none
    | _ => none

private def stage34SamePatterns (xs ys : List String) : Bool :=
  xs.length == ys.length && xs.length == xs.eraseDups.length &&
    ys.length == ys.eraseDups.length && xs.all ys.contains && ys.all xs.contains

private def stage34Matches (config : Stage34Config) (patterns : List String)
    (rows : List (String × Bool)) : Bool := Id.run do
  let keys := rows.map Prod.fst
  if !stage34SamePatterns patterns keys then return false
  return rows.all fun (pattern, expected) =>
    stage34HasFeasibleAssignment config pattern == expected

private def stage34PairTickValid (config : Stage34Config) (i j : Nat) : Bool :=
  let q := (config.q[i]!)[j]!
  let x := config.bins[i]!
  let y := config.bins[j]!
  if q == 0 then true
  else if decide (x.2 + y.2 < 2) then
    i < 2 && j < 2 && q == 8700
  else
    fifteenTickCertificateValid x y (i == 0 || j == 0) false q

private def stage34TableValid (config : Stage34Config) : Bool :=
  config.bins.size == config.q.size &&
    (List.range config.bins.size).all fun i =>
      config.q[i]!.size == config.bins.size &&
        (List.range config.bins.size).all fun j =>
          stage34PairTickValid config i j

private def stage34Stage3Source : String :=
  include_str "../../../../research/fifteen_equal_completion/candidate_bundle/stage3.tsv"

private def stage34Stage4Source : String :=
  include_str "../../../../research/fifteen_equal_completion/candidate_bundle/stage4.tsv"

private def stage34Rows3 : List (String × Bool) := stage34ParseRows stage34Stage3Source
private def stage34Rows4 : List (String × Bool) := stage34ParseRows stage34Stage4Source

def fifteenStage3Replay : Bool := Id.run do
  let input := fifteenStage0SurvivorPatterns
  if input.length != 378 then return false
  if !stage34TableValid stage34Config3 then return false
  if !stage34Matches stage34Config3 input stage34Rows3 then return false
  let survivors := stage34Rows3.filterMap fun (pattern, alive) =>
    if alive then some pattern else none
  return survivors.length == 23 &&
    (stage34Rows3.filter fun row => !row.2).length == 355

def fifteenStage4Replay : Bool := Id.run do
  if !fifteenStage3Replay then return false
  let input := stage34Rows3.filterMap fun (pattern, alive) =>
    if alive then some pattern else none
  if input.length != 23 then return false
  if !stage34TableValid stage34Config4 then return false
  if !stage34Matches stage34Config4 input stage34Rows4 then return false
  let survivors := stage34Rows4.filterMap fun (pattern, alive) =>
    if alive then some pattern else none
  return survivors.length == 4 &&
    (stage34Rows4.filter fun row => !row.2).length == 19

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem fifteenStage4Certificate_replays : fifteenStage4Replay = true := by
  native_decide

theorem fifteenStage3Certificate_replays : fifteenStage3Replay = true := by
  have h := fifteenStage4Certificate_replays
  by_contra hfalse
  have hzero : fifteenStage4Replay = false := by
    simp [fifteenStage4Replay, hfalse]
  rw [hzero] at h
  contradiction

end CirclePacking
