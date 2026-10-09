import CirclePacking.FifteenStage4Table

/-!
# Generic checker for compact Stage 4 pruning certificates

Each certificate is a prefix tree over the twelve Stage 4 choices at every
inner position.  Structural leaves record a small-count, origin, rank, or
mixed-bin contradiction.  A cycle leaf refers to a dictionary entry containing
only its directed edge topology; Lean recomputes the edge weights from the
current radial labels and checks topology and strict negativity.

The checker never runs a graph search.  The C++ producer is outside the trust
boundary: every branch, leaf reason, cycle edge, and integer cycle sum is
replayed here.  Connecting these abstract exclusions to the geometric packing
model remains a separate soundness obligation.
-/

namespace CirclePacking

private def s4N : Nat := 15
private def s4TwoPi : Nat := 17600

private def s4InnerPositions (pattern : String) : Array Nat :=
  ((List.range s4N).filter fun i => pattern.toList[i]? == some '1').toArray

private def s4PatternValid (pattern : String) : Bool :=
  let bits := pattern.toList
  bits.length == s4N &&
    bits.all (fun c => c == '0' || c == '1') &&
    let count := bits.filter (· == '1') |>.length
    5 ≤ count && count ≤ 8

private structure S4State where
  labels : Array Nat
  depth : Nat
  small : Nat
  high : Nat
  high2 : Nat
  deriving Inhabited

private structure S4CertEdge where
  source : Nat
  target : Nat
  kind : Char

private structure S4WeightedEdge where
  source : Nat
  target : Nat
  kind : Char
  ticks : Nat

private def s4Initial (pattern : String) : S4State := Id.run do
  let bits := pattern.toList.toArray
  let labels := (Array.range s4N).map fun i =>
    if bits[i]? == some '1' then 12 else 11
  return ⟨labels, 0, 0, 0, 0⟩

private def s4SmallReason (s : S4State) : Bool := s.small > 1

private def s4OriginReason (inner : Array Nat) (s : S4State) : Bool :=
  (inner.toList.any fun p => s.labels[p]! == 13) &&
  (inner.toList.any fun p => s.labels[p]! < 8 && s.labels[p]! != 13)

private def s4RankReason (inner : Array Nat) (s : S4State) : Bool :=
  let remaining := inner.size - s.depth
  s.high + remaining < inner.size - 4 ||
    s.high2 + remaining < max 0 (inner.size - 5)

private def s4MixedReason (s : S4State) : Bool := Id.run do
  if s.small != 1 then return false
  let hasZero := s.labels.toList.any (fun t => t == 0 || t == 13)
  let hasTwo := s.labels.toList.any (fun t => t == 2)
  return hasZero && hasTwo

private def s4StructurallyPruned (inner : Array Nat) (s : S4State) : Bool :=
  s4SmallReason s || s4OriginReason inner s || s4RankReason inner s ||
    s4MixedReason s

private def s4PairTick (labels : Array Nat) (i j : Nat) : Nat := Id.run do
  let a := labels[i]!
  let b := labels[j]!
  if a >= 12 || b >= 12 then return 0
  return (fifteenStage4Q[a]!)[b]!

private def s4Digit? (c : Char) : Option Nat :=
  let n := c.toNat
  if 48 ≤ n && n ≤ 57 then some (n - 48)
  else if 65 ≤ n && n ≤ 70 then some (n - 65 + 10)
  else none

private def s4Decode64? (c : Char) : Option Nat :=
  if '0' ≤ c && c ≤ '9' then some (c.toNat - 48)
  else if 'A' ≤ c && c ≤ 'Z' then some (c.toNat - 65 + 10)
  else if 'a' ≤ c && c ≤ 'z' then some (c.toNat - 97 + 36)
  else if c == '-' then some 62
  else if c == '_' then some 63
  else none

private def s4ParseCycleId? : List Char → Option (Nat × List Char)
  | a :: b :: rest => do
      let hi ← s4Decode64? a
      let lo ← s4Decode64? b
      some (hi * 64 + lo, rest)
  | _ => none

private def s4ParseEdges : Nat → List Char → Option (List S4CertEdge × List Char)
  | 0, rest => some ([], rest)
  | n + 1, sourceChar :: targetChar :: kind :: rest => do
      let source ← s4Digit? sourceChar
      let target ← s4Digit? targetChar
      let (edges, tail) ← s4ParseEdges n rest
      some (⟨source, target, kind⟩ :: edges, tail)
  | _ + 1, _ => none
termination_by n _ => n

private def s4ParseCycle? (text : String) : Option (List S4CertEdge) := do
  let chars := text.toList
  guard (chars.length % 3 == 0)
  let (edges, rest) ← s4ParseEdges (chars.length / 3) chars
  guard rest.isEmpty
  some edges

private def s4ParseCycleDictionary? (text : String) : Option (Array (List S4CertEdge)) := do
  guard (text != "")
  let cycles ← (text.splitOn ";").mapM s4ParseCycle?
  some cycles.toArray

private def s4EdgeTick (labels : Array Nat) (e : S4CertEdge) : Nat := Id.run do
  if e.kind == 'O' then return 0
  if e.kind == 'L' then return s4PairTick labels e.target e.source
  if e.kind == 'U' then return s4PairTick labels e.source e.target
  return 0

private def s4MaterializeEdge (labels : Array Nat) (e : S4CertEdge) : S4WeightedEdge :=
  ⟨e.source, e.target, e.kind, s4EdgeTick labels e⟩

private def s4EdgeShape (e : S4WeightedEdge) : Bool :=
  decide (e.source < s4N) && decide (e.target < s4N) && decide (e.ticks ≤ 8790) &&
    (if e.kind == 'O' then
      decide (e.source == e.target + 1) && decide (e.target < 14) && decide (e.ticks == 0)
    else if e.kind == 'L' then decide (e.source > e.target)
    else if e.kind == 'U' then decide (e.source < e.target)
    else false)

private def s4EdgeWeight (e : S4WeightedEdge) : Int :=
  if e.kind == 'O' then 0
  else if e.kind == 'L' then -(Int.ofNat e.ticks)
  else Int.ofNat (s4TwoPi - e.ticks)

private def s4LinkValid : List S4WeightedEdge → Bool
  | [] => true
  | [_] => true
  | first :: second :: rest =>
      decide (first.target == second.source) && s4LinkValid (second :: rest)

private def s4EndsClosed (edges : List S4WeightedEdge) : Bool :=
  match edges.head?, edges.getLast? with
  | some first, some last => decide (last.target == first.source)
  | _, _ => false

private def s4Weight (edges : List S4WeightedEdge) : Int :=
  edges.foldl (fun total edge => total + s4EdgeWeight edge) 0

private def s4CycleValid (labels : Array Nat) (edges : List S4CertEdge) : Bool := Id.run do
  let materialized := edges.map (s4MaterializeEdge labels)
  return decide (2 ≤ edges.length) && decide (edges.length ≤ 15) &&
    materialized.all s4EdgeShape &&
    s4LinkValid materialized && s4EndsClosed materialized &&
    decide (s4Weight materialized < 0)

private def s4Next (inner : Array Nat) (s : S4State) (label : Nat) : S4State := Id.run do
  let p := inner[s.depth]!
  return {
    labels := s.labels.set! p label,
    depth := s.depth + 1,
    small := s.small + (if label <= 1 || label == 13 then 1 else 0),
    high := s.high + (if label >= 5 && label <= 10 then 1 else 0),
    high2 := s.high2 + (if label >= 8 && label <= 10 then 1 else 0)
  }

private def s4CheckStream : Nat → Array Nat → Array (List S4CertEdge) →
    S4State → List Char → Option (List Char)
  | 0, _, _, _, 'B' :: _ => none
  | _, _, _, s, 'S' :: rest => if s4SmallReason s then some rest else none
  | _, inner, _, s, 'O' :: rest => if s4OriginReason inner s then some rest else none
  | _, inner, _, s, 'R' :: rest => if s4RankReason inner s then some rest else none
  | _, _, _, s, 'M' :: rest => if s4MixedReason s then some rest else none
  | _, inner, cycles, s, 'C' :: refHi :: refLo :: rest => do
      let (id, tail) ← s4ParseCycleId? (refHi :: refLo :: rest)
      let edges ← cycles[id]?
      if s.depth >= 3 && !s4StructurallyPruned inner s &&
          s4CycleValid s.labels edges then some tail else none
  | fuel + 1, inner, cycles, s, 'B' :: rest => do
      if s.depth >= inner.size || s4StructurallyPruned inner s then none else do
        let tail ← s4CheckStream fuel inner cycles (s4Next inner s 0) rest
        let tail ← s4CheckStream fuel inner cycles (s4Next inner s 13) tail
        let tail ← s4CheckStream fuel inner cycles (s4Next inner s 1) tail
        let tail ← s4CheckStream fuel inner cycles (s4Next inner s 2) tail
        let tail ← s4CheckStream fuel inner cycles (s4Next inner s 3) tail
        let tail ← s4CheckStream fuel inner cycles (s4Next inner s 4) tail
        let tail ← s4CheckStream fuel inner cycles (s4Next inner s 5) tail
        let tail ← s4CheckStream fuel inner cycles (s4Next inner s 6) tail
        let tail ← s4CheckStream fuel inner cycles (s4Next inner s 7) tail
        let tail ← s4CheckStream fuel inner cycles (s4Next inner s 8) tail
        let tail ← s4CheckStream fuel inner cycles (s4Next inner s 9) tail
        s4CheckStream fuel inner cycles (s4Next inner s 10) tail
  | _, _, _, _, _ => none
termination_by fuel _ _ _ _ => fuel

private structure S4CertificateRecord where
  pattern : String
  cycles : Array (List S4CertEdge)
  stream : String

private def s4ParseRecord? (line : String) : Option S4CertificateRecord := do
  match line.splitOn "\t" with
  | [pattern, cycleText, stream] => do
      guard (s4PatternValid pattern)
      let cycles ← s4ParseCycleDictionary? cycleText
      some ⟨pattern, cycles, stream⟩
  | _ => none

private def s4ParseBatch? (source : String) : Option (List S4CertificateRecord) := do
  let lines := (source.splitOn "\n").filter (· != "")
  guard (!lines.isEmpty)
  lines.mapM s4ParseRecord?

private def s4RecordValid (record : S4CertificateRecord) : Bool := Id.run do
  let inner := s4InnerPositions record.pattern
  match s4CheckStream inner.size inner record.cycles (s4Initial record.pattern)
      record.stream.toList with
  | some [] => return true
  | _ => return false

/-- Replay all branch coverage and prune witnesses, matching the declared IDs. -/
def fifteenStage4CheckBatch (source : String) (expectedPatterns : List String) : Bool :=
  match s4ParseBatch? source with
  | some records =>
      let patterns := records.map (·.pattern)
      patterns == expectedPatterns &&
        patterns.eraseDups.length == patterns.length && records.all s4RecordValid
  | none => false

end CirclePacking
