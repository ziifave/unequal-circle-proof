import CirclePacking.FifteenStage3Table

/-!
# Generic checker for compact Stage 3 pruning certificates

Each certificate is a prefix tree over the eight radial-bin choices at every
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

private def s3N : Nat := 15
private def s3TwoPi : Nat := 17600

private def s3InnerPositions (pattern : String) : Array Nat :=
  ((List.range s3N).filter fun i => pattern.toList[i]? == some '1').toArray

private def s3PatternValid (pattern : String) : Bool :=
  let bits := pattern.toList
  bits.length == s3N &&
    bits.all (fun c => c == '0' || c == '1') &&
    let count := bits.filter (· == '1') |>.length
    5 ≤ count && count ≤ 8

private structure S3State where
  labels : Array Nat
  depth : Nat
  small : Nat
  high : Nat
  high2 : Nat
  deriving Inhabited

private structure S3CertEdge where
  source : Nat
  target : Nat
  kind : Char

private structure S3WeightedEdge where
  source : Nat
  target : Nat
  kind : Char
  ticks : Nat

private def s3Initial (pattern : String) : S3State := Id.run do
  let bits := pattern.toList.toArray
  let labels := (Array.range s3N).map fun i =>
    if bits[i]? == some '1' then 8 else 7
  return ⟨labels, 0, 0, 0, 0⟩

private def s3SmallReason (s : S3State) : Bool := s.small > 1

private def s3OriginReason (inner : Array Nat) (s : S3State) : Bool :=
  (inner.toList.any fun p => s.labels[p]! == 9) &&
  (inner.toList.any fun p => s.labels[p]! < 6 && s.labels[p]! != 9)

private def s3RankReason (inner : Array Nat) (s : S3State) : Bool :=
  let remaining := inner.size - s.depth
  s.high + remaining < inner.size - 4 ||
    s.high2 + remaining < max 0 (inner.size - 5)

private def s3MixedReason (s : S3State) : Bool := Id.run do
  if s.small != 1 then return false
  let hasZero := s.labels.toList.any (fun t => t == 0 || t == 9)
  let hasTwo := s.labels.toList.any (fun t => t == 2)
  return hasZero && hasTwo

private def s3StructurallyPruned (inner : Array Nat) (s : S3State) : Bool :=
  s3SmallReason s || s3OriginReason inner s || s3RankReason inner s ||
    s3MixedReason s

private def s3PairTick (labels : Array Nat) (i j : Nat) : Nat := Id.run do
  let a := labels[i]!
  let b := labels[j]!
  if a >= 8 || b >= 8 then return 0
  return (fifteenStage3Q[a]!)[b]!

private def s3Digit? (c : Char) : Option Nat :=
  let n := c.toNat
  if 48 ≤ n && n ≤ 57 then some (n - 48)
  else if 65 ≤ n && n ≤ 70 then some (n - 65 + 10)
  else none

private def s3Decode64? (c : Char) : Option Nat :=
  if '0' ≤ c && c ≤ '9' then some (c.toNat - 48)
  else if 'A' ≤ c && c ≤ 'Z' then some (c.toNat - 65 + 10)
  else if 'a' ≤ c && c ≤ 'z' then some (c.toNat - 97 + 36)
  else if c == '-' then some 62
  else if c == '_' then some 63
  else none

private def s3ParseCycleId? : List Char → Option (Nat × List Char)
  | a :: b :: rest => do
      let hi ← s3Decode64? a
      let lo ← s3Decode64? b
      some (hi * 64 + lo, rest)
  | _ => none

private def s3ParseEdges : Nat → List Char → Option (List S3CertEdge × List Char)
  | 0, rest => some ([], rest)
  | n + 1, sourceChar :: targetChar :: kind :: rest => do
      let source ← s3Digit? sourceChar
      let target ← s3Digit? targetChar
      let (edges, tail) ← s3ParseEdges n rest
      some (⟨source, target, kind⟩ :: edges, tail)
  | _ + 1, _ => none
termination_by n _ => n

private def s3ParseCycle? (text : String) : Option (List S3CertEdge) := do
  let chars := text.toList
  guard (chars.length % 3 == 0)
  let (edges, rest) ← s3ParseEdges (chars.length / 3) chars
  guard rest.isEmpty
  some edges

private def s3ParseCycleDictionary? (text : String) : Option (Array (List S3CertEdge)) := do
  guard (text != "")
  let cycles ← (text.splitOn ";").mapM s3ParseCycle?
  some cycles.toArray

private def s3EdgeTick (labels : Array Nat) (e : S3CertEdge) : Nat := Id.run do
  if e.kind == 'O' then return 0
  if e.kind == 'L' then return s3PairTick labels e.target e.source
  if e.kind == 'U' then return s3PairTick labels e.source e.target
  return 0

private def s3MaterializeEdge (labels : Array Nat) (e : S3CertEdge) : S3WeightedEdge :=
  ⟨e.source, e.target, e.kind, s3EdgeTick labels e⟩

private def s3EdgeShape (e : S3WeightedEdge) : Bool :=
  decide (e.source < s3N) && decide (e.target < s3N) && decide (e.ticks ≤ 8790) &&
    (if e.kind == 'O' then
      decide (e.source == e.target + 1) && decide (e.target < 14) && decide (e.ticks == 0)
    else if e.kind == 'L' then decide (e.source > e.target)
    else if e.kind == 'U' then decide (e.source < e.target)
    else false)

private def s3EdgeWeight (e : S3WeightedEdge) : Int :=
  if e.kind == 'O' then 0
  else if e.kind == 'L' then -(Int.ofNat e.ticks)
  else Int.ofNat (s3TwoPi - e.ticks)

private def s3LinkValid : List S3WeightedEdge → Bool
  | [] => true
  | [_] => true
  | first :: second :: rest =>
      decide (first.target == second.source) && s3LinkValid (second :: rest)

private def s3EndsClosed (edges : List S3WeightedEdge) : Bool :=
  match edges.head?, edges.getLast? with
  | some first, some last => decide (last.target == first.source)
  | _, _ => false

private def s3Weight (edges : List S3WeightedEdge) : Int :=
  edges.foldl (fun total edge => total + s3EdgeWeight edge) 0

private def s3CycleValid (labels : Array Nat) (edges : List S3CertEdge) : Bool := Id.run do
  let materialized := edges.map (s3MaterializeEdge labels)
  return decide (2 ≤ edges.length) && decide (edges.length ≤ 15) &&
    materialized.all s3EdgeShape &&
    s3LinkValid materialized && s3EndsClosed materialized &&
    decide (s3Weight materialized < 0)

private def s3Next (inner : Array Nat) (s : S3State) (label : Nat) : S3State := Id.run do
  let p := inner[s.depth]!
  return {
    labels := s.labels.set! p label,
    depth := s.depth + 1,
    small := s.small + (if label <= 1 || label == 9 then 1 else 0),
    high := s.high + (if label >= 5 && label <= 6 then 1 else 0),
    high2 := s.high2 + (if label == 6 then 1 else 0)
  }

private def s3CheckStream : Nat → Array Nat → Array (List S3CertEdge) →
    S3State → List Char → Option (List Char)
  | 0, _, _, _, 'B' :: _ => none
  | _, _, _, s, 'S' :: rest => if s3SmallReason s then some rest else none
  | _, inner, _, s, 'O' :: rest => if s3OriginReason inner s then some rest else none
  | _, inner, _, s, 'R' :: rest => if s3RankReason inner s then some rest else none
  | _, _, _, s, 'M' :: rest => if s3MixedReason s then some rest else none
  | _, inner, cycles, s, 'C' :: refHi :: refLo :: rest => do
      let (id, tail) ← s3ParseCycleId? (refHi :: refLo :: rest)
      let edges ← cycles[id]?
      if s.depth >= 3 && !s3StructurallyPruned inner s &&
          s3CycleValid s.labels edges then some tail else none
  | fuel + 1, inner, cycles, s, 'B' :: rest => do
      if s.depth >= inner.size || s3StructurallyPruned inner s then none else do
        let tail ← s3CheckStream fuel inner cycles (s3Next inner s 0) rest
        let tail ← s3CheckStream fuel inner cycles (s3Next inner s 9) tail
        let tail ← s3CheckStream fuel inner cycles (s3Next inner s 1) tail
        let tail ← s3CheckStream fuel inner cycles (s3Next inner s 2) tail
        let tail ← s3CheckStream fuel inner cycles (s3Next inner s 3) tail
        let tail ← s3CheckStream fuel inner cycles (s3Next inner s 4) tail
        let tail ← s3CheckStream fuel inner cycles (s3Next inner s 5) tail
        s3CheckStream fuel inner cycles (s3Next inner s 6) tail
  | _, _, _, _, _ => none
termination_by fuel _ _ _ _ => fuel

private structure S3CertificateRecord where
  pattern : String
  cycles : Array (List S3CertEdge)
  stream : String

private def s3ParseRecord? (line : String) : Option S3CertificateRecord := do
  match line.splitOn "\t" with
  | [pattern, cycleText, stream] => do
      guard (s3PatternValid pattern)
      let cycles ← s3ParseCycleDictionary? cycleText
      some ⟨pattern, cycles, stream⟩
  | _ => none

private def s3ParseBatch? (source : String) : Option (List S3CertificateRecord) := do
  let lines := (source.splitOn "\n").filter (· != "")
  guard (!lines.isEmpty)
  lines.mapM s3ParseRecord?

private def s3RecordValid (record : S3CertificateRecord) : Bool := Id.run do
  let inner := s3InnerPositions record.pattern
  match s3CheckStream inner.size inner record.cycles (s3Initial record.pattern)
      record.stream.toList with
  | some [] => return true
  | _ => return false

/-- Replay all branch coverage and prune witnesses, matching the declared IDs. -/
def fifteenStage3CheckBatch (source : String) (expectedPatterns : List String) : Bool :=
  match s3ParseBatch? source with
  | some records =>
      let patterns := records.map (·.pattern)
      patterns == expectedPatterns &&
        patterns.eraseDups.length == patterns.length && records.all s3RecordValid
  | none => false

end CirclePacking
