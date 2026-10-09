import CirclePacking.FifteenStage3CertificateData
import CirclePacking.FifteenStage3Table

/-!
# Compact prefix-certificate checker for one Stage 3 pattern

The C++ producer emits a flat prefix stream.  A `B` token means eight children
in the fixed order `0, origin, 1, ..., 6`; `S/O/R/M` are structural leaves;
`C` stores a cycle length followed by `(source,target,kind)` triples.  Lean
consumes the stream directly.  It does not enumerate alternatives or search
for a negative cycle.

This first vertical slice checks the closed Stage 3 pattern
`000000010101011`.  The checker validates branch coverage, every structural
prune, cycle topology, cycle-edge weights, and strict negativity.  Connecting
these checked facts to the geometric model is a separate soundness layer.
-/

namespace CirclePacking

private def s3N : Nat := 15
private def s3TwoPi : Nat := 17600

private def s3Inner : Array Nat := #[7,9,11,13,14]

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

private def s3Initial : S3State :=
  let labels := ((Array.replicate s3N 7).set! 7 8 |>.set! 9 8 |>.set! 11 8
      |>.set! 13 8 |>.set! 14 8)
  ⟨labels, 0, 0, 0, 0⟩

private def s3SmallReason (s : S3State) : Bool := s.small > 1

private def s3OriginReason (s : S3State) : Bool :=
  (s3Inner.toList.any fun p => s.labels[p]! == 9) &&
  (s3Inner.toList.any fun p => s.labels[p]! < 6 && s.labels[p]! != 9)

private def s3RankReason (s : S3State) : Bool :=
  let remaining := s3Inner.size - s.depth
  s.high + remaining < s3Inner.size - 4 ||
    s.high2 + remaining < max 0 (s3Inner.size - 5)

private def s3MixedReason (s : S3State) : Bool := Id.run do
  if s.small != 1 then return false
  let hasZero := s.labels.toList.any (fun t => t == 0 || t == 9)
  let hasTwo := s.labels.toList.any (fun t => t == 2)
  return hasZero && hasTwo

private def s3StructurallyPruned (s : S3State) : Bool :=
  s3SmallReason s || s3OriginReason s || s3RankReason s || s3MixedReason s

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

private def s3ParseEdges : Nat → List Char → Option (List S3CertEdge × List Char)
  | 0, rest => some ([], rest)
  | n + 1, sourceChar :: targetChar :: kind :: rest => do
      let source ← s3Digit? sourceChar
      let target ← s3Digit? targetChar
      let (edges, tail) ← s3ParseEdges n rest
      some (⟨source, target, kind⟩ :: edges, tail)
  | _ + 1, _ => none
termination_by n _ => n

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

private def s3Next (s : S3State) (label : Nat) : S3State := Id.run do
  let p := s3Inner[s.depth]!
  return {
    labels := s.labels.set! p label,
    depth := s.depth + 1,
    small := s.small + (if label <= 1 || label == 9 then 1 else 0),
    high := s.high + (if label >= 5 && label <= 6 then 1 else 0),
    high2 := s.high2 + (if label == 6 then 1 else 0)
  }

private def s3CheckStream : Nat → S3State → List Char → Option (List Char)
  | 0, _, 'B' :: _ => none
  | _, s, 'S' :: rest => if s3SmallReason s then some rest else none
  | _, s, 'O' :: rest => if s3OriginReason s then some rest else none
  | _, s, 'R' :: rest => if s3RankReason s then some rest else none
  | _, s, 'M' :: rest => if s3MixedReason s then some rest else none
  | _, s, 'C' :: lengthChar :: rest => do
      let length ← s3Digit? lengthChar
      let (edges, tail) ← s3ParseEdges length rest
      if s.depth >= 3 && !s3StructurallyPruned s && s3CycleValid s.labels edges then
        some tail else none
  | fuel + 1, s, 'B' :: rest => do
      if s.depth >= s3Inner.size || s3StructurallyPruned s then none else do
        let tail ← s3CheckStream fuel (s3Next s 0) rest
        let tail ← s3CheckStream fuel (s3Next s 9) tail
        let tail ← s3CheckStream fuel (s3Next s 1) tail
        let tail ← s3CheckStream fuel (s3Next s 2) tail
        let tail ← s3CheckStream fuel (s3Next s 3) tail
        let tail ← s3CheckStream fuel (s3Next s 4) tail
        let tail ← s3CheckStream fuel (s3Next s 5) tail
        s3CheckStream fuel (s3Next s 6) tail
  | _, _, _ => none
termination_by fuel _ _ => fuel

def fifteenStage3PatternCertificateChecks : Bool :=
  match s3CheckStream s3Inner.size s3Initial stage3Pattern000000010101011Text.toList with
  | some [] => true
  | _ => false

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fifteenStage3PatternCertificate_checks :
    fifteenStage3PatternCertificateChecks = true := by
  native_decide

end CirclePacking
