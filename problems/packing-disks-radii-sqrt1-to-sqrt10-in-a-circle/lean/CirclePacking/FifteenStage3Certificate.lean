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

def s3InnerPositions (pattern : String) : Array Nat :=
  ((List.range s3N).filter fun i => pattern.toList[i]? == some '1').toArray

theorem s3InnerPositions_mem_iff_char (pattern : String) (i : Nat) :
    i ∈ (s3InnerPositions pattern).toList ↔
      i < s3N ∧ pattern.toList[i]? = some '1' := by
  simp [s3InnerPositions]

private def s3PatternValid (pattern : String) : Bool :=
  let bits := pattern.toList
  bits.length == s3N &&
    bits.all (fun c => c == '0' || c == '1') &&
    let count := bits.filter (· == '1') |>.length
    5 ≤ count && count ≤ 8

structure S3State where
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

def s3Initial (pattern : String) : S3State := Id.run do
  let bits := pattern.toList.toArray
  let labels := (Array.range s3N).map fun i =>
    if bits[i]? == some '1' then 8 else 7
  return ⟨labels, 0, 0, 0, 0⟩

private def s3SmallReason (s : S3State) : Bool := s.small > 1

def s3OriginReason (inner : Array Nat) (s : S3State) : Bool :=
  (inner.toList.any fun p => s.labels[p]! == 9) &&
  (inner.toList.any fun p => s.labels[p]! < 6 && s.labels[p]! != 9)

private def s3RankReason (inner : Array Nat) (s : S3State) : Bool :=
  let remaining := inner.size - s.depth
  s.high + remaining < inner.size - 4 ||
    s.high2 + remaining < max 0 (inner.size - 5)

def s3MixedReason (s : S3State) : Bool := Id.run do
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

def s3Next (inner : Array Nat) (s : S3State) (label : Nat) : S3State :=
  { labels := s.labels.set! inner[s.depth]! label
    depth := s.depth + 1
    small := s.small + (if label <= 1 || label == 9 then 1 else 0)
    high := s.high + (if label >= 5 && label <= 6 then 1 else 0)
    high2 := s.high2 + (if label == 6 then 1 else 0) }

/-- The checker counters are the exact counts of predicates on the labels
assigned at positions before `depth`. -/
def fifteenStage3PrefixCount (inner labels : Array Nat) (depth : Nat)
    (predicate : Nat → Bool) : Nat :=
  ((List.range depth).filter fun k => predicate labels[inner[k]!]!).length

/-- One transition adds precisely the new label's contribution to a prefix
count.  The distinct-position premise ensures the array update cannot alter
any earlier assignment. -/
theorem fifteenStage3PrefixCount_step
    (inner labels : Array Nat) (depth label : Nat) (predicate : Nat → Bool)
    (hnodup : inner.toList.Nodup) (hdepth : depth < inner.size)
    (hposition : inner[depth]! < labels.size) :
    fifteenStage3PrefixCount inner (labels.set! inner[depth]! label) (depth + 1) predicate =
      fifteenStage3PrefixCount inner labels depth predicate +
        (if predicate label then 1 else 0) := by
  have hne : ∀ k, k < depth → inner[k]! ≠ inner[depth]! := by
    intro k hk
    intro hEqArray
    have h1 : k < inner.toList.length := by
      simpa using Nat.lt_trans hk hdepth
    have h2 : depth < inner.toList.length := by simpa using hdepth
    have hEq : inner.toList[k]! = inner.toList[depth]! := by
      calc
        inner.toList[k]! = inner[k]! := by rw [Array.getElem!_toList]
        _ = inner[depth]! := hEqArray
        _ = inner.toList[depth]! := by rw [Array.getElem!_toList]
    have hindex := (hnodup.getElem!_inj h1 h2).mp hEq
    have hfalse : False := by
      have hkEq : k = depth := hindex
      subst depth
      exact Nat.lt_irrefl k hk
    exact hfalse.elim
  unfold fifteenStage3PrefixCount
  rw [List.range_succ, List.filter_append, List.length_append]
  congr 1
  · apply congrArg List.length
    apply List.filter_congr
    intro k hk
    have hklt : k < depth := List.mem_range.mp hk
    rw [Array.getElem!_set!_ne labels (inner[depth]!) (inner[k]!) label
      (Ne.symm (hne k hklt))]
  · simp only [List.filter_cons, List.filter_nil]
    rw [Array.getElem!_set!_self labels (inner[depth]!) label hposition]
    split <;> rfl

/-- The three incremental counters faithfully summarize the assigned prefix. -/
def fifteenStage3CountersConsistent (inner : Array Nat) (s : S3State) : Prop :=
  s.small = fifteenStage3PrefixCount inner s.labels s.depth (fun t => t ≤ 1 || t == 9) ∧
  s.high = fifteenStage3PrefixCount inner s.labels s.depth (fun t => 5 ≤ t && t ≤ 6) ∧
  s.high2 = fifteenStage3PrefixCount inner s.labels s.depth (fun t => t == 6)

/-- Counter consistency is preserved by every legal checker transition. -/
theorem fifteenStage3CountersConsistent_step
    (inner : Array Nat) (s : S3State) (label : Nat)
    (hnodup : inner.toList.Nodup) (hdepth : s.depth < inner.size)
    (hposition : inner[s.depth]! < s.labels.size)
    (hconsistent : fifteenStage3CountersConsistent inner s) :
    fifteenStage3CountersConsistent inner (s3Next inner s label) := by
  rcases s with ⟨labels, depth, small, high, high2⟩
  change depth < inner.size at hdepth
  change inner[depth]! < labels.size at hposition
  change small = fifteenStage3PrefixCount inner labels depth (fun t => t ≤ 1 || t == 9) ∧
    high = fifteenStage3PrefixCount inner labels depth (fun t => 5 ≤ t && t ≤ 6) ∧
    high2 = fifteenStage3PrefixCount inner labels depth (fun t => t == 6) at hconsistent
  change small + (if label ≤ 1 || label == 9 then 1 else 0) =
      fifteenStage3PrefixCount inner (labels.set! inner[depth]! label) (depth + 1)
        (fun t => t ≤ 1 || t == 9) ∧
    high + (if label >= 5 && label <= 6 then 1 else 0) =
      fifteenStage3PrefixCount inner (labels.set! inner[depth]! label) (depth + 1)
        (fun t => 5 ≤ t && t ≤ 6) ∧
    high2 + (if label == 6 then 1 else 0) =
      fifteenStage3PrefixCount inner (labels.set! inner[depth]! label) (depth + 1)
        (fun t => t == 6)
  rcases hconsistent with ⟨hsmall, hhigh, hhigh2⟩
  refine ⟨?_, ?_, ?_⟩
  · rw [fifteenStage3PrefixCount_step inner labels depth label _ hnodup hdepth hposition]
    rw [← hsmall]
  · rw [fifteenStage3PrefixCount_step inner labels depth label _ hnodup hdepth hposition]
    rw [← hhigh]
  · rw [fifteenStage3PrefixCount_step inner labels depth label _ hnodup hdepth hposition]
    rw [← hhigh2]

theorem fifteenStage3InnerPositions_nodup (pattern : String) :
    (s3InnerPositions pattern).toList.Nodup := by
  unfold s3InnerPositions
  rw [List.nodup_iff_pairwise_ne]
  exact List.Pairwise.filter _ (List.nodup_iff_pairwise_ne.mp List.nodup_range)

theorem fifteenStage3InnerPosition_mem_bound (pattern : String) {p : Nat}
    (hp : p ∈ (s3InnerPositions pattern).toList) : p < s3N := by
  unfold s3InnerPositions at hp
  simp only [List.mem_filter, List.mem_range] at hp
  exact hp.1

theorem fifteenStage3InnerPosition_get_bound (pattern : String) {i : Nat}
    (hi : i < (s3InnerPositions pattern).size) :
    (s3InnerPositions pattern)[i]! < s3N := by
  have hmemOrdinary : (s3InnerPositions pattern)[i] ∈
      (s3InnerPositions pattern).toList := Array.getElem_mem_toList hi
  have hmem : (s3InnerPositions pattern)[i]! ∈ (s3InnerPositions pattern).toList := by
    rw [getElem!_pos (s3InnerPositions pattern) i hi]
    exact hmemOrdinary
  exact fifteenStage3InnerPosition_mem_bound pattern hmem

theorem fifteenStage3Initial_labels_size (pattern : String) :
    (s3Initial pattern).labels.size = s3N := by
  simp [s3Initial, s3N]

theorem fifteenStage3Next_labels_size (inner : Array Nat) (s : S3State) (label : Nat) :
    (s3Next inner s label).labels.size = s.labels.size := by
  cases s
  simp [s3Next]

theorem fifteenStage3Initial_countersConsistent (pattern : String) :
    fifteenStage3CountersConsistent (s3InnerPositions pattern) (s3Initial pattern) := by
  unfold fifteenStage3CountersConsistent fifteenStage3PrefixCount
  simp [s3Initial]

/-- The state paths generated by the recursive checker, abstracting away the
certificate text while retaining its exact transition function. -/
inductive FifteenStage3StateReachable (pattern : String) : S3State → Prop where
  | initial : FifteenStage3StateReachable pattern (s3Initial pattern)
  | step {s : S3State} {label : Nat} :
      FifteenStage3StateReachable pattern s →
      s.depth < (s3InnerPositions pattern).size →
      FifteenStage3StateReachable pattern
        (s3Next (s3InnerPositions pattern) s label)

/-- Every state generated from the checker's initial state has exact prefix
counters, keeps the fifteen-label array intact, and stays within the profile. -/
theorem fifteenStage3ReachableState_semantics (pattern : String) {s : S3State}
    (hs : FifteenStage3StateReachable pattern s) :
    fifteenStage3CountersConsistent (s3InnerPositions pattern) s ∧
      s.labels.size = s3N ∧ s.depth ≤ (s3InnerPositions pattern).size := by
  induction hs with
  | initial =>
      exact ⟨fifteenStage3Initial_countersConsistent pattern,
        fifteenStage3Initial_labels_size pattern, Nat.zero_le _⟩
  | @step s label hs hdepth ih =>
      rcases ih with ⟨hconsistent, hlabels, hdepthBound⟩
      have hposition : (s3InnerPositions pattern)[s.depth]! < s.labels.size := by
        rw [hlabels]
        exact fifteenStage3InnerPosition_get_bound pattern hdepth
      exact ⟨fifteenStage3CountersConsistent_step (s3InnerPositions pattern) s label
          (fifteenStage3InnerPositions_nodup pattern) hdepth hposition hconsistent,
        by rw [fifteenStage3Next_labels_size]; exact hlabels,
        by change s.depth + 1 ≤ (s3InnerPositions pattern).size
           exact Nat.succ_le_of_lt hdepth⟩

/-- The single root-to-leaf branch selected by a proposed full owner-label
array.  The certificate checker splits in the order `0, 9, 1, ..., 6`; this
relation follows the child carrying the proposed owner's actual label. -/
inductive FifteenStage3TargetPath (pattern : String) (target : Array Nat) :
    S3State → Prop where
  | initial : FifteenStage3TargetPath pattern target (s3Initial pattern)
  | step {s : S3State} :
      FifteenStage3TargetPath pattern target s →
      s.depth < (s3InnerPositions pattern).size →
      FifteenStage3TargetPath pattern target
        (s3Next (s3InnerPositions pattern) s
          target[(s3InnerPositions pattern)[s.depth]!]!)

theorem fifteenStage3TargetPath_reachable (pattern : String) (target : Array Nat)
    {s : S3State} (hpath : FifteenStage3TargetPath pattern target s) :
    FifteenStage3StateReachable pattern s := by
  induction hpath with
  | initial => exact .initial
  | @step s hpath hdepth ih =>
      exact .step ih hdepth

/-- Along the owner-selected branch, every position already split by the
checker carries exactly its proposed owner label.  This is the state/geometry
interface needed before proving that a verified stream excludes the branch. -/
theorem fifteenStage3TargetPath_prefix_agrees (pattern : String) (target : Array Nat)
    {s : S3State} (hpath : FifteenStage3TargetPath pattern target s) :
    ∀ k, k < s.depth →
      s.labels[(s3InnerPositions pattern)[k]!]! =
        target[(s3InnerPositions pattern)[k]!]! := by
  induction hpath with
  | initial =>
      intro k hk
      simp [s3Initial] at hk
  | @step s hpath hdepth ih =>
      intro k hk
      change k < s.depth + 1 at hk
      have hreachable := fifteenStage3TargetPath_reachable pattern target hpath
      have hsem := fifteenStage3ReachableState_semantics pattern hreachable
      have hposition : (s3InnerPositions pattern)[s.depth]! < s.labels.size := by
        rw [hsem.2.1]
        exact fifteenStage3InnerPosition_get_bound pattern hdepth
      have hsplit : k < s.depth ∨ k = s.depth := by omega
      rcases hsplit with hprevious | rfl
      · have hdifferent :
            (s3InnerPositions pattern)[k]! ≠
              (s3InnerPositions pattern)[s.depth]! := by
          intro heq
          have h1 : k < (s3InnerPositions pattern).toList.length := by
            simpa using Nat.lt_trans hprevious hdepth
          have h2 : s.depth < (s3InnerPositions pattern).toList.length := by
            simpa using hdepth
          have hindexEq : k = s.depth :=
            (fifteenStage3InnerPositions_nodup pattern).getElem!_inj h1 h2 |>.mp (by
              calc
                (s3InnerPositions pattern).toList[k]! =
                    (s3InnerPositions pattern)[k]! := by rw [Array.getElem!_toList]
                _ = (s3InnerPositions pattern)[s.depth]! := heq
                _ = (s3InnerPositions pattern).toList[s.depth]! := by
                    rw [Array.getElem!_toList])
          omega
        change getElem! (s.labels.set! (s3InnerPositions pattern)[s.depth]!
          target[(s3InnerPositions pattern)[s.depth]!]!)
            ((s3InnerPositions pattern)[k]!) =
          target[(s3InnerPositions pattern)[k]!]!
        rw [Array.getElem!_set!_ne _ _ _ _ (Ne.symm hdifferent)]
        exact ih k hprevious
      · change getElem! (s.labels.set! (s3InnerPositions pattern)[s.depth]!
          target[(s3InnerPositions pattern)[s.depth]!]!)
            ((s3InnerPositions pattern)[s.depth]!) =
          target[(s3InnerPositions pattern)[s.depth]!]!
        rw [Array.getElem!_set!_self _ _ _ hposition]

/-- On a target path, every inner slot is either already assigned its target
label or still has the checker's unassigned sentinel `8`.  This stronger
prefix invariant lets the geometric soundness proof interpret predicates
which scan the whole label array, even when the certificate prunes early. -/
theorem fifteenStage3TargetPath_slot_semantics (pattern : String) (target : Array Nat)
    {s : S3State} (hpath : FifteenStage3TargetPath pattern target s) :
    ∀ k, k < (s3InnerPositions pattern).size →
      s.labels[(s3InnerPositions pattern)[k]!]! =
        if k < s.depth then
          target[(s3InnerPositions pattern)[k]!]!
        else 8 := by
  induction hpath with
  | initial =>
      intro k hk
      have hmemOrdinary : (s3InnerPositions pattern)[k] ∈
          (s3InnerPositions pattern).toList := Array.getElem_mem_toList hk
      have hmem : (s3InnerPositions pattern)[k]! ∈
          (s3InnerPositions pattern).toList := by
        rw [getElem!_pos (s3InnerPositions pattern) k hk]
        exact hmemOrdinary
      have hchar := (s3InnerPositions_mem_iff_char pattern
        ((s3InnerPositions pattern)[k]!)).mp hmem
      have hindex : (s3InnerPositions pattern)[k]! < s3N := hchar.1
      have hbits : pattern.toList[(s3InnerPositions pattern)[k]!]? = some '1' := hchar.2
      simp [s3Initial, hbits, hindex]
  | @step s hpath hdepth ih =>
      intro k hk
      have hposition : (s3InnerPositions pattern)[s.depth]! < s.labels.size := by
        rw [(fifteenStage3ReachableState_semantics pattern
          (fifteenStage3TargetPath_reachable pattern target hpath)).2.1]
        exact fifteenStage3InnerPosition_get_bound pattern hdepth
      have hsplit : k < s.depth ∨ k = s.depth ∨ s.depth < k := by omega
      rcases hsplit with hprev | heq | hnext
      · have hdifferent :
            (s3InnerPositions pattern)[k]! ≠
              (s3InnerPositions pattern)[s.depth]! := by
          intro heqArray
          have h1 : k < (s3InnerPositions pattern).toList.length := by
            simpa using Nat.lt_trans hprev hdepth
          have h2 : s.depth < (s3InnerPositions pattern).toList.length := by
            simpa using hdepth
          have hindexEq : k = s.depth :=
            (fifteenStage3InnerPositions_nodup pattern).getElem!_inj h1 h2 |>.mp (by
              calc
                (s3InnerPositions pattern).toList[k]! =
                    (s3InnerPositions pattern)[k]! := by rw [Array.getElem!_toList]
                _ = (s3InnerPositions pattern)[s.depth]! := heqArray
                _ = (s3InnerPositions pattern).toList[s.depth]! := by
                    rw [Array.getElem!_toList])
          omega
        change getElem! (s.labels.set! (s3InnerPositions pattern)[s.depth]!
          target[(s3InnerPositions pattern)[s.depth]!]!)
            ((s3InnerPositions pattern)[k]!) = _
        rw [Array.getElem!_set!_ne _ _ _ _ (Ne.symm hdifferent)]
        rw [ih k (by omega)]
        simp [s3Next, hprev]
        intro hbad
        omega
      · subst k
        change getElem! (s.labels.set! (s3InnerPositions pattern)[s.depth]!
          target[(s3InnerPositions pattern)[s.depth]!]!)
            ((s3InnerPositions pattern)[s.depth]!) = _
        rw [Array.getElem!_set!_self _ _ _ hposition]
        simp [s3Next]
      · have hdifferent :
            (s3InnerPositions pattern)[k]! ≠
              (s3InnerPositions pattern)[s.depth]! := by
          intro heqArray
          have h1 : s.depth < (s3InnerPositions pattern).toList.length := by
            simpa using hdepth
          have h2 : k < (s3InnerPositions pattern).toList.length := by
            simpa using hk
          have hindexEq : s.depth = k :=
            (fifteenStage3InnerPositions_nodup pattern).getElem!_inj h1 h2 |>.mp (by
              calc
                (s3InnerPositions pattern).toList[s.depth]! =
                    (s3InnerPositions pattern)[s.depth]! := by rw [Array.getElem!_toList]
                _ = (s3InnerPositions pattern)[k]! := heqArray.symm
                _ = (s3InnerPositions pattern).toList[k]! := by
                    rw [Array.getElem!_toList])
          omega
        change getElem! (s.labels.set! (s3InnerPositions pattern)[s.depth]!
          target[(s3InnerPositions pattern)[s.depth]!]!)
            ((s3InnerPositions pattern)[k]!) = _
        rw [Array.getElem!_set!_ne _ _ _ _ (Ne.symm hdifferent)]
        rw [ih k hk]
        simp [s3Next, Nat.not_lt_of_ge (Nat.le_of_lt hnext)]
        intro hbad
        omega

theorem fifteenStage3TargetPath_depth_le_size (pattern : String) (target : Array Nat)
    {s : S3State} (hpath : FifteenStage3TargetPath pattern target s) :
    s.depth ≤ (s3InnerPositions pattern).size :=
  (fifteenStage3ReachableState_semantics pattern
    (fifteenStage3TargetPath_reachable pattern target hpath)).2.2

/-- Any proposed owner array determines a complete root-to-leaf branch in the
uncertified split tree.  Whether its leaf can be pruned is established by the
separate geometric soundness and stream replay theorems. -/
theorem fifteenStage3TargetPath_full (pattern : String) (target : Array Nat) :
    ∃ s : S3State, FifteenStage3TargetPath pattern target s ∧
      s.depth = (s3InnerPositions pattern).size := by
  let inner := s3InnerPositions pattern
  have hbuild : ∀ n, n ≤ inner.size →
      ∃ s : S3State, FifteenStage3TargetPath pattern target s ∧ s.depth = n := by
    intro n
    induction n with
    | zero =>
        intro _
        exact ⟨s3Initial pattern, .initial, rfl⟩
    | succ n ih =>
        intro hbound
        have hprev : n ≤ inner.size := by omega
        obtain ⟨s, hs, hdepth⟩ := ih hprev
        have hsplit : s.depth < inner.size := by omega
        refine ⟨s3Next inner s target[inner[s.depth]!]!, .step hs ?_, ?_⟩
        · simpa [inner] using hsplit
        · simp [s3Next, hdepth]
  simpa [inner] using hbuild inner.size (Nat.le_refl _)

/-- The proposed label at each next inner slot is one of the eight choices
enumerated by the Stage 3 certificate, provided the target array records only
legal owner labels on inner positions. -/
theorem fifteenStage3TargetPath_next_label_allowed
    (pattern : String) (target : Array Nat) {s : S3State}
    (_hpath : FifteenStage3TargetPath pattern target s)
    (hdepth : s.depth < (s3InnerPositions pattern).size)
    (hallowed : ∀ p ∈ (s3InnerPositions pattern).toList,
      target[p]! ∈ [0, 9, 1, 2, 3, 4, 5, 6]) :
    target[(s3InnerPositions pattern)[s.depth]!]! ∈ [0, 9, 1, 2, 3, 4, 5, 6] := by
  have hmemOrdinary : (s3InnerPositions pattern)[s.depth] ∈
      (s3InnerPositions pattern).toList := Array.getElem_mem_toList hdepth
  have hmem : (s3InnerPositions pattern)[s.depth]! ∈
      (s3InnerPositions pattern).toList := by
    rw [getElem!_pos (s3InnerPositions pattern) s.depth hdepth]
    exact hmemOrdinary
  exact hallowed _ hmem

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
