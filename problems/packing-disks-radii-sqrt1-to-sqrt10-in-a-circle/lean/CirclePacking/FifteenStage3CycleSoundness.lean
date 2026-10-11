import CirclePacking.FifteenStage3Certificate
import CirclePacking.FifteenStage3AngularEdge
import CirclePacking.FifteenCycleSoundness

/-! Soundness lemmas for the directed cycle leaves in the Stage 3 stream. -/

namespace CirclePacking

def s3CycleKindString (kind : Char) : String :=
  if kind == 'O' then "O" else if kind == 'L' then "L" else "U"

def s3WeightedCycleEdge (edge : S3WeightedEdge) : FifteenCycleEdge :=
  ⟨edge.source, edge.target, s3CycleKindString edge.kind, edge.ticks⟩

theorem s3WeightedCycleEdge_shape (edge : S3WeightedEdge)
    (hshape : s3EdgeShape edge = true) :
    fifteenCycleEdgeShape (s3WeightedCycleEdge edge) = true := by
  by_cases hO : edge.kind == 'O'
  · have hparts := hshape
    simp [s3EdgeShape, s3N, hO] at hparts
    have hpartsProp : ((edge.source < 15 ∧ edge.target < 15) ∧
        edge.ticks ≤ 8790) ∧
        ((edge.source = edge.target + 1 ∧ edge.target < 14) ∧ edge.ticks = 0) := by
      exact ⟨⟨⟨of_decide_eq_true hparts.1.1.1,
        of_decide_eq_true hparts.1.1.2⟩, hparts.1.2⟩,
        ⟨hparts.2.1, hparts.2.2⟩⟩
    simpa [s3WeightedCycleEdge, s3CycleKindString,
      fifteenCycleEdgeShape, s3N, hO] using hpartsProp
  · by_cases hL : edge.kind == 'L'
    · have hparts := hshape
      simp [s3EdgeShape, s3N, hO, hL] at hparts
      have hpartsProp : ((edge.source < 15 ∧ edge.target < 15) ∧
          edge.ticks ≤ 8790) ∧ edge.target < edge.source := by
        exact ⟨⟨⟨of_decide_eq_true hparts.1.1.1,
          of_decide_eq_true hparts.1.1.2⟩, hparts.1.2⟩, hparts.2⟩
      simpa [s3WeightedCycleEdge, s3CycleKindString,
        fifteenCycleEdgeShape, s3N, hO, hL] using hpartsProp
    · by_cases hU : edge.kind == 'U'
      · have hparts := hshape
        simp [s3EdgeShape, s3N, hO, hL, hU] at hparts
        have hpartsProp : ((edge.source < 15 ∧ edge.target < 15) ∧
            edge.ticks ≤ 8790) ∧ edge.source < edge.target := by
          exact ⟨⟨⟨of_decide_eq_true hparts.1.1.1,
            of_decide_eq_true hparts.1.1.2⟩, hparts.1.2⟩, hparts.2⟩
        simpa [s3WeightedCycleEdge, s3CycleKindString,
          fifteenCycleEdgeShape, s3N, hO, hL, hU] using hpartsProp
      · simp [s3EdgeShape, hO, hL, hU] at hshape

theorem s3WeightedCycleEdge_weight (edge : S3WeightedEdge) :
    s3EdgeWeight edge = fifteenCycleEdgeWeight (s3WeightedCycleEdge edge) := by
  by_cases hO : edge.kind == 'O'
  · simp [s3EdgeWeight, fifteenCycleEdgeWeight, s3WeightedCycleEdge,
      s3CycleKindString, hO]
  · by_cases hL : edge.kind == 'L'
    · simp [s3EdgeWeight, fifteenCycleEdgeWeight, s3WeightedCycleEdge,
        s3CycleKindString, hO, hL]
    · norm_num [s3EdgeWeight, fifteenCycleEdgeWeight, s3WeightedCycleEdge,
        s3CycleKindString, s3TwoPi, hO, hL]

theorem s3CycleValid_specs (labels : Array Nat) (edges : List S3CertEdge)
    (hvalid : s3CycleValid labels edges = true) :
    2 ≤ edges.length ∧ edges.length ≤ 15 ∧
      (edges.map (s3MaterializeEdge labels)).all s3EdgeShape = true ∧
      s3LinkValid (edges.map (s3MaterializeEdge labels)) = true ∧
      s3EndsClosed (edges.map (s3MaterializeEdge labels)) = true ∧
      s3Weight (edges.map (s3MaterializeEdge labels)) < 0 := by
  have h := hvalid
  simp only [s3CycleValid, Id.run] at h
  change (decide (2 ≤ edges.length) && decide (edges.length ≤ 15) &&
      (edges.map (s3MaterializeEdge labels)).all s3EdgeShape &&
      s3LinkValid (edges.map (s3MaterializeEdge labels)) &&
      s3EndsClosed (edges.map (s3MaterializeEdge labels)) &&
      decide (s3Weight (edges.map (s3MaterializeEdge labels)) < 0)) = true at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  rcases h with ⟨⟨⟨⟨⟨hlo, hhi⟩, hshape⟩, hlink⟩, hclosed⟩, hnegative⟩
  exact ⟨hlo, hhi, hshape, hlink, hclosed, hnegative⟩

def s3CycleEdges (labels : Array Nat) (edges : List S3CertEdge) :
    List FifteenCycleEdge :=
  (edges.map (s3MaterializeEdge labels)).map s3WeightedCycleEdge

private theorem s3LinkValid_map (edges : List S3WeightedEdge) :
    fifteenCycleLinkValid (edges.map s3WeightedCycleEdge) = s3LinkValid edges := by
  induction edges with
  | nil => rfl
  | cons first rest ih =>
      cases rest with
      | nil => rfl
      | cons second tail =>
          have hbeq : (first.target == second.source) =
              decide (first.target = second.source) := by rfl
          change (first.target == second.source &&
                fifteenCycleLinkValid ((second :: tail).map s3WeightedCycleEdge)) =
              (decide (first.target = second.source) && s3LinkValid (second :: tail))
          rw [hbeq, ih]

private theorem s3ListGetLastMap {α β : Type} (f : α → β) :
    ∀ edges : List α, (edges.map f).getLast? = edges.getLast?.map f := by
  intro edges
  induction edges with
  | nil => rfl
  | cons first rest ih =>
      cases rest with
      | nil => rfl
      | cons second tail =>
          simpa [List.getLast?] using ih

private theorem s3EndsClosed_map (edges : List S3WeightedEdge) :
    fifteenCycleEndsClosed (edges.map s3WeightedCycleEdge) = s3EndsClosed edges := by
  have hheadMap : (edges.map s3WeightedCycleEdge).head? =
      edges.head?.map s3WeightedCycleEdge := by
    cases edges <;> rfl
  have hlastMap := s3ListGetLastMap s3WeightedCycleEdge edges
  unfold fifteenCycleEndsClosed s3EndsClosed
  rw [hheadMap, hlastMap]
  cases hhead : edges.head? <;> cases hlast : edges.getLast? <;>
    simp [hhead, hlast, s3WeightedCycleEdge]

/-- A Stage 3 cycle leaf contains an ordinary, closed negative cycle after
translating its character tags to the shared angular-cycle representation. -/
theorem s3CycleValid_transfers_cycle_data
    (labels : Array Nat) (edges : List S3CertEdge)
    (hvalid : s3CycleValid labels edges = true) :
    2 ≤ (s3CycleEdges labels edges).length ∧
      (s3CycleEdges labels edges).length ≤ 15 ∧
      (∀ edge ∈ s3CycleEdges labels edges, fifteenCycleEdgeShape edge = true) ∧
      fifteenCycleLinkValid (s3CycleEdges labels edges) = true ∧
      fifteenCycleEndsClosed (s3CycleEdges labels edges) = true ∧
      fifteenCycleWeightTicks (s3CycleEdges labels edges) < 0 := by
  have hspec := s3CycleValid_specs labels edges hvalid
  rcases hspec with ⟨hlenLo, hlenHi, hshape, hlink, hclosed, hnegative⟩
  have hshapeAll : ∀ weighted ∈ edges.map (s3MaterializeEdge labels),
      s3EdgeShape weighted = true :=
    fifteenListAllTrue_spec _ _ hshape
  have hcycleShape : ∀ cycleEdge ∈ s3CycleEdges labels edges,
      fifteenCycleEdgeShape cycleEdge = true := by
    intro cycleEdge hmem
    change cycleEdge ∈
      ((edges.map (s3MaterializeEdge labels)).map s3WeightedCycleEdge) at hmem
    obtain ⟨weighted, hweightedMem, heq⟩ := List.mem_map.mp hmem
    subst cycleEdge
    exact s3WeightedCycleEdge_shape weighted (hshapeAll weighted hweightedMem)
  have hcycleLink : fifteenCycleLinkValid (s3CycleEdges labels edges) = true := by
    simpa only [s3CycleEdges] using
      (s3LinkValid_map (edges.map (s3MaterializeEdge labels))).trans hlink
  have hcycleClosed : fifteenCycleEndsClosed (s3CycleEdges labels edges) = true := by
    simpa only [s3CycleEdges] using
      (s3EndsClosed_map (edges.map (s3MaterializeEdge labels))).trans hclosed
  have hweightFold : s3Weight (edges.map (s3MaterializeEdge labels)) =
      ((edges.map (s3MaterializeEdge labels)).map s3EdgeWeight).sum := by
    unfold s3Weight
    rw [fifteenListFoldlAddMapSum]
    simp
  have hweightMap :
      ((edges.map (s3MaterializeEdge labels)).map s3EdgeWeight).sum =
        ((edges.map (s3MaterializeEdge labels)).map
          (fun weighted => fifteenCycleEdgeWeight
            (s3WeightedCycleEdge weighted))).sum := by
    apply fifteenListSumMapCongr
    intro weighted hmem
    exact s3WeightedCycleEdge_weight weighted
  have hnegativeCycle :
      fifteenCycleWeightTicks (s3CycleEdges labels edges) < 0 := by
    have heq : s3Weight (edges.map (s3MaterializeEdge labels)) =
        fifteenCycleWeightTicks (s3CycleEdges labels edges) := by
      unfold fifteenCycleWeightTicks
      calc
        s3Weight (edges.map (s3MaterializeEdge labels)) =
            ((edges.map (s3MaterializeEdge labels)).map s3EdgeWeight).sum := hweightFold
        _ = ((edges.map (s3MaterializeEdge labels)).map
            (fun weighted => fifteenCycleEdgeWeight
              (s3WeightedCycleEdge weighted))).sum := hweightMap
        _ = ((s3CycleEdges labels edges).map fifteenCycleEdgeWeight).sum := by
            simp [s3CycleEdges, List.map_map, Function.comp_def]
    rw [← heq]
    exact hnegative
  refine ⟨?_, ?_, hcycleShape, hcycleLink, hcycleClosed, hnegativeCycle⟩
  · simpa [s3CycleEdges] using hlenLo
  · simpa [s3CycleEdges] using hlenHi

/-- The negative integer sum checked by a Stage 3 cycle leaf contradicts
any real angle potential satisfying the corresponding converted edge bounds. -/
theorem s3CycleValid_excludes_angularPotential
    (labels : Array Nat) (edges : List S3CertEdge) (theta : Fin 15 → ℝ)
    (hvalid : s3CycleValid labels edges = true)
    (hbound : ∀ edge ∈ s3CycleEdges labels edges,
      theta (fifteenCycleFin edge.target) - theta (fifteenCycleFin edge.source) ≤
        (fifteenCycleEdgeWeight edge : ℝ) / fifteenAngleScale) : False := by
  obtain ⟨hlenLo, _, hshape, hlink, hclosed, hnegative⟩ :=
    s3CycleValid_transfers_cycle_data labels edges hvalid
  cases hcycles : s3CycleEdges labels edges with
  | nil => simp [hcycles] at hlenLo
  | cons first rest =>
      cases rest with
      | nil => simp [hcycles] at hlenLo
      | cons second tail =>
          have hfirst : (first :: second :: tail).head? = some first := by simp
          let last := (second :: tail).getLast (by simp)
          have hlast : (first :: second :: tail).getLast? = some last := by
            simpa [last] using
              (List.getLast?_eq_some_getLast (by simp : (first :: second :: tail) ≠ []))
          have hlink' : fifteenCycleLinkValid (first :: second :: tail) = true := by
            simpa [hcycles] using hlink
          have hclosed' : fifteenCycleEndsClosed (first :: second :: tail) = true := by
            simpa [hcycles] using hclosed
          have hshape' : ∀ edge ∈ first :: second :: tail,
              fifteenCycleEdgeShape edge = true := by
            simpa [hcycles] using hshape
          have hbound' : ∀ edge ∈ first :: second :: tail,
              theta (fifteenCycleFin edge.target) - theta (fifteenCycleFin edge.source) ≤
                (fifteenCycleEdgeWeight edge : ℝ) / fifteenAngleScale := by
            simpa [hcycles] using hbound
          have hstart : fifteenCycleHeadSource? (first :: second :: tail) =
              some first.source := by
            simp [fifteenCycleHeadSource?, hfirst]
          have hfinish : fifteenCycleLastTarget? (first :: second :: tail) =
              some last.target := by
            simp [fifteenCycleLastTarget?, hlast, last]
          have hchain := fifteenCycleLinkValid_chain hlink' hstart hfinish
          have hends := fifteenCycleEndsClosed_spec hfirst hlast hclosed'
          have hnegative' : fifteenCycleWeightTicks (first :: second :: tail) < 0 := by
            simpa [hcycles] using hnegative
          rw [hends] at hchain
          exact fifteenNegativeCycle_excludes hchain hshape' hbound' hnegative'

end CirclePacking
