import CirclePacking.FifteenStage4Certificate
import CirclePacking.FifteenStage4AngularEdge
import CirclePacking.FifteenCycleSoundness

/-! Soundness lemmas for the directed cycle leaves in the Stage 3 stream. -/

namespace CirclePacking

def s4CycleKindString (kind : Char) : String :=
  if kind == 'O' then "O" else if kind == 'L' then "L" else "U"

def s4WeightedCycleEdge (edge : S4WeightedEdge) : FifteenCycleEdge :=
  ⟨edge.source, edge.target, s4CycleKindString edge.kind, edge.ticks⟩

theorem s4WeightedCycleEdge_shape (edge : S4WeightedEdge)
    (hshape : s4EdgeShape edge = true) :
    fifteenCycleEdgeShape (s4WeightedCycleEdge edge) = true := by
  by_cases hO : edge.kind == 'O'
  · have hparts := hshape
    simp [s4EdgeShape, s4N, hO] at hparts
    have hpartsProp : ((edge.source < 15 ∧ edge.target < 15) ∧
        edge.ticks ≤ 8790) ∧
        ((edge.source = edge.target + 1 ∧ edge.target < 14) ∧ edge.ticks = 0) := by
      exact ⟨⟨⟨of_decide_eq_true hparts.1.1.1,
        of_decide_eq_true hparts.1.1.2⟩, hparts.1.2⟩,
        ⟨hparts.2.1, hparts.2.2⟩⟩
    simpa [s4WeightedCycleEdge, s4CycleKindString,
      fifteenCycleEdgeShape, s4N, hO] using hpartsProp
  · by_cases hL : edge.kind == 'L'
    · have hparts := hshape
      simp [s4EdgeShape, s4N, hO, hL] at hparts
      have hpartsProp : ((edge.source < 15 ∧ edge.target < 15) ∧
          edge.ticks ≤ 8790) ∧ edge.target < edge.source := by
        exact ⟨⟨⟨of_decide_eq_true hparts.1.1.1,
          of_decide_eq_true hparts.1.1.2⟩, hparts.1.2⟩, hparts.2⟩
      simpa [s4WeightedCycleEdge, s4CycleKindString,
        fifteenCycleEdgeShape, s4N, hO, hL] using hpartsProp
    · by_cases hU : edge.kind == 'U'
      · have hparts := hshape
        simp [s4EdgeShape, s4N, hO, hL, hU] at hparts
        have hpartsProp : ((edge.source < 15 ∧ edge.target < 15) ∧
            edge.ticks ≤ 8790) ∧ edge.source < edge.target := by
          exact ⟨⟨⟨of_decide_eq_true hparts.1.1.1,
            of_decide_eq_true hparts.1.1.2⟩, hparts.1.2⟩, hparts.2⟩
        simpa [s4WeightedCycleEdge, s4CycleKindString,
          fifteenCycleEdgeShape, s4N, hO, hL, hU] using hpartsProp
      · simp [s4EdgeShape, hO, hL, hU] at hshape

theorem s4WeightedCycleEdge_weight (edge : S4WeightedEdge) :
    s4EdgeWeight edge = fifteenCycleEdgeWeight (s4WeightedCycleEdge edge) := by
  by_cases hO : edge.kind == 'O'
  · simp [s4EdgeWeight, fifteenCycleEdgeWeight, s4WeightedCycleEdge,
      s4CycleKindString, hO]
  · by_cases hL : edge.kind == 'L'
    · simp [s4EdgeWeight, fifteenCycleEdgeWeight, s4WeightedCycleEdge,
        s4CycleKindString, hO, hL]
    · norm_num [s4EdgeWeight, fifteenCycleEdgeWeight, s4WeightedCycleEdge,
        s4CycleKindString, s4TwoPi, hO, hL]

theorem s4CycleValid_specs (labels : Array Nat) (edges : List S4CertEdge)
    (hvalid : s4CycleValid labels edges = true) :
    2 ≤ edges.length ∧ edges.length ≤ 15 ∧
      (edges.map (s4MaterializeEdge labels)).all s4EdgeShape = true ∧
      s4LinkValid (edges.map (s4MaterializeEdge labels)) = true ∧
      s4EndsClosed (edges.map (s4MaterializeEdge labels)) = true ∧
      s4Weight (edges.map (s4MaterializeEdge labels)) < 0 := by
  have h := hvalid
  simp only [s4CycleValid, Id.run] at h
  change (decide (2 ≤ edges.length) && decide (edges.length ≤ 15) &&
      (edges.map (s4MaterializeEdge labels)).all s4EdgeShape &&
      s4LinkValid (edges.map (s4MaterializeEdge labels)) &&
      s4EndsClosed (edges.map (s4MaterializeEdge labels)) &&
      decide (s4Weight (edges.map (s4MaterializeEdge labels)) < 0)) = true at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  rcases h with ⟨⟨⟨⟨⟨hlo, hhi⟩, hshape⟩, hlink⟩, hclosed⟩, hnegative⟩
  exact ⟨hlo, hhi, hshape, hlink, hclosed, hnegative⟩

def s4CycleEdges (labels : Array Nat) (edges : List S4CertEdge) :
    List FifteenCycleEdge :=
  (edges.map (s4MaterializeEdge labels)).map s4WeightedCycleEdge

private theorem s4DecideBool (b : Bool) : decide b = b := by
  cases b <;> rfl

private theorem s4LinkValid_map (edges : List S4WeightedEdge) :
    fifteenCycleLinkValid (edges.map s4WeightedCycleEdge) = s4LinkValid edges := by
  induction edges with
  | nil => rfl
  | cons first rest ih =>
      cases rest with
      | nil => rfl
      | cons second tail =>
          simp only [List.map_cons, fifteenCycleLinkValid, s4LinkValid,
            s4WeightedCycleEdge]
          rw [s4DecideBool]
          apply congrArg (fun ok => (first.target == second.source) && ok)
          simpa only [List.map_cons, s4WeightedCycleEdge] using ih

private theorem s4ListGetLastMap {α β : Type} (f : α → β) :
    ∀ edges : List α, (edges.map f).getLast? = edges.getLast?.map f := by
  intro edges
  induction edges with
  | nil => rfl
  | cons first rest ih =>
      cases rest with
      | nil => rfl
      | cons second tail =>
          simpa [List.getLast?] using ih

private theorem s4EndsClosed_map (edges : List S4WeightedEdge) :
    fifteenCycleEndsClosed (edges.map s4WeightedCycleEdge) = s4EndsClosed edges := by
  have hheadMap : (edges.map s4WeightedCycleEdge).head? =
      edges.head?.map s4WeightedCycleEdge := by
    cases edges <;> rfl
  have hlastMap := s4ListGetLastMap s4WeightedCycleEdge edges
  unfold fifteenCycleEndsClosed s4EndsClosed
  rw [hheadMap, hlastMap]
  cases hhead : edges.head? <;> cases hlast : edges.getLast? <;>
    simp [hhead, hlast, s4WeightedCycleEdge]

/-- A Stage 3 cycle leaf contains an ordinary, closed negative cycle after
translating its character tags to the shared angular-cycle representation. -/
theorem s4CycleValid_transfers_cycle_data
    (labels : Array Nat) (edges : List S4CertEdge)
    (hvalid : s4CycleValid labels edges = true) :
    2 ≤ (s4CycleEdges labels edges).length ∧
      (s4CycleEdges labels edges).length ≤ 15 ∧
      (∀ edge ∈ s4CycleEdges labels edges, fifteenCycleEdgeShape edge = true) ∧
      fifteenCycleLinkValid (s4CycleEdges labels edges) = true ∧
      fifteenCycleEndsClosed (s4CycleEdges labels edges) = true ∧
      fifteenCycleWeightTicks (s4CycleEdges labels edges) < 0 := by
  have hspec := s4CycleValid_specs labels edges hvalid
  rcases hspec with ⟨hlenLo, hlenHi, hshape, hlink, hclosed, hnegative⟩
  have hshapeAll : ∀ weighted ∈ edges.map (s4MaterializeEdge labels),
      s4EdgeShape weighted = true :=
    fifteenListAllTrue_spec _ _ hshape
  have hcycleShape : ∀ cycleEdge ∈ s4CycleEdges labels edges,
      fifteenCycleEdgeShape cycleEdge = true := by
    intro cycleEdge hmem
    change cycleEdge ∈
      ((edges.map (s4MaterializeEdge labels)).map s4WeightedCycleEdge) at hmem
    obtain ⟨weighted, hweightedMem, heq⟩ := List.mem_map.mp hmem
    subst cycleEdge
    exact s4WeightedCycleEdge_shape weighted (hshapeAll weighted hweightedMem)
  have hcycleLink : fifteenCycleLinkValid (s4CycleEdges labels edges) = true := by
    simpa only [s4CycleEdges] using
      (s4LinkValid_map (edges.map (s4MaterializeEdge labels))).trans hlink
  have hcycleClosed : fifteenCycleEndsClosed (s4CycleEdges labels edges) = true := by
    simpa only [s4CycleEdges] using
      (s4EndsClosed_map (edges.map (s4MaterializeEdge labels))).trans hclosed
  have hweightFold : s4Weight (edges.map (s4MaterializeEdge labels)) =
      ((edges.map (s4MaterializeEdge labels)).map s4EdgeWeight).sum := by
    unfold s4Weight
    rw [fifteenListFoldlAddMapSum]
    simp
  have hweightMap :
      ((edges.map (s4MaterializeEdge labels)).map s4EdgeWeight).sum =
        ((edges.map (s4MaterializeEdge labels)).map
          (fun weighted => fifteenCycleEdgeWeight
            (s4WeightedCycleEdge weighted))).sum := by
    apply fifteenListSumMapCongr
    intro weighted hmem
    exact s4WeightedCycleEdge_weight weighted
  have hnegativeCycle :
      fifteenCycleWeightTicks (s4CycleEdges labels edges) < 0 := by
    have heq : s4Weight (edges.map (s4MaterializeEdge labels)) =
        fifteenCycleWeightTicks (s4CycleEdges labels edges) := by
      unfold fifteenCycleWeightTicks
      calc
        s4Weight (edges.map (s4MaterializeEdge labels)) =
            ((edges.map (s4MaterializeEdge labels)).map s4EdgeWeight).sum := hweightFold
        _ = ((edges.map (s4MaterializeEdge labels)).map
            (fun weighted => fifteenCycleEdgeWeight
              (s4WeightedCycleEdge weighted))).sum := hweightMap
        _ = ((s4CycleEdges labels edges).map fifteenCycleEdgeWeight).sum := by
            simp [s4CycleEdges, List.map_map, Function.comp_def]
    rw [← heq]
    exact hnegative
  refine ⟨?_, ?_, hcycleShape, hcycleLink, hcycleClosed, hnegativeCycle⟩
  · simpa [s4CycleEdges] using hlenLo
  · simpa [s4CycleEdges] using hlenHi

/-- The negative integer sum checked by a Stage 3 cycle leaf contradicts
any real angle potential satisfying the corresponding converted edge bounds. -/
theorem s4CycleValid_excludes_angularPotential
    (labels : Array Nat) (edges : List S4CertEdge) (theta : Fin 15 → ℝ)
    (hvalid : s4CycleValid labels edges = true)
    (hbound : ∀ edge ∈ s4CycleEdges labels edges,
      theta (fifteenCycleFin edge.target) - theta (fifteenCycleFin edge.source) ≤
        (fifteenCycleEdgeWeight edge : ℝ) / fifteenAngleScale) : False := by
  obtain ⟨hlenLo, _, hshape, hlink, hclosed, hnegative⟩ :=
    s4CycleValid_transfers_cycle_data labels edges hvalid
  cases hcycles : s4CycleEdges labels edges with
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
