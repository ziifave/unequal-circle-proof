import CirclePacking.FifteenPackingCycleBridge
import CirclePacking.FifteenTickSymmetry

/-! A verified negative-cycle certificate excludes every unit-disk packing
whose sorted radial vector lies in the certificate's positive rational box.
The only extra box metadata needed here is that edge endpoints use the regular
(nonzero-origin) angle table. -/

namespace CirclePacking

theorem fifteen_unit_packing_cycle_certificate_excludes
    {R : ℝ} (P : Packing 15 R)
    (hunit : ∀ i, (P.circles i).radius = 1)
    {edges : List FifteenCycleEdge} {box : FifteenBox}
    {positiveZero exactZero : List Nat}
    (spec : FifteenCycleEdgesSpec edges box positiveZero exactZero)
    (hboxGood : ∀ i, i < 15 →
      0 < ((box[i]!).1 : ℝ) ∧ box[i]!.1 ≤ box[i]!.2)
    (hboxRadius : ∀ i, i < 15 →
      ((box[i]!).1 : ℝ) ≤ fifteenPackingSortedRadius P (fifteenCycleFin i) ∧
      fifteenPackingSortedRadius P (fifteenCycleFin i) ≤ ((box[i]!).2 : ℝ))
    (hnoZeroFlags : ∀ edge, edge ∈ edges →
      (positiveZero.contains edge.source || positiveZero.contains edge.target) = false ∧
      (exactZero.contains edge.source || exactZero.contains edge.target) = false) :
    False := by
  obtain ⟨first, last, hfirst, hlast, hchain⟩ :=
    fifteenCycleEdgesSpec_has_closed_chain spec
  apply fifteenCycleEdgesSpec_excludes spec hchain
  intro edge hedge
  have hshape := spec.edgeShapes edge hedge
  have htick := spec.edgeTicks edge hedge
  have hsemantic := (fifteenCycleEdgeShape_spec edge hshape).2.2.2
  rcases hsemantic with houter | hlower | hupper
  · rcases houter with ⟨hkind, hstep, htickZero⟩
    have hsource := (fifteenCycleEdgeShape_spec edge hshape).1
    exact fifteen_unit_packing_outer_cycle_edge_bound P edge hshape
      ⟨hkind, hstep, by omega, htickZero⟩
  · have hp0 := (hnoZeroFlags edge hedge).1
    have he0 := (hnoZeroFlags edge hedge).2
    have hp : (positiveZero.contains edge.target ||
        positiveZero.contains edge.source) = false := by
      simpa only [Bool.or_comm] using hp0
    have he : (exactZero.contains edge.target ||
        exactZero.contains edge.source) = false := by
      simpa only [Bool.or_comm] using he0
    have hvalidRev := fifteenCycleEdgeTickValid_lower_regular_spec
      edge box positiveZero exactZero hlower.1 hp he htick
    have hvalid : fifteenTickCertificateValid box[edge.source]! box[edge.target]!
        false false edge.ticks = true := by
      rw [fifteenTickCertificateValid_swap]
      exact hvalidRev
    have hsum := fifteenTickCertificateValid_sum_spec
      box[edge.source]! box[edge.target]! false false edge.ticks hvalid
    have hsrc := (fifteenCycleEdgeShape_spec edge hshape).1
    have htgt := (fifteenCycleEdgeShape_spec edge hshape).2.1
    have hsourceGood := hboxGood edge.source hsrc
    have htargetGood := hboxGood edge.target htgt
    have hsourceRad := hboxRadius edge.source hsrc
    have htargetRad := hboxRadius edge.target htgt
    exact fifteen_unit_packing_regular_cycle_edge_bound P hunit edge
      box[edge.source]! box[edge.target]! hshape (Or.inl hlower)
      hsum hvalid hsourceGood.2 htargetGood.2 hsourceGood.1 htargetGood.1
      hsourceRad.1 hsourceRad.2 htargetRad.1 htargetRad.2
  · have hp0 := (hnoZeroFlags edge hedge).1
    have he0 := (hnoZeroFlags edge hedge).2
    have hvalid := fifteenCycleEdgeTickValid_upper_regular_spec
      edge box positiveZero exactZero hupper.1 hp0 he0 htick
    have hsum := fifteenTickCertificateValid_sum_spec
      box[edge.source]! box[edge.target]! false false edge.ticks hvalid
    have hsrc := (fifteenCycleEdgeShape_spec edge hshape).1
    have htgt := (fifteenCycleEdgeShape_spec edge hshape).2.1
    have hsourceGood := hboxGood edge.source hsrc
    have htargetGood := hboxGood edge.target htgt
    have hsourceRad := hboxRadius edge.source hsrc
    have htargetRad := hboxRadius edge.target htgt
    exact fifteen_unit_packing_regular_cycle_edge_bound P hunit edge
      box[edge.source]! box[edge.target]! hshape (Or.inr hupper)
      hsum hvalid hsourceGood.2 htargetGood.2 hsourceGood.1 htargetGood.1
      hsourceRad.1 hsourceRad.2 htargetRad.1 htargetRad.2

end CirclePacking
