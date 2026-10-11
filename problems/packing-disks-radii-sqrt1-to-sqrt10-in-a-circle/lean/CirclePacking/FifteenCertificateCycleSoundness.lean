import CirclePacking.FifteenCertificateTreeSoundness
import CirclePacking.FifteenPackingCycleBridge

/-! Geometric soundness of ordinary `CYCLE` leaves in the exact radial
certificate.  The proof consumes only the checked edge list and the claim
that every sorted packing radius lies in its rational box.  Origin-special
leaves are handled separately because their polar angle needs a distinct
zero-radius argument. -/

namespace CirclePacking

theorem fifteenCosineRuleCap_comm (a b : Rat) :
    fifteenCosineRuleCap a b = fifteenCosineRuleCap b a := by
  unfold fifteenCosineRuleCap
  congr 1 <;> ring

private theorem fifteenMax4_swap (a b c d : Rat) :
    fifteenMax4 a b c d = fifteenMax4 a c b d := by
  unfold fifteenMax4
  calc
    max (max a b) (max c d) = max a (max b (max c d)) := by rw [max_assoc]
    _ = max a (max (max b c) d) := by rw [max_assoc]
    _ = max a (max (max c b) d) := by rw [max_comm b c]
    _ = max a (max c (max b d)) := by rw [max_assoc]
    _ = max (max a c) (max b d) := by rw [← max_assoc]

theorem fifteenBoxCosineCap_comm (x y : FifteenInterval) :
    fifteenBoxCosineCap x y = fifteenBoxCosineCap y x := by
  unfold fifteenBoxCosineCap
  rw [fifteenCosineRuleCap_comm x.1 y.1,
    fifteenCosineRuleCap_comm x.1 y.2,
    fifteenCosineRuleCap_comm x.2 y.1,
    fifteenCosineRuleCap_comm x.2 y.2]
  exact fifteenMax4_swap _ _ _ _

theorem fifteenTickCertificateValid_regular_comm
    (x y : FifteenInterval) (ticks : Nat) :
    fifteenTickCertificateValid x y false false ticks =
      fifteenTickCertificateValid y x false false ticks := by
  simp [fifteenTickCertificateValid, add_comm, fifteenBoxCosineCap_comm]

private theorem fifteenCycleEdge_regular_bound_of_box
    {R : ℝ} (P : Packing 15 R)
    (hunit : ∀ i, (P.circles i).radius = 1)
    (box : FifteenBox) (edge : FifteenCycleEdge)
    (hshape : fifteenCycleEdgeShape edge = true)
    (hregular : (edge.kind = "L" ∧ edge.source > edge.target) ∨
      (edge.kind = "U" ∧ edge.source < edge.target))
    (htick : fifteenCycleEdgeTickValid edge box [] [] = true)
    (_hboxSize : box.size = 15)
    (hboxPositive : ∀ i, i < 15 → 0 < (box[i]!.1 : ℝ))
    (hradial : ∀ i : Fin 15,
      (box[i.1]!.1 : ℝ) ≤ fifteenPackingSortedRadius P i ∧
        fifteenPackingSortedRadius P i ≤ (box[i.1]!.2 : ℝ)) :
    fifteenPackingSortedAngle P (fifteenCycleFin edge.target) -
        fifteenPackingSortedAngle P (fifteenCycleFin edge.source) ≤
      (fifteenCycleEdgeWeight edge : ℝ) / fifteenAngleScale := by
  rcases hregular with hlower | hupper
  · have hvalidTargetSource :=
      fifteenCycleEdgeTickValid_lower_regular_spec edge box [] [] hlower.1
        (by simp) (by simp) htick
    let x := box[edge.source]!
    let y := box[edge.target]!
    have hvalid : fifteenTickCertificateValid x y false false edge.ticks = true := by
      have hsymmetric := fifteenTickCertificateValid_regular_comm y x edge.ticks
      simpa [x, y] using hsymmetric.symm.trans hvalidTargetSource
    have hsumTargetSource := fifteenTickCertificateValid_sum_spec
      box[edge.target]! box[edge.source]! false false edge.ticks hvalidTargetSource
    have hsum : 2 ≤ x.2 + y.2 := by
      simpa [x, y, add_comm] using hsumTargetSource
    have hsource : edge.source < 15 := (fifteenCycleEdgeShape_spec edge hshape).1
    have htarget : edge.target < 15 := (fifteenCycleEdgeShape_spec edge hshape).2.1
    have hsourceFin : (fifteenCycleFin edge.source).val = edge.source :=
      Nat.mod_eq_of_lt hsource
    have htargetFin : (fifteenCycleFin edge.target).val = edge.target :=
      Nat.mod_eq_of_lt htarget
    have hxOrder : x.1 ≤ x.2 := by
      have h := hradial (fifteenCycleFin edge.source)
      have hlo : (x.1 : ℝ) ≤ fifteenPackingSortedRadius P
          (fifteenCycleFin edge.source) := by simpa [x, hsourceFin] using h.1
      have hhi : fifteenPackingSortedRadius P (fifteenCycleFin edge.source) ≤
          (x.2 : ℝ) := by simpa [x, hsourceFin] using h.2
      exact_mod_cast le_trans hlo hhi
    have hyOrder : y.1 ≤ y.2 := by
      have h := hradial (fifteenCycleFin edge.target)
      have hlo : (y.1 : ℝ) ≤ fifteenPackingSortedRadius P
          (fifteenCycleFin edge.target) := by simpa [y, htargetFin] using h.1
      have hhi : fifteenPackingSortedRadius P (fifteenCycleFin edge.target) ≤
          (y.2 : ℝ) := by simpa [y, htargetFin] using h.2
      exact_mod_cast le_trans hlo hhi
    have hx0 : 0 < (x.1 : ℝ) := by
      simpa [x, hsourceFin] using hboxPositive edge.source hsource
    have hy0 : 0 < (y.1 : ℝ) := by
      simpa [y, htargetFin] using hboxPositive edge.target htarget
    have hsourceBound := hradial (fifteenCycleFin edge.source)
    have htargetBound := hradial (fifteenCycleFin edge.target)
    have hsourceL : (x.1 : ℝ) ≤ fifteenPackingSortedRadius P
        (fifteenCycleFin edge.source) := by simpa [x, hsourceFin] using hsourceBound.1
    have hsourceU : fifteenPackingSortedRadius P
        (fifteenCycleFin edge.source) ≤ (x.2 : ℝ) := by simpa [x, hsourceFin] using hsourceBound.2
    have htargetL : (y.1 : ℝ) ≤ fifteenPackingSortedRadius P
        (fifteenCycleFin edge.target) := by simpa [y, htargetFin] using htargetBound.1
    have htargetU : fifteenPackingSortedRadius P
        (fifteenCycleFin edge.target) ≤ (y.2 : ℝ) := by simpa [y, htargetFin] using htargetBound.2
    exact fifteen_unit_packing_regular_cycle_edge_bound P hunit edge x y
      hshape (Or.inl hlower) hsum hvalid hxOrder hyOrder hx0 hy0
      hsourceL hsourceU htargetL htargetU
  · have hvalid := fifteenCycleEdgeTickValid_upper_regular_spec edge box [] [] hupper.1
        (by simp) (by simp) htick
    let x := box[edge.source]!
    let y := box[edge.target]!
    have hsum := fifteenTickCertificateValid_sum_spec x y false false
      edge.ticks hvalid
    have hsource := (fifteenCycleEdgeShape_spec edge hshape).1
    have htarget := (fifteenCycleEdgeShape_spec edge hshape).2.1
    have hsourceFin : (fifteenCycleFin edge.source).val = edge.source :=
      Nat.mod_eq_of_lt hsource
    have htargetFin : (fifteenCycleFin edge.target).val = edge.target :=
      Nat.mod_eq_of_lt htarget
    have hsourceBound := hradial (fifteenCycleFin edge.source)
    have htargetBound := hradial (fifteenCycleFin edge.target)
    have hxOrder : x.1 ≤ x.2 := by
      have hlo : (x.1 : ℝ) ≤ fifteenPackingSortedRadius P
          (fifteenCycleFin edge.source) := by simpa [x, hsourceFin] using hsourceBound.1
      have hhi : fifteenPackingSortedRadius P (fifteenCycleFin edge.source) ≤
          (x.2 : ℝ) := by simpa [x, hsourceFin] using hsourceBound.2
      exact_mod_cast le_trans hlo hhi
    have hyOrder : y.1 ≤ y.2 := by
      have hlo : (y.1 : ℝ) ≤ fifteenPackingSortedRadius P
          (fifteenCycleFin edge.target) := by simpa [y, htargetFin] using htargetBound.1
      have hhi : fifteenPackingSortedRadius P (fifteenCycleFin edge.target) ≤
          (y.2 : ℝ) := by simpa [y, htargetFin] using htargetBound.2
      exact_mod_cast le_trans hlo hhi
    have hx0 : 0 < (x.1 : ℝ) := by
      simpa [x, hsourceFin] using hboxPositive edge.source hsource
    have hy0 : 0 < (y.1 : ℝ) := by
      simpa [y, htargetFin] using hboxPositive edge.target htarget
    have hsourceL : (x.1 : ℝ) ≤ fifteenPackingSortedRadius P
        (fifteenCycleFin edge.source) := by simpa [x, hsourceFin] using hsourceBound.1
    have hsourceU : fifteenPackingSortedRadius P
        (fifteenCycleFin edge.source) ≤ (x.2 : ℝ) := by simpa [x, hsourceFin] using hsourceBound.2
    have htargetL : (y.1 : ℝ) ≤ fifteenPackingSortedRadius P
        (fifteenCycleFin edge.target) := by simpa [y, htargetFin] using htargetBound.1
    have htargetU : fifteenPackingSortedRadius P
        (fifteenCycleFin edge.target) ≤ (y.2 : ℝ) := by simpa [y, htargetFin] using htargetBound.2
    exact fifteen_unit_packing_regular_cycle_edge_bound P hunit edge x y
      hshape (Or.inr hupper) hsum hvalid hxOrder hyOrder hx0 hy0
      hsourceL hsourceU htargetL htargetU

/-- A checked negative cycle in a strictly positive exact radial box cannot
be realized by a unit-disk packing. -/
theorem fifteen_unit_packing_regular_cycle_certificate_excludes
    {R : ℝ} (P : Packing 15 R)
    (hunit : ∀ i, (P.circles i).radius = 1)
    (box : FifteenBox) (edges : List FifteenCycleEdge)
    (hvalid : fifteenCycleEdgesValid edges box [] [] = true)
    (_hboxSize : box.size = 15)
    (hboxPositive : ∀ i, i < 15 → 0 < (box[i]!.1 : ℝ))
    (hradial : ∀ i : Fin 15,
      (box[i.1]!.1 : ℝ) ≤ fifteenPackingSortedRadius P i ∧
        fifteenPackingSortedRadius P i ≤ (box[i.1]!.2 : ℝ)) :
    False := by
  have hspec := fifteenCycleEdgesValid_sound edges box [] [] hvalid
  obtain ⟨start, finish, hstart, hfinish, hchain⟩ :=
    fifteenCycleEdgesSpec_has_closed_chain hspec
  apply fifteenCycleEdgesSpec_excludes hspec hchain
  intro edge hedge
  have hshape := hspec.edgeShapes edge hedge
  rcases (fifteenCycleEdgeShape_spec edge hshape).2.2.2 with
    houter | hlower | hupper
  · have htarget : edge.target < 14 := by
      have hsource := (fifteenCycleEdgeShape_spec edge hshape).1
      omega
    exact fifteen_unit_packing_outer_cycle_edge_bound P edge hshape
      ⟨houter.1, houter.2.1, htarget, houter.2.2⟩
  · exact fifteenCycleEdge_regular_bound_of_box P hunit box edge hshape
      (Or.inl hlower) (hspec.edgeTicks edge hedge) _hboxSize hboxPositive hradial
  · exact fifteenCycleEdge_regular_bound_of_box P hunit box edge hshape
      (Or.inr hupper) (hspec.edgeTicks edge hedge) _hboxSize hboxPositive hradial

end CirclePacking
