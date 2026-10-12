import CirclePacking.FifteenCertificateCycleSoundness
import CirclePacking.FifteenCertificateLeafSoundness

/-! Generic geometric soundness for the exact radial certificate.  Unlike
the packing-specialized lemmas, these results accept an explicit polar list
and its pairwise separation facts.  This lets a reindexed Stage 4 profile
feed the certificate without rebuilding a packing whose angle sort may
reorder tied angles. -/

namespace CirclePacking

private theorem fifteenGeometricCycleEdgeBound_regular
    (radii theta : Fin 15 → ℝ) (box : FifteenBox)
    (edge : FifteenCycleEdge)
    (hsorted : ∀ i j : Fin 15, i.1 < j.1 → theta i ≤ theta j)
    (hthetaLo : ∀ i, 0 ≤ theta i)
    (hthetaHi : ∀ i, theta i ≤ 2 * Real.pi)
    (hsep : ∀ i j : Fin 15, i ≠ j →
      4 ≤ pointNorm
        ((polarPoint (radii i) (theta i)).1 -
            (polarPoint (radii j) (theta j)).1,
         (polarPoint (radii i) (theta i)).2 -
            (polarPoint (radii j) (theta j)).2) ^ 2)
    (hbox : fifteenBoxGood box)
    (hradial : ∀ i : Fin 15,
      (box[i.1]!.1 : ℝ) ≤ radii i ∧
        radii i ≤ (box[i.1]!.2 : ℝ))
    (hshape : fifteenCycleEdgeShape edge = true)
    (htick : fifteenCycleEdgeTickValid edge box [] [] = true)
    (hregular : (edge.kind = "L" ∧ edge.source > edge.target) ∨
      (edge.kind = "U" ∧ edge.source < edge.target)) :
    theta (fifteenCycleFin edge.target) -
        theta (fifteenCycleFin edge.source) ≤
      (fifteenCycleEdgeWeight edge : ℝ) / fifteenAngleScale := by
  rcases hregular with hlower | hupper
  · have hvalid := fifteenCycleEdgeTickValid_lower_regular_spec edge box [] []
      hlower.1 (by simp) (by simp) htick
    let x := box[edge.source]!
    let y := box[edge.target]!
    have hvalid' : fifteenTickCertificateValid x y false false edge.ticks = true := by
      have hsymmetric := fifteenTickCertificateValid_regular_comm y x edge.ticks
      simpa [x, y] using hsymmetric.symm.trans hvalid
    have hsum' := fifteenTickCertificateValid_sum_spec
      box[edge.target]! box[edge.source]! false false edge.ticks hvalid
    have hsum : 2 ≤ x.2 + y.2 := by simpa [x, y, add_comm] using hsum'
    have hsource := (fifteenCycleEdgeShape_spec edge hshape).1
    have htarget := (fifteenCycleEdgeShape_spec edge hshape).2.1
    have hsourceFin : (fifteenCycleFin edge.source).val = edge.source :=
      Nat.mod_eq_of_lt hsource
    have htargetFin : (fifteenCycleFin edge.target).val = edge.target :=
      Nat.mod_eq_of_lt htarget
    have hsourceMod : edge.source % 15 = edge.source := Nat.mod_eq_of_lt hsource
    have htargetMod : edge.target % 15 = edge.target := Nat.mod_eq_of_lt htarget
    have hxOrder : x.1 ≤ x.2 := by
      have hr := hradial (fifteenCycleFin edge.source)
      have hlo : (x.1 : ℝ) ≤ radii (fifteenCycleFin edge.source) := by
        simpa [x, fifteenCycleFin, hsourceMod] using hr.1
      have hhi : radii (fifteenCycleFin edge.source) ≤ (x.2 : ℝ) := by
        simpa [x, fifteenCycleFin, hsourceMod] using hr.2
      exact_mod_cast le_trans hlo hhi
    have hyOrder : y.1 ≤ y.2 := by
      have hr := hradial (fifteenCycleFin edge.target)
      have hlo : (y.1 : ℝ) ≤ radii (fifteenCycleFin edge.target) := by
        simpa [y, fifteenCycleFin, htargetMod] using hr.1
      have hhi : radii (fifteenCycleFin edge.target) ≤ (y.2 : ℝ) := by
        simpa [y, fifteenCycleFin, htargetMod] using hr.2
      exact_mod_cast le_trans hlo hhi
    have hx0 : 0 < (x.1 : ℝ) := hbox.2 edge.source hsource
    have hy0 : 0 < (y.1 : ℝ) := hbox.2 edge.target htarget
    have hsourceBox := hradial (fifteenCycleFin edge.source)
    have htargetBox := hradial (fifteenCycleFin edge.target)
    have hsourceL : (x.1 : ℝ) ≤ radii (fifteenCycleFin edge.source) := by
      simpa [x, fifteenCycleFin, hsourceMod] using hsourceBox.1
    have hsourceU : radii (fifteenCycleFin edge.source) ≤ (x.2 : ℝ) := by
      simpa [x, fifteenCycleFin, hsourceMod] using hsourceBox.2
    have htargetL : (y.1 : ℝ) ≤ radii (fifteenCycleFin edge.target) := by
      simpa [y, fifteenCycleFin, htargetMod] using htargetBox.1
    have htargetU : radii (fifteenCycleFin edge.target) ≤ (y.2 : ℝ) := by
      simpa [y, fifteenCycleFin, htargetMod] using htargetBox.2
    have hsep' := hsep (fifteenCycleFin edge.source)
      (fifteenCycleFin edge.target) (by
        have hsourceNeTarget : edge.source ≠ edge.target := by omega
        intro heq
        apply hsourceNeTarget
        calc
          edge.source = (fifteenCycleFin edge.source).val := hsourceFin.symm
          _ = (fifteenCycleFin edge.target).val := congrArg Fin.val heq
          _ = edge.target := htargetFin)
    exact fifteenRegularTick_cycleEdge_weight_bound edge x y theta
      (radii (fifteenCycleFin edge.source))
      (radii (fifteenCycleFin edge.target))
      ((fifteenPiUpperTicks : ℝ) / fifteenAngleScale)
      hshape (Or.inl hlower) hsum hvalid' hxOrder hyOrder hx0 hy0
      hsourceL hsourceU htargetL htargetU hsorted hthetaLo hthetaHi
      hsep' fifteen_two_pi_le_cycle_tau rfl
  · have hvalid := fifteenCycleEdgeTickValid_upper_regular_spec edge box [] []
      hupper.1 (by simp) (by simp) htick
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
    have hsourceMod : edge.source % 15 = edge.source := Nat.mod_eq_of_lt hsource
    have htargetMod : edge.target % 15 = edge.target := Nat.mod_eq_of_lt htarget
    have hrS := hradial (fifteenCycleFin edge.source)
    have hrT := hradial (fifteenCycleFin edge.target)
    have hxOrder : x.1 ≤ x.2 := by
      have hlo : (x.1 : ℝ) ≤ radii (fifteenCycleFin edge.source) := by
        simpa [x, fifteenCycleFin, hsourceMod] using hrS.1
      have hhi : radii (fifteenCycleFin edge.source) ≤ (x.2 : ℝ) := by
        simpa [x, fifteenCycleFin, hsourceMod] using hrS.2
      exact_mod_cast le_trans hlo hhi
    have hyOrder : y.1 ≤ y.2 := by
      have hlo : (y.1 : ℝ) ≤ radii (fifteenCycleFin edge.target) := by
        simpa [y, fifteenCycleFin, htargetMod] using hrT.1
      have hhi : radii (fifteenCycleFin edge.target) ≤ (y.2 : ℝ) := by
        simpa [y, fifteenCycleFin, htargetMod] using hrT.2
      exact_mod_cast le_trans hlo hhi
    have hx0 : 0 < (x.1 : ℝ) := hbox.2 edge.source hsource
    have hy0 : 0 < (y.1 : ℝ) := hbox.2 edge.target htarget
    have hsourceL : (x.1 : ℝ) ≤ radii (fifteenCycleFin edge.source) := by
      simpa [x, fifteenCycleFin, hsourceMod] using hrS.1
    have hsourceU : radii (fifteenCycleFin edge.source) ≤ (x.2 : ℝ) := by
      simpa [x, fifteenCycleFin, hsourceMod] using hrS.2
    have htargetL : (y.1 : ℝ) ≤ radii (fifteenCycleFin edge.target) := by
      simpa [y, fifteenCycleFin, htargetMod] using hrT.1
    have htargetU : radii (fifteenCycleFin edge.target) ≤ (y.2 : ℝ) := by
      simpa [y, fifteenCycleFin, htargetMod] using hrT.2
    have hvalid' : fifteenTickCertificateValid x y false false edge.ticks = true := by
      simpa [x, y] using hvalid
    have hsep' := hsep (fifteenCycleFin edge.source)
      (fifteenCycleFin edge.target) (by
        have hsourceNeTarget : edge.source ≠ edge.target := by omega
        intro heq
        apply hsourceNeTarget
        calc
          edge.source = (fifteenCycleFin edge.source).val := hsourceFin.symm
          _ = (fifteenCycleFin edge.target).val := congrArg Fin.val heq
          _ = edge.target := htargetFin)
    exact fifteenRegularTick_cycleEdge_weight_bound edge x y theta
      (radii (fifteenCycleFin edge.source))
      (radii (fifteenCycleFin edge.target))
      ((fifteenPiUpperTicks : ℝ) / fifteenAngleScale)
      hshape (Or.inr hupper) hsum hvalid' hxOrder hyOrder hx0 hy0
      hsourceL hsourceU htargetL htargetU hsorted hthetaLo hthetaHi
      hsep' fifteen_two_pi_le_cycle_tau rfl

private theorem fifteenGeometricCycleEdgeBound
    (radii theta : Fin 15 → ℝ) (box : FifteenBox)
    (edge : FifteenCycleEdge)
    (hsorted : ∀ i j : Fin 15, i.1 < j.1 → theta i ≤ theta j)
    (hthetaLo : ∀ i, 0 ≤ theta i)
    (hthetaHi : ∀ i, theta i ≤ 2 * Real.pi)
    (hsep : ∀ i j : Fin 15, i ≠ j →
      4 ≤ pointNorm
        ((polarPoint (radii i) (theta i)).1 -
            (polarPoint (radii j) (theta j)).1,
         (polarPoint (radii i) (theta i)).2 -
            (polarPoint (radii j) (theta j)).2) ^ 2)
    (hbox : fifteenBoxGood box)
    (hradial : ∀ i : Fin 15,
      (box[i.1]!.1 : ℝ) ≤ radii i ∧
        radii i ≤ (box[i.1]!.2 : ℝ))
    (hshape : fifteenCycleEdgeShape edge = true)
    (htick : fifteenCycleEdgeTickValid edge box [] [] = true) :
    theta (fifteenCycleFin edge.target) -
        theta (fifteenCycleFin edge.source) ≤
      (fifteenCycleEdgeWeight edge : ℝ) / fifteenAngleScale := by
  have hspec := fifteenCycleEdgeShape_spec edge hshape
  rcases hspec.2.2.2 with houter | hlower | hupper
  · have htarget : edge.target < 14 := by omega
    have horder : (fifteenCycleFin edge.target).val <
        (fifteenCycleFin edge.source).val := by
      change edge.target % 15 < edge.source % 15
      rw [Nat.mod_eq_of_lt hspec.2.1, Nat.mod_eq_of_lt hspec.1]
      omega
    have hangle := hsorted (fifteenCycleFin edge.target)
      (fifteenCycleFin edge.source) horder
    have hweight : fifteenCycleEdgeWeight edge = 0 := by
      simp [fifteenCycleEdgeWeight, houter.1]
    rw [hweight]
    norm_num [fifteenAngleScale]
    linarith
  · exact fifteenGeometricCycleEdgeBound_regular radii theta box edge
      hsorted hthetaLo hthetaHi hsep hbox hradial hshape htick (Or.inl hlower)
  · exact fifteenGeometricCycleEdgeBound_regular radii theta box edge
      hsorted hthetaLo hthetaHi hsep hbox hradial hshape htick (Or.inr hupper)

/-- A checked exact-certificate cycle is impossible for any explicit polar
configuration satisfying the certificate's box, angular, and separation
conditions. -/
theorem fifteenGeometricTerminalCycleExcludes
    (radii theta : Fin 15 → ℝ) (box : FifteenBox) (inner : List Nat)
    (node : Lean.Json) (allowLocal : Bool)
    (hsorted : ∀ i j : Fin 15, i.1 < j.1 → theta i ≤ theta j)
    (hthetaLo : ∀ i, 0 ≤ theta i)
    (hthetaHi : ∀ i, theta i ≤ 2 * Real.pi)
    (hsep : ∀ i j : Fin 15, i ≠ j →
      4 ≤ pointNorm
        ((polarPoint (radii i) (theta i)).1 -
            (polarPoint (radii j) (theta j)).1,
         (polarPoint (radii i) (theta i)).2 -
            (polarPoint (radii j) (theta j)).2) ^ 2)
    (hbox : fifteenBoxGood box)
    (hradial : ∀ i : Fin 15,
      (box[i.1]!.1 : ℝ) ≤ radii i ∧
        radii i ≤ (box[i.1]!.2 : ℝ))
    (htag : fifteenJsonAt? node 0 >>= fifteenJsonString? = some "CYCLE")
    (hvalid : fifteenTerminalValid box inner node allowLocal = true) : False := by
  obtain ⟨edges, hedges⟩ := fifteenTerminalValid_cycle_edges_spec
    box inner node allowLocal [] [] htag hvalid
  have hspec := fifteenCycleEdgesValid_sound edges box [] [] hedges
  obtain ⟨start, finish, hstart, hfinish, hchain⟩ :=
    fifteenCycleEdgesSpec_has_closed_chain hspec
  apply fifteenCycleEdgesSpec_excludes hspec hchain
  intro edge hedge
  exact fifteenGeometricCycleEdgeBound radii theta box edge hsorted
    hthetaLo hthetaHi hsep hbox hradial (hspec.edgeShapes edge hedge)
    (hspec.edgeTicks edge hedge)

/-- A checked `SUM` leaf is impossible under an explicit pairwise radial-sum
lower bound; this condition is already part of the Stage 3 geometric handoff. -/
theorem fifteenGeometricTerminalSumExcludes
    (radii : Fin 15 → ℝ) (box : FifteenBox) (inner : List Nat)
    (node : Lean.Json) (allowLocal : Bool)
    (hpair : ∀ i j : Fin 15, i ≠ j → 2 ≤ radii i + radii j)
    (htag : fifteenJsonAt? node 0 >>= fifteenJsonString? = some "SUM")
    (hvalid : fifteenTerminalValid box inner node allowLocal = true)
    (hradial : ∀ i : Fin 15, radii i ≤ (box[i.1]!.2 : ℝ)) : False := by
  obtain ⟨i, j, hij, hj15, _himem, _hjmem, hsum⟩ :=
    fifteenTerminalValid_sum_spec box inner node allowLocal [] [] htag hvalid
  have hi15 : i < 15 := Nat.lt_trans hij hj15
  let fi : Fin 15 := ⟨i, hi15⟩
  let fj : Fin 15 := ⟨j, hj15⟩
  have hfij : fi ≠ fj := by
    intro heq
    have hval : i = j := by simpa [fi, fj] using congrArg Fin.val heq
    exact (Nat.ne_of_lt hij) hval
  have hlower := hpair fi fj hfij
  have hupper : (box[i]!.2 : ℝ) + (box[j]!.2 : ℝ) < 2 := by
    exact_mod_cast hsum
  have hradialSum : radii fi + radii fj ≤
      (box[i]!.2 : ℝ) + (box[j]!.2 : ℝ) :=
    add_le_add (hradial fi) (hradial fj)
  exact (not_lt_of_ge hlower) (lt_of_le_of_lt hradialSum hupper)

end CirclePacking
