import CirclePacking.FifteenCertificateTreeSoundness
import CirclePacking.FifteenCertificateLeafSoundness
import CirclePacking.FifteenCertificateCycleSoundness

/-! Semantic endpoint of the exact certificate work-list replay. -/

namespace CirclePacking

/-- If an accepted certificate work-list contains a profile and every valid
`CYCLE` or `SUM` terminal contradicts that profile, the replay reaches a
`LOCAL` box and the local terminal checker forces each designated inner radius
into the interval `[42/25, 43/25]`. -/
theorem fifteenCheckTasks_profile_reaches_local_bounds
    (fuel : Nat) (tasks : List FifteenTask) (counts result : FifteenTreeCounts)
    (radii : Fin 15 → ℝ)
    (hcycleImpossible : ∀ box inner node,
      fifteenBoxGood box →
      fifteenJsonAt? node 0 >>= fifteenJsonString? = some "CYCLE" →
      fifteenTerminalValid box inner node false = true →
      fifteenRealBoxContains box radii → False)
    (hsumImpossible : ∀ box inner node,
      fifteenJsonAt? node 0 >>= fifteenJsonString? = some "SUM" →
      fifteenTerminalValid box inner node false = true →
      fifteenRealBoxContains box radii → False)
    (hcheck : fifteenCheckTasks fuel tasks counts = some result)
    (hboxesGood : fifteenTaskListBoxesGood tasks)
    (hcontains : ∃ task, task ∈ tasks ∧ fifteenTaskHasProfile task radii) :
    ∃ box inner, fifteenRealBoxContains box radii ∧
      inner = fifteenInnerPositions "001001001001001" ∧
      ∀ p ∈ inner,
        fifteenLocalLo ≤ box[p]!.1 ∧ box[p]!.2 ≤ fifteenLocalHi := by
  obtain ⟨box, inner, node, hprofile, htag, hvalid⟩ :=
    fifteenCheckTasks_profile_reaches_local fuel tasks counts result radii
      hcycleImpossible hsumImpossible hcheck hboxesGood hcontains
  obtain ⟨hinner, hbounds⟩ := fifteenTerminalValid_local_spec
    box inner node true [] [] htag hvalid
  exact ⟨box, inner, hprofile, hinner, hbounds⟩

/-- Packing-specialized form of the work-list reduction. The only remaining
box-side hypothesis is strict positivity and correct dimension at accepted
cycle leaves; sorted radial containment itself discharges every `SUM` leaf. -/
theorem fifteenPackingCheckTasks_force_local_profile
    {R : ℝ} (P : Packing 15 R) (hunit : ∀ k, (P.circles k).radius = 1)
    (fuel : Nat) (tasks : List FifteenTask) (counts result : FifteenTreeCounts)
    (hcheck : fifteenCheckTasks fuel tasks counts = some result)
    (hboxesGood : fifteenTaskListBoxesGood tasks)
    (hcontains : ∃ task, task ∈ tasks ∧
      fifteenTaskHasProfile task (fifteenPackingSortedRadius P)) :
    ∃ box inner,
      fifteenRealBoxContains box (fifteenPackingSortedRadius P) ∧
      inner = fifteenInnerPositions "001001001001001" ∧
      ∀ p ∈ inner,
        fifteenLocalLo ≤ box[p]!.1 ∧ box[p]!.2 ≤ fifteenLocalHi := by
  apply fifteenCheckTasks_profile_reaches_local_bounds fuel tasks counts result
    (fifteenPackingSortedRadius P)
  · intro box inner node hboxGood htag hvalid hprofile
    have hradial : ∀ k : Fin 15,
        (box[k.1]!.1 : ℝ) ≤ fifteenPackingSortedRadius P k ∧
          fifteenPackingSortedRadius P k ≤ (box[k.1]!.2 : ℝ) := by
      intro k
      exact hprofile k
    exact fifteen_unit_packing_terminal_cycle_excludes P hunit box inner node
      false htag hvalid hboxGood.1 hboxGood.2 hradial
  · intro box inner node htag hvalid hprofile
    have hradial : ∀ k : Fin 15,
        fifteenPackingSortedRadius P k ≤ (box[k.1]!.2 : ℝ) := by
      intro k
      exact (hprofile k).2
    exact fifteen_unit_packing_terminal_sum_excludes P hunit box inner node
      false [] [] htag hvalid hradial
  · exact hcheck
  · exact hboxesGood
  · exact hcontains

end CirclePacking
