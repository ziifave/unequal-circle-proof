import CirclePacking.FifteenCertificateTreeSoundness
import CirclePacking.FifteenCertificateLeafSoundness

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
      fifteenJsonAt? node 0 >>= fifteenJsonString? = some "CYCLE" →
      fifteenTerminalValid box inner node false = true →
      fifteenRealBoxContains box radii → False)
    (hsumImpossible : ∀ box inner node,
      fifteenJsonAt? node 0 >>= fifteenJsonString? = some "SUM" →
      fifteenTerminalValid box inner node false = true →
      fifteenRealBoxContains box radii → False)
    (hcheck : fifteenCheckTasks fuel tasks counts = some result)
    (hcontains : ∃ task, task ∈ tasks ∧ fifteenTaskHasProfile task radii) :
    ∃ box inner, fifteenRealBoxContains box radii ∧
      inner = fifteenInnerPositions "001001001001001" ∧
      ∀ p ∈ inner,
        fifteenLocalLo ≤ box[p]!.1 ∧ box[p]!.2 ≤ fifteenLocalHi := by
  obtain ⟨box, inner, node, hprofile, htag, hvalid⟩ :=
    fifteenCheckTasks_profile_reaches_local fuel tasks counts result radii
      hcycleImpossible hsumImpossible hcheck hcontains
  obtain ⟨hinner, hbounds⟩ := fifteenTerminalValid_local_spec
    box inner node true [] [] htag hvalid
  exact ⟨box, inner, hprofile, hinner, hbounds⟩

end CirclePacking
