import CirclePacking.FifteenStage3CycleGeometry
import CirclePacking.FifteenStage3OwnerPath

/-! Geometry and the certificate's partial-label state meet here. -/

namespace CirclePacking

/-- If a slot on the checker-selected path has a known radial label, that
label agrees with the geometric owner. Inner slots use the target-path
assignment invariant; outer slots retain the wall sentinel `7`. -/
theorem fifteenStage3TargetPath_knownOwnerLabel
    (labels : Fin 15 → Nat) (profile : Fin 15 → Bool)
    (houterLabel : ∀ i, profile i = false → labels i = 7)
    {s : S3State}
    (hpath : FifteenStage3TargetPath (fifteenStage0ProfileWord profile)
      (fifteenStage3OwnerLabelArray labels) s)
    (i : Fin 15) (hknown : s.labels[i.1]! < 8) :
    s.labels[i.1]! = labels i := by
  let pattern := fifteenStage0ProfileWord profile
  let inner := s3InnerPositions pattern
  by_cases hinner : profile i = true
  · have hmem : i.1 ∈ inner.toList := by
      apply (fifteenStage3ProfileWord_inner_iff profile i).mpr
      simpa [pattern] using hinner
    obtain ⟨k, hk, hget⟩ := List.mem_iff_getElem.mp hmem
    have hkSize : k < inner.size := by simpa using hk
    have hposition : inner[k]! = i.1 := by
      calc
        inner[k]! = inner.toList[k]! := by rw [Array.getElem!_toList]
        _ = inner.toList[k] := getElem!_pos inner.toList k hk
        _ = i.1 := hget
    have hslot := fifteenStage3TargetPath_slot_semantics pattern
      (fifteenStage3OwnerLabelArray labels) hpath k (by simpa [inner] using hkSize)
    have hslotNotSentinel : s.labels[inner[k]!]! ≠ 8 := by
      rw [hposition]
      omega
    have hassigned : k < s.depth := by
      by_contra hnot
      have hge : s.depth ≤ k := Nat.le_of_not_gt hnot
      have hslotEight : s.labels[inner[k]!]! = 8 := by
        simpa [not_lt.mpr hge] using hslot
      exact hslotNotSentinel hslotEight
    have hassignedLabel : s.labels[inner[k]!]! =
        (fifteenStage3OwnerLabelArray labels)[inner[k]!]! := by
      simpa [hassigned] using hslot
    rw [hposition] at hassignedLabel
    calc
      s.labels[i.1]! = (fifteenStage3OwnerLabelArray labels)[i.1]! := hassignedLabel
      _ = labels i := fifteenStage3OwnerLabelArray_get labels i.1 i.isLt
  · have hfalse : profile i = false := Bool.eq_false_of_not_eq_true hinner
    have hnotmem : i.1 ∉ inner.toList := by
      intro hmem
      have htrue := (fifteenStage3ProfileWord_inner_iff profile i).mp
        (by simpa [pattern, inner] using hmem)
      exact hinner htrue
    have hwall := fifteenStage3TargetPath_outerSlot_seven pattern
      (fifteenStage3OwnerLabelArray labels) hpath i.1 i.isLt
      (by simpa [inner] using hnotmem)
    rw [hwall, houterLabel i hfalse]

/-- A verified Stage 3 cycle leaf is incompatible with a geometrically valid
owner path, even when the checker has not assigned every inner slot yet.
The sentinel label `8` is handled by the zero-tick angular bound. -/
theorem fifteenStage3TargetPath_cycleLeaf_excluded
    (radii : Fin 15 → ℝ) (labels : Fin 15 → Nat)
    (howners : ∀ i, fifteenStage3OwnerSpec (labels i) (radii i))
    (hsum : ∀ i j, i ≠ j → 2 ≤ radii i + radii j)
    (theta : Fin 15 → ℝ)
    (hsorted : ∀ i j : Fin 15, i.1 < j.1 → theta i ≤ theta j)
    (hthetaLo : ∀ i, 0 ≤ theta i)
    (hthetaHi : ∀ i, theta i ≤ 2 * Real.pi)
    (hsep : ∀ i j : Fin 15, i ≠ j →
      4 ≤ pointNorm
        ((polarPoint (radii i) (theta i)).1 - (polarPoint (radii j) (theta j)).1,
         (polarPoint (radii i) (theta i)).2 - (polarPoint (radii j) (theta j)).2) ^ 2)
    (profile : Fin 15 → Bool)
    (houterLabel : ∀ i, profile i = false → labels i = 7)
    {s : S3State}
    (hpath : FifteenStage3TargetPath (fifteenStage0ProfileWord profile)
      (fifteenStage3OwnerLabelArray labels) s)
    (edges : List S3CertEdge)
    (hcycle : s3CycleValid s.labels edges = true) : False := by
  have hpartialOwners : ∀ i,
      s3ArrayOwnerLabels s.labels i < 8 →
        fifteenStage3OwnerSpec (s3ArrayOwnerLabels s.labels i) (radii i) := by
    intro i hi
    have hlabel := fifteenStage3TargetPath_knownOwnerLabel labels profile
      houterLabel hpath i (by simpa [s3ArrayOwnerLabels] using hi)
    have harray : s3ArrayOwnerLabels s.labels i = s.labels[i.1]! := rfl
    rw [harray, hlabel]
    exact howners i
  exact s3CycleValid_excludes_ownerAngles s.labels radii hpartialOwners hsum
    theta hsorted hthetaLo hthetaHi hsep edges hcycle

end CirclePacking
