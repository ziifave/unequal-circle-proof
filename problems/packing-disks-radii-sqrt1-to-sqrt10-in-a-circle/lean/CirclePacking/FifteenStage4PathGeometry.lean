import CirclePacking.FifteenStage4Projection
import CirclePacking.FifteenStage4CycleGeometry
import CirclePacking.FifteenStage3OwnerPath

/-! Geometry-facing invariants for the Stage 4 target branch.  Along this
branch, assigned inner slots retain their chosen refined radial owner, other
inner slots retain the sentinel 12, and outer slots retain wall label 11. -/

namespace CirclePacking

/-- Any owner array determines the complete branch obtained by reading its
labels in the profile's inner-slot order. -/
theorem fifteenStage4TargetPath_full (pattern : String) (target : Array Nat) :
    ∃ s : S4State, FifteenStage4TargetPath pattern target s ∧
      s.depth = (s4InnerPositions pattern).size := by
  let inner := s4InnerPositions pattern
  have hbuild : ∀ n, n ≤ inner.size →
      ∃ s : S4State, FifteenStage4TargetPath pattern target s ∧ s.depth = n := by
    intro n
    induction n with
    | zero =>
        intro _
        exact ⟨s4Initial pattern, .initial, rfl⟩
    | succ n ih =>
        intro hbound
        have hprev : n ≤ inner.size := by omega
        obtain ⟨s, hs, hdepth⟩ := ih hprev
        have hsplit : s.depth < inner.size := by omega
        refine ⟨s4Next inner s target[inner[s.depth]!]!, .step hs ?_, ?_⟩
        · simpa [inner] using hsplit
        · simp [s4Next, hdepth]
  simpa [inner] using hbuild inner.size (Nat.le_refl _)

def fifteenStage4OwnerLabelArray (labels : Fin 15 → Nat) : Array Nat :=
  Array.ofFn labels

theorem fifteenStage4OwnerLabelArray_get (labels : Fin 15 → Nat) (i : Nat)
    (hi : i < 15) :
    (fifteenStage4OwnerLabelArray labels)[i]! = labels ⟨i, hi⟩ := by
  unfold fifteenStage4OwnerLabelArray
  rw [getElem!_pos _ _ (by simpa using hi)]
  rw [Array.getElem_ofFn (by simpa using hi)]

theorem fifteenStage4TargetPath_labels_size (pattern : String) (target : Array Nat)
    {s : S4State} (hpath : FifteenStage4TargetPath pattern target s) :
    s.labels.size = s4N := by
  induction hpath with
  | initial => simp [s4Initial, s4N]
  | @step s hpath hdepth ih =>
      simp [s4Next, ih]

private theorem s4InitialLabel_spec (pattern : String) (p : Nat)
    (hp : p < s4N) :
    (s4Initial pattern).labels[p]! =
      if pattern.toList[p]? = some '1' then 12 else 11 := by
  simp [s4Initial, s4N]
  have hp15 : p < 15 := by simpa [s4N] using hp
  have hmap : p < ((Array.range 15).map
      (fun i => if pattern.toList[i]? = some '1' then 12 else 11)).size := by
    simp [hp15]
  rw [getElem!_pos
    ((Array.range 15).map
      (fun i => if pattern.toList[i]? = some '1' then 12 else 11)) p hmap]
  rw [Array.getElem_map
    (fun i => if pattern.toList[i]? = some '1' then 12 else 11) hmap]
  simp [hp15]

/-- The target label has been written exactly at each already visited inner
slot; unvisited inner slots keep the checker sentinel 12. -/
theorem fifteenStage4TargetPath_slot_semantics (pattern : String)
    (target : Array Nat) {s : S4State}
    (hpath : FifteenStage4TargetPath pattern target s) :
    ∀ k, k < (s4InnerPositions pattern).size →
      s.labels[(s4InnerPositions pattern)[k]!]! =
        if k < s.depth then target[(s4InnerPositions pattern)[k]!]! else 12 := by
  induction hpath with
  | initial =>
      intro k hk
      let inner := s4InnerPositions pattern
      have hmemOrdinary : inner[k] ∈ inner.toList := Array.getElem_mem_toList hk
      have hmem : inner[k]! ∈ inner.toList := by
        rw [getElem!_pos inner k hk]
        exact hmemOrdinary
      have hchar := (s3InnerPositions_mem_iff_char pattern inner[k]!).mp (by
        simpa [inner, s4InnerPositions_eq_s3] using hmem)
      have hindex : inner[k]! < s4N := by
        simpa [s4N, s3N] using hchar.1
      have hbits : pattern.toList[(s4InnerPositions pattern)[k]!]? = some '1' := by
        simpa [inner] using hchar.2
      change (s4Initial pattern).labels[(s4InnerPositions pattern)[k]!]! = 12
      rw [s4InitialLabel_spec pattern _ (by simpa using hindex)]
      simp [hbits]
  | @step s hpath hdepth ih =>
      intro k hk
      let inner := s4InnerPositions pattern
      have hposition : inner[s.depth]! < s.labels.size := by
        rw [fifteenStage4TargetPath_labels_size pattern target hpath]
        have hdepth' : s.depth < (s3InnerPositions pattern).size := by
          simpa [inner, s4InnerPositions_eq_s3] using hdepth
        have hbound := fifteenStage3InnerPosition_get_bound pattern hdepth'
        simpa [inner, s4N, s4InnerPositions_eq_s3] using hbound
      have hsplit : k < s.depth ∨ k = s.depth ∨ s.depth < k := by omega
      rcases hsplit with hprev | heq | hnext
      · have hdifferent : inner[k]! ≠ inner[s.depth]! := by
          intro heqArray
          have h1 : k < inner.toList.length := by simpa using Nat.lt_trans hprev hdepth
          have h2 : s.depth < inner.toList.length := by simpa using hdepth
          have hindexEq : k = s.depth :=
            (fifteenStage3InnerPositions_nodup pattern).getElem!_inj h1 h2 |>.mp (by
              calc
                inner.toList[k]! = inner[k]! := by rw [Array.getElem!_toList]
                _ = inner[s.depth]! := heqArray
                _ = inner.toList[s.depth]! := by rw [Array.getElem!_toList])
          omega
        change getElem! (s.labels.set! inner[s.depth]!
          target[inner[s.depth]!]!) (inner[k]!) = _
        rw [Array.getElem!_set!_ne _ _ _ _ (Ne.symm hdifferent)]
        rw [ih k (by omega)]
        simp [s4Next, hprev]
        intro hbad
        omega
      · subst k
        change getElem! (s.labels.set! inner[s.depth]!
          target[inner[s.depth]!]!) (inner[s.depth]!) = _
        rw [Array.getElem!_set!_self _ _ _ hposition]
        simp [s4Next, inner]
      · have hdifferent : inner[k]! ≠ inner[s.depth]! := by
          intro heqArray
          have h1 : s.depth < inner.toList.length := by simpa using hdepth
          have h2 : k < inner.toList.length := by simpa using hk
          have hindexEq : s.depth = k :=
            (fifteenStage3InnerPositions_nodup pattern).getElem!_inj h1 h2 |>.mp (by
              calc
                inner.toList[s.depth]! = inner[s.depth]! := by rw [Array.getElem!_toList]
                _ = inner[k]! := heqArray.symm
                _ = inner.toList[k]! := by rw [Array.getElem!_toList])
          omega
        change getElem! (s.labels.set! inner[s.depth]!
          target[inner[s.depth]!]!) (inner[k]!) = _
        rw [Array.getElem!_set!_ne _ _ _ _ (Ne.symm hdifferent)]
        rw [ih k hk]
        simp [s4Next, Nat.not_lt_of_ge (Nat.le_of_lt hnext)]
        intro hbad
        omega

theorem fifteenStage4TargetPath_outerSlot_eleven (pattern : String)
    (target : Array Nat) {s : S4State}
    (hpath : FifteenStage4TargetPath pattern target s)
    (p : Nat) (hp : p < s4N)
    (houter : p ∉ (s4InnerPositions pattern).toList) : s.labels[p]! = 11 := by
  induction hpath with
  | initial =>
      have hchar : pattern.toList[p]? ≠ some '1' := by
        intro h
        apply houter
        have hmem := (s3InnerPositions_mem_iff_char pattern p).mpr ⟨hp, h⟩
        simpa [s4InnerPositions_eq_s3] using hmem
      change (s4Initial pattern).labels[p]! = 11
      rw [s4InitialLabel_spec pattern p hp]
      simp [hchar]
  | @step s hpath hdepth ih =>
      have hposition : (s4InnerPositions pattern)[s.depth]! < s.labels.size := by
        rw [fifteenStage4TargetPath_labels_size pattern target hpath]
        have hdepth' : s.depth < (s3InnerPositions pattern).size := by
          simpa [s4InnerPositions_eq_s3] using hdepth
        have hbound := fifteenStage3InnerPosition_get_bound pattern hdepth'
        simpa [s4N, s4InnerPositions_eq_s3] using hbound
      have hmemOrdinary : (s4InnerPositions pattern)[s.depth] ∈
          (s4InnerPositions pattern).toList := Array.getElem_mem_toList hdepth
      have hmem : (s4InnerPositions pattern)[s.depth]! ∈
          (s4InnerPositions pattern).toList := by
        rw [getElem!_pos (s4InnerPositions pattern) s.depth hdepth]
        exact hmemOrdinary
      have hdifferent : p ≠ (s4InnerPositions pattern)[s.depth]! := by
        intro heq
        apply houter
        rw [heq]
        exact hmem
      change getElem! (s.labels.set! (s4InnerPositions pattern)[s.depth]!
        target[(s4InnerPositions pattern)[s.depth]!]!) p = 11
      rw [Array.getElem!_set!_ne _ _ _ _ (Ne.symm hdifferent)]
      exact ih

theorem fifteenStage4TargetPath_knownOwnerLabel
    (labels : Fin 15 → Nat) (profile : Fin 15 → Bool)
    (houterLabel : ∀ i, profile i = false → labels i = 11)
    {s : S4State}
    (hpath : FifteenStage4TargetPath (fifteenStage0ProfileWord profile)
      (fifteenStage4OwnerLabelArray labels) s)
    (i : Fin 15) (hknown : s.labels[i.1]! < 12) :
    s.labels[i.1]! = labels i := by
  let pattern := fifteenStage0ProfileWord profile
  let inner := s4InnerPositions pattern
  by_cases hinner : profile i = true
  · have hmem : i.1 ∈ inner.toList := by
      apply (fifteenStage3ProfileWord_inner_iff profile i).mpr
      simpa [pattern, inner, s4InnerPositions_eq_s3] using hinner
    obtain ⟨k, hk, hget⟩ := List.mem_iff_getElem.mp hmem
    have hkSize : k < inner.size := by simpa using hk
    have hposition : inner[k]! = i.1 := by
      calc
        inner[k]! = inner.toList[k]! := by rw [Array.getElem!_toList]
        _ = inner.toList[k] := getElem!_pos inner.toList k hk
        _ = i.1 := hget
    have hslot := fifteenStage4TargetPath_slot_semantics pattern
      (fifteenStage4OwnerLabelArray labels) hpath k (by simpa [inner] using hkSize)
    have hassigned : k < s.depth := by
      by_contra hnot
      have hge : s.depth ≤ k := Nat.le_of_not_gt hnot
      have hsentinel : s.labels[inner[k]!]! = 12 := by
        simpa [not_lt.mpr hge] using hslot
      rw [hposition] at hsentinel
      omega
    have htarget : s.labels[inner[k]!]! =
        (fifteenStage4OwnerLabelArray labels)[inner[k]!]! := by
      simpa [hassigned] using hslot
    rw [hposition] at htarget
    calc
      s.labels[i.1]! = (fifteenStage4OwnerLabelArray labels)[i.1]! := htarget
      _ = labels i := fifteenStage4OwnerLabelArray_get labels i.1 i.isLt
  · have hfalse : profile i = false := Bool.eq_false_of_not_eq_true hinner
    have hnotmem : i.1 ∉ inner.toList := by
      intro hmem
      have htrue := (fifteenStage3ProfileWord_inner_iff profile i).mp
        (by simpa [pattern, inner, s4InnerPositions_eq_s3] using hmem)
      exact hinner htrue
    have hwall := fifteenStage4TargetPath_outerSlot_eleven pattern
      (fifteenStage4OwnerLabelArray labels) hpath i.1 i.isLt
      (by simpa [inner] using hnotmem)
    rw [hwall, houterLabel i hfalse]

theorem fifteenStage4TargetPath_cycleLeaf_excluded
    (radii : Fin 15 → ℝ) (labels : Fin 15 → Nat)
    (howners : ∀ i, fifteenStage4OwnerSpec (labels i) (radii i))
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
    (houterLabel : ∀ i, profile i = false → labels i = 11)
    {s : S4State}
    (hpath : FifteenStage4TargetPath (fifteenStage0ProfileWord profile)
      (fifteenStage4OwnerLabelArray labels) s)
    (edges : List S4CertEdge)
    (hcycle : s4CycleValid s.labels edges = true) : False := by
  have hpartialOwners : ∀ i,
      s4ArrayOwnerLabels s.labels i < 12 →
        fifteenStage4OwnerSpec (s4ArrayOwnerLabels s.labels i) (radii i) := by
    intro i hi
    have hlabel := fifteenStage4TargetPath_knownOwnerLabel labels profile
      houterLabel hpath i (by simpa [s4ArrayOwnerLabels] using hi)
    change s.labels[i.1]! = labels i at hlabel
    change fifteenStage4OwnerSpec s.labels[i.1]! (radii i)
    rw [hlabel]
    exact howners i
  exact s4CycleValid_excludes_ownerAngles s.labels radii hpartialOwners hsum
    theta hsorted hthetaLo hthetaHi hsep edges hcycle

end CirclePacking
