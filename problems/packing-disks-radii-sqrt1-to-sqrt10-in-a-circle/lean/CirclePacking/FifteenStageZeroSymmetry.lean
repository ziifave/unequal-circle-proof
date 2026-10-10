import CirclePacking.FifteenStageZero

/-! Exact interface between Stage 0's canonical representative and the
dihedral action on cyclic inner/outer words. -/

namespace CirclePacking

private theorem stage0_foldl_min_mem (initial : Nat) (xs : List Nat) :
    List.foldl Nat.min initial xs ∈ initial :: xs := by
  induction xs generalizing initial with
  | nil => simp
  | cons head tail ih =>
      simp only [List.foldl_cons]
      have hmin : Nat.min initial head = initial ∨
          Nat.min initial head = head := by
        by_cases h : initial ≤ head
        · exact Or.inl (Nat.min_eq_left h)
        · right
          have h' : head ≤ initial := by omega
          exact Nat.min_eq_right h'
      rcases List.mem_cons.mp (ih (Nat.min initial head)) with hfirst | htail
      · rcases hmin with hmin | hmin
        · rw [hfirst, hmin]
          simp
        · rw [hfirst, hmin]
          simp
      · simp [htail]

/-- The canonical mask is one of the original mask or one of its 30 rotations
and reflected rotations.  This makes the symmetry choice used by the finite
enumerator explicit for later geometric transport lemmas. -/
theorem fifteenStage0CanonicalMask_dihedral_origin (mask : Nat) :
    fifteenStage0CanonicalMask mask = mask ∨
      ∃ shift, shift < 15 ∧
        (fifteenStage0CanonicalMask mask = fifteenStage0RotateMask mask shift ∨
          fifteenStage0CanonicalMask mask =
            fifteenStage0RotateMask (fifteenStage0ReverseMask mask) shift) := by
  have hmem :
      List.foldl Nat.min mask (fifteenStage0DihedralMaskCandidates mask) ∈
        mask :: fifteenStage0DihedralMaskCandidates mask :=
    stage0_foldl_min_mem mask (fifteenStage0DihedralMaskCandidates mask)
  rcases List.mem_cons.mp hmem with hmask | hcandidate
  · exact Or.inl hmask
  · right
    obtain ⟨shift, hshift, hentry⟩ := List.mem_flatMap.mp hcandidate
    have hshift15 : shift < 15 := by
      simpa using (List.mem_range.mp hshift)
    rcases List.mem_cons.mp hentry with hrotate | hentry
    · exact ⟨shift, hshift15, Or.inl hrotate⟩
    · exact ⟨shift, hshift15, Or.inr (List.mem_singleton.mp hentry)⟩

end CirclePacking
