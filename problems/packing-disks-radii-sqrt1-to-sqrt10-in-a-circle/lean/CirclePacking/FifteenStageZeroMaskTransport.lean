import CirclePacking.FifteenStageZeroSymmetry
import CirclePacking.FifteenStageZeroProfileTransport
import Mathlib.Algebra.BigOperators.Group.List.Basic

/-! Match the actual permutation of a binary radius profile to the exact
rotation/reflection arithmetic used by the Stage 0 enumerator. No finite
evaluation of the possible profiles is required. -/

namespace CirclePacking

private theorem stage0_selected_fold_sum
    (bits : Nat → Bool) (term : Nat → Nat)
    (items : List Nat) (initial : Nat) :
    items.foldl (fun result i => if bits i then result + term i else result)
        initial =
      initial + (items.map fun i => (bits i).toNat * term i).sum := by
  induction items generalizing initial with
  | nil => simp
  | cons head tail ih =>
      simp only [List.foldl_cons, List.map_cons, List.sum_cons]
      rw [ih]
      cases bits head <;> simp [Nat.add_assoc]

private theorem stage0_list_range_sum (term : Nat → Nat) (n : Nat) :
    ((List.range n).map term).sum = ∑ i ∈ Finset.range n, term i := by
  induction n with
  | zero => simp
  | succ n ih =>
      simp [List.range_succ, List.map_append, List.sum_append,
        Finset.sum_range_succ, ih]

private theorem stage0_rotate_profile_sum
    (profile : Fin 15 → Bool) (shift : Fin 15) :
    fifteenStage0RotateMask (fifteenStage0ProfileMask profile) shift.val =
      ∑ i : Fin 15, (profile i).toNat * 2 ^ (14 - (i + shift).val) := by
  change (List.range 15).foldl (fun result i =>
    if Nat.testBit (fifteenStage0ProfileMask profile) (14 - i) then
      result + 2 ^ (14 - ((i + shift.val) % 15)) else result) 0 = _
  rw [stage0_selected_fold_sum, zero_add, stage0_list_range_sum, Finset.sum_range]
  apply Finset.sum_congr rfl
  intro i _
  rw [fifteenStage0ProfileMask_testBit profile i, Fin.val_add]

theorem fifteenStage0ProfileMask_rotation
    (profile : Fin 15 → Bool) (shift : Fin 15) :
    fifteenStage0ProfileMask (fifteenStage0TransformProfile profile false shift) =
      fifteenStage0RotateMask (fifteenStage0ProfileMask profile) shift.val := by
  rw [fifteenStage0ProfileMask_sum, stage0_rotate_profile_sum]
  exact (Fintype.sum_equiv (finCycle shift)
    (fun i : Fin 15 => (profile i).toNat * 2 ^ (14 - (i + shift).val))
    (fun j : Fin 15 =>
      (fifteenStage0TransformProfile profile false shift j).toNat *
        2 ^ (14 - j.val)) (fun i => by
          simp [fifteenStage0TransformProfile, fifteenStage0DihedralPermutation])).symm

private theorem stage0_reverse_profile_sum (profile : Fin 15 → Bool) :
    fifteenStage0ReverseMask (fifteenStage0ProfileMask profile) =
      ∑ i : Fin 15, (profile i).toNat * 2 ^ i.val := by
  change (List.range 15).foldl (fun result i =>
    if Nat.testBit (fifteenStage0ProfileMask profile) (14 - i) then
      result + 2 ^ i else result) 0 = _
  rw [stage0_selected_fold_sum, zero_add, stage0_list_range_sum, Finset.sum_range]
  apply Finset.sum_congr rfl
  intro i _
  rw [fifteenStage0ProfileMask_testBit profile i]

theorem fifteenStage0ProfileMask_reflection (profile : Fin 15 → Bool) :
    fifteenStage0ProfileMask (fun i => profile i.rev) =
      fifteenStage0ReverseMask (fifteenStage0ProfileMask profile) := by
  rw [fifteenStage0ProfileMask_sum, stage0_reverse_profile_sum]
  exact (Fintype.sum_equiv Fin.revPerm
    (fun i : Fin 15 => (profile i).toNat * 2 ^ i.val)
    (fun j : Fin 15 => (profile j.rev).toNat * 2 ^ (14 - j.val))
    (fun i => by
      have hrev : 14 - i.rev.val = i.val := by rw [Fin.val_rev]; omega
      change (profile i).toNat * 2 ^ i.val =
        (profile i.rev.rev).toNat * 2 ^ (14 - i.rev.val)
      rw [Fin.rev_rev, hrev])).symm

theorem fifteenStage0ProfileMask_reflected_rotation
    (profile : Fin 15 → Bool) (shift : Fin 15) :
    fifteenStage0ProfileMask (fifteenStage0TransformProfile profile true shift) =
      fifteenStage0RotateMask
        (fifteenStage0ReverseMask (fifteenStage0ProfileMask profile)) shift.val := by
  change fifteenStage0ProfileMask
    (fifteenStage0TransformProfile (fun i => profile i.rev) false shift) = _
  rw [fifteenStage0ProfileMask_rotation, fifteenStage0ProfileMask_reflection]

/-- Some explicit dihedral permutation of the geometric profile has exactly
the canonical mask used by the finite enumerator. -/
theorem fifteenStage0Profile_canonical_dihedral
    (profile : Fin 15 → Bool) :
    ∃ reflected : Bool, ∃ shift : Fin 15,
      fifteenStage0ProfileMask (fifteenStage0TransformProfile profile reflected shift) =
        fifteenStage0CanonicalMask (fifteenStage0ProfileMask profile) := by
  rcases fifteenStage0CanonicalMask_dihedral_origin
      (fifteenStage0ProfileMask profile) with horiginal | ⟨shift, hshift, hcases⟩
  · refine ⟨false, 0, ?_⟩
    have hid : fifteenStage0TransformProfile profile false 0 = profile := by
      funext i
      change profile (i - (0 : Fin 15)) = profile i
      rw [sub_zero]
    rw [hid]
    exact horiginal.symm
  · rcases hcases with hrotation | hreflection
    · exact ⟨false, ⟨shift, hshift⟩,
        (fifteenStage0ProfileMask_rotation profile ⟨shift, hshift⟩).trans
          hrotation.symm⟩
    · exact ⟨true, ⟨shift, hshift⟩,
        (fifteenStage0ProfileMask_reflected_rotation profile ⟨shift, hshift⟩).trans
          hreflection.symm⟩

theorem fifteenStage0ProfileWord_eq_canonical_of_mask
    (profile canonical : Fin 15 → Bool)
    (hmask : fifteenStage0ProfileMask canonical =
      fifteenStage0CanonicalMask (fifteenStage0ProfileMask profile)) :
    fifteenStage0ProfileWord canonical = fifteenStage0CanonicalProfileWord profile := by
  exact congrArg (fun mask : Nat => String.ofList ((List.range 15).map
    fun i => if Nat.testBit mask (14 - i) then '1' else '0')) hmask

end CirclePacking
