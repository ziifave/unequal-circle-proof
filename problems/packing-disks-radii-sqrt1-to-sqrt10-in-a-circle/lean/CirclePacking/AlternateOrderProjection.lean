import CirclePacking.NineCirclePackingSoundness

/-!
# Finite order projection for the alternate skeleton cases

The global certificate leaves four sector assignments around the ordered
large-circle skeleton `(10, 7, 8, 9)`.  Their effective masks are three copies
of `(5, 16, 40, 2)` and one copy of `(4, 16, 41, 2)`.  This file replays the
finite combinatorial step that every sector-local ordering of either mask,
after deleting disk 1, is one of the checked nine-circle orders P or Q.

The Lean geometry theorems for P and Q can then be applied once an angular
argument supplies the cyclic order of the four skeleton disks and the order
inside each sector.  Deriving those sector facts from the main radial-tree
terminal hypotheses is a separate remaining step.
-/

namespace CirclePacking

private def d0 : Fin 10 := ⟨0, by decide⟩
private def d1 : Fin 10 := ⟨1, by decide⟩
private def d2 : Fin 10 := ⟨2, by decide⟩
private def d3 : Fin 10 := ⟨3, by decide⟩
private def d4 : Fin 10 := ⟨4, by decide⟩
private def d5 : Fin 10 := ⟨5, by decide⟩
private def d6 : Fin 10 := ⟨6, by decide⟩
private def d7 : Fin 10 := ⟨7, by decide⟩
private def d8 : Fin 10 := ⟨8, by decide⟩
private def d9 : Fin 10 := ⟨9, by decide⟩

/-- Convert a six-bit sector mask to the corresponding standard disk indices.
Bit zero represents disk 1, through bit five representing disk 6. -/
def alternateSectorMaskLabels (mask : Nat) : List (Fin 10) :=
  (List.range 6).filterMap fun k =>
    if (mask / 2 ^ k) % 2 = 1 then
      if hk : k < 10 then some ⟨k, hk⟩ else none
    else none

def alternateSectorMasksA : List Nat := [5, 16, 40, 2]
def alternateSectorMasksB : List Nat := [4, 16, 41, 2]

theorem alternateSectorMasksA_decode :
    alternateSectorMasksA.map alternateSectorMaskLabels =
      [[d0, d2], [d4], [d3, d5], [d1]] := by
  native_decide

theorem alternateSectorMasksB_decode :
    alternateSectorMasksB.map alternateSectorMaskLabels =
      [[d2], [d4], [d0, d3, d5], [d1]] := by
  native_decide

private theorem perm_pair_mem_options {a b : Fin 10} (hab : a ≠ b)
    {xs : List (Fin 10)} (h : [a, b].Perm xs) :
    xs ∈ [[a, b], [b, a]] := by
  have hlen : xs.length = 2 := by simpa using h.length_eq.symm
  rcases List.length_eq_two.mp hlen with ⟨x, y, hxy⟩
  subst xs
  have hnd : List.Nodup [x, y] := h.nodup_iff.mp (by simp [hab])
  have hneq : x ≠ y := by simpa using (List.nodup_cons.mp hnd).1
  have hx : x = a ∨ x = b := by
    have hm : x ∈ [a, b] := h.mem_iff.mpr (by simp)
    simpa using hm
  have hy : y = a ∨ y = b := by
    have hm : y ∈ [a, b] := h.mem_iff.mpr (by simp)
    simpa using hm
  rcases hx with hxa | hxb
  · subst x
    rcases hy with hya | hyb
    · subst y
      exact False.elim (hneq rfl)
    · subst y
      simp
  · subst x
    rcases hy with hya | hyb
    · subst y
      simp
    · subst y
      exact False.elim (hneq rfl)

private theorem perm_singleton_eq {a : Fin 10} {xs : List (Fin 10)}
    (h : [a].Perm xs) : xs = [a] := by
  have hlen : xs.length = 0 + 1 := by simpa using h.length_eq.symm
  rcases List.length_eq_succ_iff.mp hlen with ⟨x, tail, hxs, htail⟩
  have htail' : tail = [] := by simpa using htail
  subst tail
  have hxa : x = a := by
    have hx : x ∈ xs := by rw [← hxs]; simp
    have hm : x ∈ [a] := h.mem_iff.mpr hx
    simpa using hm
  subst x
  simpa using hxs.symm

private theorem perm_triple_mem_options {a b c : Fin 10}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    {xs : List (Fin 10)} (h : [a, b, c].Perm xs) :
    xs ∈ [[a, b, c], [a, c, b], [b, a, c], [b, c, a],
      [c, a, b], [c, b, a]] := by
  have hlen : xs.length = 3 := by simpa using h.length_eq.symm
  rcases List.length_eq_three.mp hlen with ⟨x, y, z, hxyz⟩
  subst xs
  have hnd : List.Nodup [x, y, z] :=
    h.nodup_iff.mp (by simp [hab, hac, hbc])
  rcases List.nodup_cons.mp hnd with ⟨hxnot, hyznd⟩
  have hxy : x ≠ y := by
    intro heq
    apply hxnot
    simp [heq]
  have hxz : x ≠ z := by
    intro heq
    apply hxnot
    simp [heq]
  have hyz : y ≠ z := by
    simpa using (List.nodup_cons.mp hyznd).1
  have hx : x = a ∨ x = b ∨ x = c := by
    have hm : x ∈ [a, b, c] := h.mem_iff.mpr (by simp)
    simpa using hm
  have hy : y = a ∨ y = b ∨ y = c := by
    have hm : y ∈ [a, b, c] := h.mem_iff.mpr (by simp)
    simpa using hm
  have hz : z = a ∨ z = b ∨ z = c := by
    have hm : z ∈ [a, b, c] := h.mem_iff.mpr (by simp)
    simpa using hm
  rcases hx with hxa | hxb | hxc <;>
    rcases hy with hya | hyb | hyc <;>
    rcases hz with hza | hzb | hzc <;>
      subst_vars <;> simp_all

/-- Insert four sector-local lists between the cyclic skeleton
`10, 7, 8, 9`.  The indices here are labels minus one. -/
def alternateInterleave (s0 s1 s2 s3 : List (Fin 10)) : List (Fin 10) :=
  [d9] ++ s0 ++ [d6] ++ s1 ++ [d7] ++ s2 ++ [d8] ++ s3

def alternateSectorOrders
    (s0 s1 s2 s3 : List (List (Fin 10))) : List (List (Fin 10)) :=
  s0.flatMap fun a => s1.flatMap fun b => s2.flatMap fun c =>
    s3.map fun d => alternateInterleave a b c d

/-- All local permutations for the mask `(5,16,40,2)`. -/
def alternateOrdersA : List (List (Fin 10)) :=
  alternateSectorOrders
    [[d0, d2], [d2, d0]]
    [[d4]]
    [[d3, d5], [d5, d3]]
    [[d1]]

/-- All local permutations for the mask `(4,16,41,2)`. -/
def alternateOrdersB : List (List (Fin 10)) :=
  alternateSectorOrders
    [[d2]]
    [[d4]]
    [[d0, d3, d5], [d0, d5, d3], [d3, d0, d5],
      [d3, d5, d0], [d5, d0, d3], [d5, d3, d0]]
    [[d1]]

def alternateNineOrderP : List (Fin 10) :=
  [d9, d2, d6, d4, d7, d3, d5, d8, d1]

def alternateNineOrderQ : List (Fin 10) :=
  [d9, d2, d6, d4, d7, d5, d3, d8, d1]

def alternateDeleteDiskOne (order : List (Fin 10)) : List (Fin 10) :=
  order.filter (· != d0)

def alternateProjectionCheck (orders : List (List (Fin 10))) : Bool :=
  orders.all fun order =>
    decide (alternateDeleteDiskOne order = alternateNineOrderP) ||
      decide (alternateDeleteDiskOne order = alternateNineOrderQ)

theorem alternateOrdersA_projection_check :
    alternateProjectionCheck alternateOrdersA = true := by
  native_decide

theorem alternateOrdersB_projection_check :
    alternateProjectionCheck alternateOrdersB = true := by
  native_decide

theorem alternateOrdersA_project_to_P_or_Q (order : List (Fin 10))
    (horder : order ∈ alternateOrdersA) :
    alternateDeleteDiskOne order = alternateNineOrderP ∨
      alternateDeleteDiskOne order = alternateNineOrderQ := by
  have h := (List.all_eq_true.mp alternateOrdersA_projection_check) order horder
  simpa [alternateProjectionCheck, Bool.or_eq_true, decide_eq_true_eq] using h

theorem alternateOrdersB_project_to_P_or_Q (order : List (Fin 10))
    (horder : order ∈ alternateOrdersB) :
    alternateDeleteDiskOne order = alternateNineOrderP ∨
      alternateDeleteDiskOne order = alternateNineOrderQ := by
  have h := (List.all_eq_true.mp alternateOrdersB_projection_check) order horder
  simpa [alternateProjectionCheck, Bool.or_eq_true, decide_eq_true_eq] using h

theorem alternateOrdersA_mem_of_sector_orders
    {s0 s1 s2 s3 : List (Fin 10)}
    (h0 : s0 ∈ [[d0, d2], [d2, d0]])
    (h1 : s1 ∈ [[d4]])
    (h2 : s2 ∈ [[d3, d5], [d5, d3]])
    (h3 : s3 ∈ [[d1]]) :
    alternateInterleave s0 s1 s2 s3 ∈ alternateOrdersA := by
  simp only [alternateOrdersA, alternateSectorOrders,
    List.mem_flatMap, List.mem_map]
  exact ⟨s0, h0, s1, h1, s2, h2, s3, h3, rfl⟩

theorem alternateOrdersB_mem_of_sector_orders
    {s0 s1 s2 s3 : List (Fin 10)}
    (h0 : s0 ∈ [[d2]])
    (h1 : s1 ∈ [[d4]])
    (h2 : s2 ∈ [[d0, d3, d5], [d0, d5, d3], [d3, d0, d5],
      [d3, d5, d0], [d5, d0, d3], [d5, d3, d0]])
    (h3 : s3 ∈ [[d1]]) :
    alternateInterleave s0 s1 s2 s3 ∈ alternateOrdersB := by
  simp only [alternateOrdersB, alternateSectorOrders,
    List.mem_flatMap, List.mem_map]
  exact ⟨s0, h0, s1, h1, s2, h2, s3, h3, rfl⟩

theorem alternateNineOrderP_eq_certificateSlots :
    alternateNineOrderP =
      (List.finRange 9).map nineCircleProofP_diskIndex := by
  native_decide

theorem alternateNineOrderQ_eq_certificateSlots :
    alternateNineOrderQ =
      (List.finRange 9).map nineCircleProofQ_diskIndex := by
  native_decide

noncomputable def alternateTurnAngle {R : ℝ} (P : Packing 10 R) (i : Fin 10) : ℝ :=
  angleFromOrigin
    (pointPolarAngle (P.circles d9).center)
    (pointPolarAngle (P.circles i).center)

theorem alternatePairwiseOrder_gives_P_cyclic_order
    {R : ℝ} (P : Packing 10 R) (order : List (Fin 10))
    (horder : order.Pairwise fun i j =>
      alternateTurnAngle P i ≤ alternateTurnAngle P j)
    (hprojection : alternateDeleteDiskOne order = alternateNineOrderP) :
    ∀ i j : Fin 9, i.1 < j.1 →
      angleFromOrigin
        (pointPolarAngle (P.circles (nineCircleProofP_diskIndex 0)).center)
        (pointPolarAngle (P.circles (nineCircleProofP_diskIndex i)).center) ≤
      angleFromOrigin
        (pointPolarAngle (P.circles (nineCircleProofP_diskIndex 0)).center)
        (pointPolarAngle (P.circles (nineCircleProofP_diskIndex j)).center) := by
  have hfirst : nineCircleProofP_diskIndex 0 = d9 := by decide
  have hfiltered := horder.filter (fun i => i != d0)
  have hget := (List.pairwise_iff_getElem.mp hfiltered)
  have hprojection' : List.filter (fun i => i != d0) order = alternateNineOrderP := by
    simpa [alternateDeleteDiskOne] using hprojection
  intro i j hij
  have hi : i.1 < (alternateDeleteDiskOne order).length := by
    rw [hprojection, alternateNineOrderP_eq_certificateSlots]
    simp
  have hj : j.1 < (alternateDeleteDiskOne order).length := by
    rw [hprojection, alternateNineOrderP_eq_certificateSlots]
    simp
  have h := hget i.1 j.1 hi hj hij
  simpa [alternateTurnAngle, hprojection', alternateNineOrderP_eq_certificateSlots,
    hfirst] using h

theorem alternatePairwiseOrder_gives_Q_cyclic_order
    {R : ℝ} (P : Packing 10 R) (order : List (Fin 10))
    (horder : order.Pairwise fun i j =>
      alternateTurnAngle P i ≤ alternateTurnAngle P j)
    (hprojection : alternateDeleteDiskOne order = alternateNineOrderQ) :
    ∀ i j : Fin 9, i.1 < j.1 →
      angleFromOrigin
        (pointPolarAngle (P.circles (nineCircleProofQ_diskIndex 0)).center)
        (pointPolarAngle (P.circles (nineCircleProofQ_diskIndex i)).center) ≤
      angleFromOrigin
        (pointPolarAngle (P.circles (nineCircleProofQ_diskIndex 0)).center)
        (pointPolarAngle (P.circles (nineCircleProofQ_diskIndex j)).center) := by
  have hfirst : nineCircleProofQ_diskIndex 0 = d9 := by decide
  have hfiltered := horder.filter (fun i => i != d0)
  have hget := (List.pairwise_iff_getElem.mp hfiltered)
  have hprojection' : List.filter (fun i => i != d0) order = alternateNineOrderQ := by
    simpa [alternateDeleteDiskOne] using hprojection
  intro i j hij
  have hi : i.1 < (alternateDeleteDiskOne order).length := by
    rw [hprojection, alternateNineOrderQ_eq_certificateSlots]
    simp
  have hj : j.1 < (alternateDeleteDiskOne order).length := by
    rw [hprojection, alternateNineOrderQ_eq_certificateSlots]
    simp
  have h := hget i.1 j.1 hi hj hij
  simpa [alternateTurnAngle, hprojection', alternateNineOrderQ_eq_certificateSlots,
    hfirst] using h

theorem alternateCaseA_excluded
    {R : ℝ} (P : Packing 10 R)
    (hstandardRadius : ∀ k : Fin 10,
      (P.circles k).radius ^ 2 = ((k.1 + 1 : ℕ) : ℝ))
    (hcontainer : R ≤
      (nineCircleProofP.radiusUpper : ℝ) / nineCircleProofP.scale)
    {s0 s1 s2 s3 : List (Fin 10)}
    (h0 : s0 ∈ [[d0, d2], [d2, d0]])
    (h1 : s1 ∈ [[d4]])
    (h2 : s2 ∈ [[d3, d5], [d5, d3]])
    (h3 : s3 ∈ [[d1]])
    (horder : (alternateInterleave s0 s1 s2 s3).Pairwise fun i j =>
      alternateTurnAngle P i ≤ alternateTurnAngle P j) :
    False := by
  let order := alternateInterleave s0 s1 s2 s3
  have hmem := alternateOrdersA_mem_of_sector_orders h0 h1 h2 h3
  have hprojected := alternateOrdersA_project_to_P_or_Q order hmem
  rcases hprojected with hP | hQ
  · exact nineCircleProofP_excludes_standard_cyclic_subpacking_order P
      hstandardRadius hcontainer
      (alternatePairwiseOrder_gives_P_cyclic_order P order (by simpa [order] using horder) hP)
  · have hcontainerQ : R ≤
        (nineCircleProofQ.radiusUpper : ℝ) / nineCircleProofQ.scale := by
      rw [← show (nineCircleProofP.radiusUpper : ℝ) / nineCircleProofP.scale =
        (nineCircleProofQ.radiusUpper : ℝ) / nineCircleProofQ.scale by rfl]
      exact hcontainer
    exact nineCircleProofQ_excludes_standard_cyclic_subpacking_order P
      hstandardRadius hcontainerQ
      (alternatePairwiseOrder_gives_Q_cyclic_order P order (by simpa [order] using horder) hQ)

theorem alternateCaseB_excluded
    {R : ℝ} (P : Packing 10 R)
    (hstandardRadius : ∀ k : Fin 10,
      (P.circles k).radius ^ 2 = ((k.1 + 1 : ℕ) : ℝ))
    (hcontainer : R ≤
      (nineCircleProofP.radiusUpper : ℝ) / nineCircleProofP.scale)
    {s0 s1 s2 s3 : List (Fin 10)}
    (h0 : s0 ∈ [[d2]])
    (h1 : s1 ∈ [[d4]])
    (h2 : s2 ∈ [[d0, d3, d5], [d0, d5, d3], [d3, d0, d5],
      [d3, d5, d0], [d5, d0, d3], [d5, d3, d0]])
    (h3 : s3 ∈ [[d1]])
    (horder : (alternateInterleave s0 s1 s2 s3).Pairwise fun i j =>
      alternateTurnAngle P i ≤ alternateTurnAngle P j) :
    False := by
  let order := alternateInterleave s0 s1 s2 s3
  have hmem := alternateOrdersB_mem_of_sector_orders h0 h1 h2 h3
  have hprojected := alternateOrdersB_project_to_P_or_Q order hmem
  rcases hprojected with hP | hQ
  · exact nineCircleProofP_excludes_standard_cyclic_subpacking_order P
      hstandardRadius hcontainer
      (alternatePairwiseOrder_gives_P_cyclic_order P order (by simpa [order] using horder) hP)
  · have hcontainerQ : R ≤
        (nineCircleProofQ.radiusUpper : ℝ) / nineCircleProofQ.scale := by
      rw [← show (nineCircleProofP.radiusUpper : ℝ) / nineCircleProofP.scale =
        (nineCircleProofQ.radiusUpper : ℝ) / nineCircleProofQ.scale by rfl]
      exact hcontainer
    exact nineCircleProofQ_excludes_standard_cyclic_subpacking_order P
      hstandardRadius hcontainerQ
      (alternatePairwiseOrder_gives_Q_cyclic_order P order (by simpa [order] using horder) hQ)

theorem alternateCaseA_excluded_of_sector_permutations
    {R : ℝ} (P : Packing 10 R)
    (hstandardRadius : ∀ k : Fin 10,
      (P.circles k).radius ^ 2 = ((k.1 + 1 : ℕ) : ℝ))
    (hcontainer : R ≤
      (nineCircleProofP.radiusUpper : ℝ) / nineCircleProofP.scale)
    {s0 s1 s2 s3 : List (Fin 10)}
    (h0 : s0.Perm (alternateSectorMaskLabels 5))
    (h1 : s1.Perm (alternateSectorMaskLabels 16))
    (h2 : s2.Perm (alternateSectorMaskLabels 40))
    (h3 : s3.Perm (alternateSectorMaskLabels 2))
    (horder : (alternateInterleave s0 s1 s2 s3).Pairwise fun i j =>
      alternateTurnAngle P i ≤ alternateTurnAngle P j) :
    False := by
  have hm5 : alternateSectorMaskLabels 5 = [d0, d2] := by native_decide
  have hm16 : alternateSectorMaskLabels 16 = [d4] := by native_decide
  have hm40 : alternateSectorMaskLabels 40 = [d3, d5] := by native_decide
  have hm2 : alternateSectorMaskLabels 2 = [d1] := by native_decide
  have hperm0 : [d0, d2].Perm s0 := by rw [← hm5]; exact h0.symm
  have hperm1 : [d4].Perm s1 := by rw [← hm16]; exact h1.symm
  have hperm2 : [d3, d5].Perm s2 := by rw [← hm40]; exact h2.symm
  have hperm3 : [d1].Perm s3 := by rw [← hm2]; exact h3.symm
  have h0' : s0 ∈ [[d0, d2], [d2, d0]] :=
    perm_pair_mem_options (by decide) hperm0
  have h1' : s1 ∈ [[d4]] := by
    have hs := perm_singleton_eq hperm1
    rw [hs]
    simp
  have h2' : s2 ∈ [[d3, d5], [d5, d3]] :=
    perm_pair_mem_options (by decide) hperm2
  have h3' : s3 ∈ [[d1]] := by
    have hs := perm_singleton_eq hperm3
    rw [hs]
    simp
  exact alternateCaseA_excluded P hstandardRadius hcontainer h0' h1' h2' h3' horder

theorem alternateCaseB_excluded_of_sector_permutations
    {R : ℝ} (P : Packing 10 R)
    (hstandardRadius : ∀ k : Fin 10,
      (P.circles k).radius ^ 2 = ((k.1 + 1 : ℕ) : ℝ))
    (hcontainer : R ≤
      (nineCircleProofP.radiusUpper : ℝ) / nineCircleProofP.scale)
    {s0 s1 s2 s3 : List (Fin 10)}
    (h0 : s0.Perm (alternateSectorMaskLabels 4))
    (h1 : s1.Perm (alternateSectorMaskLabels 16))
    (h2 : s2.Perm (alternateSectorMaskLabels 41))
    (h3 : s3.Perm (alternateSectorMaskLabels 2))
    (horder : (alternateInterleave s0 s1 s2 s3).Pairwise fun i j =>
      alternateTurnAngle P i ≤ alternateTurnAngle P j) :
    False := by
  have hm4 : alternateSectorMaskLabels 4 = [d2] := by native_decide
  have hm16 : alternateSectorMaskLabels 16 = [d4] := by native_decide
  have hm41 : alternateSectorMaskLabels 41 = [d0, d3, d5] := by native_decide
  have hm2 : alternateSectorMaskLabels 2 = [d1] := by native_decide
  have hperm0 : [d2].Perm s0 := by rw [← hm4]; exact h0.symm
  have hperm1 : [d4].Perm s1 := by rw [← hm16]; exact h1.symm
  have hperm2 : [d0, d3, d5].Perm s2 := by rw [← hm41]; exact h2.symm
  have hperm3 : [d1].Perm s3 := by rw [← hm2]; exact h3.symm
  have h0' : s0 ∈ [[d2]] := by
    have hs := perm_singleton_eq hperm0
    rw [hs]
    simp
  have h1' : s1 ∈ [[d4]] := by
    have hs := perm_singleton_eq hperm1
    rw [hs]
    simp
  have h2' : s2 ∈ [[d0, d3, d5], [d0, d5, d3], [d3, d0, d5],
      [d3, d5, d0], [d5, d0, d3], [d5, d3, d0]] :=
    perm_triple_mem_options (by decide) (by decide) (by decide) hperm2
  have h3' : s3 ∈ [[d1]] := by
    have hs := perm_singleton_eq hperm3
    rw [hs]
    simp
  exact alternateCaseB_excluded P hstandardRadius hcontainer h0' h1' h2' h3' horder

end CirclePacking
