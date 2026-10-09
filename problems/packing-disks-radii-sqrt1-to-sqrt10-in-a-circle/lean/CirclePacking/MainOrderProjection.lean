import CirclePacking.AlternateOrderProjection

/-!
# Finite projection for the main seven-disk order

The 193 unresolved main-order occurrences in the exact radial-tree replay
have large-circle skeleton `(10, 7, 9, 8)` and effective sector masks
`(20, 1, 2, 40)` or `(24, 1, 2, 36)`. This module decodes both mask tuples,
enumerates every sector-local permutation, and checks that after deleting
disks 1, 3, and 4, every projected order is `(10, 5, 7, 9, 2, 8, 6)`.

It turns the terminal-case sector data into the exact ordered-core premise
needed by the seven-disk angle-barrier theorem. It does not yet replay the
radial tree or formalize that analytic angle-barrier theorem.
-/

namespace CirclePacking

private def mainD0 : Fin 10 := ⟨0, by decide⟩
private def mainD1 : Fin 10 := ⟨1, by decide⟩
private def mainD2 : Fin 10 := ⟨2, by decide⟩
private def mainD3 : Fin 10 := ⟨3, by decide⟩
private def mainD4 : Fin 10 := ⟨4, by decide⟩
private def mainD5 : Fin 10 := ⟨5, by decide⟩
private def mainD6 : Fin 10 := ⟨6, by decide⟩
private def mainD7 : Fin 10 := ⟨7, by decide⟩
private def mainD8 : Fin 10 := ⟨8, by decide⟩
private def mainD9 : Fin 10 := ⟨9, by decide⟩

def mainOrderSectorMasksA : List Nat := [20, 1, 2, 40]
def mainOrderSectorMasksB : List Nat := [24, 1, 2, 36]

theorem mainOrderSectorMasksA_decode :
    mainOrderSectorMasksA.map alternateSectorMaskLabels =
      [[mainD2, mainD4], [mainD0], [mainD1], [mainD3, mainD5]] := by
  native_decide

theorem mainOrderSectorMasksB_decode :
    mainOrderSectorMasksB.map alternateSectorMaskLabels =
      [[mainD3, mainD4], [mainD0], [mainD1], [mainD2, mainD5]] := by
  native_decide

/-- Interleave sectors around the skeleton `(10, 7, 9, 8)`. -/
def mainOrderInterleave (s0 s1 s2 s3 : List (Fin 10)) : List (Fin 10) :=
  [mainD9] ++ s0 ++ [mainD6] ++ s1 ++ [mainD8] ++ s2 ++ [mainD7] ++ s3

def mainOrderSectorOrders
    (s0 s1 s2 s3 : List (List (Fin 10))) : List (List (Fin 10)) :=
  s0.flatMap fun a => s1.flatMap fun b => s2.flatMap fun c =>
    s3.map fun d => mainOrderInterleave a b c d

/-- The four sector-local permutations for masks `(20, 1, 2, 40)`. -/
def mainOrdersA : List (List (Fin 10)) :=
  mainOrderSectorOrders
    [[mainD2, mainD4], [mainD4, mainD2]]
    [[mainD0]]
    [[mainD1]]
    [[mainD3, mainD5], [mainD5, mainD3]]

/-- The four sector-local permutations for masks `(24, 1, 2, 36)`. -/
def mainOrdersB : List (List (Fin 10)) :=
  mainOrderSectorOrders
    [[mainD3, mainD4], [mainD4, mainD3]]
    [[mainD0]]
    [[mainD1]]
    [[mainD2, mainD5], [mainD5, mainD2]]

def mainCoreOrder : List (Fin 10) :=
  [mainD9, mainD4, mainD6, mainD8, mainD1, mainD7, mainD5]

def mainCoreMember (i : Fin 10) : Bool :=
  decide (i = mainD1 ∨ i = mainD4 ∨ i = mainD5 ∨ i = mainD6 ∨
    i = mainD7 ∨ i = mainD8 ∨ i = mainD9)

def mainDeleteOutsideCore (order : List (Fin 10)) : List (Fin 10) :=
  order.filter mainCoreMember

def mainOrderProjectionCheck (orders : List (List (Fin 10))) : Bool :=
  orders.all fun order => decide (mainDeleteOutsideCore order = mainCoreOrder)

theorem mainOrdersA_projection_check : mainOrderProjectionCheck mainOrdersA = true := by
  native_decide

theorem mainOrdersB_projection_check : mainOrderProjectionCheck mainOrdersB = true := by
  native_decide

theorem mainOrdersA_project_to_core (order : List (Fin 10))
    (horder : order ∈ mainOrdersA) :
    mainDeleteOutsideCore order = mainCoreOrder := by
  have h := (List.all_eq_true.mp mainOrdersA_projection_check) order horder
  simpa [mainOrderProjectionCheck, decide_eq_true_eq] using h

theorem mainOrdersB_project_to_core (order : List (Fin 10))
    (horder : order ∈ mainOrdersB) :
    mainDeleteOutsideCore order = mainCoreOrder := by
  have h := (List.all_eq_true.mp mainOrdersB_projection_check) order horder
  simpa [mainOrderProjectionCheck, decide_eq_true_eq] using h

theorem mainOrdersA_mem_of_sector_orders
    {s0 s1 s2 s3 : List (Fin 10)}
    (h0 : s0 ∈ [[mainD2, mainD4], [mainD4, mainD2]])
    (h1 : s1 ∈ [[mainD0]])
    (h2 : s2 ∈ [[mainD1]])
    (h3 : s3 ∈ [[mainD3, mainD5], [mainD5, mainD3]]) :
    mainOrderInterleave s0 s1 s2 s3 ∈ mainOrdersA := by
  simp only [mainOrdersA, mainOrderSectorOrders,
    List.mem_flatMap, List.mem_map]
  exact ⟨s0, h0, s1, h1, s2, h2, s3, h3, rfl⟩

theorem mainOrdersB_mem_of_sector_orders
    {s0 s1 s2 s3 : List (Fin 10)}
    (h0 : s0 ∈ [[mainD3, mainD4], [mainD4, mainD3]])
    (h1 : s1 ∈ [[mainD0]])
    (h2 : s2 ∈ [[mainD1]])
    (h3 : s3 ∈ [[mainD2, mainD5], [mainD5, mainD2]]) :
    mainOrderInterleave s0 s1 s2 s3 ∈ mainOrdersB := by
  simp only [mainOrdersB, mainOrderSectorOrders,
    List.mem_flatMap, List.mem_map]
  exact ⟨s0, h0, s1, h1, s2, h2, s3, h3, rfl⟩

/-- A pairwise-ordered full sector projection induces the ordered core
premise used by the main seven-disk angle argument. -/
theorem mainCorePairwise_of_full_order
    {R : ℝ} (P : Packing 10 R) (order : List (Fin 10))
    (horder : order.Pairwise fun i j =>
      alternateTurnAngle P i ≤ alternateTurnAngle P j)
    (hprojection : mainDeleteOutsideCore order = mainCoreOrder) :
    mainCoreOrder.Pairwise fun i j =>
      alternateTurnAngle P i ≤ alternateTurnAngle P j := by
  have hfiltered := horder.filter mainCoreMember
  rw [← hprojection]
  exact hfiltered

theorem mainCorePairwise_of_sector_ordersA
    {R : ℝ} (P : Packing 10 R) (s0 s1 s2 s3 : List (Fin 10))
    (h0 : s0 ∈ [[mainD2, mainD4], [mainD4, mainD2]])
    (h1 : s1 ∈ [[mainD0]])
    (h2 : s2 ∈ [[mainD1]])
    (h3 : s3 ∈ [[mainD3, mainD5], [mainD5, mainD3]])
    (horder : (mainOrderInterleave s0 s1 s2 s3).Pairwise fun i j =>
      alternateTurnAngle P i ≤ alternateTurnAngle P j) :
    mainCoreOrder.Pairwise fun i j =>
      alternateTurnAngle P i ≤ alternateTurnAngle P j := by
  apply mainCorePairwise_of_full_order P _ horder
  exact mainOrdersA_project_to_core _
    (mainOrdersA_mem_of_sector_orders h0 h1 h2 h3)

theorem mainCorePairwise_of_sector_ordersB
    {R : ℝ} (P : Packing 10 R) (s0 s1 s2 s3 : List (Fin 10))
    (h0 : s0 ∈ [[mainD3, mainD4], [mainD4, mainD3]])
    (h1 : s1 ∈ [[mainD0]])
    (h2 : s2 ∈ [[mainD1]])
    (h3 : s3 ∈ [[mainD2, mainD5], [mainD5, mainD2]])
    (horder : (mainOrderInterleave s0 s1 s2 s3).Pairwise fun i j =>
      alternateTurnAngle P i ≤ alternateTurnAngle P j) :
    mainCoreOrder.Pairwise fun i j =>
      alternateTurnAngle P i ≤ alternateTurnAngle P j := by
  apply mainCorePairwise_of_full_order P _ horder
  exact mainOrdersB_project_to_core _
    (mainOrdersB_mem_of_sector_orders h0 h1 h2 h3)

end CirclePacking
