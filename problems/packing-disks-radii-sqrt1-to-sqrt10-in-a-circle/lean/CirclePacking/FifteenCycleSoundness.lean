import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import CirclePacking.FifteenCertificate

/-!
# Soundness of the 15-disk angular negative-cycle certificate

The subdivision checker verifies that every recorded integer cycle has
negative total weight. This file gives the graph-theoretic meaning of that
integer: after division by 2800, every edge weight is an upper bound on the
corresponding difference of polar angles. A closed chain of such bounds cannot
have a negative total. The remaining geometric task is to prove those edge
bounds from the pairwise contact-angle estimates.
-/

namespace CirclePacking

def fifteenAngleScale : ℝ := 2800
def fifteenPiUpperTicks : ℕ := 17600

def fifteenCycleFin (i : ℕ) : Fin 15 :=
  ⟨i % 15, Nat.mod_lt _ (by decide)⟩

structure FifteenAngularEdge where
  src : Fin 15
  dst : Fin 15
  lower : ℝ

noncomputable def fifteenCycleAngularEdge (edge : FifteenCycleEdge) :
    FifteenAngularEdge :=
  ⟨fifteenCycleFin edge.source, fifteenCycleFin edge.target,
    (edge.ticks : ℝ) / fifteenAngleScale⟩

def fifteenCycleWeightTicks (edges : List FifteenCycleEdge) : ℤ :=
  (edges.map fifteenCycleEdgeWeight).sum

def fifteenCycleEdgeSemanticallyValid (edge : FifteenCycleEdge) : Prop :=
  (edge.kind = "O" ∧ edge.source = edge.target + 1 ∧ edge.ticks = 0) ∨
  (edge.kind = "L" ∧ edge.source > edge.target) ∨
  (edge.kind = "U" ∧ edge.source < edge.target)

theorem fifteenCycleEdgeShape_spec (edge : FifteenCycleEdge)
    (hshape : fifteenCycleEdgeShape edge = true) :
    edge.source < 15 ∧ edge.target < 15 ∧
      edge.ticks ≤ fifteenPiUpperTicks ∧
      fifteenCycleEdgeSemanticallyValid edge := by
  by_cases houter : edge.kind == "O"
  · have hkind : edge.kind = "O" := by simpa using houter
    have hdata := hshape
    simp [fifteenCycleEdgeShape, houter] at hdata
    refine ⟨hdata.1.1.1, hdata.1.1.2, ?_, ?_⟩
    · exact le_trans hdata.1.2 (by norm_num [fifteenPiUpperTicks])
    · exact Or.inl ⟨hkind, hdata.2.1.1, hdata.2.2⟩
  · by_cases hlower : edge.kind == "L"
    · have hkind : edge.kind = "L" := by simpa using hlower
      have hdata := hshape
      simp [fifteenCycleEdgeShape, houter, hlower] at hdata
      refine ⟨hdata.1.1.1, hdata.1.1.2, ?_, ?_⟩
      · exact le_trans hdata.1.2 (by norm_num [fifteenPiUpperTicks])
      · exact Or.inr (Or.inl ⟨hkind, hdata.2⟩)
    · by_cases hupper : edge.kind == "U"
      · have hkind : edge.kind = "U" := by simpa using hupper
        have hdata := hshape
        simp [fifteenCycleEdgeShape, houter, hlower, hupper] at hdata
        refine ⟨hdata.1.1.1, hdata.1.1.2, ?_, ?_⟩
        · exact le_trans hdata.1.2 (by norm_num [fifteenPiUpperTicks])
        · exact Or.inr (Or.inr ⟨hkind, hdata.2⟩)
      · simp [fifteenCycleEdgeShape, houter, hlower, hupper] at hshape

def FifteenCycleChain (start : ℕ) : List FifteenCycleEdge → ℕ → Prop
  | [], finish => finish = start
  | edge :: rest, finish =>
      edge.source = start ∧ FifteenCycleChain edge.target rest finish

def fifteenAngularEdgeUpper (tauUpper : ℝ) (edge : FifteenAngularEdge) : ℝ :=
  if edge.src.1 < edge.dst.1 then tauUpper - edge.lower else -edge.lower

def FifteenAngularChain (start : Fin 15) :
    List FifteenAngularEdge → Fin 15 → Prop
  | [], finish => finish = start
  | edge :: rest, finish =>
      edge.src = start ∧ FifteenAngularChain edge.dst rest finish

theorem fifteenAngularChain_telescope
    (theta : Fin 15 → ℝ) (start finish : Fin 15)
    (edges : List FifteenAngularEdge)
    (hchain : FifteenAngularChain start edges finish) :
    (edges.map (fun edge => theta edge.dst - theta edge.src)).sum =
      theta finish - theta start := by
  induction edges generalizing start finish with
  | nil =>
      simp only [FifteenAngularChain] at hchain
      subst finish
      simp
  | cons edge rest ih =>
      simp only [FifteenAngularChain] at hchain
      rcases hchain with ⟨hsrc, hrest⟩
      subst start
      simp only [List.map_cons, List.sum_cons]
      rw [ih edge.dst finish hrest]
      ring

theorem fifteenListSumMapLe {α : Type} (items : List α)
    (f g : α → ℝ) (h : ∀ item ∈ items, f item ≤ g item) :
    (items.map f).sum ≤ (items.map g).sum := by
  induction items with
  | nil => simp
  | cons item rest ih =>
      simp only [List.map_cons, List.sum_cons]
      exact add_le_add (h item (by simp))
        (ih (fun next hnext => h next (by simp [hnext])))

theorem fifteenNegativeAngularCycle_impossible
    (theta : Fin 15 → ℝ) (tauUpper : ℝ) (start : Fin 15)
    (edges : List FifteenAngularEdge)
    (hchain : FifteenAngularChain start edges start)
    (hedges : ∀ edge ∈ edges,
      theta edge.dst - theta edge.src ≤ fifteenAngularEdgeUpper tauUpper edge)
    (hnegative :
      (edges.map (fifteenAngularEdgeUpper tauUpper)).sum < 0) : False := by
  have hsumle :
      (edges.map (fun edge => theta edge.dst - theta edge.src)).sum ≤
        (edges.map (fifteenAngularEdgeUpper tauUpper)).sum :=
    fifteenListSumMapLe edges
      (fun edge => theta edge.dst - theta edge.src)
      (fifteenAngularEdgeUpper tauUpper) hedges
  have htelescope := fifteenAngularChain_telescope theta start start edges hchain
  simp only [sub_self] at htelescope
  have hnonnegative :
      0 ≤ (edges.map (fifteenAngularEdgeUpper tauUpper)).sum := by
    rw [← htelescope]
    exact hsumle
  exact (not_lt_of_ge hnonnegative) hnegative

theorem fifteenListSumMapCongr {α β : Type} [AddCommMonoid β]
    (items : List α) (f g : α → β)
    (h : ∀ item ∈ items, f item = g item) :
    (items.map f).sum = (items.map g).sum := by
  induction items with
  | nil => rfl
  | cons item rest ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [h item (by simp)]
      apply congrArg (fun x => g item + x)
      apply ih
      intro next hnext
      exact h next (by simp [hnext])

theorem fifteenCycleChain_to_angular
    {start finish : ℕ} {edges : List FifteenCycleEdge}
    (hchain : FifteenCycleChain start edges finish) :
    FifteenAngularChain (fifteenCycleFin start)
      (edges.map fifteenCycleAngularEdge) (fifteenCycleFin finish) := by
  induction edges generalizing start finish with
  | nil =>
      simp only [FifteenCycleChain] at hchain
      subst finish
      rfl
  | cons edge rest ih =>
      simp only [FifteenCycleChain] at hchain
      rcases hchain with ⟨hsource, hrest⟩
      simp only [FifteenAngularChain, List.map_cons]
      exact ⟨congrArg fifteenCycleFin hsource, ih hrest⟩

theorem fifteenCycleAngularEdge_upper_eq_weight
    (edge : FifteenCycleEdge)
    (hsource : edge.source < 15) (htarget : edge.target < 15)
    (hsem : fifteenCycleEdgeSemanticallyValid edge)
    (hticks : edge.ticks ≤ fifteenPiUpperTicks) :
    fifteenAngularEdgeUpper
        ((fifteenPiUpperTicks : ℝ) / fifteenAngleScale)
        (fifteenCycleAngularEdge edge) =
      (fifteenCycleEdgeWeight edge : ℝ) / fifteenAngleScale := by
  have hsourceFin : (fifteenCycleFin edge.source).1 = edge.source :=
    Nat.mod_eq_of_lt hsource
  have htargetFin : (fifteenCycleFin edge.target).1 = edge.target :=
    Nat.mod_eq_of_lt htarget
  rcases hsem with houter | hlower | hupper
  · rcases houter with ⟨hkind, hstep, htickZero⟩
    have hnotForward : ¬ edge.source < edge.target := by omega
    simp [fifteenCycleAngularEdge, hsourceFin, htargetFin,
      fifteenAngularEdgeUpper, hnotForward, fifteenCycleEdgeWeight,
      hkind, htickZero, fifteenAngleScale]
  · rcases hlower with ⟨hkind, hdirection⟩
    have hnotForward : ¬ edge.source < edge.target := by omega
    simp [fifteenCycleAngularEdge, hsourceFin, htargetFin,
      fifteenAngularEdgeUpper, hnotForward, fifteenCycleEdgeWeight,
      hkind, fifteenAngleScale]
    ring_nf
  · rcases hupper with ⟨hkind, hdirection⟩
    have hforward : edge.source < edge.target := hdirection
    have hcastSub : ((fifteenPiUpperTicks - edge.ticks : ℕ) : ℝ) =
        (fifteenPiUpperTicks : ℝ) - edge.ticks := by
      exact Nat.cast_sub hticks
    norm_num [fifteenPiUpperTicks] at hcastSub
    simp [fifteenCycleAngularEdge, hsourceFin, htargetFin,
      fifteenAngularEdgeUpper, hforward, fifteenCycleEdgeWeight,
      hkind, fifteenPiUpperTicks, fifteenAngleScale]
    rw [hcastSub]
    norm_num [fifteenPiUpperTicks, fifteenAngleScale]
    ring

theorem fifteenCycleWeightRealSum
    (edges : List FifteenCycleEdge) :
    (edges.map (fun edge =>
      (fifteenCycleEdgeWeight edge : ℝ) / fifteenAngleScale)).sum =
        (fifteenCycleWeightTicks edges : ℝ) / fifteenAngleScale := by
  change (edges.map (fun edge =>
    (fifteenCycleEdgeWeight edge : ℝ) / fifteenAngleScale)).sum =
      ((edges.map fifteenCycleEdgeWeight).sum : ℝ) / fifteenAngleScale
  induction edges with
  | nil => simp
  | cons edge rest ih =>
      simp only [List.map_cons, List.sum_cons, Int.cast_add]
      rw [ih]
      ring

theorem fifteenNegativeCycle_excludes
    {edges : List FifteenCycleEdge} {start : ℕ}
    {theta : Fin 15 → ℝ}
    (hchain : FifteenCycleChain start edges start)
    (hvalid : ∀ edge ∈ edges, fifteenCycleEdgeShape edge = true)
    (hbound : ∀ edge ∈ edges,
      theta (fifteenCycleFin edge.target) -
          theta (fifteenCycleFin edge.source) ≤
        (fifteenCycleEdgeWeight edge : ℝ) / fifteenAngleScale)
    (hnegative : fifteenCycleWeightTicks edges < 0) : False := by
  have hspec : ∀ edge ∈ edges,
      edge.source < 15 ∧ edge.target < 15 ∧
        edge.ticks ≤ fifteenPiUpperTicks ∧
        fifteenCycleEdgeSemanticallyValid edge := by
    intro edge hedge
    exact fifteenCycleEdgeShape_spec edge (hvalid edge hedge)
  let angularEdges := edges.map fifteenCycleAngularEdge
  have hangularChain :
      FifteenAngularChain (fifteenCycleFin start) angularEdges
        (fifteenCycleFin start) := by
    simpa [angularEdges] using fifteenCycleChain_to_angular hchain
  have hupper : ∀ edge ∈ angularEdges,
      theta edge.dst - theta edge.src ≤
        fifteenAngularEdgeUpper
          ((fifteenPiUpperTicks : ℝ) / fifteenAngleScale) edge := by
    intro angularEdge hmem
    obtain ⟨edge, hedge, heq⟩ := List.mem_map.mp hmem
    subst angularEdge
    rw [fifteenCycleAngularEdge_upper_eq_weight edge
      (hspec edge hedge).1 (hspec edge hedge).2.1
      (hspec edge hedge).2.2.2 (hspec edge hedge).2.2.1]
    exact hbound edge hedge
  have hnegReal : (fifteenCycleWeightTicks edges : ℝ) < 0 := by
    simpa using (Int.cast_lt (R := ℝ)).2 hnegative
  have hnegScaled :
      (fifteenCycleWeightTicks edges : ℝ) / fifteenAngleScale < 0 :=
    div_neg_of_neg_of_pos hnegReal (by norm_num [fifteenAngleScale])
  have hmapSum :
      (edges.map (fun edge =>
        fifteenAngularEdgeUpper
          ((fifteenPiUpperTicks : ℝ) / fifteenAngleScale)
          (fifteenCycleAngularEdge edge))).sum =
        (edges.map (fun edge =>
          (fifteenCycleEdgeWeight edge : ℝ) / fifteenAngleScale)).sum :=
    fifteenListSumMapCongr edges
      (fun edge => fifteenAngularEdgeUpper
        ((fifteenPiUpperTicks : ℝ) / fifteenAngleScale)
        (fifteenCycleAngularEdge edge))
      (fun edge => (fifteenCycleEdgeWeight edge : ℝ) / fifteenAngleScale)
      (fun edge hedge => fifteenCycleAngularEdge_upper_eq_weight edge
        (hspec edge hedge).1 (hspec edge hedge).2.1
        (hspec edge hedge).2.2.2 (hspec edge hedge).2.2.1)
  have hnegativeEdges :
      (angularEdges.map
        (fifteenAngularEdgeUpper
          ((fifteenPiUpperTicks : ℝ) / fifteenAngleScale))).sum < 0 := by
    change ((edges.map fifteenCycleAngularEdge).map
      (fifteenAngularEdgeUpper
        ((fifteenPiUpperTicks : ℝ) / fifteenAngleScale))).sum < 0
    rw [List.map_map]
    change (edges.map (fun edge =>
      fifteenAngularEdgeUpper
        ((fifteenPiUpperTicks : ℝ) / fifteenAngleScale)
        (fifteenCycleAngularEdge edge))).sum < 0
    rw [hmapSum, fifteenCycleWeightRealSum]
    exact hnegScaled
  exact fifteenNegativeAngularCycle_impossible theta
    ((fifteenPiUpperTicks : ℝ) / fifteenAngleScale)
    (fifteenCycleFin start) angularEdges hangularChain hupper hnegativeEdges

end CirclePacking
