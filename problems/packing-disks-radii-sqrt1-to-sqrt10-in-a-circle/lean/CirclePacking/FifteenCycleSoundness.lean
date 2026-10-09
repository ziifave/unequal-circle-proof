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

theorem fifteenCycleEdgeTickValid_lower_eq
    (edge : FifteenCycleEdge) (box : FifteenBox)
    (positiveZero exactZero : List Nat) (hkind : edge.kind = "L") :
    fifteenCycleEdgeTickValid edge box positiveZero exactZero =
      fifteenTickCertificateValid box[edge.target]! box[edge.source]!
        (positiveZero.contains edge.target || positiveZero.contains edge.source)
        (exactZero.contains edge.target || exactZero.contains edge.source)
        edge.ticks := by
  simp [fifteenCycleEdgeTickValid, hkind]

theorem fifteenCycleEdgeTickValid_upper_eq
    (edge : FifteenCycleEdge) (box : FifteenBox)
    (positiveZero exactZero : List Nat) (hkind : edge.kind = "U") :
    fifteenCycleEdgeTickValid edge box positiveZero exactZero =
      fifteenTickCertificateValid box[edge.source]! box[edge.target]!
        (positiveZero.contains edge.source || positiveZero.contains edge.target)
        (exactZero.contains edge.source || exactZero.contains edge.target)
        edge.ticks := by
  simp [fifteenCycleEdgeTickValid, hkind]

theorem fifteenCycleEdgeTickValid_lower_regular_spec
    (edge : FifteenCycleEdge) (box : FifteenBox)
    (positiveZero exactZero : List Nat)
    (hkind : edge.kind = "L")
    (hpositive :
      (positiveZero.contains edge.target || positiveZero.contains edge.source) = false)
    (hexact :
      (exactZero.contains edge.target || exactZero.contains edge.source) = false)
    (hvalid : fifteenCycleEdgeTickValid edge box positiveZero exactZero = true) :
    fifteenTickCertificateValid box[edge.target]! box[edge.source]!
      false false edge.ticks = true := by
  rw [fifteenCycleEdgeTickValid_lower_eq edge box positiveZero exactZero hkind] at hvalid
  rw [hpositive, hexact] at hvalid
  exact hvalid

theorem fifteenCycleEdgeTickValid_lower_positiveZero_spec
    (edge : FifteenCycleEdge) (box : FifteenBox)
    (positiveZero exactZero : List Nat)
    (hkind : edge.kind = "L")
    (hpositive :
      (positiveZero.contains edge.target || positiveZero.contains edge.source) = true)
    (hexact :
      (exactZero.contains edge.target || exactZero.contains edge.source) = false)
    (hvalid : fifteenCycleEdgeTickValid edge box positiveZero exactZero = true) :
    fifteenTickCertificateValid box[edge.target]! box[edge.source]!
      true false edge.ticks = true := by
  rw [fifteenCycleEdgeTickValid_lower_eq edge box positiveZero exactZero hkind] at hvalid
  rw [hpositive, hexact] at hvalid
  exact hvalid

theorem fifteenCycleEdgeTickValid_upper_regular_spec
    (edge : FifteenCycleEdge) (box : FifteenBox)
    (positiveZero exactZero : List Nat)
    (hkind : edge.kind = "U")
    (hpositive :
      (positiveZero.contains edge.source || positiveZero.contains edge.target) = false)
    (hexact :
      (exactZero.contains edge.source || exactZero.contains edge.target) = false)
    (hvalid : fifteenCycleEdgeTickValid edge box positiveZero exactZero = true) :
    fifteenTickCertificateValid box[edge.source]! box[edge.target]!
      false false edge.ticks = true := by
  rw [fifteenCycleEdgeTickValid_upper_eq edge box positiveZero exactZero hkind] at hvalid
  rw [hpositive, hexact] at hvalid
  exact hvalid

theorem fifteenCycleEdgeTickValid_upper_positiveZero_spec
    (edge : FifteenCycleEdge) (box : FifteenBox)
    (positiveZero exactZero : List Nat)
    (hkind : edge.kind = "U")
    (hpositive :
      (positiveZero.contains edge.source || positiveZero.contains edge.target) = true)
    (hexact :
      (exactZero.contains edge.source || exactZero.contains edge.target) = false)
    (hvalid : fifteenCycleEdgeTickValid edge box positiveZero exactZero = true) :
    fifteenTickCertificateValid box[edge.source]! box[edge.target]!
      true false edge.ticks = true := by
  rw [fifteenCycleEdgeTickValid_upper_eq edge box positiveZero exactZero hkind] at hvalid
  rw [hpositive, hexact] at hvalid
  exact hvalid

theorem fifteenCycleEdgeTickValid_exactZero_spec
    (edge : FifteenCycleEdge) (box : FifteenBox)
    (positiveZero exactZero : List Nat)
    (hkind : edge.kind = "L")
    (hpositive :
      (positiveZero.contains edge.target || positiveZero.contains edge.source) = false)
    (hexact :
      (exactZero.contains edge.target || exactZero.contains edge.source) = true)
    (hvalid : fifteenCycleEdgeTickValid edge box positiveZero exactZero = true)
    (hsum : 2 ≤ (box[edge.target]!).2 + (box[edge.source]!).2) :
    edge.ticks = 0 := by
  rw [fifteenCycleEdgeTickValid_lower_eq edge box positiveZero exactZero hkind] at hvalid
  rw [hpositive, hexact] at hvalid
  have htick : fifteenTickCertificateValid box[edge.target]! box[edge.source]!
      false true edge.ticks = true := by
    exact hvalid
  have hnotSum : ¬ (box[edge.target]!).2 + (box[edge.source]!).2 < 2 := not_lt_of_ge hsum
  simpa [fifteenTickCertificateValid, hnotSum] using htick

theorem fifteenCycleEdgeTickValid_upper_exactZero_spec
    (edge : FifteenCycleEdge) (box : FifteenBox)
    (positiveZero exactZero : List Nat)
    (hkind : edge.kind = "U")
    (hpositive :
      (positiveZero.contains edge.source || positiveZero.contains edge.target) = false)
    (hexact :
      (exactZero.contains edge.source || exactZero.contains edge.target) = true)
    (hvalid : fifteenCycleEdgeTickValid edge box positiveZero exactZero = true)
    (hsum : 2 ≤ (box[edge.source]!).2 + (box[edge.target]!).2) :
    edge.ticks = 0 := by
  rw [fifteenCycleEdgeTickValid_upper_eq edge box positiveZero exactZero hkind] at hvalid
  rw [hpositive, hexact] at hvalid
  have hnotSum : ¬ (box[edge.source]!).2 + (box[edge.target]!).2 < 2 := not_lt_of_ge hsum
  simpa [fifteenTickCertificateValid, hnotSum] using hvalid

theorem fifteenCycleEdgeTickValid_outer_zero_spec
    (edge : FifteenCycleEdge) (box : FifteenBox)
    (positiveZero exactZero : List Nat)
    (hkind : edge.kind = "O")
    (hvalid : fifteenCycleEdgeTickValid edge box positiveZero exactZero = true) :
    edge.ticks = 0 := by
  simpa [fifteenCycleEdgeTickValid, hkind] using hvalid

def FifteenCycleChain (start : ℕ) : List FifteenCycleEdge → ℕ → Prop
  | [], finish => finish = start
  | edge :: rest, finish =>
      edge.source = start ∧ FifteenCycleChain edge.target rest finish

structure FifteenCycleEdgesSpec (edges : List FifteenCycleEdge)
    (box : FifteenBox) (positiveZero exactZero : List Nat) : Prop where
  lengthLower : 2 ≤ edges.length
  lengthUpper : edges.length ≤ 15
  edgeShapes : ∀ edge ∈ edges, fifteenCycleEdgeShape edge = true
  edgeTicks : ∀ edge ∈ edges,
    fifteenCycleEdgeTickValid edge box positiveZero exactZero = true
  links : fifteenCycleLinkValid edges = true
  endpointsClosed : fifteenCycleEndsClosed edges = true
  negativeWeight : fifteenCycleFoldWeight edges < 0

theorem fifteenListAllTrue_spec {α : Type} (items : List α)
    (predicate : α → Bool) (hall : items.all predicate = true) :
    ∀ item, item ∈ items → predicate item = true := by
  induction items with
  | nil => simp
  | cons head tail ih =>
      simp only [List.all_cons, Bool.and_eq_true] at hall
      intro item hmem
      simp only [List.mem_cons] at hmem
      rcases hmem with heq | hmem
      · subst item
        exact hall.1
      · exact ih hall.2 item hmem

theorem fifteenCycleEdgesValid_sound
    (edges : List FifteenCycleEdge) (box : FifteenBox)
    (positiveZero exactZero : List Nat)
    (hvalid : fifteenCycleEdgesValid edges box positiveZero exactZero = true) :
    FifteenCycleEdgesSpec edges box positiveZero exactZero := by
  unfold fifteenCycleEdgesValid at hvalid
  have h1 := Bool.and_eq_true_iff.mp hvalid
  have h2 := Bool.and_eq_true_iff.mp h1.1
  have h3 := Bool.and_eq_true_iff.mp h2.1
  have h4 := Bool.and_eq_true_iff.mp h3.1
  have h5 := Bool.and_eq_true_iff.mp h4.1
  have h6 := Bool.and_eq_true_iff.mp h5.1
  have hmin := h6.1
  have hmax := h6.2
  have hshape := h5.2
  have htick := h4.2
  have hlinks := h3.2
  have hclosed := h2.2
  have hnegative := h1.2
  have hmin' : 2 ≤ edges.length := of_decide_eq_true hmin
  have hmax' : edges.length ≤ 15 := of_decide_eq_true hmax
  have hnegative' : fifteenCycleFoldWeight edges < 0 :=
    of_decide_eq_true hnegative
  refine ⟨hmin', hmax', ?_, ?_, hlinks, hclosed, hnegative'⟩
  · exact fifteenListAllTrue_spec edges fifteenCycleEdgeShape hshape
  · exact fifteenListAllTrue_spec edges
      (fun edge => fifteenCycleEdgeTickValid edge box positiveZero exactZero) htick

def fifteenCycleHeadSource? (edges : List FifteenCycleEdge) : Option Nat :=
  edges.head?.map FifteenCycleEdge.source

def fifteenCycleLastTarget? (edges : List FifteenCycleEdge) : Option Nat :=
  edges.getLast?.map FifteenCycleEdge.target

theorem fifteenCycleLinkValid_chain
    {edges : List FifteenCycleEdge} {start finish : Nat}
    (hlink : fifteenCycleLinkValid edges = true)
    (hstart : fifteenCycleHeadSource? edges = some start)
    (hfinish : fifteenCycleLastTarget? edges = some finish) :
    FifteenCycleChain start edges finish := by
  induction edges generalizing start finish with
  | nil => simp [fifteenCycleHeadSource?] at hstart
  | cons first rest ih =>
      cases rest with
      | nil =>
          have hsource : first.source = start := by
            simpa [fifteenCycleHeadSource?] using hstart
          have htarget : first.target = finish := by
            simpa [fifteenCycleLastTarget?] using hfinish
          subst start
          subst finish
          simp [FifteenCycleChain]
      | cons second tail =>
          have hparts : first.target = second.source ∧
              fifteenCycleLinkValid (second :: tail) = true := by
            simpa [fifteenCycleLinkValid] using hlink
          have hstartRest : fifteenCycleHeadSource? (second :: tail) =
              some first.target := by
            simp [fifteenCycleHeadSource?, hparts.1]
          have hfinishRest : fifteenCycleLastTarget? (second :: tail) =
              some finish := by
            simpa [fifteenCycleLastTarget?] using hfinish
          have hchainRest := ih hparts.2 hstartRest hfinishRest
          have hsource : first.source = start := by
            simpa [fifteenCycleHeadSource?] using hstart
          change first.source = start ∧
            FifteenCycleChain first.target (second :: tail) finish
          exact ⟨hsource, hchainRest⟩

theorem fifteenCycleEndsClosed_spec
    {edges : List FifteenCycleEdge} {first last : FifteenCycleEdge}
    (hfirst : edges.head? = some first)
    (hlast : edges.getLast? = some last)
    (hclosed : fifteenCycleEndsClosed edges = true) :
    last.target = first.source := by
  have hdecide : decide (last.target = first.source) = true := by
    simpa [fifteenCycleEndsClosed, hfirst, hlast] using hclosed
  exact of_decide_eq_true hdecide

theorem fifteenCycleEdgesSpec_has_closed_chain
    {edges : List FifteenCycleEdge} {box : FifteenBox}
    {positiveZero exactZero : List Nat}
    (hspec : FifteenCycleEdgesSpec edges box positiveZero exactZero) :
    ∃ first last, edges.head? = some first ∧ edges.getLast? = some last ∧
      FifteenCycleChain first.source edges first.source := by
  have hexists : ∃ first last,
      edges.head? = some first ∧ edges.getLast? = some last := by
    cases edges with
    | nil =>
        have hlen := hspec.lengthLower
        simp at hlen
    | cons first rest =>
        cases rest with
        | nil =>
            have hlen := hspec.lengthLower
            simp at hlen
        | cons second tail =>
            refine ⟨first, (first :: second :: tail).getLast (by simp), ?_, ?_⟩
            · simp
            · exact List.getLast?_eq_some_getLast (by simp)
  obtain ⟨first, last, hfirst, hlast⟩ := hexists
  have hstart : fifteenCycleHeadSource? edges = some first.source := by
    simp [fifteenCycleHeadSource?, hfirst]
  have hfinish : fifteenCycleLastTarget? edges = some last.target := by
    simp [fifteenCycleLastTarget?, hlast]
  have hchain := fifteenCycleLinkValid_chain hspec.links hstart hfinish
  have hclosed := fifteenCycleEndsClosed_spec hfirst hlast hspec.endpointsClosed
  refine ⟨first, last, hfirst, hlast, ?_⟩
  simpa [hclosed] using hchain

theorem fifteenCycleValid_produces_spec
    (j : Lean.Json) (box : FifteenBox) (positiveZero exactZero : List Nat)
    (hvalid : fifteenCycleValid j box positiveZero exactZero = true) :
    ∃ edges, fifteenParseCycleEdges? j = some edges ∧
      FifteenCycleEdgesSpec edges box positiveZero exactZero := by
  obtain ⟨edges, hparse, hcheck⟩ :=
    fifteenCycleValid_produces_edges j box positiveZero exactZero hvalid
  exact ⟨edges, hparse,
    fifteenCycleEdgesValid_sound edges box positiveZero exactZero hcheck⟩

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

theorem fifteenListFoldlAddMapSum {α : Type} (items : List α)
    (f : α → Int) (initial : Int) :
    items.foldl (fun total item => total + f item) initial =
      initial + (items.map f).sum := by
  induction items generalizing initial with
  | nil => simp
  | cons item rest ih =>
      simp only [List.foldl_cons, List.map_cons, List.sum_cons]
      rw [ih]
      ring

theorem fifteenCycleFoldWeight_eq_weightTicks
    (edges : List FifteenCycleEdge) :
    fifteenCycleFoldWeight edges = fifteenCycleWeightTicks edges := by
  unfold fifteenCycleFoldWeight fifteenCycleWeightTicks
  rw [fifteenListFoldlAddMapSum edges fifteenCycleEdgeWeight 0]
  simp

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

theorem fifteenCycleEdgesSpec_excludes
    {edges : List FifteenCycleEdge} {box : FifteenBox}
    {positiveZero exactZero : List Nat}
    (spec : FifteenCycleEdgesSpec edges box positiveZero exactZero)
    {start : Nat} {theta : Fin 15 → ℝ}
    (hchain : FifteenCycleChain start edges start)
    (hbound : ∀ edge ∈ edges,
      theta (fifteenCycleFin edge.target) -
          theta (fifteenCycleFin edge.source) ≤
        (fifteenCycleEdgeWeight edge : ℝ) / fifteenAngleScale) :
    False := by
  have hnegative : fifteenCycleWeightTicks edges < 0 := by
    rw [← fifteenCycleFoldWeight_eq_weightTicks edges]
    exact spec.negativeWeight
  exact fifteenNegativeCycle_excludes hchain spec.edgeShapes hbound hnegative

theorem fifteenCycleValid_excludes_with_edge_bounds
    (j : Lean.Json) (box : FifteenBox) (positiveZero exactZero : List Nat)
    (theta : Fin 15 → ℝ)
    (hvalid : fifteenCycleValid j box positiveZero exactZero = true)
    (hbound : ∀ edges, fifteenParseCycleEdges? j = some edges →
      ∀ edge ∈ edges,
        theta (fifteenCycleFin edge.target) -
            theta (fifteenCycleFin edge.source) ≤
          (fifteenCycleEdgeWeight edge : ℝ) / fifteenAngleScale) :
    False := by
  obtain ⟨edges, hparse, hspec⟩ :=
    fifteenCycleValid_produces_spec j box positiveZero exactZero hvalid
  obtain ⟨first, last, hfirst, hlast, hchain⟩ :=
    fifteenCycleEdgesSpec_has_closed_chain hspec
  exact fifteenCycleEdgesSpec_excludes hspec hchain (hbound edges hparse)

end CirclePacking
