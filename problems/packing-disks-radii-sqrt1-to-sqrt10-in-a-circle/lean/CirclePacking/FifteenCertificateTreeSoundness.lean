import Mathlib.Basic.Real.Basic
import Mathlib.Data.Rat.Cast.Order
import CirclePacking.FifteenCertificate

/-! Semantic facts about the exact certificate's closed rational boxes.
These are the interval-covering lemmas needed to lift a checked subdivision
tree from rational endpoints to the real radii of a packing. -/

namespace CirclePacking

open Lean

def fifteenRealIntervalContains (interval : FifteenInterval) (x : ℝ) : Prop :=
  (interval.1 : ℝ) ≤ x ∧ x ≤ (interval.2 : ℝ)

def fifteenRealBoxContains (box : FifteenBox) (radii : Fin 15 → ℝ) : Prop :=
  ∀ i : Fin 15, fifteenRealIntervalContains box[i.1]! (radii i)

def fifteenRealBoxStrictlyPositive (box : FifteenBox) : Prop :=
  ∀ i, i < 15 → 0 < (box[i]!.1 : ℝ)

theorem fifteenRealBox_set_size (box : FifteenBox) (axis : Nat)
    (interval : FifteenInterval) :
    (box.set! axis interval).size = box.size := by
  simp

theorem fifteenRealBox_leftChild_strictlyPositive
    (box : FifteenBox) (axis : Nat) (cut : Rat)
    (haxisLtSize : axis < box.size) (haxis : axis < 15)
    (hpositive : fifteenRealBoxStrictlyPositive box) :
    fifteenRealBoxStrictlyPositive
      (box.set! axis ((box[axis]!).1, cut)) := by
  intro i hi
  by_cases hia : i = axis
  · subst i
    simpa only [fifteenRealBoxStrictlyPositive, Array.set!_eq_setIfInBounds,
      Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?,
      Array.getElem?_setIfInBounds_self_of_lt haxisLtSize,
      Option.getD_some] using hpositive axis haxis
  · rw [Array.getElem!_set!_ne box axis i ((box[axis]!).1, cut) (Ne.symm hia)]
    exact hpositive i hi

theorem fifteenRealBox_rightChild_strictlyPositive
    (box : FifteenBox) (axis : Nat) (cut : Rat)
    (haxisLtSize : axis < box.size) (haxis : axis < 15)
    (hcut : (box[axis]!).1 < cut)
    (hpositive : fifteenRealBoxStrictlyPositive box) :
    fifteenRealBoxStrictlyPositive
      (box.set! axis (cut, (box[axis]!).2)) := by
  intro i hi
  by_cases hia : i = axis
  · subst i
    have hcut' : (box[axis]!.1 : ℝ) < (cut : ℝ) := Rat.cast_lt.mpr hcut
    have hlower := hpositive axis haxis
    have hnew : 0 < (cut : ℝ) := lt_trans hlower hcut'
    simpa only [Array.set!_eq_setIfInBounds, Array.getElem!_eq_getD,
      Array.getD_eq_getD_getElem?,
      Array.getElem?_setIfInBounds_self_of_lt haxisLtSize,
      Option.getD_some] using hnew
  · rw [Array.getElem!_set!_ne box axis i (cut, (box[axis]!).2) (Ne.symm hia)]
    exact hpositive i hi

def fifteenBoxGood (box : FifteenBox) : Prop :=
  box.size = 15 ∧ fifteenRealBoxStrictlyPositive box

def fifteenTaskBoxGood (task : FifteenTask) : Prop :=
  fifteenBoxGood task.1

def fifteenTaskListBoxesGood (tasks : List FifteenTask) : Prop :=
  ∀ task, task ∈ tasks → fifteenTaskBoxGood task

theorem fifteenRealBox_split_children_good
    (box : FifteenBox) (axis : Nat) (cut : Rat) (lo hi : Rat)
    (hbox : box[axis]? = some (lo, hi)) (haxis : axis < 15)
    (hcut : lo < cut)
    (hparent : fifteenBoxGood box) :
    fifteenBoxGood (box.set! axis (lo, cut)) ∧
      fifteenBoxGood (box.set! axis (cut, hi)) := by
  have haxisLtSize : axis < box.size :=
    (Array.getElem?_eq_some_iff.mp hbox).1
  have hboxValue : box[axis]! = (lo, hi) := by
    simp [Array.getElem!_eq_getD, hbox]
  have hleftPositive := fifteenRealBox_leftChild_strictlyPositive
    box axis cut haxisLtSize haxis hparent.2
  have hrightCut : (box[axis]!).1 < cut := by
    rw [hboxValue]
    exact hcut
  have hrightPositive := fifteenRealBox_rightChild_strictlyPositive
    box axis cut haxisLtSize haxis hrightCut hparent.2
  have hleftSize : (box.set! axis (lo, cut)).size = 15 :=
    (fifteenRealBox_set_size box axis (lo, cut)).trans hparent.1
  have hrightSize : (box.set! axis (cut, hi)).size = 15 :=
    (fifteenRealBox_set_size box axis (cut, hi)).trans hparent.1
  constructor
  · exact ⟨hleftSize, by simpa [hboxValue] using hleftPositive⟩
  · exact ⟨hrightSize, by simpa [hboxValue] using hrightPositive⟩

theorem fifteenTaskListBoxesGood_split
    (box : FifteenBox) (inner : List Nat) (left right : Json)
    (rest : List FifteenTask) (axis : Nat) (cut lo hi : Rat)
    (hchildren : fifteenTaskBoxGood
        (box.set! axis (lo, cut), inner, left) ∧
      fifteenTaskBoxGood (box.set! axis (cut, hi), inner, right))
    (hrest : fifteenTaskListBoxesGood rest) :
    fifteenTaskListBoxesGood
      ((box.set! axis (lo, cut), inner, left) ::
        (box.set! axis (cut, hi), inner, right) :: rest) := by
  intro task htask
  simp only [List.mem_cons] at htask
  rcases htask with hleft | htail
  · cases hleft
    exact hchildren.1
  · rcases htail with hright | hrest'
    · cases hright
      exact hchildren.2
    · exact hrest task hrest'

/-- The split convention is closed on both sides, so a radius on the cut is
covered by either child (in fact, by both). -/
theorem fifteenRealIntervalSplitCovers (lo cut hi : Rat) (x : ℝ)
    (hx : fifteenRealIntervalContains (lo, hi) x) :
    fifteenRealIntervalContains (lo, cut) x ∨
      fifteenRealIntervalContains (cut, hi) x := by
  rcases hx with ⟨hlo, hhi⟩
  rcases le_total x (cut : ℝ) with hleft | hright
  · exact Or.inl ⟨hlo, hleft⟩
  · exact Or.inr ⟨hright, hhi⟩

theorem fifteenRealIntervalLeftChildSubset (lo cut hi : Rat) (x : ℝ)
    (hcut : (cut : ℝ) ≤ hi)
    (hx : fifteenRealIntervalContains (lo, cut) x) :
    fifteenRealIntervalContains (lo, hi) x := by
  rcases hx with ⟨hlo, hxcut⟩
  exact ⟨hlo, le_trans hxcut hcut⟩

theorem fifteenRealIntervalRightChildSubset (lo cut hi : Rat) (x : ℝ)
    (hcut : (lo : ℝ) ≤ cut)
    (hx : fifteenRealIntervalContains (cut, hi) x) :
    fifteenRealIntervalContains (lo, hi) x := by
  rcases hx with ⟨hcutx, hhi⟩
  exact ⟨le_trans hcut hcutx, hhi⟩

theorem fifteenRealBox_leftChildSubset
    (box : FifteenBox) (radii : Fin 15 → ℝ) (axis : Nat) (cut : Rat)
    (hsize : box.size = 15) (haxis : axis < 15)
    (hcut : (cut : ℝ) ≤ (box[axis]!.2 : ℝ))
    (hchild : fifteenRealBoxContains
      (box.set! axis ((box[axis]!).1, cut)) radii) :
    fifteenRealBoxContains box radii := by
  have haxisBox : axis < box.size := by omega
  intro i
  by_cases hi : i.1 = axis
  · have heq : i = ⟨axis, by omega⟩ := Fin.ext hi
    subst i
    have hpart := hchild ⟨axis, by omega⟩
    have hpart' : fifteenRealIntervalContains ((box[axis]!).1, cut)
        (radii ⟨axis, by omega⟩) := by
      simpa only [fifteenRealIntervalContains, Array.set!_eq_setIfInBounds,
      Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?,
      Array.getElem?_setIfInBounds_self_of_lt haxisBox,
      Option.getD_some] using hpart
    exact fifteenRealIntervalLeftChildSubset (box[axis]!).1 cut
      (box[axis]!).2 (radii ⟨axis, by omega⟩) hcut hpart'
  · have hpart := hchild i
    rw [Array.getElem!_set!_ne box axis i.1 ((box[axis]!).1, cut)
      (Ne.symm hi)] at hpart
    exact hpart

theorem fifteenRealBox_rightChildSubset
    (box : FifteenBox) (radii : Fin 15 → ℝ) (axis : Nat) (cut : Rat)
    (hsize : box.size = 15) (haxis : axis < 15)
    (hcut : (box[axis]!.1 : ℝ) ≤ cut)
    (hchild : fifteenRealBoxContains
      (box.set! axis (cut, (box[axis]!).2)) radii) :
    fifteenRealBoxContains box radii := by
  have haxisBox : axis < box.size := by omega
  intro i
  by_cases hi : i.1 = axis
  · have heq : i = ⟨axis, by omega⟩ := Fin.ext hi
    subst i
    have hpart := hchild ⟨axis, by omega⟩
    have hpart' : fifteenRealIntervalContains (cut, (box[axis]!).2)
        (radii ⟨axis, by omega⟩) := by
      simpa only [fifteenRealIntervalContains, Array.set!_eq_setIfInBounds,
      Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?,
      Array.getElem?_setIfInBounds_self_of_lt haxisBox,
      Option.getD_some] using hpart
    exact fifteenRealIntervalRightChildSubset (box[axis]!).1 cut
      (box[axis]!).2 (radii ⟨axis, by omega⟩) hcut hpart'
  · have hpart := hchild i
    rw [Array.getElem!_set!_ne box axis i.1 (cut, (box[axis]!).2)
      (Ne.symm hi)] at hpart
    exact hpart

/-- Every real profile in a parent box remains in at least one of the two
array boxes produced by the checker at a legal split coordinate. -/
theorem fifteenRealBox_split_covers
    (box : FifteenBox) (radii : Fin 15 → ℝ) (axis : Nat) (cut : Rat)
    (haxisLtSize : axis < box.size) (haxis : axis < 15)
    (hparent : fifteenRealBoxContains box radii) :
    fifteenRealBoxContains (box.set! axis ((box[axis]!).1, cut)) radii ∨
      fifteenRealBoxContains (box.set! axis (cut, (box[axis]!).2)) radii := by
  have hparentAxis := hparent ⟨axis, by omega⟩
  have hcoord := fifteenRealIntervalSplitCovers (box[axis]!).1 cut
    (box[axis]!).2 (radii ⟨axis, by omega⟩) hparentAxis
  rcases hcoord with hleft | hright
  · left
    intro i
    by_cases hi : i.1 = axis
    · have heq : i = ⟨axis, by omega⟩ := Fin.ext hi
      subst i
      simpa only [fifteenRealIntervalContains, Array.set!_eq_setIfInBounds,
        Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?,
        Array.getElem?_setIfInBounds_self_of_lt haxisLtSize,
        Option.getD_some] using hleft
    · rw [Array.getElem!_set!_ne box axis i.1 ((box[axis]!).1, cut)
        (Ne.symm hi)]
      exact hparent i
  · right
    intro i
    by_cases hi : i.1 = axis
    · have heq : i = ⟨axis, by omega⟩ := Fin.ext hi
      subst i
      simpa only [fifteenRealIntervalContains, Array.set!_eq_setIfInBounds,
        Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?,
        Array.getElem?_setIfInBounds_self_of_lt haxisLtSize,
        Option.getD_some] using hright
    · rw [Array.getElem!_set!_ne box axis i.1 (cut, (box[axis]!).2)
        (Ne.symm hi)]
      exact hparent i

/- If a work-list replay accepts a split task, its recorded bisection is a
legal midpoint split of one of the fifteen coordinates. This extracts the
facts needed to apply `fifteenRealBox_split_covers` to an actual profile. -/
theorem fifteenCheckTasks_split_wellFormed
    (fuel : Nat) (box : FifteenBox) (inner : List Nat) (node : Json)
    (rest : List FifteenTask) (counts result : FifteenTreeCounts)
    (htag : fifteenJsonAt? node 0 >>= fifteenJsonString? = some "SPLIT")
    (haccepted : fifteenCheckTasks (fuel + 1)
      ((box, inner, node) :: rest) counts = some result) :
    ∃ axis cut left right lo hi,
      fifteenSplitParts? node = some (axis, cut, left, right) ∧
      box[axis]? = some (lo, hi) ∧ axis < 15 ∧ axis ∈ inner ∧
      lo < cut ∧ cut < hi ∧ cut = (lo + hi) / 2 := by
  cases hparts : fifteenSplitParts? node with
  | none => simp [fifteenCheckTasks, Id.run, htag, hparts] at haccepted
  | some parts =>
    rcases parts with ⟨axis, cut, left, right⟩
    cases hbox : box[axis]? with
    | none => simp [fifteenCheckTasks, Id.run, htag, hparts, hbox] at haccepted
    | some endpoints =>
      rcases endpoints with ⟨lo, hi⟩
      have hvalid :
          ¬ ((((15 ≤ axis ∨ axis ∉ inner) ∨ cut ≤ lo) ∨ hi ≤ cut) ∨
            cut ≠ (lo + hi) / 2) := by
        intro hbad
        simp [fifteenCheckTasks, Id.run, htag, hparts, hbox, hbad] at haccepted
      simp only [not_or] at hvalid
      rcases hvalid with ⟨⟨⟨⟨haxis, hmem⟩, hlo⟩, hhi⟩, hmid⟩
      have haxis' : axis < 15 := by omega
      have hmem' : axis ∈ inner := by
        by_contra h
        exact hmem h
      have hlo' : lo < cut := lt_of_not_ge hlo
      have hhi' : cut < hi := lt_of_not_ge hhi
      have hmid' : cut = (lo + hi) / 2 := by
        by_contra h
        exact hmid h
      exact ⟨axis, cut, left, right, lo, hi, rfl, hbox, haxis',
        hmem', hlo', hhi', hmid'⟩

/-- An accepted split node preserves containment of an actual profile in at
least one of the two child tasks. -/
theorem fifteenCheckTasks_split_profile_children
    (fuel : Nat) (box : FifteenBox) (inner : List Nat) (node : Json)
    (rest : List FifteenTask) (counts result : FifteenTreeCounts)
    (radii : Fin 15 → ℝ)
    (hparent : fifteenRealBoxContains box radii)
    (htag : fifteenJsonAt? node 0 >>= fifteenJsonString? = some "SPLIT")
    (haccepted : fifteenCheckTasks (fuel + 1)
      ((box, inner, node) :: rest) counts = some result) :
    ∃ axis cut left right,
      fifteenSplitParts? node = some (axis, cut, left, right) ∧
        (fifteenRealBoxContains
            (box.set! axis ((box[axis]!).1, cut)) radii ∨
          fifteenRealBoxContains
            (box.set! axis (cut, (box[axis]!).2)) radii) := by
  obtain ⟨axis, cut, left, right, _lo, _hi, hparts, hbox, haxis,
      _hinner, _hlo, _hhi, _hmid⟩ :=
    fifteenCheckTasks_split_wellFormed fuel box inner node rest counts result
      htag haccepted
  have haxisLtSize : axis < box.size :=
    (Array.getElem?_eq_some_iff.mp hbox).1
  exact ⟨axis, cut, left, right, hparts,
    fifteenRealBox_split_covers box radii axis cut haxisLtSize haxis hparent⟩

/-- A successful split replay continues with exactly the two recorded child
tasks, in front of the original queue. -/
theorem fifteenCheckTasks_split_recursion
    (fuel : Nat) (box : FifteenBox) (inner : List Nat) (node : Json)
    (rest : List FifteenTask) (counts result : FifteenTreeCounts)
    (htag : fifteenJsonAt? node 0 >>= fifteenJsonString? = some "SPLIT")
    (haccepted : fifteenCheckTasks (fuel + 1)
      ((box, inner, node) :: rest) counts = some result) :
    ∃ axis cut left right lo hi,
      fifteenSplitParts? node = some (axis, cut, left, right) ∧
      box[axis]? = some (lo, hi) ∧
      axis < 15 ∧ axis ∈ inner ∧ lo < cut ∧ cut < hi ∧
      cut = (lo + hi) / 2 ∧
      fifteenCheckTasks fuel
        ((box.set! axis (lo, cut), inner, left) ::
          (box.set! axis (cut, hi), inner, right) :: rest)
        { counts with nodes := counts.nodes + 1 } = some result := by
  cases hparts : fifteenSplitParts? node with
  | none => simp [fifteenCheckTasks, Id.run, htag, hparts] at haccepted
  | some parts =>
    rcases parts with ⟨axis, cut, left, right⟩
    cases hbox : box[axis]? with
    | none => simp [fifteenCheckTasks, Id.run, htag, hparts, hbox] at haccepted
    | some endpoints =>
      rcases endpoints with ⟨lo, hi⟩
      have hvalid :
          ¬ ((((15 ≤ axis ∨ axis ∉ inner) ∨ cut ≤ lo) ∨ hi ≤ cut) ∨
            cut ≠ (lo + hi) / 2) := by
        intro hbad
        simp [fifteenCheckTasks, Id.run, htag, hparts, hbox, hbad] at haccepted
      have hguard := hvalid
      simp only [not_or] at hvalid
      rcases hvalid with ⟨⟨⟨⟨haxis, hmem⟩, hlo⟩, hhi⟩, hmid⟩
      have haxis' : axis < 15 := by omega
      have hmem' : axis ∈ inner := by
        by_contra h
        exact hmem h
      have hlo' : lo < cut := lt_of_not_ge hlo
      have hhi' : cut < hi := lt_of_not_ge hhi
      have hmid' : cut = (lo + hi) / 2 := by
        by_contra h
        exact hmid h
      have hrec0 := haccepted
      simp [fifteenCheckTasks, Id.run, htag, hparts, hbox, hguard] at hrec0
      have hrec : fifteenCheckTasks fuel
          ((box.set! axis (lo, cut), inner, left) ::
            (box.set! axis (cut, hi), inner, right) :: rest)
          { counts with nodes := counts.nodes + 1 } = some result := by
        have hrec1 := hrec0
        change fifteenCheckTasks fuel
          ((Array.setIfInBounds box axis (lo, cut), inner, left) ::
            (Array.setIfInBounds box axis (cut, hi), inner, right) :: rest)
          { counts with nodes := counts.nodes + 1 } = some result at hrec1
        simpa [Array.set!_eq_setIfInBounds] using hrec1
      exact ⟨axis, cut, left, right, lo, hi, rfl, hbox, haxis', hmem',
        hlo', hhi', hmid', hrec⟩

/-- The accepted work-list step simultaneously certifies the recursive queue
and preserves a profile in one of the recorded child boxes. -/
theorem fifteenCheckTasks_split_step_sound
    (fuel : Nat) (box : FifteenBox) (inner : List Nat) (node : Json)
    (rest : List FifteenTask) (counts result : FifteenTreeCounts)
    (radii : Fin 15 → ℝ)
    (hparent : fifteenRealBoxContains box radii)
    (htag : fifteenJsonAt? node 0 >>= fifteenJsonString? = some "SPLIT")
    (haccepted : fifteenCheckTasks (fuel + 1)
      ((box, inner, node) :: rest) counts = some result) :
    ∃ axis cut left right lo hi,
      fifteenSplitParts? node = some (axis, cut, left, right) ∧
      box[axis]? = some (lo, hi) ∧ axis < 15 ∧ axis ∈ inner ∧
      lo < cut ∧ cut < hi ∧ cut = (lo + hi) / 2 ∧
      (fifteenRealBoxContains
          (box.set! axis (lo, cut)) radii ∨
        fifteenRealBoxContains
          (box.set! axis (cut, hi)) radii) ∧
      fifteenCheckTasks fuel
        ((box.set! axis (lo, cut), inner, left) ::
          (box.set! axis (cut, hi), inner, right) :: rest)
        { counts with nodes := counts.nodes + 1 } = some result := by
  obtain ⟨axis, cut, left, right, lo, hi, hparts, hbox, haxis,
      hinner, hlo, hhi, hmid, hrec⟩ :=
    fifteenCheckTasks_split_recursion fuel box inner node rest counts result
      htag haccepted
  have haxisLtSize : axis < box.size :=
    (Array.getElem?_eq_some_iff.mp hbox).1
  have hchildren := fifteenRealBox_split_covers box radii axis cut
    haxisLtSize haxis hparent
  have hboxValue : box[axis]! = (lo, hi) := by
    simp [Array.getElem!_eq_getD, hbox]
  rw [hboxValue] at hchildren
  exact ⟨axis, cut, left, right, lo, hi, hparts, hbox, haxis, hinner,
    hlo, hhi, hmid, hchildren, hrec⟩

/-- An accepted `CYCLE` terminal is valid and the queue replay continues with
the remaining tasks. -/
theorem fifteenCheckTasks_cycle_recursion
    (fuel : Nat) (box : FifteenBox) (inner : List Nat) (node : Json)
    (rest : List FifteenTask) (counts result : FifteenTreeCounts)
    (htag : fifteenJsonAt? node 0 >>= fifteenJsonString? = some "CYCLE")
    (haccepted : fifteenCheckTasks (fuel + 1)
      ((box, inner, node) :: rest) counts = some result) :
    fifteenTerminalValid box inner node false = true ∧
      fifteenCheckTasks fuel rest
        { counts with nodes := counts.nodes + 1, cycles := counts.cycles + 1 } =
          some result := by
  cases hterminal : fifteenTerminalValid box inner node false with
  | false => simp [fifteenCheckTasks, Id.run, htag, hterminal] at haccepted
  | true =>
      have hrec := haccepted
      simp [fifteenCheckTasks, Id.run, htag, hterminal] at hrec
      have hrec1 := hrec
      change fifteenCheckTasks fuel rest
        { counts with nodes := counts.nodes + 1, cycles := counts.cycles + 1 } =
          some result at hrec1
      exact ⟨rfl, hrec1⟩

/-- An accepted `SUM` terminal is valid and the queue replay continues with
the remaining tasks. -/
theorem fifteenCheckTasks_sum_recursion
    (fuel : Nat) (box : FifteenBox) (inner : List Nat) (node : Json)
    (rest : List FifteenTask) (counts result : FifteenTreeCounts)
    (htag : fifteenJsonAt? node 0 >>= fifteenJsonString? = some "SUM")
    (haccepted : fifteenCheckTasks (fuel + 1)
      ((box, inner, node) :: rest) counts = some result) :
    fifteenTerminalValid box inner node false = true ∧
      fifteenCheckTasks fuel rest
        { counts with nodes := counts.nodes + 1, sums := counts.sums + 1 } =
          some result := by
  cases hterminal : fifteenTerminalValid box inner node false with
  | false => simp [fifteenCheckTasks, Id.run, htag, hterminal] at haccepted
  | true =>
      have hrec := haccepted
      simp [fifteenCheckTasks, Id.run, htag, hterminal] at hrec
      have hrec1 := hrec
      change fifteenCheckTasks fuel rest
        { counts with nodes := counts.nodes + 1, sums := counts.sums + 1 } =
          some result at hrec1
      exact ⟨rfl, hrec1⟩

/-- An accepted `LOCAL` terminal is valid and the queue replay continues with
the remaining tasks. -/
theorem fifteenCheckTasks_local_recursion
    (fuel : Nat) (box : FifteenBox) (inner : List Nat) (node : Json)
    (rest : List FifteenTask) (counts result : FifteenTreeCounts)
    (htag : fifteenJsonAt? node 0 >>= fifteenJsonString? = some "LOCAL")
    (haccepted : fifteenCheckTasks (fuel + 1)
      ((box, inner, node) :: rest) counts = some result) :
    fifteenTerminalValid box inner node true = true ∧
      fifteenCheckTasks fuel rest
        { counts with nodes := counts.nodes + 1, localLeaves := counts.localLeaves + 1 } =
          some result := by
  cases hterminal : fifteenTerminalValid box inner node true with
  | false => simp [fifteenCheckTasks, Id.run, htag, hterminal] at haccepted
  | true =>
      have hrec := haccepted
      simp [fifteenCheckTasks, Id.run, htag, hterminal] at hrec
      have hrec1 := hrec
      change fifteenCheckTasks fuel rest
        { counts with nodes := counts.nodes + 1, localLeaves := counts.localLeaves + 1 } =
          some result at hrec1
      exact ⟨rfl, hrec1⟩

def fifteenTaskHasProfile (task : FifteenTask) (radii : Fin 15 → ℝ) : Prop :=
  fifteenRealBoxContains task.1 radii

/-- A successful work-list replay cannot discard every task containing a real
profile: it reaches a compatible checked terminal (`CYCLE`, `SUM`, or
`LOCAL`). Geometric exclusion of the first two terminal types is supplied by
the separate cycle and sum soundness theorems. -/
theorem fifteenCheckTasks_profile_reaches_terminal :
    ∀ (fuel : Nat) (tasks : List FifteenTask) (counts result : FifteenTreeCounts)
      (radii : Fin 15 → ℝ),
      fifteenCheckTasks fuel tasks counts = some result →
      fifteenTaskListBoxesGood tasks →
      (∃ task, task ∈ tasks ∧ fifteenTaskHasProfile task radii) →
      ∃ box inner node, fifteenBoxGood box ∧ fifteenRealBoxContains box radii ∧
        ((fifteenJsonAt? node 0 >>= fifteenJsonString? = some "CYCLE" ∧
            fifteenTerminalValid box inner node false = true) ∨
          (fifteenJsonAt? node 0 >>= fifteenJsonString? = some "SUM" ∧
            fifteenTerminalValid box inner node false = true) ∨
          (fifteenJsonAt? node 0 >>= fifteenJsonString? = some "LOCAL" ∧
            fifteenTerminalValid box inner node true = true)) := by
  intro fuel
  induction fuel with
  | zero =>
      intro tasks counts result radii hcheck _hboxesGood hcontains
      cases tasks with
      | nil => simp at hcontains
      | cons task rest => simp [fifteenCheckTasks] at hcheck
  | succ fuel ih =>
      intro tasks counts result radii hcheck hboxesGood hcontains
      cases tasks with
      | nil => simp at hcontains
      | cons task rest =>
          rcases task with ⟨box, inner, node⟩
          have hheadGood : fifteenBoxGood box := by
            exact hboxesGood (box, inner, node) (by simp)
          have hrestGood : fifteenTaskListBoxesGood rest := by
            intro next hnext
            exact hboxesGood next (by simp [hnext])
          cases htag : (fifteenJsonAt? node 0 >>= fifteenJsonString?) with
          | none => simp [fifteenCheckTasks, Id.run, htag] at hcheck
          | some tag =>
              by_cases hsplit : tag = "SPLIT"
              · have htagSplit :
                    fifteenJsonAt? node 0 >>= fifteenJsonString? = some "SPLIT" := by
                  simpa [htag, hsplit]
                by_cases hhead : fifteenRealBoxContains box radii
                · have hstep := fifteenCheckTasks_split_step_sound fuel box inner node rest
                    counts result radii hhead htagSplit hcheck
                  rcases hstep with ⟨axis, cut, left, right, lo, hi, _hparts, hbox,
                    haxis, _hinner, hlo, _hhi, _hmid, hchildren, hrec⟩
                  have hchildrenGood := fifteenRealBox_split_children_good
                    box axis cut lo hi hbox haxis hlo hheadGood
                  have hnewGood := fifteenTaskListBoxesGood_split box inner left right
                    rest axis cut lo hi hchildrenGood hrestGood
                  rcases hchildren with hleft | hright
                  · have hnew :
                        ∃ next, next ∈
                          ((box.set! axis (lo, cut), inner, left) ::
                            (box.set! axis (cut, hi), inner, right) :: rest) ∧
                            fifteenTaskHasProfile next radii := by
                      exact ⟨(box.set! axis (lo, cut), inner, left), by simp,
                        hleft⟩
                    exact ih
                      ((box.set! axis (lo, cut), inner, left) ::
                        (box.set! axis (cut, hi), inner, right) :: rest)
                      { counts with nodes := counts.nodes + 1 } result radii hrec
                      hnewGood hnew
                  · have hnew :
                        ∃ next, next ∈
                          ((box.set! axis (lo, cut), inner, left) ::
                            (box.set! axis (cut, hi), inner, right) :: rest) ∧
                            fifteenTaskHasProfile next radii := by
                      exact ⟨(box.set! axis (cut, hi), inner, right), by simp,
                        hright⟩
                    exact ih
                      ((box.set! axis (lo, cut), inner, left) ::
                        (box.set! axis (cut, hi), inner, right) :: rest)
                      { counts with nodes := counts.nodes + 1 } result radii hrec
                      hnewGood hnew
                · have hrest :
                      ∃ next, next ∈ rest ∧ fifteenTaskHasProfile next radii := by
                    rcases hcontains with ⟨next, hmem, hprofile⟩
                    rcases List.mem_cons.mp hmem with heq | htail
                    · subst next
                      exact (hhead hprofile).elim
                    · exact ⟨next, htail, hprofile⟩
                  obtain ⟨axis, cut, left, right, lo, hi, _hparts, hbox,
                    haxis, _hinner, hlo, _hhi, _hmid, hrec⟩ :=
                    fifteenCheckTasks_split_recursion fuel box inner node rest
                      counts result htagSplit hcheck
                  have hchildrenGood := fifteenRealBox_split_children_good
                    box axis cut lo hi hbox haxis hlo hheadGood
                  have hnewGood := fifteenTaskListBoxesGood_split box inner left right
                    rest axis cut lo hi hchildrenGood hrestGood
                  have hnew :
                      ∃ next, next ∈
                        ((box.set! axis (lo, cut), inner, left) ::
                          (box.set! axis (cut, hi), inner, right) :: rest) ∧
                          fifteenTaskHasProfile next radii := by
                    rcases hrest with ⟨next, hmem, hprofile⟩
                    exact ⟨next, by simp [hmem], hprofile⟩
                  exact ih
                    ((box.set! axis (lo, cut), inner, left) ::
                      (box.set! axis (cut, hi), inner, right) :: rest)
                    { counts with nodes := counts.nodes + 1 } result radii hrec
                    hnewGood hnew
              · by_cases hcycle : tag = "CYCLE"
                · have htagCycle :
                      fifteenJsonAt? node 0 >>= fifteenJsonString? = some "CYCLE" := by
                    simpa [htag, hcycle]
                  obtain ⟨hterminal, hrec⟩ :=
                    fifteenCheckTasks_cycle_recursion fuel box inner node rest
                      counts result htagCycle hcheck
                  by_cases hhead : fifteenRealBoxContains box radii
                  · exact ⟨box, inner, node, hheadGood, hhead,
                      Or.inl ⟨htagCycle, hterminal⟩⟩
                  · have hrest :
                        ∃ next, next ∈ rest ∧ fifteenTaskHasProfile next radii := by
                      rcases hcontains with ⟨next, hmem, hprofile⟩
                      rcases List.mem_cons.mp hmem with heq | htail
                      · subst next
                        exact (hhead hprofile).elim
                      · exact ⟨next, htail, hprofile⟩
                    exact ih rest
                      { counts with nodes := counts.nodes + 1, cycles := counts.cycles + 1 }
                      result radii hrec hrestGood hrest
                · by_cases hsum : tag = "SUM"
                  · have htagSum :
                        fifteenJsonAt? node 0 >>= fifteenJsonString? = some "SUM" := by
                      simpa [htag, hsum]
                    obtain ⟨hterminal, hrec⟩ :=
                      fifteenCheckTasks_sum_recursion fuel box inner node rest
                        counts result htagSum hcheck
                    by_cases hhead : fifteenRealBoxContains box radii
                    · exact ⟨box, inner, node, hheadGood, hhead,
                        Or.inr (Or.inl ⟨htagSum, hterminal⟩)⟩
                    · have hrest :
                          ∃ next, next ∈ rest ∧ fifteenTaskHasProfile next radii := by
                        rcases hcontains with ⟨next, hmem, hprofile⟩
                        rcases List.mem_cons.mp hmem with heq | htail
                        · subst next
                          exact (hhead hprofile).elim
                        · exact ⟨next, htail, hprofile⟩
                      exact ih rest
                        { counts with nodes := counts.nodes + 1, sums := counts.sums + 1 }
                        result radii hrec hrestGood hrest
                  · by_cases hlocal : tag = "LOCAL"
                    · have htagLocal :
                          fifteenJsonAt? node 0 >>= fifteenJsonString? = some "LOCAL" := by
                        simpa [htag, hlocal]
                      obtain ⟨hterminal, hrec⟩ :=
                        fifteenCheckTasks_local_recursion fuel box inner node rest
                          counts result htagLocal hcheck
                      by_cases hhead : fifteenRealBoxContains box radii
                      · exact ⟨box, inner, node, hheadGood, hhead,
                          Or.inr (Or.inr ⟨htagLocal, hterminal⟩)⟩
                      · have hrest :
                            ∃ next, next ∈ rest ∧ fifteenTaskHasProfile next radii := by
                          rcases hcontains with ⟨next, hmem, hprofile⟩
                          rcases List.mem_cons.mp hmem with heq | htail
                          · subst next
                            exact (hhead hprofile).elim
                          · exact ⟨next, htail, hprofile⟩
                        exact ih rest
                          { counts with nodes := counts.nodes + 1, localLeaves := counts.localLeaves + 1 }
                          result radii hrec hrestGood hrest
                    · have hbad := hcheck
                      simp [fifteenCheckTasks, Id.run, htag, hsplit, hcycle,
                        hsum, hlocal] at hbad

/-- If `CYCLE` and `SUM` terminals are geometrically impossible for a given
profile, an accepted work-list replay containing that profile must reach a
valid `LOCAL` terminal. -/
theorem fifteenCheckTasks_profile_reaches_local
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
    ∃ box inner node, fifteenRealBoxContains box radii ∧
      fifteenJsonAt? node 0 >>= fifteenJsonString? = some "LOCAL" ∧
      fifteenTerminalValid box inner node true = true := by
  obtain ⟨box, inner, node, _hboxGood, hprofile, hterminal⟩ :=
    fifteenCheckTasks_profile_reaches_terminal fuel tasks counts result radii
      hcheck hboxesGood hcontains
  rcases hterminal with hcycle | hsum | hlocal
  · exact False.elim (hcycleImpossible box inner node _hboxGood hcycle.1 hcycle.2 hprofile)
  · exact False.elim (hsumImpossible box inner node hsum.1 hsum.2 hprofile)
  · exact ⟨box, inner, node, hprofile, hlocal.1, hlocal.2⟩

end CirclePacking
