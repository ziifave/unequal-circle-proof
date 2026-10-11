import Mathlib.Basic.Real.Basic
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
    (hsize : box.size = 15) (haxis : axis < 15)
    (hparent : fifteenRealBoxContains box radii) :
    fifteenRealBoxContains (box.set! axis ((box[axis]!).1, cut)) radii ∨
      fifteenRealBoxContains (box.set! axis (cut, (box[axis]!).2)) radii := by
  have haxisLtSize : axis < box.size := by omega
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
    (radii : Fin 15 → ℝ) (hsize : box.size = 15)
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
  obtain ⟨axis, cut, left, right, _lo, _hi, hparts, _hbox, haxis,
      _hinner, _hlo, _hhi, _hmid⟩ :=
    fifteenCheckTasks_split_wellFormed fuel box inner node rest counts result
      htag haccepted
  exact ⟨axis, cut, left, right, hparts,
    fifteenRealBox_split_covers box radii axis cut hsize haxis hparent⟩

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
    (radii : Fin 15 → ℝ) (hsize : box.size = 15)
    (hparent : fifteenRealBoxContains box radii)
    (htag : fifteenJsonAt? node 0 >>= fifteenJsonString? = some "SPLIT")
    (haccepted : fifteenCheckTasks (fuel + 1)
      ((box, inner, node) :: rest) counts = some result) :
    ∃ axis cut left right lo hi,
      fifteenSplitParts? node = some (axis, cut, left, right) ∧
      box[axis]? = some (lo, hi) ∧ axis < 15 ∧ axis ∈ inner ∧
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
  have hchildren := fifteenRealBox_split_covers box radii axis cut
    hsize haxis hparent
  have hboxValue : box[axis]! = (lo, hi) := by
    simp [Array.getElem!_eq_getD, hbox]
  rw [hboxValue] at hchildren
  exact ⟨axis, cut, left, right, lo, hi, hparts, hbox, haxis, hinner,
    hchildren, hrec⟩

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

end CirclePacking
