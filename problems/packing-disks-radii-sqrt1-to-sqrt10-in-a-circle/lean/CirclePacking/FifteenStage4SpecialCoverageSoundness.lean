import CirclePacking.FifteenStage4SpecialCoverageReplay
import CirclePacking.FifteenStage4Coverage003

/-! Semantic replay for the origin-special Stage 4 leaves.  The exact JSON
certificate distinguishes a positive radius in the first bin from a center
at the origin; both cases are checked here using the same leaf checker as the
main subdivision certificate. -/

namespace CirclePacking

open Lean

def s4CoverageSpecialRows : List (String × Array Nat) :=
  [("636808", #[6, 3, 6, 8, 0, 8]),
   ("646808", #[6, 4, 6, 8, 0, 8]),
   ("656808", #[6, 5, 6, 8, 0, 8])]

def s4CoverageSpecialModes : List String :=
  ["POSITIVE_LOW", "POSITIVE_HIGH", "EXACT_ZERO"]

theorem s4CoverageSpecialPositions_exact :
    s4InnerPositions fifteenSpecialPattern = #[2, 5, 8, 11, 13, 14] := by
  native_decide

def s4CoverageSpecialOriginInterval (mode : String) : FifteenInterval :=
  if mode == "POSITIVE_LOW" then (fifteenRational 0 1, fifteenRational 1 4)
  else if mode == "POSITIVE_HIGH" then
    (fifteenRational 1 4, fifteenRational 1 2)
  else (fifteenRational 0 1, fifteenRational 0 1)

def s4CoverageSpecialExpectedBox (digits : Array Nat) (mode : String) :
    FifteenBox := Array.ofFn (fun i : Fin 15 =>
  if i.val = 2 then fifteenBins[digits[0]!]! else
  if i.val = 5 then fifteenBins[digits[1]!]! else
  if i.val = 8 then fifteenBins[digits[2]!]! else
  if i.val = 11 then fifteenBins[digits[3]!]! else
  if i.val = 13 then s4CoverageSpecialOriginInterval mode else
  if i.val = 14 then fifteenBins[digits[5]!]! else fifteenBins[11]!)

def s4CoverageSpecialBoxReplay : Bool :=
  s4CoverageSpecialRows.all (fun row =>
    s4CoverageSpecialModes.all (fun mode =>
      decide (fifteenSpecialBox? row.1 mode 13 =
        some (s4CoverageSpecialExpectedBox row.2 mode))))

set_option maxRecDepth 100000 in
theorem s4CoverageSpecialBoxReplay_replays :
    s4CoverageSpecialBoxReplay = true := by
  native_decide

theorem s4CoverageSpecialBox_matches
    {assignment mode : String} {digits : Array Nat}
    (hrow : (assignment, digits) ∈ s4CoverageSpecialRows)
    (hmode : mode ∈ s4CoverageSpecialModes) :
    fifteenSpecialBox? assignment mode 13 =
      some (s4CoverageSpecialExpectedBox digits mode) := by
  have hReplay := s4CoverageSpecialBoxReplay_replays
  have hrows : s4CoverageSpecialRows.all (fun row =>
      s4CoverageSpecialModes.all (fun mode =>
        decide (fifteenSpecialBox? row.1 mode 13 =
          some (s4CoverageSpecialExpectedBox row.2 mode)))) = true := by
    simpa [s4CoverageSpecialBoxReplay] using hReplay
  have hrowData := List.all_eq_true.mp hrows (assignment, digits) hrow
  have hmodesData : s4CoverageSpecialModes.all (fun mode =>
      decide (fifteenSpecialBox? assignment mode 13 =
        some (s4CoverageSpecialExpectedBox digits mode))) = true := by
    simpa using hrowData
  have hbox := List.all_eq_true.mp hmodesData mode hmode
  exact of_decide_eq_true hbox

theorem s4CoverageSpecialHighBox_good
    {assignment : String} {digits : Array Nat}
    (hrow : (assignment, digits) ∈ s4CoverageSpecialRows) :
    fifteenBoxGood (s4CoverageSpecialExpectedBox digits "POSITIVE_HIGH") := by
  simp only [s4CoverageSpecialRows, List.mem_cons, List.not_mem_nil,
    or_false] at hrow
  rcases hrow with hrow | hrow | hrow
  all_goals
    cases hrow
    constructor
    · simp [s4CoverageSpecialExpectedBox]
    · intro i hi
      interval_cases i <;>
        norm_num [fifteenRealBoxStrictlyPositive,
          s4CoverageSpecialExpectedBox, s4CoverageSpecialOriginInterval,
          fifteenBins, fifteenRational, Rat.normalize_eq_mkRat,
          Rat.cast_mkRat_of_ne_zero]

private theorem s4CoverageSpecialExpectedBox_outside
    (digits : Array Nat) (mode : String) (i : Nat)
    (hi : i < 15)
    (hnot : i ∉ [2, 5, 8, 11, 13, 14]) :
    (s4CoverageSpecialExpectedBox digits mode)[i]! = fifteenBins[11]! := by
  have hi2 : i ≠ 2 := by intro h; subst i; simp at hnot
  have hi5 : i ≠ 5 := by intro h; subst i; simp at hnot
  have hi8 : i ≠ 8 := by intro h; subst i; simp at hnot
  have hi11 : i ≠ 11 := by intro h; subst i; simp at hnot
  have hi13 : i ≠ 13 := by intro h; subst i; simp at hnot
  have hi14 : i ≠ 14 := by intro h; subst i; simp at hnot
  have hget : (s4CoverageSpecialExpectedBox digits mode)[i]! =
      (s4CoverageSpecialExpectedBox digits mode)[i] := by
    have hlt : i < (s4CoverageSpecialExpectedBox digits mode).size := by
      simpa [s4CoverageSpecialExpectedBox] using hi
    exact getElem!_pos _ i hlt
  rw [hget]
  simp [s4CoverageSpecialExpectedBox, hi2, hi5, hi8, hi11, hi13, hi14]

private theorem s4CoverageSpecialExpectedBox_inner
    (digits : Array Nat) (mode : String) (k : Nat)
    (hk : k < 6) (hk4 : k ≠ 4) :
    (s4CoverageSpecialExpectedBox digits mode)[
      (s4InnerPositions fifteenSpecialPattern)[k]!]! = fifteenBins[digits[k]!]! := by
  rw [s4CoverageSpecialPositions_exact]
  interval_cases k <;>
    simp_all [s4CoverageSpecialExpectedBox, s4CoverageSpecialOriginInterval,
      s4CoverageSpecialPositions_exact]

theorem s4CoverageSpecialLookup_box_spec
    {cases : Array Json} {assignment mode : String}
    {box : FifteenBox} {leaf : Json}
    (hlookup : s4CoverageSpecialLookup? cases assignment mode = some (box, leaf)) :
    fifteenSpecialBox? assignment mode 13 = some box := by
  unfold s4CoverageSpecialLookup? at hlookup
  cases hitem : cases.toList.find? (fun item =>
      fifteenFieldString? item "pattern" == some fifteenSpecialPattern &&
      fifteenFieldString? item "assignment" == some assignment &&
      fifteenFieldString? item "mode" == some mode &&
      fifteenFieldNat? item "vertex" == some 13) with
  | none => simp [hitem] at hlookup
  | some item =>
      cases hbox : fifteenSpecialBox? assignment mode 13 with
      | none => simp [hitem, hbox] at hlookup
      | some foundBox =>
          cases hleaf : fifteenJsonField? item "leaf" with
          | none => simp [hitem, hbox, hleaf] at hlookup
          | some foundLeaf =>
              have hpair : (foundBox, foundLeaf) = (box, leaf) := by
                simpa [hitem, hbox, hleaf] using hlookup
              have hfoundBox : foundBox = box := congrArg Prod.fst hpair
              exact congrArg (fun b : FifteenBox => some b) hfoundBox

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem s4CoverageSpecialTarget_mem
    (G : FifteenStage4CoverageGeometry)
    (hword : fifteenSpecialPattern = fifteenStage0ProfileWord G.profile) :
    s4CoverageTargetAssignment (s4InnerPositions fifteenSpecialPattern)
      (s4CoverageGeometryTarget G) ∈
        [#[6, 3, 6, 8, 0, 8], #[6, 4, 6, 8, 0, 8],
          #[6, 5, 6, 8, 0, 8]] := by
  obtain ⟨record, _hparse, hrecordPattern, hrecordValid⟩ :=
    s4CoverageSourceValid_record fifteenStage4Coverage003_replays
  have hallowedStream := s4CoverageRecordValid_stream hrecordValid
  obtain ⟨allowed, hallowed, hstream⟩ := hallowedStream
  have hallowed' : s4ResidualAssignments? fifteenSpecialPattern = some allowed := by
    rw [hrecordPattern] at hallowed
    exact hallowed
  have hstream' : s4CoverageStream
      (s4InnerPositions fifteenSpecialPattern).size
      (s4InnerPositions fifteenSpecialPattern) record.cycles allowed
      (s4Initial fifteenSpecialPattern) record.stream.toList = some [] := by
    simpa [fifteenSpecialPattern, hrecordPattern] using hstream
  have hstream'' : s4CoverageStream
      (s4InnerPositions (fifteenStage0ProfileWord G.profile)).size
      (s4InnerPositions (fifteenStage0ProfileWord G.profile)) record.cycles allowed
      (s4Initial (fifteenStage0ProfileWord G.profile)) record.stream.toList =
        some [] := by
    simpa [hword] using hstream'
  have hmem := fifteenStage4CoverageGeometricTargetAssignment_mem
    G.radii G.labels G.hlabels G.hgeometry G.profile G.hprofile
    G.hnonneg G.hclassification G.theta G.hsorted G.hthetaLo G.hthetaHi G.hsep
    allowed record.cycles record.stream.toList hstream''
  have hmem' : s4CoverageTargetAssignment
      (s4InnerPositions fifteenSpecialPattern) (s4CoverageGeometryTarget G) ∈
        allowed := by
    simpa [hword, s4CoverageGeometryTarget] using hmem
  have hassignments := s4CoverageSpecialResidualAssignments_exact
  rw [hallowed'] at hassignments
  have hallowedEq : allowed =
      [#[6, 3, 6, 8, 0, 8], #[6, 4, 6, 8, 0, 8],
        #[6, 5, 6, 8, 0, 8]] := by
    injection hassignments
  rw [hallowedEq] at hmem'
  exact hmem'

private theorem s4CoverageSpecialTarget_digit
    (G : FifteenStage4CoverageGeometry)
    (hword : fifteenSpecialPattern = fifteenStage0ProfileWord G.profile)
    (k : Nat) (hk : k < (s4InnerPositions fifteenSpecialPattern).size) :
    (s4CoverageTargetAssignment (s4InnerPositions fifteenSpecialPattern)
      (s4CoverageGeometryTarget G))[k]! =
        s4CoverageDigit (fifteenStage4RadialOwner
          (G.radii ⟨(s4InnerPositions fifteenSpecialPattern)[k]!, by
            have hk' : k < 6 := by
              rw [s4CoverageSpecialPositions_exact] at hk
              simpa using hk
            rw [s4CoverageSpecialPositions_exact]
            interval_cases k <;> norm_num⟩)) := by
  let inner := s4InnerPositions fifteenSpecialPattern
  have hpositions : inner = #[2, 5, 8, 11, 13, 14] :=
    s4CoverageSpecialPositions_exact
  have hk' : k < 6 := by
    rw [s4CoverageSpecialPositions_exact] at hk
    simpa using hk
  have hpositionBound : inner[k]! < 15 := by
    rw [hpositions]
    have : k < 6 := hk'
    interval_cases k <;> norm_num
  let p := inner[k]!
  let j : Fin 15 := ⟨p, hpositionBound⟩
  have hpositionMem : p ∈ inner.toList := by
    dsimp [p]
    rw [getElem!_pos inner k hk]
    exact Array.getElem_mem_toList hk
  have hprofileMem : p ∈
      (s3InnerPositions (fifteenStage0ProfileWord G.profile)).toList := by
    simpa [inner, s4InnerPositions_eq_s3, hword] using hpositionMem
  have hprofileTrue : G.profile j = true :=
    (fifteenStage3ProfileWord_inner_iff G.profile j).mp hprofileMem
  have hradiusInner : G.radii j < fifteenCandidateInnerThreshold :=
    (G.hprofile j).mp hprofileTrue
  have htargetLabel : (s4CoverageGeometryTarget G)[p]! =
      fifteenStage4RadialLabel (G.radii j) := by
    change (fifteenStage4OwnerLabelArray
        (fun l => fifteenStage4RadialLabel (G.radii l)))[p]! = _
    exact fifteenStage4OwnerLabelArray_get _ p hpositionBound
  have hassignment :
      (s4CoverageTargetAssignment (s4InnerPositions fifteenSpecialPattern)
        (s4CoverageGeometryTarget G))[k]! =
      s4CoverageDigit (fifteenStage4RadialOwner (G.radii j)) := by
    unfold s4CoverageTargetAssignment
    have hkMap : k < ((s4InnerPositions fifteenSpecialPattern).map
        (fun q => s4CoverageDigit (s4CoverageGeometryTarget G)[q]!)).size := by
      simpa [inner] using hk
    rw [getElem!_pos _ k hkMap]
    rw [Array.getElem_map _ hkMap]
    rw [← getElem!_pos inner k hk]
    change s4CoverageDigit (s4CoverageGeometryTarget G)[p]! = _
    rw [htargetLabel]
    simp [fifteenStage4RadialLabel, hradiusInner]
  simpa [p, j] using hassignment

private theorem s4CoverageSpecialTarget_position_inner
    (G : FifteenStage4CoverageGeometry)
    (hword : fifteenSpecialPattern = fifteenStage0ProfileWord G.profile)
    (k : Nat) (hk : k < (s4InnerPositions fifteenSpecialPattern).size) :
    G.radii ⟨(s4InnerPositions fifteenSpecialPattern)[k]!, by
      have hk' : k < 6 := by
        rw [s4CoverageSpecialPositions_exact] at hk
        simpa using hk
      rw [s4CoverageSpecialPositions_exact]
      interval_cases k <;> norm_num⟩ <
        fifteenCandidateInnerThreshold := by
  let inner := s4InnerPositions fifteenSpecialPattern
  have hpositions : inner = #[2, 5, 8, 11, 13, 14] :=
    s4CoverageSpecialPositions_exact
  have hk' : k < 6 := by
    rw [s4CoverageSpecialPositions_exact] at hk
    simpa using hk
  have hpositionBound : inner[k]! < 15 := by
    rw [hpositions]
    interval_cases k <;> norm_num
  let p := inner[k]!
  let j : Fin 15 := ⟨p, hpositionBound⟩
  have hpositionMem : p ∈ inner.toList := by
    dsimp [p]
    rw [getElem!_pos inner k hk]
    exact Array.getElem_mem_toList hk
  have hprofileMem : p ∈
      (s3InnerPositions (fifteenStage0ProfileWord G.profile)).toList := by
    simpa [inner, s4InnerPositions_eq_s3, hword] using hpositionMem
  have hprofileTrue : G.profile j = true :=
    (fifteenStage3ProfileWord_inner_iff G.profile j).mp hprofileMem
  have hradiusInner : G.radii j < fifteenCandidateInnerThreshold :=
    (G.hprofile j).mp hprofileTrue
  simpa [p, j] using hradiusInner

private theorem s4CoverageSpecialRadialDigit_closedBin {r : ℝ}
    (hnonneg : 0 ≤ r) (hinner : r < fifteenCandidateInnerThreshold) :
    ((fifteenBins[s4CoverageDigit (fifteenStage4RadialOwner r)]!.1 : ℝ) ≤ r) ∧
      r ≤ (fifteenBins[s4CoverageDigit (fifteenStage4RadialOwner r)]!.2 : ℝ) := by
  by_cases hz : r = 0
  · subst r
    norm_num [s4CoverageDigit, fifteenStage4RadialOwner, fifteenBins,
      fifteenRational, Rat.normalize_eq_mkRat, Rat.cast_mkRat_of_ne_zero]
  · have hupper : r < (2385432 : ℝ) / 1000000 :=
      lt_trans hinner fifteenCandidateInnerThreshold_lt_2385432_1e6
    have howner := fifteenExactRadialOwner_spec hnonneg hupper
    have hownerNotOrigin : fifteenExactRadialOwner r ≠ 13 := by
      intro h
      have hzero := howner
      rw [h] at hzero
      simp [fifteenExactRadialOwnerSpec] at hzero
      exact hz hzero
    have hdigit :
        s4CoverageDigit (fifteenStage4RadialOwner r) =
          fifteenExactRadialOwner r := by
      have howners : fifteenStage4RadialOwner r = fifteenExactRadialOwner r := rfl
      rw [howners]
      simp [s4CoverageDigit, hownerNotOrigin]
    have hclosed := fifteenExactRadialOwnerSpec_certificate_interval howner
    rw [if_neg hownerNotOrigin] at hclosed
    simpa only [hdigit] using hclosed

private theorem s4CoverageSpecialExpectedBox_contains
    (G : FifteenStage4CoverageGeometry) (mode : String)
    (digits : Array Nat)
    (hword : fifteenSpecialPattern = fifteenStage0ProfileWord G.profile)
    (hassignment : s4CoverageTargetAssignment
      (s4InnerPositions fifteenSpecialPattern) (s4CoverageGeometryTarget G) = digits)
    (horigin : (s4CoverageSpecialOriginInterval mode).1 ≤
        G.radii ⟨13, by norm_num⟩ ∧
      G.radii ⟨13, by norm_num⟩ ≤ (s4CoverageSpecialOriginInterval mode).2) :
    ∀ i : Fin 15,
      ((s4CoverageSpecialExpectedBox digits mode)[i.1]!.1 : ℝ) ≤ G.radii i ∧
        G.radii i ≤ ((s4CoverageSpecialExpectedBox digits mode)[i.1]!.2 : ℝ) := by
  have hpositions : s4InnerPositions fifteenSpecialPattern =
      #[2, 5, 8, 11, 13, 14] := s4CoverageSpecialPositions_exact
  intro i
  by_cases hmem : i.1 ∈
      (s4InnerPositions fifteenSpecialPattern).toList
  · obtain ⟨k, hk, hget⟩ := List.mem_iff_getElem.mp hmem
    have hposition :
        (s4InnerPositions fifteenSpecialPattern)[k]! = i.1 := by
      calc
        (s4InnerPositions fifteenSpecialPattern)[k]! =
            (s4InnerPositions fifteenSpecialPattern).toList[k]! := by
              rw [Array.getElem!_toList]
        _ = (s4InnerPositions fifteenSpecialPattern).toList[k] :=
              getElem!_pos _ k hk
        _ = i.1 := hget
    have hk6 : k < 6 := by
      have hkArray : k < (s4InnerPositions fifteenSpecialPattern).size := by
        simpa only [Array.length_toList] using hk
      rw [s4CoverageSpecialPositions_exact] at hkArray
      exact hkArray
    have hdigit : digits[k]! =
        s4CoverageDigit (fifteenStage4RadialOwner
          (G.radii ⟨(s4InnerPositions fifteenSpecialPattern)[k]!, by
            rw [hpositions]
            interval_cases k <;> norm_num⟩)) := by
      have htarget := s4CoverageSpecialTarget_digit G hword k (by simpa using hk)
      have hgetDigit := congrArg (fun a : Array Nat => a[k]!) hassignment
      simpa [htarget] using hgetDigit.symm
    by_cases hk4 : k = 4
    · subst k
      rw [hpositions] at hposition
      have hi : i.1 = 13 := by simpa using hposition.symm
      have hrad : G.radii i = G.radii ⟨13, by norm_num⟩ := by
        congr 1
        apply Fin.ext
        exact hi
      rw [hrad]
      have hbox :
          (s4CoverageSpecialExpectedBox digits mode)[13]! =
            s4CoverageSpecialOriginInterval mode := by
        simp [s4CoverageSpecialExpectedBox]
      have hiFin : i = ⟨13, by norm_num⟩ := Fin.ext hi
      rw [hiFin]
      rw [hbox]
      exact horigin
    · have hradiusInner := s4CoverageSpecialTarget_position_inner G hword k
        (by simpa using hk)
      have hnonneg := G.hnonneg
        (⟨(s4InnerPositions fifteenSpecialPattern)[k]!, by
          rw [hpositions]
          interval_cases k <;> norm_num⟩ : Fin 15)
      have hbin := s4CoverageSpecialRadialDigit_closedBin hnonneg hradiusInner
      have hkArray : k < (s4InnerPositions fifteenSpecialPattern).size := by
        simpa only [Array.length_toList] using hk
      have hboxBin := s4CoverageSpecialExpectedBox_inner digits mode k
        hkArray hk4
      have hboxLower :
          (s4CoverageSpecialExpectedBox digits mode)[i.1]!.1 =
            (fifteenBins[digits[k]!]!).1 := by
        rw [← hposition, hboxBin]
      have hboxUpper :
          (s4CoverageSpecialExpectedBox digits mode)[i.1]!.2 =
            (fifteenBins[digits[k]!]!).2 := by
        rw [← hposition, hboxBin]
      have hbin' := hbin
      rw [← hdigit] at hbin'
      have hji : (⟨(s4InnerPositions fifteenSpecialPattern)[k]!, by
          rw [hpositions]
          interval_cases k <;> norm_num⟩ : Fin 15) = i := Fin.ext hposition
      rw [hji] at hbin'
      rw [hboxLower, hboxUpper]
      simpa using hbin'
  · have hnotProfile : i.1 ∉
        (s3InnerPositions (fifteenStage0ProfileWord G.profile)).toList := by
      simpa [s4InnerPositions_eq_s3, hword] using hmem
    have hwall : G.radii i = fifteenCandidateOuterRadius := by
      rcases G.hclassification i with hwall | hinner
      · exact hwall
      · have htrue := (G.hprofile i).2 hinner
        exact (hnotProfile
          ((fifteenStage3ProfileWord_inner_iff G.profile i).mpr htrue)).elim
    have hboxWall := s4CoverageSpecialExpectedBox_outside digits mode i.1
      i.isLt
      (by simpa [hpositions] using hmem)
    rw [hboxWall, hwall]
    exact fifteenCandidateOuterRadius_certificate_interval

/-- Once the special leaf's radius box contains a feasible profile, its
checked terminal is contradictory.  The positive-high branch uses the
strictly-positive cycle soundness theorem; the other two branches use the
pairwise radial-sum bound and preserve their origin flags. -/
theorem s4CoverageSpecialLeafExcludes
    (G : FifteenStage4CoverageGeometry) (mode : String)
    (box : FifteenBox) (leaf : Json)
    (hmode : mode ∈ ["POSITIVE_LOW", "POSITIVE_HIGH", "EXACT_ZERO"])
    (htag : fifteenJsonAt? leaf 0 >>= fifteenJsonString? =
      some (if mode == "POSITIVE_HIGH" then "CYCLE" else "SUM"))
    (hvalid : fifteenTerminalValid box (fifteenInnerPositions fifteenSpecialPattern)
      leaf false (if mode == "POSITIVE_LOW" then [13] else [])
        (if mode == "EXACT_ZERO" then [13] else []) = true)
    (hcontains : ∀ i : Fin 15,
      ((box[i.1]!.1 : ℝ) ≤ G.radii i) ∧
        G.radii i ≤ (box[i.1]!.2 : ℝ))
    (hboxGood : mode = "POSITIVE_HIGH" → fifteenBoxGood box) : False := by
  by_cases hhigh : mode = "POSITIVE_HIGH"
  · subst mode
    exact fifteenGeometricTerminalCycleExcludes G.radii G.theta box
      (fifteenInnerPositions fifteenSpecialPattern) leaf false
      G.hsorted G.hthetaLo G.hthetaHi G.hsep (hboxGood rfl)
      hcontains (by simpa using htag) (by simpa using hvalid)
  · have hlow : mode = "POSITIVE_LOW" ∨ mode = "EXACT_ZERO" := by
      simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil,
        or_false] at hmode
      rcases hmode with h | h | h
      · exact Or.inl h
      · exact (hhigh h).elim
      · exact Or.inr h
    rcases hlow with hlow | hexact
    · subst mode
      exact fifteenGeometricTerminalSumExcludesWithFlags G.radii box
        (fifteenInnerPositions fifteenSpecialPattern) leaf false [13] []
        G.hgeometry.pairSum (by simpa using htag) (by simpa using hvalid)
        (fun i => (hcontains i).2)
    · subst mode
      exact fifteenGeometricTerminalSumExcludesWithFlags G.radii box
        (fifteenInnerPositions fifteenSpecialPattern) leaf false [] [13]
        G.hgeometry.pairSum (by simpa using htag) (by simpa using hvalid)
        (fun i => (hcontains i).2)

private theorem s4CoverageSpecialOriginMode
    (G : FifteenStage4CoverageGeometry)
    (hword : fifteenSpecialPattern = fifteenStage0ProfileWord G.profile) :
    ∃ mode, mode ∈ s4CoverageSpecialModes ∧
      (s4CoverageSpecialOriginInterval mode).1 ≤ G.radii ⟨13, by norm_num⟩ ∧
      G.radii ⟨13, by norm_num⟩ ≤ (s4CoverageSpecialOriginInterval mode).2 := by
  have htarget := s4CoverageSpecialTarget_mem G hword
  have htargetZero :
      (s4CoverageTargetAssignment (s4InnerPositions fifteenSpecialPattern)
        (s4CoverageGeometryTarget G))[4]! = 0 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at htarget
    rcases htarget with h | h | h
    · simpa [h]
    · simpa [h]
    · simpa [h]
  let i : Fin 15 := ⟨13, by norm_num⟩
  have hposition : 13 ∈ (s4InnerPositions fifteenSpecialPattern).toList := by
    rw [s4CoverageSpecialPositions_exact]
    decide
  have hprofileMem : 13 ∈
      (s3InnerPositions (fifteenStage0ProfileWord G.profile)).toList := by
    simpa [s4InnerPositions_eq_s3, hword] using hposition
  have hprofileTrue : G.profile i = true :=
    (fifteenStage3ProfileWord_inner_iff G.profile i).mp hprofileMem
  have hinner : G.radii i < fifteenCandidateInnerThreshold :=
    (G.hprofile i).mp hprofileTrue
  have htargetDigit := s4CoverageSpecialTarget_digit G hword 4
    (by norm_num [s4CoverageSpecialPositions_exact])
  have hdigit :
      s4CoverageDigit (fifteenStage4RadialOwner (G.radii i)) = 0 := by
    calc
      _ = (s4CoverageTargetAssignment
          (s4InnerPositions fifteenSpecialPattern) (s4CoverageGeometryTarget G))[4]! :=
        htargetDigit.symm
      _ = 0 := htargetZero
  have howner := fifteenStage4RadialOwner_spec (G.radii i) (G.hnonneg i) hinner
  by_cases hzero : fifteenStage4RadialOwner (G.radii i) = 13
  · have hrzero : G.radii i = 0 := by
      simpa [fifteenStage4OwnerSpec, hzero] using howner
    have hrzero13 : G.radii ⟨13, by norm_num⟩ = 0 := by
      simpa [i] using hrzero
    refine ⟨"EXACT_ZERO", by simp [s4CoverageSpecialModes], ?_⟩
    have hbounds : (0 : ℝ) ≤ G.radii ⟨13, by norm_num⟩ ∧
        G.radii ⟨13, by norm_num⟩ ≤ 0 := by
      rw [hrzero13]
      exact ⟨le_rfl, le_rfl⟩
    simpa [s4CoverageSpecialOriginInterval, fifteenRational,
      Rat.normalize_eq_mkRat, Rat.cast_mkRat_of_ne_zero] using hbounds
  · have hownerZero : fifteenStage4RadialOwner (G.radii i) = 0 := by
      simpa [s4CoverageDigit, hzero] using hdigit
    have hrange : 0 < G.radii i ∧ G.radii i < 1 / 2 := by
      simpa [fifteenStage4OwnerSpec, hownerZero] using howner
    have hrange13 : 0 < G.radii ⟨13, by norm_num⟩ ∧
        G.radii ⟨13, by norm_num⟩ < 1 / 2 := by
      simpa [i] using hrange
    by_cases hlow : G.radii i ≤ 1 / 4
    have hlow13 : G.radii ⟨13, by norm_num⟩ ≤ 1 / 4 := by
      simpa [i] using hlow
    · refine ⟨"POSITIVE_LOW", by simp [s4CoverageSpecialModes], ?_⟩
      have hbounds : (0 : ℝ) ≤ G.radii ⟨13, by norm_num⟩ ∧
          G.radii ⟨13, by norm_num⟩ ≤ (1 : ℝ) / 4 :=
        ⟨le_of_lt hrange13.1, hlow13⟩
      simpa [s4CoverageSpecialOriginInterval, fifteenRational,
        Rat.normalize_eq_mkRat, Rat.cast_mkRat_of_ne_zero] using hbounds
    · have hhigh : 1 / 4 < G.radii i := lt_of_not_ge hlow
      have hhigh13 : 1 / 4 < G.radii ⟨13, by norm_num⟩ := by
        simpa [i] using hhigh
      refine ⟨"POSITIVE_HIGH", by simp [s4CoverageSpecialModes], ?_⟩
      have hbounds : (1 : ℝ) / 4 ≤ G.radii ⟨13, by norm_num⟩ ∧
          G.radii ⟨13, by norm_num⟩ ≤ (1 : ℝ) / 2 :=
        ⟨le_of_lt hhigh13, le_of_lt hrange13.2⟩
      simpa [s4CoverageSpecialOriginInterval, fifteenRational,
        Rat.normalize_eq_mkRat, Rat.cast_mkRat_of_ne_zero] using hbounds

private theorem s4CoverageSpecialAssignmentExcludes
    (G : FifteenStage4CoverageGeometry)
    (hword : fifteenSpecialPattern = fifteenStage0ProfileWord G.profile)
    (assignment : String) (digits : Array Nat)
    (hrow : (assignment, digits) ∈ s4CoverageSpecialRows)
    (hassignment : s4CoverageTargetAssignment
      (s4InnerPositions fifteenSpecialPattern) (s4CoverageGeometryTarget G) = digits)
    (mode : String) (hmode : mode ∈ s4CoverageSpecialModes)
    (horigin : (s4CoverageSpecialOriginInterval mode).1 ≤
        G.radii ⟨13, by norm_num⟩ ∧
      G.radii ⟨13, by norm_num⟩ ≤ (s4CoverageSpecialOriginInterval mode).2) : False := by
  have hassignmentName : assignment ∈ ["636808", "646808", "656808"] := by
    have hmem := hrow
    simp only [s4CoverageSpecialRows, List.mem_cons, List.not_mem_nil,
      or_false] at hmem
    rcases hmem with h0 | h1 | h2
    · cases h0; simp
    · cases h1; simp
    · cases h2; simp
  obtain ⟨cases, box, leaf, hcases, hlookup, htag, hvalid⟩ :=
    s4CoverageSpecialLeafData hassignmentName
      (by simpa [s4CoverageSpecialModes] using hmode)
  have hlookupBox := s4CoverageSpecialLookup_box_spec hlookup
  have hmatchedBox := s4CoverageSpecialBox_matches hrow hmode
  have hboxEq : box = s4CoverageSpecialExpectedBox digits mode := by
    have hsome : some box = some (s4CoverageSpecialExpectedBox digits mode) := by
      calc
        some box = fifteenSpecialBox? assignment mode 13 := hlookupBox.symm
        _ = some (s4CoverageSpecialExpectedBox digits mode) := hmatchedBox
    exact Option.some.inj hsome
  subst box
  have hcontains := s4CoverageSpecialExpectedBox_contains G mode digits
    hword hassignment horigin
  have hgood : mode = "POSITIVE_HIGH" →
      fifteenBoxGood (s4CoverageSpecialExpectedBox digits mode) := by
    intro hhigh
    subst mode
    exact s4CoverageSpecialHighBox_good hrow
  exact s4CoverageSpecialLeafExcludes G mode
    (s4CoverageSpecialExpectedBox digits mode) leaf hmode htag hvalid
    hcontains hgood

/-- The exceptional six-inner profile has no feasible Stage 4 geometry: its
checked origin-special leaf is matched to the target assignment and contains
all fifteen radii. -/
theorem s4CoverageSpecialGeometry_impossible
    (G : FifteenStage4CoverageGeometry)
    (hword : fifteenSpecialPattern = fifteenStage0ProfileWord G.profile) : False := by
  obtain ⟨mode, hmode, horigin⟩ := s4CoverageSpecialOriginMode G hword
  have htarget := s4CoverageSpecialTarget_mem G hword
  simp only [List.mem_cons, List.not_mem_nil, or_false] at htarget
  rcases htarget with h | h | h
  · exact s4CoverageSpecialAssignmentExcludes G hword "636808"
      #[6, 3, 6, 8, 0, 8] (by simp [s4CoverageSpecialRows]) h mode hmode horigin
  · exact s4CoverageSpecialAssignmentExcludes G hword "646808"
      #[6, 4, 6, 8, 0, 8] (by simp [s4CoverageSpecialRows]) h mode hmode horigin
  · exact s4CoverageSpecialAssignmentExcludes G hword "656808"
      #[6, 5, 6, 8, 0, 8] (by simp [s4CoverageSpecialRows]) h mode hmode horigin


end CirclePacking
