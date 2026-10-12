import CirclePacking.FifteenStage4Coverage000
import CirclePacking.FifteenStage4Coverage001
import CirclePacking.FifteenStage4Coverage002
import CirclePacking.FifteenStage4CoverageSoundness
import CirclePacking.FifteenStage4CoverageRoots
import CirclePacking.FifteenStage4FiniteGeometry
import CirclePacking.FifteenGeometricCertificateSoundness
import CirclePacking.FifteenCertificateWorklistSemantic

/-! The Stage 4 coverage trees are connected to geometric data and to the
normal roots of the exact radial-subdivision certificate. The exceptional
six-inner profile remains a separate origin-special case. -/

namespace CirclePacking

structure FifteenStage4CoverageGeometry where
  radii : Fin 15 → ℝ
  labels : Fin 15 → Nat
  hlabels : ∀ i, labels i = fifteenStage3RadialLabel (radii i)
  hgeometry : FifteenStage3GeometricConditions radii labels
  profile : Fin 15 → Bool
  hprofile : ∀ i, profile i = true ↔
    radii i < fifteenCandidateInnerThreshold
  hnonneg : ∀ i, 0 ≤ radii i
  hclassification : ∀ i, radii i = fifteenCandidateOuterRadius ∨
    radii i < fifteenCandidateInnerThreshold
  theta : Fin 15 → ℝ
  hsorted : ∀ i j : Fin 15, i.1 < j.1 → theta i ≤ theta j
  hthetaLo : ∀ i, 0 ≤ theta i
  hthetaHi : ∀ i, theta i ≤ 2 * Real.pi
  hsep : ∀ i j : Fin 15, i ≠ j →
    4 ≤ pointNorm
      ((polarPoint (radii i) (theta i)).1 - (polarPoint (radii j) (theta j)).1,
       (polarPoint (radii i) (theta i)).2 - (polarPoint (radii j) (theta j)).2) ^ 2

noncomputable def s4CoverageGeometryTarget
    (G : FifteenStage4CoverageGeometry) : Array Nat :=
  fifteenStage4OwnerLabelArray (fun i => fifteenStage4RadialLabel (G.radii i))

theorem s4CoverageNormalSource_replays (pattern : String)
    (hpattern : pattern ∈ s4CoverageNormalPatterns) :
    ∃ source, s4CoverageSourceValid source pattern = true := by
  simp [s4CoverageNormalPatterns] at hpattern
  rcases hpattern with h0 | h1 | h2
  · subst pattern
    exact ⟨fifteenStage4Coverage000Source, by
      change fifteenStage4Coverage000Valid = true
      exact fifteenStage4Coverage000_replays⟩
  · subst pattern
    exact ⟨fifteenStage4Coverage001Source, by
      change fifteenStage4Coverage001Valid = true
      exact fifteenStage4Coverage001_replays⟩
  · subst pattern
    exact ⟨fifteenStage4Coverage002Source, by
      change fifteenStage4Coverage002Valid = true
      exact fifteenStage4Coverage002_replays⟩

/- A geometrically feasible normal Stage 4 profile follows the checked
coverage path to an accepted radial assignment, and that assignment is one
of the exact certificate's validated roots. -/
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem s4CoverageGeometricNormalTarget_root
    (pattern : String) (G : FifteenStage4CoverageGeometry)
    (hword : pattern = fifteenStage0ProfileWord G.profile)
    (hpattern : pattern ∈ s4CoverageNormalPatterns) :
    ∃ roots, s4CoverageRootBoxes? = some roots ∧
      ∃ box, (pattern, s4CoverageTargetAssignment (s4InnerPositions pattern)
        (s4CoverageGeometryTarget G), box) ∈ roots ∧
        ∀ k, k < (s4InnerPositions pattern).size →
          box[(s4InnerPositions pattern)[k]!]! =
            fifteenBins[(s4CoverageTargetAssignment
              (s4InnerPositions pattern) (s4CoverageGeometryTarget G))[k]!]! := by
  obtain ⟨source, hsource⟩ := s4CoverageNormalSource_replays pattern hpattern
  obtain ⟨record, _hparse, hrecordPattern, hrecordValid⟩ :=
    s4CoverageSourceValid_record hsource
  obtain ⟨allowed, hallowed, hstream⟩ :=
    s4CoverageRecordValid_stream hrecordValid
  have hallowed' : s4ResidualAssignments? pattern = some allowed := by
    rw [hrecordPattern] at hallowed
    exact hallowed
  have hstream' : s4CoverageStream (s4InnerPositions pattern).size
      (s4InnerPositions pattern) record.cycles allowed
      (s4Initial pattern) record.stream.toList = some [] := by
    rw [hrecordPattern] at hstream
    exact hstream
  have hstream'' : s4CoverageStream
      (s4InnerPositions (fifteenStage0ProfileWord G.profile)).size
      (s4InnerPositions (fifteenStage0ProfileWord G.profile)) record.cycles allowed
      (s4Initial (fifteenStage0ProfileWord G.profile)) record.stream.toList =
        some [] := by
    simpa [hword] using hstream'
  have hmemWord := fifteenStage4CoverageGeometricTargetAssignment_mem
    G.radii G.labels G.hlabels G.hgeometry G.profile G.hprofile
    G.hnonneg G.hclassification G.theta G.hsorted G.hthetaLo G.hthetaHi G.hsep
    allowed record.cycles record.stream.toList hstream''
  have hmem : s4CoverageTargetAssignment (s4InnerPositions pattern)
      (s4CoverageGeometryTarget G) ∈ allowed := by
    simpa [hword, s4CoverageGeometryTarget] using hmemWord
  obtain ⟨roots, hroots, box, hroot⟩ :=
    s4CoverageResidualAssignment_has_root_box hpattern
      ⟨allowed, hallowed', hmem⟩
  exact ⟨roots, hroots, box, hroot,
    s4CoverageRootBoxDataCorrect_of_mem hroots hroot⟩

private theorem s4CoverageStage4Owner_eq_exact (r : ℝ) :
    fifteenStage4RadialOwner r = fifteenExactRadialOwner r := by
  rfl

/-- The coverage-tree digit selected by a real inner radius indexes a closed
certificate interval containing that radius.  The exact origin is sent to
bin zero by the coverage format and is handled separately. -/
private theorem s4CoverageRadialDigit_closedBin {r : ℝ}
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
      rw [s4CoverageStage4Owner_eq_exact]
      simp [s4CoverageDigit, hownerNotOrigin]
    have hclosed := fifteenExactRadialOwnerSpec_certificate_interval howner
    rw [if_neg hownerNotOrigin] at hclosed
    simpa only [hdigit] using hclosed

/- Along a geometrically feasible normal Stage 4 owner word, every entry of
the matched exact-certificate root box contains the corresponding real
radius. -/
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem s4CoverageGeometricNormalTarget_root_contains
    (pattern : String) (G : FifteenStage4CoverageGeometry)
    (hword : pattern = fifteenStage0ProfileWord G.profile)
    (hpattern : pattern ∈ s4CoverageNormalPatterns) :
    ∃ roots, s4CoverageRootBoxes? = some roots ∧
      ∃ box, (pattern, s4CoverageTargetAssignment (s4InnerPositions pattern)
        (s4CoverageGeometryTarget G), box) ∈ roots ∧
        (∀ k, (hk : k < (s4InnerPositions pattern).size) →
          box[(s4InnerPositions pattern)[k]!]! =
            fifteenBins[(s4CoverageTargetAssignment
              (s4InnerPositions pattern) (s4CoverageGeometryTarget G))[k]!]!) ∧
        (∀ i : Fin 15,
          ((box[i.1]!.1 : ℝ) ≤ G.radii i) ∧
            G.radii i ≤ (box[i.1]!.2 : ℝ)) := by
  obtain ⟨roots, hroots, box, hroot, hboxBin⟩ :=
    s4CoverageGeometricNormalTarget_root pattern G hword hpattern
  refine ⟨roots, hroots, box, hroot, hboxBin, ?_⟩
  intro i
  let inner := s4InnerPositions pattern
  by_cases hmem : i.1 ∈ inner.toList
  · obtain ⟨k, hk, hget⟩ := List.mem_iff_getElem.mp hmem
    have hposition : inner[k]! = i.1 := by
      calc
        inner[k]! = inner.toList[k]! := by rw [Array.getElem!_toList]
        _ = inner.toList[k] := getElem!_pos inner.toList k hk
        _ = i.1 := hget
    have hindexBound : inner[k]! < 15 := by
      rw [hposition]
      exact i.isLt
    have hboxBin' := hboxBin k (by simpa [inner] using hk)
    have hboxPair := hboxBin'
    have hboxLower : box[inner[k]!]!.1 = fifteenBins[
        (s4CoverageTargetAssignment (s4InnerPositions pattern)
          (s4CoverageGeometryTarget G))[k]!]!.1 := by
      exact congrArg Prod.fst hboxPair
    have hboxUpper : box[inner[k]!]!.2 = fifteenBins[
        (s4CoverageTargetAssignment (s4InnerPositions pattern)
          (s4CoverageGeometryTarget G))[k]!]!.2 := by
      exact congrArg Prod.snd hboxPair
    let p := inner[k]!
    let j : Fin 15 := ⟨p, hindexBound⟩
    have hmemOrdinary : inner[k] ∈ inner.toList := Array.getElem_mem_toList hk
    have hmemPosition : p ∈ inner.toList := by
      dsimp [p]
      rw [getElem!_pos inner k hk]
      exact hmemOrdinary
    have hprofileMem : p ∈
        (s3InnerPositions (fifteenStage0ProfileWord G.profile)).toList := by
      simpa [inner, s4InnerPositions_eq_s3, hword] using hmemPosition
    have hprofileTrue : G.profile j = true :=
      (fifteenStage3ProfileWord_inner_iff G.profile j).mp hprofileMem
    have hradiusInner : G.radii j < fifteenCandidateInnerThreshold :=
      (G.hprofile j).mp hprofileTrue
    have htargetLabel : (s4CoverageGeometryTarget G)[p]! =
        fifteenStage4RadialLabel (G.radii j) := by
      change (fifteenStage4OwnerLabelArray
          (fun l => fifteenStage4RadialLabel (G.radii l)))[p]! = _
      exact fifteenStage4OwnerLabelArray_get _ p hindexBound
    have hassignment :
        (s4CoverageTargetAssignment (s4InnerPositions pattern)
          (s4CoverageGeometryTarget G))[k]! =
          s4CoverageDigit (fifteenStage4RadialOwner (G.radii j)) := by
      unfold s4CoverageTargetAssignment
      have hkMap : k < ((s4InnerPositions pattern).map (fun q =>
          s4CoverageDigit (s4CoverageGeometryTarget G)[q]!)).size := by
        simpa [inner] using hk
      rw [getElem!_pos _ k hkMap]
      rw [Array.getElem_map _ hkMap]
      rw [← getElem!_pos inner k hk]
      change s4CoverageDigit (s4CoverageGeometryTarget G)[p]! = _
      rw [htargetLabel]
      simp [fifteenStage4RadialLabel, hradiusInner]
    have hbin := s4CoverageRadialDigit_closedBin (G.hnonneg j) hradiusInner
    rw [hassignment] at hboxLower hboxUpper
    have hbound :
        ((box[p]!.1 : ℝ) ≤ G.radii j) ∧
          G.radii j ≤ (box[p]!.2 : ℝ) := by
      constructor
      · rw [hboxLower]
        exact hbin.1
      · rw [hboxUpper]
        exact hbin.2
    simpa [p, j, hposition] using hbound
  · have hboxWall :=
      s4CoverageRootOutsideBoxDataCorrect_of_mem hroots hroot i.1 i.isLt
        (by simpa [inner] using hmem)
    have hnotWord : i.1 ∉
        (s3InnerPositions (fifteenStage0ProfileWord G.profile)).toList := by
      simpa [inner, s4InnerPositions_eq_s3, hword] using hmem
    have hradiusWall : G.radii i = fifteenCandidateOuterRadius := by
      rcases G.hclassification i with hwall | hinner
      · exact hwall
      · have hprofileTrue := (G.hprofile i).2 hinner
        exact (hnotWord
          ((fifteenStage3ProfileWord_inner_iff G.profile i).mpr hprofileTrue)).elim
    rw [hboxWall, hradiusWall]
    exact fifteenCandidateOuterRadius_certificate_interval

/-- Once a normal Stage 4 geometry is placed in an exact-certificate root,
the verified subdivision cannot terminate at a `CYCLE` or `SUM` leaf. It
therefore forces that root's path into the unique local box. -/
theorem s4CoverageNormalGeometry_task_forces_local
    (G : FifteenStage4CoverageGeometry)
    (tasks : List FifteenTask) (counts result : FifteenTreeCounts)
    (hcheck : fifteenCheckTasks 60000 tasks counts = some result)
    (hboxesGood : fifteenTaskListBoxesGood tasks)
    (hcontains : ∃ task, task ∈ tasks ∧
      fifteenTaskHasProfile task G.radii) :
    ∃ box inner, fifteenRealBoxContains box G.radii ∧
      inner = fifteenInnerPositions "001001001001001" ∧
      ∀ p ∈ inner,
        fifteenLocalLo ≤ box[p]!.1 ∧ box[p]!.2 ≤ fifteenLocalHi := by
  apply fifteenCheckTasks_profile_reaches_local_bounds 60000 tasks counts result
    G.radii
  · intro box inner node hboxGood htag hvalid hprofile
    apply fifteenGeometricTerminalCycleExcludes G.radii G.theta box inner node
      false G.hsorted G.hthetaLo G.hthetaHi G.hsep hboxGood
    · intro i
      exact hprofile i
    · exact htag
    · exact hvalid
  · intro box inner node htag hvalid hprofile
    apply fifteenGeometricTerminalSumExcludes G.radii box inner node false
      G.hgeometry.pairSum htag hvalid
    intro i
    exact (hprofile i).2
  · exact hcheck
  · exact hboxesGood
  · exact hcontains

/-! The root boxes above and the exact-certificate work list are both parsed
from the same JSON document.  The following finite links make that relation
explicit and expose the accepted root tasks to the semantic work-list theorem. -/

def s4CoverageExactTasks? : Option (List FifteenTask) := do
  let document ← (Lean.Json.parse fifteenCertificateSource).toOption
  let rootsJson ← fifteenJsonField? document "roots"
  let roots ← fifteenJsonArray? rootsJson
  fifteenRootTasksAux roots.toList

def s4CoverageExactWorklistReplay : Bool := Id.run do
  let some tasks := s4CoverageExactTasks? | return false
  let some counts := fifteenCheckTasks 60000 tasks {} | return false
  return counts.nodes == 58860 && counts.cycles == 30032 &&
    counts.sums == 0 && counts.localLeaves == 31

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem s4CoverageExactWorklist_replays :
    s4CoverageExactWorklistReplay = true := by
  native_decide

def s4CoverageRootTaskMatches
    (roots : List (String × Array Nat × FifteenBox))
    (tasks : List FifteenTask) : Bool :=
  roots.all (fun row => tasks.any (fun task =>
    decide (task.1 = row.2.2 ∧
      task.2.1 = fifteenInnerPositions row.1)))

def s4CoverageRootTaskLinksReplay : Bool :=
  match s4CoverageRootBoxes?, s4CoverageExactTasks? with
  | some roots, some tasks => s4CoverageRootTaskMatches roots tasks
  | _, _ => false

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem s4CoverageRootTaskLinks_replay :
    s4CoverageRootTaskLinksReplay = true := by
  native_decide

theorem s4CoverageRootTask_mem
    {roots : List (String × Array Nat × FifteenBox)}
    {tasks : List FifteenTask}
    {row : String × Array Nat × FifteenBox}
    (hroots : s4CoverageRootBoxes? = some roots)
    (htasks : s4CoverageExactTasks? = some tasks)
    (hrow : row ∈ roots) :
    ∃ task, task ∈ tasks ∧ task.1 = row.2.2 ∧
      task.2.1 = fifteenInnerPositions row.1 := by
  have hlinks : s4CoverageRootTaskMatches roots tasks = true := by
    simpa [s4CoverageRootTaskLinksReplay, hroots, htasks] using
      s4CoverageRootTaskLinks_replay
  have hrowLink := List.all_eq_true.mp hlinks row hrow
  obtain ⟨task, hmem, hmatch⟩ := List.any_eq_true.mp hrowLink
  have hpair : task.1 = row.2.2 ∧
      task.2.1 = fifteenInnerPositions row.1 := of_decide_eq_true hmatch
  exact ⟨task, hmem, hpair.1, hpair.2⟩

def s4CoverageTaskBoxDataGood (task : FifteenTask) : Bool :=
  decide (task.1.size = 15) &&
    (List.range 15).all (fun i => decide (0 < task.1[i]!.1))

def s4CoverageExactTaskBoxesGood : Bool :=
  match s4CoverageExactTasks? with
  | none => false
  | some tasks => tasks.all s4CoverageTaskBoxDataGood

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem s4CoverageExactTaskBoxesGood_replay :
    s4CoverageExactTaskBoxesGood = true := by
  native_decide

theorem s4CoverageExactTasks_boxesGood {tasks : List FifteenTask}
    (htasks : s4CoverageExactTasks? = some tasks) :
    fifteenTaskListBoxesGood tasks := by
  have hdata : tasks.all s4CoverageTaskBoxDataGood = true := by
    simpa [s4CoverageExactTaskBoxesGood, htasks] using
      s4CoverageExactTaskBoxesGood_replay
  intro task hmem
  have htask := List.all_eq_true.mp hdata task hmem
  have hparts := Bool.and_eq_true_iff.mp htask
  constructor
  · exact of_decide_eq_true hparts.1
  · intro i hi
    have hpositive := List.all_eq_true.mp hparts.2 i (List.mem_range.mpr hi)
    exact Rat.cast_pos.mpr (of_decide_eq_true hpositive)

theorem s4CoverageGeometricNormalTarget_forces_local
    (pattern : String) (G : FifteenStage4CoverageGeometry)
    (hword : pattern = fifteenStage0ProfileWord G.profile)
    (hpattern : pattern ∈ s4CoverageNormalPatterns) :
    ∃ box inner,
      fifteenRealBoxContains box G.radii ∧
      inner = fifteenInnerPositions "001001001001001" ∧
      ∀ p ∈ inner,
        fifteenLocalLo ≤ box[p]!.1 ∧ box[p]!.2 ≤ fifteenLocalHi := by
  obtain ⟨roots, hroots, box, hrow, _hbinData, hcontains⟩ :=
    s4CoverageGeometricNormalTarget_root_contains pattern G hword hpattern
  have hworklist : ∃ tasks counts,
      s4CoverageExactTasks? = some tasks ∧
        fifteenCheckTasks 60000 tasks {} = some counts := by
    have hwork := s4CoverageExactWorklist_replays
    unfold s4CoverageExactWorklistReplay at hwork
    cases htask : s4CoverageExactTasks? with
    | none => simp [htask] at hwork
    | some tasks =>
        cases hcounts : fifteenCheckTasks 60000 tasks {} with
        | none => simp [htask, hcounts] at hwork
        | some counts =>
            exact ⟨tasks, counts, rfl, hcounts⟩
  obtain ⟨tasks, counts, htasks, hcheck⟩ := hworklist
  have hboxesGood := s4CoverageExactTasks_boxesGood htasks
  let row : String × Array Nat × FifteenBox :=
    (pattern, s4CoverageTargetAssignment (s4InnerPositions pattern)
      (s4CoverageGeometryTarget G), box)
  have hrow' : row ∈ roots := by simpa [row] using hrow
  obtain ⟨task, htask, hboxEq, _hinnerEq⟩ :=
    s4CoverageRootTask_mem hroots htasks hrow'
  have htaskContains : fifteenTaskHasProfile task G.radii := by
    change fifteenRealBoxContains task.1 G.radii
    rw [hboxEq]
    exact hcontains
  exact s4CoverageNormalGeometry_task_forces_local G tasks {} counts
    hcheck hboxesGood ⟨task, htask, htaskContains⟩

theorem fifteenStage4ResidualPatterns_exact :
    fifteenStage4ResidualPatterns =
      ["000100100010101", "000100100100101",
       "001001001001001", "001001001001011"] := by
  native_decide

private theorem s4Coverage_stage3Owner_nonneg {label : Nat} {r : ℝ}
    (howner : fifteenStage3OwnerSpec label r) : 0 ≤ r := by
  have hlabel : label = 0 ∨ label = 1 ∨ label = 2 ∨ label = 3 ∨
      label = 4 ∨ label = 5 ∨ label = 6 ∨ label = 7 ∨ label = 9 := by
    unfold fifteenStage3OwnerSpec at howner
    split at howner <;> simp_all
  rcases hlabel with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp_all [fifteenStage3OwnerSpec] <;>
    linarith [fifteenCandidateOuterRadius_pos]

private theorem s4Coverage_stage3Radial_classification {r : ℝ}
    (howner : fifteenStage3OwnerSpec (fifteenStage3RadialLabel r) r) :
    r = fifteenCandidateOuterRadius ∨
      r < fifteenCandidateInnerThreshold := by
  unfold fifteenStage3RadialLabel at howner
  split_ifs at howner with hinner
  · exact Or.inr hinner
  · exact Or.inl (by simpa [fifteenStage3OwnerSpec] using howner)

/-- Every packing below the candidate radius is either the six-inner origin
special profile, or its reindexed radii are forced by the checked exact
subdivision into the unique five-inner local box. -/
theorem fifteen_unit_packing_stage4_coverage_root_or_special
    {R : ℝ} (P : Packing 15 R)
    (hunit : ∀ i, (P.circles i).radius = 1)
    (hR : R ≤ fifteenCandidateOuterRadius + 1) :
    ∃ reflected : Bool, ∃ shift : Fin 15,
      let Q := fifteen_unit_packing_wall_push P hunit hR
      let radii := fifteenStage0TransformProfile (fifteenPackingSortedRadius Q)
        reflected shift
      let theta := fifteenStage0DihedralAngles (fifteenPackingSortedAngle Q)
        reflected shift
      let labels := fun i => fifteenStage3RadialLabel (radii i)
      let profile := fun i => decide
        (radii i < fifteenCandidateInnerThreshold)
      let pattern := fifteenStage0ProfileWord profile
      pattern = "001001001001011" ∨
        ∃ box inner, fifteenRealBoxContains box radii ∧
          inner = fifteenInnerPositions "001001001001001" ∧
          ∀ p ∈ inner,
            fifteenLocalLo ≤ box[p]!.1 ∧ box[p]!.2 ≤ fifteenLocalHi := by
  obtain ⟨reflected, shift, hresidual, hgeometry, hsorted, hrange, hsep⟩ :=
    fifteen_unit_packing_wall_push_stage4_residual_profile P hunit hR
  refine ⟨reflected, shift, ?_⟩
  dsimp only
  let Q := fifteen_unit_packing_wall_push P hunit hR
  let radii := fifteenStage0TransformProfile (fifteenPackingSortedRadius Q)
    reflected shift
  let theta := fifteenStage0DihedralAngles (fifteenPackingSortedAngle Q)
    reflected shift
  let labels := fun i => fifteenStage3RadialLabel (radii i)
  let profile := fun i => decide
    (radii i < fifteenCandidateInnerThreshold)
  let pattern := fifteenStage0ProfileWord profile
  have hlabels : ∀ i, labels i = fifteenStage3RadialLabel (radii i) := by
    intro i
    rfl
  have hprofile : ∀ i, profile i = true ↔
      radii i < fifteenCandidateInnerThreshold := by
    intro i
    simp [profile]
  have hnonneg : ∀ i, 0 ≤ radii i := by
    intro i
    exact s4Coverage_stage3Owner_nonneg (hgeometry.owners i)
  have hclassification : ∀ i,
      radii i = fifteenCandidateOuterRadius ∨
        radii i < fifteenCandidateInnerThreshold := by
    intro i
    exact s4Coverage_stage3Radial_classification (hgeometry.owners i)
  have hprofileList : pattern ∈
      ["000100100010101", "000100100100101",
       "001001001001001", "001001001001011"] := by
    rw [← fifteenStage4ResidualPatterns_exact]
    exact hresidual
  simp only [List.mem_cons, List.mem_singleton] at hprofileList
  let G : FifteenStage4CoverageGeometry := {
    radii := radii
    labels := labels
    hlabels := hlabels
    hgeometry := hgeometry
    profile := profile
    hprofile := hprofile
    hnonneg := hnonneg
    hclassification := hclassification
    theta := theta
    hsorted := hsorted
    hthetaLo := fun i => (hrange i).1
    hthetaHi := fun i => (hrange i).2
    hsep := hsep
  }
  rcases hprofileList with h0 | h1 | h2 | hspecial
  · right
    have hnormal : pattern ∈ s4CoverageNormalPatterns := by
      simp [s4CoverageNormalPatterns, h0]
    exact s4CoverageGeometricNormalTarget_forces_local pattern G rfl hnormal
  · right
    have hnormal : pattern ∈ s4CoverageNormalPatterns := by
      simp [s4CoverageNormalPatterns, h1]
    exact s4CoverageGeometricNormalTarget_forces_local pattern G rfl hnormal
  · right
    have hnormal : pattern ∈ s4CoverageNormalPatterns := by
      simp [s4CoverageNormalPatterns, h2]
    exact s4CoverageGeometricNormalTarget_forces_local pattern G rfl hnormal
  · left
    rcases hspecial with hspecial | hnil
    · exact hspecial
    · simp at hnil

end CirclePacking
