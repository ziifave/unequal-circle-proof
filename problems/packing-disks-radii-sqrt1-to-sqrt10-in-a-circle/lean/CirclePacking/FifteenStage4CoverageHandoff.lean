import CirclePacking.FifteenStage4Coverage000
import CirclePacking.FifteenStage4Coverage001
import CirclePacking.FifteenStage4Coverage002
import CirclePacking.FifteenStage4CoverageSoundness
import CirclePacking.FifteenStage4CoverageRoots
import CirclePacking.FifteenStage4FiniteGeometry

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

/-- Every packing below the candidate radius reaches one of the exact roots
for the three normal profiles, or the known six-inner special profile. -/
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
        ∃ roots, s4CoverageRootBoxes? = some roots ∧
          ∃ box, (pattern, s4CoverageTargetAssignment
            (s4InnerPositions pattern)
            (fifteenStage4OwnerLabelArray (fun i =>
              fifteenStage4RadialLabel (radii i))), box) ∈ roots ∧
            (∀ k, (hk : k < (s4InnerPositions pattern).size) →
              box[(s4InnerPositions pattern)[k]!]! =
                fifteenBins[(s4CoverageTargetAssignment
                  (s4InnerPositions pattern)
                  (fifteenStage4OwnerLabelArray (fun i =>
                    fifteenStage4RadialLabel (radii i))))[k]!]!) ∧
            (∀ i : Fin 15,
              ((box[i.1]!.1 : ℝ) ≤ radii i) ∧
                radii i ≤ (box[i.1]!.2 : ℝ)) := by
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
    exact s4CoverageGeometricNormalTarget_root_contains pattern G rfl hnormal
  · right
    have hnormal : pattern ∈ s4CoverageNormalPatterns := by
      simp [s4CoverageNormalPatterns, h1]
    exact s4CoverageGeometricNormalTarget_root_contains pattern G rfl hnormal
  · right
    have hnormal : pattern ∈ s4CoverageNormalPatterns := by
      simp [s4CoverageNormalPatterns, h2]
    exact s4CoverageGeometricNormalTarget_root_contains pattern G rfl hnormal
  · left
    rcases hspecial with hspecial | hnil
    · exact hspecial
    · simp at hnil

end CirclePacking
