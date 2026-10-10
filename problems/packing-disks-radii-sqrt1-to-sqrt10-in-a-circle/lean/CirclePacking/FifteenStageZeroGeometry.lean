import CirclePacking.FifteenStageZero
import CirclePacking.FifteenTickSoundness
import CirclePacking.FifteenSmallRadiusCount
import Mathlib.Tactic.FinCases

/-!
# Geometric meaning of the coarse 15-disk angle table

The stage-zero replay checks the coarse angle table with the same rational
Taylor and corner-cap calculation used by the refined certificate.  This file
turns each positive table entry into an actual contact-angle lower bound over
its full radial rectangle, so the finite graph witnesses have a geometric
interface.
-/

namespace CirclePacking

/-- The Stage 0 assignment rule requires at least `k - 4` of the `k` inner
centers to lie in the outer inner-shell `[5/3, L)`.  This is the geometric
population bound behind that rule: at most four centers in any unit-disk
packing can have radius at most `5/3`. -/
theorem fifteenStage0_smallRadialShell_population_bound
    {R : ℝ} (P : Packing 15 R)
    (hunit : ∀ i, (P.circles i).radius = 1) :
    (Finset.univ.filter fun i : Fin 15 =>
      fifteenPackingSortedRadius P i ≤ 5 / 3).card ≤ 4 :=
  fifteen_unit_packing_small_radius_count_le_four P hunit

/-- The other Stage 0 assignment restriction follows from the radial-sum
bound: at most one center can have radius below one. -/
theorem fifteenStage0_subunitShell_population_bound
    {R : ℝ} (P : Packing 15 R)
    (hunit : ∀ i, (P.circles i).radius = 1) :
    (Finset.univ.filter fun i : Fin 15 =>
      fifteenPackingSortedRadius P i < 1).card ≤ 1 :=
  fifteen_unit_packing_subunit_sorted_count_le_one P hunit

theorem fifteenStage0OuterTypeBox_bounds :
    ((fifteenStage0CoarseTypeBox (0 : Fin 4)).1 : ℝ) =
        (2385 : ℝ) / 1000 ∧
      ((fifteenStage0CoarseTypeBox (0 : Fin 4)).2 : ℝ) =
        (3522 : ℝ) / 1000 := by
  rcases fifteenStage0OuterTypeBox_rat_bounds with ⟨hlo, hhi⟩
  constructor
  · rw [hlo]
    simp [fifteenRational, Rat.normalize_eq_mkRat,
      Rat.cast_mkRat_of_ne_zero]
  · rw [hhi]
    simp [fifteenRational, Rat.normalize_eq_mkRat,
      Rat.cast_mkRat_of_ne_zero]

theorem fifteenStage0InnerTypeBox_real_bounds :
    (((fifteenStage0CoarseTypeBox (1 : Fin 4)).1 : ℝ) = 0 ∧
      ((fifteenStage0CoarseTypeBox (1 : Fin 4)).2 : ℝ) = 1) ∧
    (((fifteenStage0CoarseTypeBox (2 : Fin 4)).1 : ℝ) = 1 ∧
      ((fifteenStage0CoarseTypeBox (2 : Fin 4)).2 : ℝ) = 5 / 3) ∧
    (((fifteenStage0CoarseTypeBox (3 : Fin 4)).1 : ℝ) = 5 / 3 ∧
      ((fifteenStage0CoarseTypeBox (3 : Fin 4)).2 : ℝ) =
        (2385432 : ℝ) / 1000000) := by
  rcases fifteenStage0InnerTypeBox_rat_bounds with ⟨h1, h2, h3⟩
  rcases h1 with ⟨h10, h11⟩
  rcases h2 with ⟨h20, h21⟩
  rcases h3 with ⟨h30, h31⟩
  constructor
  · constructor
    · rw [h10]
      simp [fifteenRational, Rat.normalize_eq_mkRat,
        Rat.cast_mkRat_of_ne_zero]
    · rw [h11]
      simp [fifteenRational, Rat.normalize_eq_mkRat,
        Rat.cast_mkRat_of_ne_zero]
  constructor
  · constructor
    · rw [h20]
      simp [fifteenRational, Rat.normalize_eq_mkRat,
        Rat.cast_mkRat_of_ne_zero]
    · rw [h21]
      simp [fifteenRational, Rat.normalize_eq_mkRat,
        Rat.cast_mkRat_of_ne_zero]
  · constructor
    · rw [h30]
      simp [fifteenRational, Rat.normalize_eq_mkRat,
        Rat.cast_mkRat_of_ne_zero]
    · rw [h31]
      simp [fifteenRational, Rat.normalize_eq_mkRat,
        Rat.cast_mkRat_of_ne_zero]

theorem fifteenStage0CoarsePair_numeric_spec
    (typeI typeJ : Fin 4)
    (hpositive : 0 < fifteenStage0CoarseAngleTick typeI typeJ) :
    let x := fifteenStage0CoarseTypeBox typeI
    let y := fifteenStage0CoarseTypeBox typeJ
    2 ≤ x.2 + y.2 ∧
    fifteenBoxCosineCap x y < 1 ∧
    -1 < fifteenBoxCosineCap x y ∧
    fifteenTickCertificateValid x y false false
      (fifteenStage0CoarseAngleTick typeI typeJ) = true ∧
    x.1 ≤ x.2 ∧ y.1 ≤ y.2 ∧ 0 < x.1 ∧ 0 < y.1 := by
  fin_cases typeI <;> fin_cases typeJ <;>
    simp_all [fifteenStage0CoarseAngleTick, fifteenStage0CoarseQ] <;>
    native_decide

theorem fifteenStage0CoarsePair_lower_bounds_touch_angle
    (typeI typeJ : Fin 4)
    (hpositive : 0 < fifteenStage0CoarseAngleTick typeI typeJ)
    (a b : ℝ)
    (haL : ((fifteenStage0CoarseTypeBox typeI).1 : ℝ) ≤ a)
    (haU : a ≤ ((fifteenStage0CoarseTypeBox typeI).2 : ℝ))
    (hbL : ((fifteenStage0CoarseTypeBox typeJ).1 : ℝ) ≤ b)
    (hbU : b ≤ ((fifteenStage0CoarseTypeBox typeJ).2 : ℝ)) :
    (fifteenStage0CoarseAngleTick typeI typeJ : ℝ) / 2800 ≤
      touchAngle a b 2 := by
  let x := fifteenStage0CoarseTypeBox typeI
  let y := fifteenStage0CoarseTypeBox typeJ
  have hspec := fifteenStage0CoarsePair_numeric_spec typeI typeJ hpositive
  dsimp only at hspec
  rcases hspec with
    ⟨hsum, hcapUpper, hcapLower, hvalid, hxOrder, hyOrder, hx0, hy0⟩
  exact fifteenRegularTick_lower_bounds_touch_angle x y
    (fifteenStage0CoarseAngleTick typeI typeJ) a b hsum
    (by exact_mod_cast hcapUpper)
    (by exact_mod_cast hcapLower)
    hvalid hxOrder hyOrder
    (by exact_mod_cast hx0)
    (by exact_mod_cast hy0)
    haL haU hbL hbU

theorem fifteenStage0CoarsePair_gives_polar_edge_bound
    (typeI typeJ : Fin 4)
    (hpositive : 0 < fifteenStage0CoarseAngleTick typeI typeJ)
    (edge : FifteenAngularEdge) (theta : Fin 15 → ℝ)
    (a b tauUpper : ℝ)
    (haL : ((fifteenStage0CoarseTypeBox typeI).1 : ℝ) ≤ a)
    (haU : a ≤ ((fifteenStage0CoarseTypeBox typeI).2 : ℝ))
    (hbL : ((fifteenStage0CoarseTypeBox typeJ).1 : ℝ) ≤ b)
    (hbU : b ≤ ((fifteenStage0CoarseTypeBox typeJ).2 : ℝ))
    (hlower : edge.lower =
      (fifteenStage0CoarseAngleTick typeI typeJ : ℝ) / 2800)
    (hneq : edge.src ≠ edge.dst)
    (hsorted : ∀ i j : Fin 15, i.1 < j.1 → theta i ≤ theta j)
    (hthetaLo : ∀ i : Fin 15, 0 ≤ theta i)
    (hthetaHi : ∀ i : Fin 15, theta i ≤ 2 * Real.pi)
    (hsep : 4 ≤ pointNorm
      ((polarPoint a (theta edge.src)).1 - (polarPoint b (theta edge.dst)).1,
       (polarPoint a (theta edge.src)).2 - (polarPoint b (theta edge.dst)).2) ^ 2)
    (htau : 2 * Real.pi ≤ tauUpper) :
    theta edge.dst - theta edge.src ≤ fifteenAngularEdgeUpper tauUpper edge := by
  let x := fifteenStage0CoarseTypeBox typeI
  let y := fifteenStage0CoarseTypeBox typeJ
  have hspec := fifteenStage0CoarsePair_numeric_spec typeI typeJ hpositive
  dsimp only at hspec
  rcases hspec with
    ⟨hsum, hcapUpper, hcapLower, hvalid, hxOrder, hyOrder, hx0, hy0⟩
  exact fifteenRegularTick_gives_polar_edge_bound x y
    (fifteenStage0CoarseAngleTick typeI typeJ) edge theta a b tauUpper
    hsum
    (by exact_mod_cast hcapUpper)
    (by exact_mod_cast hcapLower)
    hvalid hxOrder hyOrder
    (by exact_mod_cast hx0)
    (by exact_mod_cast hy0)
    haL haU hbL hbU hlower hneq hsorted hthetaLo hthetaHi hsep htau

theorem fifteenStage0CoarseAngleTick_symmetric
    (typeI typeJ : Fin 4) :
    fifteenStage0CoarseAngleTick typeI typeJ =
      fifteenStage0CoarseAngleTick typeJ typeI := by
  fin_cases typeI <;> fin_cases typeJ <;>
    norm_num [fifteenStage0CoarseAngleTick, fifteenStage0CoarseQ]

theorem fifteen_two_pi_le_stage0_tau :
    2 * Real.pi ≤ (17600 : ℝ) / 2800 := by
  apply le_of_lt ?_
  calc
    2 * Real.pi < 2 * (3.1416 : ℝ) := by
      nlinarith [Real.pi_lt_d4]
    _ ≤ (17600 : ℝ) / 2800 := by norm_num

/-- The coarse Stage 0 table gives both directed gap bounds for every pair of
angle-sorted centers whose radii lie in their assigned radial boxes. The
reverse direction uses table symmetry; a zero tick uses only angle order and
the full-turn bound. -/
theorem fifteenStage0Packing_pair_angle_gaps
    {R : ℝ} (P : Packing 15 R)
    (hunit : ∀ i, (P.circles i).radius = 1)
    (typeI typeJ : Fin 4) (i j : Fin 15) (hij : i.1 < j.1)
    (hri : ((fifteenStage0CoarseTypeBox typeI).1 : ℝ) ≤
        fifteenPackingSortedRadius P i ∧
      fifteenPackingSortedRadius P i ≤
        ((fifteenStage0CoarseTypeBox typeI).2 : ℝ))
    (hrj : ((fifteenStage0CoarseTypeBox typeJ).1 : ℝ) ≤
        fifteenPackingSortedRadius P j ∧
      fifteenPackingSortedRadius P j ≤
        ((fifteenStage0CoarseTypeBox typeJ).2 : ℝ)) :
    (fifteenStage0CoarseAngleTick typeI typeJ : ℝ) / 2800 ≤
        fifteenPackingSortedAngle P j - fifteenPackingSortedAngle P i ∧
      fifteenPackingSortedAngle P j - fifteenPackingSortedAngle P i ≤
        (17600 : ℝ) / 2800 -
          (fifteenStage0CoarseAngleTick typeI typeJ : ℝ) / 2800 := by
  let q := fifteenStage0CoarseAngleTick typeI typeJ
  by_cases hqzero : q = 0
  · constructor
    · have hqzero' : fifteenStage0CoarseAngleTick typeI typeJ = 0 := by
        simpa [q] using hqzero
      simpa [hqzero'] using fifteenPackingSortedAngle_monotone P hij
    · have hdelta : fifteenPackingSortedAngle P j -
        fifteenPackingSortedAngle P i ≤ 2 * Real.pi := by
        have hj := (fifteenPackingSortedAngle_range P j).2
        have hi := (fifteenPackingSortedAngle_range P i).1
        linarith
      have hqzero' : fifteenStage0CoarseAngleTick typeI typeJ = 0 := by
        simpa [q] using hqzero
      simpa [hqzero'] using hdelta.trans fifteen_two_pi_le_stage0_tau
  · have hqpos : 0 < q := Nat.pos_of_ne_zero hqzero
    have hqpos' : 0 < fifteenStage0CoarseAngleTick typeI typeJ := by
      simpa [q] using hqpos
    have hqposRev : 0 < fifteenStage0CoarseAngleTick typeJ typeI := by
      rw [fifteenStage0CoarseAngleTick_symmetric]
      exact hqpos'
    have hne : i ≠ j := by
      intro heq
      subst j
      omega
    let forward : FifteenAngularEdge :=
      ⟨i, j, (fifteenStage0CoarseAngleTick typeI typeJ : ℝ) / 2800⟩
    let backward : FifteenAngularEdge :=
      ⟨j, i, (fifteenStage0CoarseAngleTick typeJ typeI : ℝ) / 2800⟩
    have hsepForward := fifteen_unit_packing_sorted_pair_separated
      P hunit hne
    have hsepBackward := fifteen_unit_packing_sorted_pair_separated
      P hunit hne.symm
    have hforward := fifteenStage0CoarsePair_gives_polar_edge_bound
      typeI typeJ hqpos' forward (fifteenPackingSortedAngle P)
      (fifteenPackingSortedRadius P i) (fifteenPackingSortedRadius P j)
      ((17600 : ℝ) / 2800)
      hri.1 hri.2 hrj.1 hrj.2 rfl hne
      (fun x y hxy => fifteenPackingSortedAngle_monotone P hxy)
      (fun x => (fifteenPackingSortedAngle_range P x).1)
      (fun x => (fifteenPackingSortedAngle_range P x).2)
      hsepForward fifteen_two_pi_le_stage0_tau
    have hbackward := fifteenStage0CoarsePair_gives_polar_edge_bound
      typeJ typeI hqposRev backward (fifteenPackingSortedAngle P)
      (fifteenPackingSortedRadius P j) (fifteenPackingSortedRadius P i)
      ((17600 : ℝ) / 2800)
      hrj.1 hrj.2 hri.1 hri.2 rfl hne.symm
      (fun x y hxy => fifteenPackingSortedAngle_monotone P hxy)
      (fun x => (fifteenPackingSortedAngle_range P x).1)
      (fun x => (fifteenPackingSortedAngle_range P x).2)
      hsepBackward fifteen_two_pi_le_stage0_tau
    have hforward' : fifteenPackingSortedAngle P j -
        fifteenPackingSortedAngle P i ≤
          (17600 : ℝ) / 2800 -
            (fifteenStage0CoarseAngleTick typeI typeJ : ℝ) / 2800 := by
      simpa [fifteenAngularEdgeUpper, forward, hij] using hforward
    have hbackward' : fifteenPackingSortedAngle P i -
        fifteenPackingSortedAngle P j ≤
          -((fifteenStage0CoarseAngleTick typeI typeJ : ℝ) / 2800) := by
      have hreverse : ¬ j.1 < i.1 := by omega
      simpa [fifteenAngularEdgeUpper, backward, hreverse,
        fifteenStage0CoarseAngleTick_symmetric] using hbackward
    constructor
    · nlinarith [hbackward']
    · exact hforward'

/-- The two scaled pair constraints in the Stage 0 difference graph follow
from geometric separation whenever the radii occupy the assigned boxes. -/
theorem fifteenStage0Packing_pair_difference_bounds
    {R : ℝ} (P : Packing 15 R)
    (hunit : ∀ i, (P.circles i).radius = 1)
    (typeI typeJ : Fin 4) (i j : Fin 15) (hij : i.1 < j.1)
    (hri : ((fifteenStage0CoarseTypeBox typeI).1 : ℝ) ≤
        fifteenPackingSortedRadius P i ∧
      fifteenPackingSortedRadius P i ≤
        ((fifteenStage0CoarseTypeBox typeI).2 : ℝ))
    (hrj : ((fifteenStage0CoarseTypeBox typeJ).1 : ℝ) ≤
        fifteenPackingSortedRadius P j ∧
      fifteenPackingSortedRadius P j ≤
        ((fifteenStage0CoarseTypeBox typeJ).2 : ℝ)) :
    2800 * (fifteenPackingSortedAngle P i -
        fifteenPackingSortedAngle P j) ≤
        - (fifteenStage0CoarseAngleTick typeI typeJ : ℝ) ∧
      2800 * (fifteenPackingSortedAngle P j -
        fifteenPackingSortedAngle P i) ≤
        17600 - (fifteenStage0CoarseAngleTick typeI typeJ : ℝ) := by
  have hgap := fifteenStage0Packing_pair_angle_gaps
    P hunit typeI typeJ i j hij hri hrj
  constructor <;> nlinarith [hgap.1, hgap.2]

/-- Pairwise Stage 0 difference constraints can be stated directly using the
raw labels stored in a finite-cycle witness.  The label-range hypothesis
ensures that the total `Fin 4` conversion used by the geometric angle table
agrees with the witness's unwrapped labels. -/
theorem fifteenStage0Packing_witness_pair_difference_bounds
    {R : ℝ} (P : Packing 15 R)
    (hunit : ∀ i, (P.circles i).radius = 1)
    (witness : FifteenStage0CycleWitness)
    (hlabels : ∀ i : Fin 15,
      fifteenStage0CycleWitnessLabel witness i < 4)
    (hboxes : ∀ i : Fin 15,
      ((fifteenStage0CoarseTypeBox
        (fifteenStage0CycleWitnessTypeIndex witness i)).1 : ℝ) ≤
          fifteenPackingSortedRadius P i ∧
      fifteenPackingSortedRadius P i ≤
        ((fifteenStage0CoarseTypeBox
          (fifteenStage0CycleWitnessTypeIndex witness i)).2 : ℝ))
    (i j : Fin 15) (hij : i.1 < j.1) :
    2800 * (fifteenPackingSortedAngle P i -
        fifteenPackingSortedAngle P j) ≤
        - (fifteenStage0CoarseQ
          (fifteenStage0CycleWitnessLabel witness i)
          (fifteenStage0CycleWitnessLabel witness j) : ℝ) ∧
      2800 * (fifteenPackingSortedAngle P j -
        fifteenPackingSortedAngle P i) ≤
        17600 - (fifteenStage0CoarseQ
          (fifteenStage0CycleWitnessLabel witness i)
          (fifteenStage0CycleWitnessLabel witness j) : ℝ) := by
  let typeI := fifteenStage0CycleWitnessTypeIndex witness i
  let typeJ := fifteenStage0CycleWitnessTypeIndex witness j
  have htypeI : typeI.1 = fifteenStage0CycleWitnessLabel witness i := by
    simp [typeI, fifteenStage0CycleWitnessTypeIndex,
      Nat.mod_eq_of_lt (hlabels i)]
  have htypeJ : typeJ.1 = fifteenStage0CycleWitnessLabel witness j := by
    simp [typeJ, fifteenStage0CycleWitnessTypeIndex,
      Nat.mod_eq_of_lt (hlabels j)]
  have hpair := fifteenStage0Packing_pair_difference_bounds P hunit
    typeI typeJ i j hij (hboxes i) (hboxes j)
  have hq : fifteenStage0CoarseAngleTick typeI typeJ =
      fifteenStage0CoarseQ
        (fifteenStage0CycleWitnessLabel witness i)
        (fifteenStage0CycleWitnessLabel witness j) := by
    simp only [fifteenStage0CoarseAngleTick]
    rw [htypeI, htypeJ]
  rw [hq] at hpair
  exact hpair

/-- No unit-disk packing can realize a Stage 0 cycle witness when every
sorted radius lies in the box named by that witness's radial labels.  The
proof sends the actual sorted angles through the certified difference graph. -/
theorem fifteenStage0Packing_excludes_cycle_witness
    {R : ℝ} (P : Packing 15 R)
    (hunit : ∀ i, (P.circles i).radius = 1)
    (witness : FifteenStage0CycleWitness)
    (hwitness : witness ∈ fifteenStage0NegativeCycleWitnesses)
    (hboxes : ∀ i : Fin 15,
      ((fifteenStage0CoarseTypeBox
        (fifteenStage0CycleWitnessTypeIndex witness i)).1 : ℝ) ≤
          fifteenPackingSortedRadius P i ∧
      fifteenPackingSortedRadius P i ≤
        ((fifteenStage0CoarseTypeBox
          (fifteenStage0CycleWitnessTypeIndex witness i)).2 : ℝ)) :
    False := by
  have hshape := fifteenStage0NegativeCycleWitnesses_shape_certified
    witness hwitness
  let potential : Nat → ℝ := fun n =>
    2800 * fifteenPackingSortedAngle P
      ⟨n % 15, Nat.mod_lt n (by omega)⟩
  apply fifteenStage0NegativeCycleWitness_no_real_potential
    witness hwitness potential
  intro edge hedge
  have hmem : edge ∈ witness.steps.map
      (fifteenStage0CycleWitnessStepEdge witness) := by
    simpa [fifteenStage0CycleWitnessEdges] using hedge
  obtain ⟨step, hstep, hstepEdge⟩ := List.mem_map.mp hmem
  subst edge
  have hstepShape := hshape.1 step hstep
  rcases hstepShape with ⟨hsourceLt, htargetLt, hkind⟩
  let source : Fin 15 := ⟨step.1, hsourceLt⟩
  let target : Fin 15 := ⟨step.2.1, htargetLt⟩
  have hpotentialSource : potential step.1 =
      2800 * fifteenPackingSortedAngle P source := by
    simp [potential, source, Nat.mod_eq_of_lt hsourceLt]
  have hpotentialTarget : potential step.2.1 =
      2800 * fifteenPackingSortedAngle P target := by
    simp [potential, target, Nat.mod_eq_of_lt htargetLt]
  change potential step.2.1 ≤ potential step.1 +
    ((fifteenStage0CycleWitnessStepEdge witness step).weight : ℝ)
  rcases hkind with ⟨horder, hsuccessor, _⟩ |
      ⟨hlower, hdescending⟩ | ⟨hupper, hascending⟩
  · have hangle := fifteenPackingSortedAngle_monotone P (by
      change target.1 < source.1
      dsimp [target, source]
      omega)
    have hweight :
        (fifteenStage0CycleWitnessStepEdge witness step).weight = 0 := by
      simp [fifteenStage0CycleWitnessStepEdge,
        fifteenStage0StepGraphEdge, fifteenStage0EdgeWeight,
        fifteenStage0CycleWitnessLabel, horder]
    rw [hpotentialTarget, hpotentialSource, hweight]
    have hscaled := mul_le_mul_of_nonneg_left hangle
      (by norm_num : (0 : ℝ) ≤ 2800)
    simpa using hscaled
  · have hpair := fifteenStage0Packing_witness_pair_difference_bounds
      P hunit witness hshape.2 hboxes target source (by
        change target.1 < source.1
        dsimp [target, source]
        omega)
    have hweight :
        (fifteenStage0CycleWitnessStepEdge witness step).weight =
          -(Int.ofNat (fifteenStage0CoarseQ
            (fifteenStage0CycleWitnessLabel witness target)
            (fifteenStage0CycleWitnessLabel witness source))) := by
      simp [fifteenStage0CycleWitnessStepEdge,
        fifteenStage0StepGraphEdge, fifteenStage0EdgeWeight,
        fifteenStage0CycleWitnessLabel, source, target, hlower]
    have hweightReal :
        ((fifteenStage0CycleWitnessStepEdge witness step).weight : ℝ) =
          -(fifteenStage0CoarseQ
            (fifteenStage0CycleWitnessLabel witness target)
            (fifteenStage0CycleWitnessLabel witness source) : ℝ) := by
      rw [hweight]
      simp
    rw [hpotentialTarget, hpotentialSource, hweightReal]
    nlinarith [hpair.1]
  · have hpair := fifteenStage0Packing_witness_pair_difference_bounds
      P hunit witness hshape.2 hboxes source target (by
        change source.1 < target.1
        dsimp [target, source]
        omega)
    let q := fifteenStage0CoarseQ
      (fifteenStage0CycleWitnessLabel witness source)
      (fifteenStage0CycleWitnessLabel witness target)
    have hqle : q ≤ 17600 := by
      dsimp [q, fifteenStage0CoarseQ]
      split_ifs <;> omega
    have hweight :
        (fifteenStage0CycleWitnessStepEdge witness step).weight =
          Int.ofNat (17600 - q) := by
      simp [fifteenStage0CycleWitnessStepEdge,
        fifteenStage0StepGraphEdge, fifteenStage0EdgeWeight,
        fifteenStage0CycleWitnessLabel, fifteenStage0TwoPiUpper,
        source, target, hupper, q]
    have hcastSub : ((17600 - q : ℕ) : ℝ) =
        (17600 : ℝ) - q := by
      exact Nat.cast_sub hqle
    have hweightReal :
        ((fifteenStage0CycleWitnessStepEdge witness step).weight : ℝ) =
          (17600 : ℝ) - q := by
      rw [hweight]
      exact hcastSub
    rw [hpotentialTarget, hpotentialSource, hweightReal]
    linarith [hpair.2]

theorem fifteenStage0ZeroTick_gives_polar_edge_bound
    (edge : FifteenAngularEdge) (theta : Fin 15 → ℝ) (tauUpper : ℝ)
    (hzero : edge.lower = 0) (hneq : edge.src ≠ edge.dst)
    (hsorted : ∀ i j : Fin 15, i.1 < j.1 → theta i ≤ theta j)
    (hthetaLo : ∀ i : Fin 15, 0 ≤ theta i)
    (hthetaHi : ∀ i : Fin 15, theta i ≤ 2 * Real.pi)
    (htau : 2 * Real.pi ≤ tauUpper) :
    theta edge.dst - theta edge.src ≤ fifteenAngularEdgeUpper tauUpper edge := by
  by_cases hforward : edge.src.1 < edge.dst.1
  · have hhi := hthetaHi edge.dst
    have hlo := hthetaLo edge.src
    simp [fifteenAngularEdgeUpper, hforward, hzero]
    linarith
  · have hback : edge.dst.1 < edge.src.1 := by
      have hindices : edge.src.1 ≠ edge.dst.1 := by
        intro heq
        apply hneq
        exact Fin.ext heq
      omega
    have horder := hsorted edge.dst edge.src hback
    simp [fifteenAngularEdgeUpper, hforward, hzero]
    linarith

end CirclePacking
