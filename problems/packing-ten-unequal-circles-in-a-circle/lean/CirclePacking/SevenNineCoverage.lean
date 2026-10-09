import CirclePacking.Basic
import CirclePacking.SevenNineAngleData
import CirclePacking.SevenNineAngleProofs
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FinCases

namespace CirclePacking

noncomputable section

def pointNorm (p : Point) : ℝ := Real.sqrt (p.1 ^ 2 + p.2 ^ 2)

lemma pointNorm_nonneg (p : Point) : 0 ≤ pointNorm p := by
  exact Real.sqrt_nonneg _

lemma pointNorm_sq (p : Point) : pointNorm p ^ 2 = p.1 ^ 2 + p.2 ^ 2 := by
  dsimp [pointNorm]
  rw [Real.sq_sqrt]
  positivity

lemma pointNorm_triangle (p q : Point) :
    pointNorm (p.1 - q.1, p.2 - q.2) ≤ pointNorm p + pointNorm q := by
  let a := pointNorm p
  let b := pointNorm q
  have ha : a ^ 2 = p.1 ^ 2 + p.2 ^ 2 := pointNorm_sq p
  have hb : b ^ 2 = q.1 ^ 2 + q.2 ^ 2 := pointNorm_sq q
  have hab : 0 ≤ a * b := mul_nonneg (pointNorm_nonneg p) (pointNorm_nonneg q)
  have hcs : p.1 * q.1 + p.2 * q.2 ≤ a * b := by
    rcases le_total (p.1 * q.1 + p.2 * q.2) 0 with hdot | hdot
    · exact hdot.trans hab
    · have hsq :
          (p.1 * q.1 + p.2 * q.2) ^ 2 ≤ (a * b) ^ 2 := by
        have hdet : 0 ≤ (p.1 * q.2 - p.2 * q.1) ^ 2 := sq_nonneg _
        have hid :
            (a * b) ^ 2 - (p.1 * q.1 + p.2 * q.2) ^ 2 =
              (p.1 * q.2 - p.2 * q.1) ^ 2 := by
          rw [mul_pow, ha, hb]
          ring
        nlinarith [hid, hdet]
      exact (sq_le_sq₀ hdot hab).mp hsq
  have hlower : -(a * b) ≤ p.1 * q.1 + p.2 * q.2 := by
    by_cases hdot : 0 ≤ p.1 * q.1 + p.2 * q.2
    · nlinarith [hab]
    · have hsq :
          (p.1 * q.1 + p.2 * q.2) ^ 2 ≤ (a * b) ^ 2 := by
        have hdet : 0 ≤ (p.1 * q.2 - p.2 * q.1) ^ 2 := sq_nonneg _
        have hid :
            (a * b) ^ 2 - (p.1 * q.1 + p.2 * q.2) ^ 2 =
              (p.1 * q.2 - p.2 * q.1) ^ 2 := by
          rw [mul_pow, ha, hb]
          ring
        nlinarith [hid, hdet]
      have hneg : 0 ≤ -(p.1 * q.1 + p.2 * q.2) := by linarith
      have hsq' :
          (-(p.1 * q.1 + p.2 * q.2)) ^ 2 ≤ (a * b) ^ 2 := by
        calc
          (-(p.1 * q.1 + p.2 * q.2)) ^ 2 =
              (p.1 * q.1 + p.2 * q.2) ^ 2 := by ring
          _ ≤ (a * b) ^ 2 := hsq
      have := (sq_le_sq₀ hneg hab).mp hsq'
      linarith
  have hsqdist :
      (p.1 - q.1) ^ 2 + (p.2 - q.2) ^ 2 ≤ (a + b) ^ 2 := by
    have hdist :
        (p.1 - q.1) ^ 2 + (p.2 - q.2) ^ 2 =
          a ^ 2 + b ^ 2 - 2 * (p.1 * q.1 + p.2 * q.2) := by
      nlinarith [ha, hb]
    calc
      (p.1 - q.1) ^ 2 + (p.2 - q.2) ^ 2 =
          a ^ 2 + b ^ 2 - 2 * (p.1 * q.1 + p.2 * q.2) := hdist
      _ ≤ (a + b) ^ 2 := by
        rw [show (a + b) ^ 2 = a ^ 2 + b ^ 2 + 2 * a * b by ring]
        have hnonneg : 0 ≤ a * b + (p.1 * q.1 + p.2 * q.2) :=
          by linarith [hlower]
        nlinarith [hnonneg]
  have hsqdist' :
      pointNorm (p.1 - q.1, p.2 - q.2) ^ 2 ≤
        (pointNorm p + pointNorm q) ^ 2 := by
    calc
      pointNorm (p.1 - q.1, p.2 - q.2) ^ 2 =
          (p.1 - q.1) ^ 2 + (p.2 - q.2) ^ 2 := pointNorm_sq _
      _ ≤ (a + b) ^ 2 := hsqdist
      _ = (pointNorm p + pointNorm q) ^ 2 := by rfl
  exact (sq_le_sq₀ (pointNorm_nonneg _) (add_nonneg (pointNorm_nonneg _) (pointNorm_nonneg _))).mp hsqdist'

def sevenNineLower (i : Fin 7) : ℝ :=
  if i.1 = 6 then
    Real.sqrt (i.1 + 4) + 2 * Real.sqrt 9 - (79 / 10 : ℝ)
  else
    Real.sqrt (i.1 + 4) + 2 * Real.sqrt 10 - (79 / 10 : ℝ)

def sevenNineUpper (i : Fin 7) : ℝ :=
  (79 / 10 : ℝ) - Real.sqrt (i.1 + 4)

def sevenNineCut (i state side : Nat) : Rat :=
  let p := sevenNineRadialBounds[i * 2 + state]!
  if side == 0 then p.1 else p.2

/-! The finite-box statement is deliberately separated from the geometry that
produces the radial interval.  This makes the coverage obligation explicit:
once the certified endpoint inequalities are available, choosing the half
interval independently for each circle is a finite constructive argument. -/

lemma sevenNine_global_radial_cover
    (a : Fin 7 → ℝ)
    (haL : ∀ i, sevenNineLower i ≤ a i)
    (haU : ∀ i, a i ≤ sevenNineUpper i)
    (hlo0 : ∀ i : Fin 7, (sevenNineCut i 0 0 : ℝ) ≤ sevenNineLower i)
    (hmid : ∀ i : Fin 7, (sevenNineCut i 1 0 : ℝ) ≤
      (sevenNineCut i 0 1 : ℝ))
    (hhi1 : ∀ i : Fin 7, sevenNineUpper i ≤ (sevenNineCut i 1 1 : ℝ)) :
    ∃ state : Fin 7 → Nat,
      ∀ i,
        state i ≤ 1 ∧
        (sevenNineCut i (state i) 0 : ℝ) ≤ a i ∧
        a i ≤ (sevenNineCut i (state i) 1 : ℝ) := by
  classical
  let state : Fin 7 → Nat := fun i =>
    if (sevenNineCut i 0 1 : ℝ) < a i then 1 else 0
  refine ⟨state, ?_⟩
  intro i
  by_cases h : (sevenNineCut i 0 1 : ℝ) < a i
  · have hs : state i = 1 := by simp [state, h]
    have hlow : (sevenNineCut i 1 0 : ℝ) ≤ a i :=
      (hmid i).trans (le_of_lt h)
    have hupp : a i ≤ (sevenNineCut i 1 1 : ℝ) :=
      (haU i).trans (hhi1 i)
    exact ⟨by simp [hs], by simpa [hs] using hlow, by simpa [hs] using hupp⟩
  · have hs : state i = 0 := by simp [state, h]
    have hlow : (sevenNineCut i 0 0 : ℝ) ≤ a i :=
      le_trans (hlo0 i) (haL i)
    have hupp : a i ≤ (sevenNineCut i 0 1 : ℝ) :=
      le_of_not_gt h
    exact ⟨by simp [hs], by simpa [hs] using hlow, by simpa [hs] using hupp⟩

/-! These are the finite endpoint obligations exported by the MPFI radial
partition.  The only irrational facts needed here are the downward rational
square-root bounds already replayed in `SevenNineAngleProofs`. -/

lemma sevenNine_endpoint_lower0 :
    ∀ i : Fin 7, (sevenNineCut i 0 0 : ℝ) ≤ sevenNineLower i := by
  intro i
  fin_cases i <;>
    norm_num [sevenNineCut, sevenNineRadialBounds, sevenNineLower,
      sqrt_lower_4, sqrt_lower_5, sqrt_lower_6, sqrt_lower_7,
      sqrt_lower_8, sqrt_lower_9, sqrt_lower_10] <;>
    nlinarith [sqrt_lower_4, sqrt_lower_5, sqrt_lower_6, sqrt_lower_7,
      sqrt_lower_8, sqrt_lower_9, sqrt_lower_10]

lemma sevenNine_endpoint_mid :
    ∀ i : Fin 7, (sevenNineCut i 1 0 : ℝ) ≤
      (sevenNineCut i 0 1 : ℝ) := by
  intro i
  fin_cases i <;>
    norm_num [sevenNineCut, sevenNineRadialBounds]

lemma sevenNine_endpoint_upper1 :
    ∀ i : Fin 7, sevenNineUpper i ≤ (sevenNineCut i 1 1 : ℝ) := by
  intro i
  fin_cases i <;>
    norm_num [sevenNineCut, sevenNineRadialBounds, sevenNineUpper,
      sqrt_lower_4, sqrt_lower_5, sqrt_lower_6, sqrt_lower_7,
      sqrt_lower_8, sqrt_lower_9, sqrt_lower_10] <;>
    nlinarith [sqrt_lower_4, sqrt_lower_5, sqrt_lower_6, sqrt_lower_7,
      sqrt_lower_8, sqrt_lower_9, sqrt_lower_10]

def sevenNineRadius (i : Fin 7) : ℝ := Real.sqrt (i.1 + 4)

def sevenNineCenterRadius (P : Packing 7 (79 / 10 : ℝ)) (i : Fin 7) : ℝ :=
  pointNorm ((P.circles i).center)

lemma sevenNine_upper_of_packing
    (P : Packing 7 (79 / 10 : ℝ))
    (hRadius : ∀ i, (P.circles i).radius = sevenNineRadius i)
    (i : Fin 7) :
    sevenNineCenterRadius P i ≤ sevenNineUpper i := by
  have hc := P.contained i
  rcases hc with ⟨hr, hd⟩
  have hri : (P.circles i).radius = Real.sqrt (i.1 + 4) := by
    simpa [sevenNineRadius] using hRadius i
  have hR : 0 ≤ (79 / 10 : ℝ) - (P.circles i).radius := by
    exact sub_nonneg.mpr hr
  have hs : sevenNineCenterRadius P i ^ 2 ≤
      ((79 / 10 : ℝ) - (P.circles i).radius) ^ 2 := by
    rw [show sevenNineCenterRadius P i ^ 2 =
      (P.circles i).center.1 ^ 2 + (P.circles i).center.2 ^ 2 by
        exact pointNorm_sq _]
    simpa [distSq] using hd
  have h := (sq_le_sq₀ (pointNorm_nonneg _) hR).mp hs
  simpa [sevenNineCenterRadius, sevenNineUpper, hri] using h

lemma sevenNine_pair_radial_lower
    (P : Packing 7 (79 / 10 : ℝ))
    (hRadius : ∀ i, (P.circles i).radius = sevenNineRadius i)
    {i j : Fin 7} (hij : i ≠ j) :
    sevenNineRadius i + sevenNineRadius j ≤
      sevenNineCenterRadius P i + sevenNineCenterRadius P j := by
  have hs := P.separated hij
  have hsq :
      ((P.circles i).radius + (P.circles j).radius) ^ 2 ≤
        pointNorm ((P.circles i).center.1 - (P.circles j).center.1,
          (P.circles i).center.2 - (P.circles j).center.2) ^ 2 := by
    rw [pointNorm_sq]
    simpa [Separated, distSq] using hs
  have hdist := (sq_le_sq₀ (add_nonneg (P.circles i).radius_nonneg
      (P.circles j).radius_nonneg) (pointNorm_nonneg _)).mp hsq
  have htri := pointNorm_triangle (P.circles i).center (P.circles j).center
  simpa [sevenNineCenterRadius, hRadius] using hdist.trans htri

lemma sevenNine_lower_of_packing
    (P : Packing 7 (79 / 10 : ℝ))
    (hRadius : ∀ i, (P.circles i).radius = sevenNineRadius i)
    (i : Fin 7) :
    sevenNineLower i ≤ sevenNineCenterRadius P i := by
  let j10 : Fin 7 := ⟨6, by decide⟩
  let j9 : Fin 7 := ⟨5, by decide⟩
  by_cases hi : i.1 = 6
  · have hij : i ≠ j9 := by
      intro h
      have : i.1 = 5 := by simpa [j9] using congrArg Fin.val h
      omega
    have hp := sevenNine_pair_radial_lower P hRadius hij
    have hu := sevenNine_upper_of_packing P hRadius j9
    have hi_eq : i = j10 := by
      apply Fin.ext
      simpa [j10] using hi
    subst i
    norm_num [sevenNineRadius, sevenNineUpper, sevenNineLower, j9, j10] at hp hu ⊢
    nlinarith
  · have hij : i ≠ j10 := by
      intro h
      have : i.1 = 6 := by simpa [j10] using congrArg Fin.val h
      exact hi this
    have hp := sevenNine_pair_radial_lower P hRadius hij
    have hu := sevenNine_upper_of_packing P hRadius j10
    norm_num [sevenNineRadius, sevenNineUpper, sevenNineLower, j10] at hp hu ⊢
    have hi' : ¬ (i.1 = 6) := hi
    simp [sevenNineLower, hi'] at ⊢
    nlinarith

theorem sevenNine_packing_is_covered
    (P : Packing 7 (79 / 10 : ℝ))
    (hRadius : ∀ i, (P.circles i).radius = sevenNineRadius i) :
    ∃ state : Fin 7 → Nat,
      ∀ i,
        state i ≤ 1 ∧
        (sevenNineCut i (state i) 0 : ℝ) ≤ sevenNineCenterRadius P i ∧
        sevenNineCenterRadius P i ≤ (sevenNineCut i (state i) 1 : ℝ) := by
  apply sevenNine_global_radial_cover
  · exact fun i => sevenNine_lower_of_packing P hRadius i
  · exact fun i => sevenNine_upper_of_packing P hRadius i
  · exact sevenNine_endpoint_lower0
  · exact sevenNine_endpoint_mid
  · exact sevenNine_endpoint_upper1

end
end CirclePacking
