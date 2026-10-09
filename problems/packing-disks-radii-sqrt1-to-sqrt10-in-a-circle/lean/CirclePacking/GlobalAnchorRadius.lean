import CirclePacking.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt

namespace CirclePacking

noncomputable section

/-! A two-anchor lower bound used by the global certificate.  The certificate
   supplies the small radial upper bound for disk 10; this file checks the
   geometric implication from that bound and the two circle constraints. -/

def globalPointNorm (p : Point) : ℝ := Real.sqrt (p.1 ^ 2 + p.2 ^ 2)

lemma globalPointNorm_nonneg (p : Point) : 0 ≤ globalPointNorm p :=
  Real.sqrt_nonneg _

lemma globalPointNorm_sq (p : Point) :
    globalPointNorm p ^ 2 = p.1 ^ 2 + p.2 ^ 2 := by
  dsimp [globalPointNorm]
  rw [Real.sq_sqrt]
  positivity

lemma globalPointNorm_triangle (p q : Point) :
    globalPointNorm (p.1 - q.1, p.2 - q.2) ≤
      globalPointNorm p + globalPointNorm q := by
  let a := globalPointNorm p
  let b := globalPointNorm q
  have ha : a ^ 2 = p.1 ^ 2 + p.2 ^ 2 := globalPointNorm_sq p
  have hb : b ^ 2 = q.1 ^ 2 + q.2 ^ 2 := globalPointNorm_sq q
  have hab : 0 ≤ a * b := mul_nonneg (globalPointNorm_nonneg p)
    (globalPointNorm_nonneg q)
  let dot := p.1 * q.1 + p.2 * q.2
  have hdet : 0 ≤ (p.1 * q.2 - p.2 * q.1) ^ 2 := sq_nonneg _
  have hdotSq : dot ^ 2 ≤ (a * b) ^ 2 := by
    have hid : (a * b) ^ 2 - dot ^ 2 =
        (p.1 * q.2 - p.2 * q.1) ^ 2 := by
      rw [mul_pow, ha, hb]
      dsimp [dot]
      ring
    nlinarith [hid]
  have hdotAbs : |dot| ≤ a * b := by
    apply (sq_le_sq₀ (abs_nonneg dot) hab).mp
    simpa only [sq_abs] using hdotSq
  have hdotLower : -a * b ≤ dot := by
    have h := (abs_le.mp hdotAbs).1
    dsimp [dot] at h ⊢
    linarith
  have hdistSq :
      (p.1 - q.1) ^ 2 + (p.2 - q.2) ^ 2 ≤ (a + b) ^ 2 := by
    have hid : (p.1 - q.1) ^ 2 + (p.2 - q.2) ^ 2 =
        a ^ 2 + b ^ 2 - 2 * dot := by
      rw [ha, hb]
      dsimp [dot]
      ring
    rw [show (a + b) ^ 2 = a ^ 2 + b ^ 2 + 2 * a * b by ring]
    linarith
  have hnormSq :
      globalPointNorm (p.1 - q.1, p.2 - q.2) ^ 2 ≤
        (globalPointNorm p + globalPointNorm q) ^ 2 := by
    rw [globalPointNorm_sq]
    simpa [a, b] using hdistSq
  exact (sq_le_sq₀ (globalPointNorm_nonneg _)
    (add_nonneg (globalPointNorm_nonneg p) (globalPointNorm_nonneg q))).mp hnormSq

theorem global_anchor_pair_radius_floor
    {R : ℝ} (P : Packing 10 R)
    (hRadius9 : (P.circles ⟨8, by omega⟩).radius = 3)
    (hRadius10 : (P.circles ⟨9, by omega⟩).radius = Real.sqrt 10)
    (hCenter10 : globalPointNorm (P.circles ⟨9, by omega⟩).center ≤
      (2253 / 2000 : ℝ)) :
    (15947 / 2000 : ℝ) < R := by
  let i9 : Fin 10 := ⟨8, by omega⟩
  let i10 : Fin 10 := ⟨9, by omega⟩
  let p9 := (P.circles i9).center
  let p10 := (P.circles i10).center
  have hr9 : (P.circles i9).radius = 3 := by
    simpa [i9] using hRadius9
  have hr10 : (P.circles i10).radius = Real.sqrt 10 := by
    simpa [i10] using hRadius10
  have hcontained := P.contained i9
  change (P.circles i9).radius ≤ R ∧
    distSq (P.circles i9).center (0, 0) ≤
      (R - (P.circles i9).radius) ^ 2 at hcontained
  rw [hr9] at hcontained
  have hRlower : 3 ≤ R := by
    exact hcontained.1
  have hcenter9sq : globalPointNorm p9 ^ 2 ≤ (R - 3) ^ 2 := by
    rw [globalPointNorm_sq]
    simpa [p9, distSq] using hcontained.2
  have hcenter9 : 3 + globalPointNorm p9 ≤ R := by
    have hrad : 0 ≤ R - 3 := by linarith
    have hnorm := (sq_le_sq₀ (globalPointNorm_nonneg p9) hrad).mp hcenter9sq
    linarith
  have hsep := P.separated (show i9 ≠ i10 by decide)
  have hsep' : Separated (P.circles i9) (P.circles i10) := hsep
  change ((P.circles i9).radius + (P.circles i10).radius) ^ 2 ≤
    distSq (P.circles i9).center (P.circles i10).center at hsep'
  rw [hr9, hr10] at hsep'
  have hsepSq : (3 + Real.sqrt 10) ^ 2 ≤ distSq p9 p10 := by
    simpa [Separated, p9, p10] using hsep'
  have hdiffSq : globalPointNorm (p9.1 - p10.1, p9.2 - p10.2) ^ 2 =
      distSq p9 p10 := by
    rw [globalPointNorm_sq]
    rfl
  have hdiff : 3 + Real.sqrt 10 ≤
      globalPointNorm (p9.1 - p10.1, p9.2 - p10.2) := by
    apply (sq_le_sq₀ (by positivity) (globalPointNorm_nonneg _)).mp
    rw [hdiffSq]
    exact hsepSq
  have hcenters := le_trans hdiff (globalPointNorm_triangle p9 p10)
  have hsqrt10 : (31 / 10 : ℝ) < Real.sqrt 10 := by
    have hsqrtSq : (Real.sqrt 10) ^ 2 = 10 := by
      rw [Real.sq_sqrt]
      norm_num
    have hsqrtPos : 0 ≤ Real.sqrt 10 := Real.sqrt_nonneg _
    by_contra hnot
    have hle : Real.sqrt 10 ≤ (31 / 10 : ℝ) := le_of_not_gt hnot
    have hsquares := (sq_le_sq₀ hsqrtPos (by norm_num : 0 ≤ (31 / 10 : ℝ))).mpr hle
    nlinarith [hsquares, hsqrtSq]
  have hnumeric :
      (15947 / 2000 : ℝ) < 6 + Real.sqrt 10 - 2253 / 2000 := by
    norm_num
    linarith
  have hCenter10' : globalPointNorm p10 ≤ (2253 / 2000 : ℝ) := by
    simpa [i10, p10] using hCenter10
  have hRnumeric : 6 + Real.sqrt 10 - 2253 / 2000 ≤ R := by
    dsimp [p9, p10, i9, i10] at hcenters hcenter9 hCenter10'
    nlinarith [hCenter10']
  exact lt_of_lt_of_le hnumeric hRnumeric

end
end CirclePacking
