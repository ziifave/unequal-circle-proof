import Mathlib.Basic.Real.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Algebraic core of the five-fold local barrier

This file formalizes the parts of the local argument that do not depend on
calculus: the max-of-two-slopes estimate, the odd five-cycle identity in
`ℓ¹`, and the rational positive margin after the Taylor remainder is charged.
The analytic Taylor estimates for the angle function are intentionally stated
separately; they are not assumed proved by this file.
-/

namespace CirclePacking

theorem fifteenMaxSlopeLower (c d s : ℝ) (hcd : c ≤ d) :
    c * |s| ≤ max (-c * s) (d * s) := by
  by_cases hs : 0 ≤ s
  · rw [abs_of_nonneg hs]
    exact le_trans (by nlinarith) (le_max_right (-c * s) (d * s))
  · have hs' : s < 0 := lt_of_not_ge hs
    rw [abs_of_neg hs']
    calc
      c * -s = -c * s := by ring
      _ ≤ max (-c * s) (d * s) := le_max_left _ _

theorem fifteenAbsAlternatingFive (a b c d e : ℝ) :
    |a - b + c - d + e| ≤ |a| + |b| + |c| + |d| + |e| := by
  have h₁ := abs_add_le ((((a + -b) + c) + -d)) e
  have h₂ := abs_add_le (((a + -b) + c)) (-d)
  have h₃ := abs_add_le (a + -b) c
  have h₄ := abs_add_le a (-b)
  simp only [abs_neg] at h₂ h₄
  calc
    |a - b + c - d + e| = |((((a + -b) + c) + -d) + e)| := by
      congr 1
    _ ≤ |(((a + -b) + c) + -d)| + |e| := h₁
    _ ≤ |((a + -b) + c)| + |d| + |e| := by linarith
    _ ≤ |(a + -b)| + |c| + |d| + |e| := by linarith [h₃]
    _ ≤ |a| + |b| + |c| + |d| + |e| := by linarith [h₄]

def fifteenNextFive (i : Fin 5) : Fin 5 :=
  ⟨(i.val + 1) % 5, Nat.mod_lt _ (by norm_num)⟩

def fifteenSigmaFive (x : Fin 5 → ℝ) (i : Fin 5) : ℝ :=
  x i + x (fifteenNextFive i)

def fifteenSumFive (x : Fin 5 → ℝ) : ℝ :=
  x 0 + x 1 + x 2 + x 3 + x 4

theorem fifteenSigmaFiveAlternatingIdentity (x : Fin 5 → ℝ) (i : Fin 5) :
    2 * x i = fifteenSigmaFive x i -
      fifteenSigmaFive x (fifteenNextFive i) +
      fifteenSigmaFive x (fifteenNextFive (fifteenNextFive i)) -
      fifteenSigmaFive x (fifteenNextFive (fifteenNextFive
        (fifteenNextFive i))) +
      fifteenSigmaFive x (fifteenNextFive (fifteenNextFive
        (fifteenNextFive (fifteenNextFive i)))) := by
  fin_cases i <;>
    simp [fifteenSigmaFive, fifteenNextFive] <;> ring_nf

theorem fifteenOddFiveCycleL1Indexed (x : Fin 5 → ℝ) :
    (2 / 5 : ℝ) * fifteenSumFive (fun i => |x i|) ≤
      fifteenSumFive (fun i => |fifteenSigmaFive x i|) := by
  let S := fifteenSumFive (fun i => |fifteenSigmaFive x i|)
  have hpoint (i : Fin 5) : 2 * |x i| ≤ S := by
    have hid := fifteenSigmaFiveAlternatingIdentity x i
    calc
      2 * |x i| = |2 * x i| := by rw [abs_mul]; norm_num
      _ = |fifteenSigmaFive x i -
          fifteenSigmaFive x (fifteenNextFive i) +
          fifteenSigmaFive x (fifteenNextFive (fifteenNextFive i)) -
          fifteenSigmaFive x (fifteenNextFive (fifteenNextFive
            (fifteenNextFive i))) +
          fifteenSigmaFive x (fifteenNextFive (fifteenNextFive
            (fifteenNextFive (fifteenNextFive i))))| := by rw [hid]
      _ ≤ |fifteenSigmaFive x i| +
          |fifteenSigmaFive x (fifteenNextFive i)| +
          |fifteenSigmaFive x (fifteenNextFive (fifteenNextFive i))| +
          |fifteenSigmaFive x (fifteenNextFive (fifteenNextFive
            (fifteenNextFive i)))| +
          |fifteenSigmaFive x (fifteenNextFive (fifteenNextFive
            (fifteenNextFive (fifteenNextFive i))))| :=
          fifteenAbsAlternatingFive _ _ _ _ _
      _ = S := by
        fin_cases i <;>
          simp [S, fifteenSumFive, fifteenSigmaFive, fifteenNextFive] <;> ring
  have h0 := hpoint 0
  have h1 := hpoint 1
  have h2 := hpoint 2
  have h3 := hpoint 3
  have h4 := hpoint 4
  dsimp [fifteenSumFive, S] at h0 h1 h2 h3 h4 ⊢
  nlinarith

def fifteenAbsFive (x0 x1 x2 x3 x4 : ℝ) : ℝ :=
  |x0| + |x1| + |x2| + |x3| + |x4|

theorem fifteenOddFiveCycleL1
    (x0 x1 x2 x3 x4 s0 s1 s2 s3 s4 : ℝ)
    (hs0 : s0 = x0 + x1) (hs1 : s1 = x1 + x2)
    (hs2 : s2 = x2 + x3) (hs3 : s3 = x3 + x4)
    (hs4 : s4 = x4 + x0) :
    (2 / 5 : ℝ) * fifteenAbsFive x0 x1 x2 x3 x4 ≤
      fifteenAbsFive s0 s1 s2 s3 s4 := by
  have h0id : 2 * x0 = s0 - s1 + s2 - s3 + s4 := by
    rw [hs0, hs1, hs2, hs3, hs4]
    ring
  have h1id : 2 * x1 = s1 - s2 + s3 - s4 + s0 := by
    rw [hs0, hs1, hs2, hs3, hs4]
    ring
  have h2id : 2 * x2 = s2 - s3 + s4 - s0 + s1 := by
    rw [hs0, hs1, hs2, hs3, hs4]
    ring
  have h3id : 2 * x3 = s3 - s4 + s0 - s1 + s2 := by
    rw [hs0, hs1, hs2, hs3, hs4]
    ring
  have h4id : 2 * x4 = s4 - s0 + s1 - s2 + s3 := by
    rw [hs0, hs1, hs2, hs3, hs4]
    ring
  have h0 : 2 * |x0| ≤ |s0| + |s1| + |s2| + |s3| + |s4| := by
    calc
      2 * |x0| = |2 * x0| := by rw [abs_mul]; norm_num
      _ = |s0 - s1 + s2 - s3 + s4| := by rw [h0id]
      _ ≤ _ := fifteenAbsAlternatingFive s0 s1 s2 s3 s4
  have h1 : 2 * |x1| ≤ |s0| + |s1| + |s2| + |s3| + |s4| := by
    calc
      2 * |x1| = |2 * x1| := by rw [abs_mul]; norm_num
      _ = |s1 - s2 + s3 - s4 + s0| := by rw [h1id]
      _ ≤ _ := by
        simpa [add_assoc, add_comm, add_left_comm] using
          fifteenAbsAlternatingFive s1 s2 s3 s4 s0
  have h2 : 2 * |x2| ≤ |s0| + |s1| + |s2| + |s3| + |s4| := by
    calc
      2 * |x2| = |2 * x2| := by rw [abs_mul]; norm_num
      _ = |s2 - s3 + s4 - s0 + s1| := by rw [h2id]
      _ ≤ _ := by
        simpa [add_assoc, add_comm, add_left_comm] using
          fifteenAbsAlternatingFive s2 s3 s4 s0 s1
  have h3 : 2 * |x3| ≤ |s0| + |s1| + |s2| + |s3| + |s4| := by
    calc
      2 * |x3| = |2 * x3| := by rw [abs_mul]; norm_num
      _ = |s3 - s4 + s0 - s1 + s2| := by rw [h3id]
      _ ≤ _ := by
        simpa [add_assoc, add_comm, add_left_comm] using
          fifteenAbsAlternatingFive s3 s4 s0 s1 s2
  have h4 : 2 * |x4| ≤ |s0| + |s1| + |s2| + |s3| + |s4| := by
    calc
      2 * |x4| = |2 * x4| := by rw [abs_mul]; norm_num
      _ = |s4 - s0 + s1 - s2 + s3| := by rw [h4id]
      _ ≤ _ := by
        simpa [add_assoc, add_comm, add_left_comm] using
          fifteenAbsAlternatingFive s4 s0 s1 s2 s3
  unfold fifteenAbsFive
  nlinarith

theorem fifteenSquareLeEtaAbs (x eta : ℝ)
    (hx : |x| ≤ eta) :
    x ^ 2 ≤ eta * |x| := by
  have hprod := mul_nonneg (sub_nonneg.mpr hx) (abs_nonneg x)
  nlinarith [sq_abs x]

theorem fifteenTaylorPairMaxLower
    (base c d s error h k : ℝ) (hcd : c ≤ d)
    (hh : base - c * s - error ≤ h)
    (hk : base + d * s - error ≤ k) :
    base + c * |s| - error ≤ max h k := by
  by_cases hs : 0 ≤ s
  · have habs : |s| = s := abs_of_nonneg hs
    have hsel : base + c * |s| - error ≤ k := by
      rw [habs]
      nlinarith
    exact le_trans hsel (le_max_right h k)
  · have hs' : s < 0 := lt_of_not_ge hs
    have habs : |s| = -s := abs_of_neg hs'
    have hsel : base + c * |s| - error ≤ h := by
      rw [habs]
      nlinarith
    exact le_trans hsel (le_max_left h k)

theorem fifteenLocalBarrierRationalMargin :
    (2 / 5 : ℝ) * (21 / 50) - 5 * (11 / 500) = 29 / 500 := by
  norm_num

theorem fifteenLocalBarrierPositiveMargin (c : ℝ)
    (hc : (21 / 50 : ℝ) < c) :
    (29 / 500 : ℝ) < (2 / 5) * c - 5 * (11 / 500) := by
  norm_num at hc ⊢
  nlinarith

end CirclePacking
