import CirclePacking.CosineTaylor
import CirclePacking.NineCircleCertificateChecker

namespace CirclePacking

open scoped BigOperators

theorem cosine_taylor_eighteen_remainder
    {a b x : ℝ}
    (hab : a < b)
    (hx : x ∈ Set.Icc a b) :
    ‖Real.cos x -
        taylorWithinEval Real.cos 18 (Set.Icc a b) a x‖
      ≤ (x - a) ^ 19 / ((Nat.factorial 18 : ℕ) : ℝ) := by
  have h := taylor_mean_remainder_bound (n := 18) (C := (1 : ℝ)) hab.le
      Real.contDiff_cos.contDiffOn hx (by
        intro y hy
        rw [show 18 + 1 = 19 by norm_num,
          Real.iteratedDerivWithin_cos_Icc 19 hab hy]
        simpa [Real.norm_eq_abs] using Real.abs_iteratedDeriv_cos_le_one 19 y)
  simpa using h

theorem cosine_taylor_eighteen_at_zero
    {b x : ℝ} (hb : 0 < b) :
    taylorWithinEval Real.cos 18 (Set.Icc 0 b) 0 x =
      Finset.sum (Finset.range 10) (fun k =>
        (-1 : ℝ)^k * x ^ (2 * k) /
          ((Nat.factorial (2 * k) : ℕ) : ℝ)) := by
  rw [taylor_within_apply]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial_zero,
    Nat.factorial_one, Nat.cast_one, inv_one]
  have hzero : (0 : ℝ) ∈ Set.Icc 0 b := ⟨le_rfl, hb.le⟩
  simp_rw [
    Real.iteratedDerivWithin_cos_Icc 0 hb hzero,
    Real.iteratedDerivWithin_cos_Icc 1 hb hzero,
    Real.iteratedDerivWithin_cos_Icc 2 hb hzero,
    Real.iteratedDerivWithin_cos_Icc 3 hb hzero,
    Real.iteratedDerivWithin_cos_Icc 4 hb hzero,
    Real.iteratedDerivWithin_cos_Icc 5 hb hzero,
    Real.iteratedDerivWithin_cos_Icc 6 hb hzero,
    Real.iteratedDerivWithin_cos_Icc 7 hb hzero,
    Real.iteratedDerivWithin_cos_Icc 8 hb hzero,
    Real.iteratedDerivWithin_cos_Icc 9 hb hzero,
    Real.iteratedDerivWithin_cos_Icc 10 hb hzero,
    Real.iteratedDerivWithin_cos_Icc 11 hb hzero,
    Real.iteratedDerivWithin_cos_Icc 12 hb hzero,
    Real.iteratedDerivWithin_cos_Icc 13 hb hzero,
    Real.iteratedDerivWithin_cos_Icc 14 hb hzero,
    Real.iteratedDerivWithin_cos_Icc 15 hb hzero,
    Real.iteratedDerivWithin_cos_Icc 16 hb hzero,
    Real.iteratedDerivWithin_cos_Icc 17 hb hzero,
    Real.iteratedDerivWithin_cos_Icc 18 hb hzero]
  norm_num [Real.iteratedDeriv_even_cos, Real.iteratedDeriv_odd_cos]
  ring

noncomputable def nineTaylorReal (ticks : Nat) : ℝ :=
  (nineTaylorNumerator ticks : ℝ) / (nineTaylorDenominator : ℝ)

noncomputable def nineTaylorRealStep (ticks : Nat) (total : ℝ) (k : Nat) : ℝ :=
  let term := (nineTaylorTermNumerator ticks k : ℝ) /
    (nineTaylorDenominator : ℝ)
  if k % 2 == 0 then total + term else total - term

theorem nineTaylorTerm_quotient (ticks k : Nat) (hk : k < 10) :
    (nineTaylorTermNumerator ticks k : ℝ) /
        (nineTaylorDenominator : ℝ) =
      ((ticks : ℝ) / nineAngleScale) ^ (2 * k) /
        ((Nat.factorial (2 * k) : ℕ) : ℝ) := by
  have hn : 2 * k ≤ 18 := by omega
  have hfac : Nat.factorial (2 * k) ∣ Nat.factorial 18 :=
    Nat.factorial_dvd_factorial hn
  have hfacmul :
      ((Nat.factorial 18 : ℕ) : ℝ) /
          (Nat.factorial (2 * k) : ℝ) *
          (Nat.factorial (2 * k) : ℝ) = Nat.factorial 18 := by
    rw [← Nat.cast_div_charZero hfac]
    exact_mod_cast Nat.div_mul_cancel hfac
  have hscale : (nineAngleScale : ℝ) ≠ 0 := by norm_num [nineAngleScale]
  have hfacne : (Nat.factorial (2 * k) : ℝ) ≠ 0 := by positivity
  have hpow :
      (nineAngleScale : ℝ) ^ (18 - 2 * k) *
          (nineAngleScale : ℝ) ^ (2 * k) =
        (nineAngleScale : ℝ) ^ 18 := by
    rw [← pow_add]
    congr 1
    omega
  unfold nineTaylorTermNumerator nineTaylorDenominator
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_div_charZero hfac]
  rw [div_pow, div_div]
  apply (div_eq_div_iff (by positivity) (by positivity)).2
  calc
    ((ticks : ℝ) ^ (2 * k) * (nineAngleScale : ℝ) ^ (18 - 2 * k) *
          (((Nat.factorial 18 : ℕ) : ℝ) /
            ((Nat.factorial (2 * k) : ℕ) : ℝ))) *
          ((nineAngleScale : ℝ) ^ (2 * k) *
            (Nat.factorial (2 * k) : ℝ))
        = (ticks : ℝ) ^ (2 * k) *
          ((nineAngleScale : ℝ) ^ (18 - 2 * k) *
            (nineAngleScale : ℝ) ^ (2 * k)) *
          ((((Nat.factorial 18 : ℕ) : ℝ) /
            ((Nat.factorial (2 * k) : ℕ) : ℝ)) *
            (Nat.factorial (2 * k) : ℝ)) := by ring
    _ = (ticks : ℝ) ^ (2 * k) *
          ((nineAngleScale : ℝ) ^ 18 * (Nat.factorial 18 : ℝ)) := by
        rw [hpow, hfacmul]
        ring

theorem nineTaylorFold_quotient (ticks : Nat) (l : List Nat) (init : Int) :
    ((l.foldl (nineTaylorNumeratorStep ticks) init : Int) : ℝ) /
        (nineTaylorDenominator : ℝ) =
      l.foldl (nineTaylorRealStep ticks)
        ((init : ℝ) / (nineTaylorDenominator : ℝ)) := by
  induction l generalizing init with
  | nil => simp [nineTaylorRealStep]
  | cons k rest ih =>
      simp only [List.foldl_cons]
      rw [ih (nineTaylorNumeratorStep ticks init k)]
      congr 1
      by_cases hk : k % 2 = 0
      · simp [nineTaylorNumeratorStep, nineTaylorRealStep, hk, add_div]
      · simp [nineTaylorNumeratorStep, nineTaylorRealStep, hk, sub_div]

theorem nineTaylorRealStep_eq_add_series_term (ticks k : Nat) (total : ℝ)
    (hk : k < 10) :
    nineTaylorRealStep ticks total k =
      total + (-1 : ℝ)^k * ((ticks : ℝ) / nineAngleScale) ^ (2 * k) /
        ((Nat.factorial (2 * k) : ℕ) : ℝ) := by
  have hterm := nineTaylorTerm_quotient ticks k hk
  have hsign : (-1 : ℝ)^k = if k % 2 = 0 then 1 else -1 := by
    rw [neg_one_pow_eq_pow_mod_two]
    split_ifs with h
    · simp [h]
    · have hm : k % 2 = 1 := by omega
      simp [hm]
  unfold nineTaylorRealStep
  rw [hsign]
  by_cases he : k % 2 = 0
  · simp [he, hterm]
  · simp [he, hterm, sub_eq_add_neg]
    ring

theorem nineTaylorRealFold_eq_seriesFold (ticks : Nat) (l : List Nat)
    (hbound : ∀ k ∈ l, k < 10) (total : ℝ) :
    l.foldl (nineTaylorRealStep ticks) total =
      l.foldl (fun acc k => acc + (-1 : ℝ)^k *
        ((ticks : ℝ) / nineAngleScale) ^ (2 * k) /
          ((Nat.factorial (2 * k) : ℕ) : ℝ)) total := by
  induction l generalizing total with
  | nil => simp
  | cons k rest ih =>
      have hk := hbound k (by simp)
      have hrest : ∀ j ∈ rest, j < 10 := by
        intro j hj
        exact hbound j (by simp [hj])
      simp only [List.foldl_cons]
      rw [ih hrest (nineTaylorRealStep ticks total k)]
      rw [nineTaylorRealStep_eq_add_series_term ticks k total hk]

theorem list_foldl_add_eq_sum_map {α : Type} [AddCommMonoid α]
    (l : List Nat) (f : Nat → α) (init : α) :
    l.foldl (fun acc k => acc + f k) init = init + (l.map f).sum := by
  induction l generalizing init with
  | nil => simp
  | cons k rest ih =>
      simp only [List.foldl_cons, List.map_cons, List.sum_cons]
      rw [ih]
      simp [add_assoc]

theorem list_range_map_sum_eq_finset_sum (n : Nat) (f : Nat → ℝ) :
    ((List.range n).map f).sum = ∑ k ∈ Finset.range n, f k := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.range_succ, List.map_append, List.sum_append,
        List.map_singleton, List.sum_singleton, ih, Finset.sum_range_succ]

theorem nineTaylorReal_eq_taylor_eighteen (ticks : Nat) :
    nineTaylorReal ticks =
      Finset.sum (Finset.range 10) (fun k =>
        (-1 : ℝ)^k * ((ticks : ℝ) / nineAngleScale) ^ (2 * k) /
          ((Nat.factorial (2 * k) : ℕ) : ℝ)) := by
  unfold nineTaylorReal nineTaylorNumerator
  rw [nineTaylorFold_quotient]
  simp only [Int.cast_zero, zero_div]
  have hbound : ∀ k ∈ List.range 10, k < 10 := by simp
  rw [nineTaylorRealFold_eq_seriesFold ticks (List.range 10) hbound 0]
  rw [list_foldl_add_eq_sum_map]
  simp only [zero_add]
  exact list_range_map_sum_eq_finset_sum 10 _

theorem nineTaylor_lower_cosine_with_error (ticks : Nat)
    (hticks : ticks ≤ 314159) :
    nineTaylorReal ticks -
        ((ticks : ℝ) / nineAngleScale) ^ 19 /
          ((Nat.factorial 18 : ℕ) : ℝ) ≤
      Real.cos ((ticks : ℝ) / nineAngleScale) := by
  rw [nineTaylorReal_eq_taylor_eighteen]
  let q : ℝ := (ticks : ℝ) / nineAngleScale
  have hq0 : 0 ≤ q := by positivity
  have hq4 : q ≤ 4 := by
    dsimp [q, nineAngleScale]
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 100000)).2
    have ht : ticks ≤ 400000 := by omega
    exact_mod_cast ht
  have hq : q ∈ Set.Icc 0 4 := ⟨hq0, hq4⟩
  have hrem := cosine_taylor_eighteen_remainder
    (a := 0) (b := 4) (x := q) (by norm_num) hq
  have hpoly := cosine_taylor_eighteen_at_zero (b := 4) (x := q) (by norm_num)
  rw [hpoly] at hrem
  have hlow :
      (Finset.sum (Finset.range 10) (fun k =>
        (-1 : ℝ)^k * q ^ (2 * k) /
          ((Nat.factorial (2 * k) : ℕ) : ℝ)) -
        q ^ 19 / ((Nat.factorial 18 : ℕ) : ℝ)) ≤ Real.cos q :=
    lower_bound_of_taylor_error (c :=
      Finset.sum (Finset.range 10) (fun k =>
        (-1 : ℝ)^k * q ^ (2 * k) /
          ((Nat.factorial (2 * k) : ℕ) : ℝ)) -
        q ^ 19 / ((Nat.factorial 18 : ℕ) : ℝ)) hrem (by nlinarith)
  simpa [q, nineAngleScale] using hlow

end CirclePacking
