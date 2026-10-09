import CirclePacking.Angle

namespace CirclePacking

lemma endpoint_numerator_bound
    {L U x y C c : ℝ}
    (hL : L ≤ x) (hU : x ≤ U)
    (hleft : L ^ 2 + C ≤ c * (2 * L * y))
    (hright : U ^ 2 + C ≤ c * (2 * U * y)) :
    x ^ 2 + C ≤ c * (2 * x * y) := by
  by_cases hEq : L = U
  · have hx : x = L := le_antisymm (by simpa [hEq] using hU) hL
    simpa [hx, hEq] using hleft
  · have hLU0 : L ≤ U := le_trans hL hU
    have hLU : L < U := lt_of_le_of_ne hLU0 hEq
    have hxl : 0 ≤ x - L := sub_nonneg.mpr hL
    have hux : 0 ≤ U - x := sub_nonneg.mpr hU
    have hUL : 0 ≤ U - L := (sub_pos.mpr hLU).le
    have hmul : 0 ≤ (U - x) * (x - L) * (U - L) := by positivity
    have hconv :
        (U - L) * (x ^ 2 + C) ≤
          (U - x) * (L ^ 2 + C) + (x - L) * (U ^ 2 + C) := by
      nlinarith [hmul]
    have hleft' := mul_le_mul_of_nonneg_left hleft hux
    have hright' := mul_le_mul_of_nonneg_left hright hxl
    have hsum :
        (U - x) * (L ^ 2 + C) + (x - L) * (U ^ 2 + C) ≤
          (U - L) * (c * (2 * x * y)) := by
      nlinarith
    nlinarith

theorem corner_touch_cosine_bound
    {L_a U_a L_b U_b a b d c : ℝ}
    (haL : L_a ≤ a) (haU : a ≤ U_a) (hbL : L_b ≤ b) (hbU : b ≤ U_b)
    (hLa : 0 < L_a) (hLb : 0 < L_b)
    (h00 : L_a ^ 2 + L_b ^ 2 - d ^ 2 ≤ c * (2 * L_a * L_b))
    (h01 : L_a ^ 2 + U_b ^ 2 - d ^ 2 ≤ c * (2 * L_a * U_b))
    (h10 : U_a ^ 2 + L_b ^ 2 - d ^ 2 ≤ c * (2 * U_a * L_b))
    (h11 : U_a ^ 2 + U_b ^ 2 - d ^ 2 ≤ c * (2 * U_a * U_b)) :
    touchCosine a b d ≤ c := by
  have hbpos : 0 < b := lt_of_lt_of_le hLb hbL
  have ha_pos : 0 < a := lt_of_lt_of_le hLa haL
  have hL : L_a ^ 2 + b ^ 2 - d ^ 2 ≤ c * (2 * L_a * b) := by
    have h := endpoint_numerator_bound (L := L_b) (U := U_b) (x := b)
      (y := L_a) (C := L_a ^ 2 - d ^ 2) (c := c) hbL hbU
      (by nlinarith [h00]) (by nlinarith [h01])
    nlinarith [h]
  have hU : U_a ^ 2 + b ^ 2 - d ^ 2 ≤ c * (2 * U_a * b) := by
    have h := endpoint_numerator_bound (L := L_b) (U := U_b) (x := b)
      (y := U_a) (C := U_a ^ 2 - d ^ 2) (c := c) hbL hbU
      (by nlinarith [h10]) (by nlinarith [h11])
    nlinarith [h]
  have hnum : a ^ 2 + b ^ 2 - d ^ 2 ≤ c * (2 * a * b) := by
    have h := endpoint_numerator_bound (L := L_a) (U := U_a) (x := a)
      (y := b) (C := b ^ 2 - d ^ 2) (c := c) haL haU
      (by nlinarith [hL]) (by nlinarith [hU])
    nlinarith [h]
  apply (div_le_iff₀ (mul_pos (mul_pos (by norm_num) ha_pos) hbpos)).mpr
  simpa [touchCosine, mul_assoc, mul_left_comm, mul_comm] using hnum

end CirclePacking
