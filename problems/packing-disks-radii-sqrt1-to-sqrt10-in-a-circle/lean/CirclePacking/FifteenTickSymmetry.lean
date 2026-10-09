import Mathlib.Tactic.Ring
import CirclePacking.FifteenTickBounds
namespace CirclePacking

theorem fifteenCosineRuleCap_swap (a b : Rat) : fifteenCosineRuleCap a b = fifteenCosineRuleCap b a := by
  unfold fifteenCosineRuleCap
  congr 1 <;> ring

theorem fifteenMax4_middle_swap (a b c d : Rat) :
    fifteenMax4 a b c d = fifteenMax4 a c b d := by
  unfold fifteenMax4
  apply le_antisymm
  · apply max_le
    · apply max_le
      · exact le_trans (le_max_left a c) (le_max_left (max a c) (max b d))
      · exact le_trans (le_max_left b d) (le_max_right (max a c) (max b d))
    · apply max_le
      · exact le_trans (le_max_right a c) (le_max_left (max a c) (max b d))
      · exact le_trans (le_max_right b d) (le_max_right (max a c) (max b d))
  · apply max_le
    · apply max_le
      · exact le_trans (le_max_left a b) (le_max_left (max a b) (max c d))
      · exact le_trans (le_max_left c d) (le_max_right (max a b) (max c d))
    · apply max_le
      · exact le_trans (le_max_right a b) (le_max_left (max a b) (max c d))
      · exact le_trans (le_max_right c d) (le_max_right (max a b) (max c d))

theorem fifteenBoxCosineCap_swap (x y : FifteenInterval) :
    fifteenBoxCosineCap x y = fifteenBoxCosineCap y x := by
  unfold fifteenBoxCosineCap
  rw [fifteenCosineRuleCap_swap x.1 y.1, fifteenCosineRuleCap_swap x.1 y.2,
      fifteenCosineRuleCap_swap x.2 y.1, fifteenCosineRuleCap_swap x.2 y.2]
  exact fifteenMax4_middle_swap _ _ _ _

theorem fifteenTickCertificateValid_swap (x y : FifteenInterval) (ticks : Nat) :
    fifteenTickCertificateValid x y false false ticks =
      fifteenTickCertificateValid y x false false ticks := by
  simp [fifteenTickCertificateValid, add_comm, fifteenBoxCosineCap_swap]

end CirclePacking
