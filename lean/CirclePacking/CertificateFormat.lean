import CirclePacking.Angular

namespace CirclePacking

open scoped BigOperators

/-! The Lean-facing shape of a rational angular certificate.

The JSON exporter supplies the finite arrays, including a rational upper bound
for each contact cosine.  The fields below are the
obligations that a replay theorem must discharge; in particular, the cosine
lower-bound obligations are not trusted merely because they came from MPFI.
-/

structure RationalAngularCertificate (g k : ℕ) where
  row : Fin g → Fin k → ℚ
  lower : Fin g → ℚ
  cosineUpper : Fin g → ℚ
  weight : Fin g → ℚ
  gap_nonneg : Prop
  gap_sum : Prop
  cosine_bounds : Prop
  dual_bounds : Prop
  positive_margin : Prop

end CirclePacking
