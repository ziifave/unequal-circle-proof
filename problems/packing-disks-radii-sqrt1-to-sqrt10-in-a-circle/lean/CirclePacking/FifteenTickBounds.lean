import Lean

/-!
# Exact rational angle-tick calculations for the 15-disk certificate

This module replays the rational calculation that assigns an integer angle
tick to a pair of radius intervals.  The formula uses the cosine-rule cap at
the four corners of a positive radius box and the same degree-18 Taylor lower
polynomial as the independent Python checker.  The exact-zero and
positive-zero interval types are kept separate because the polar angle is not
defined at the origin.

The analytic proof that the Taylor polynomial is a lower bound for cosine,
and the geometric proof that the corner cap bounds every feasible contact
angle, remain separate lemmas to be connected in a subsequent layer.
-/

namespace CirclePacking

abbrev FifteenInterval := Rat × Rat

def fifteenRational (n d : Nat) : Rat :=
  if hd : d = 0 then 0 else Rat.normalize (Int.ofNat n) d hd

def fifteenCosineLower (q : Nat) : Rat :=
  let x := fifteenRational q 2800
  1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720 + x ^ 8 / 40320 -
    x ^ 10 / 3628800 + x ^ 12 / 479001600 - x ^ 14 / 87178291200 +
    x ^ 16 / 20922789888000 - x ^ 18 / 6402373705728000 -
    x ^ 19 / 6402373705728000

def fifteenCosineRuleCap (a b : Rat) : Rat :=
  (a ^ 2 + b ^ 2 - 4) / (2 * a * b)

def fifteenMax4 (a b c d : Rat) : Rat := max (max a b) (max c d)

def fifteenBoxCosineCap (x y : FifteenInterval) : Rat :=
  fifteenMax4 (fifteenCosineRuleCap x.1 y.1)
    (fifteenCosineRuleCap x.1 y.2)
    (fifteenCosineRuleCap x.2 y.1)
    (fifteenCosineRuleCap x.2 y.2)

def fifteenPositiveZeroCosineCap (x y : FifteenInterval) : Rat := Id.run do
  let zeroInterval := if x.1 == 0 then x else y
  let otherInterval := if x.1 == 0 then y else x
  if otherInterval.2 ≤ 2 && 0 < otherInterval.2 then
    return fifteenCosineRuleCap zeroInterval.2 otherInterval.2
  return 1

def fifteenTickCertificateValid (x y : FifteenInterval)
    (positiveZero exactZero : Bool) (ticks : Nat) : Bool := Id.run do
  if x.2 + y.2 < 2 then return false
  if exactZero then return ticks == 0
  let upper := if positiveZero then
      fifteenPositiveZeroCosineCap x y
    else
      fifteenBoxCosineCap x y
  if upper ≥ 1 then return ticks == 0
  if upper ≤ -1 then return ticks == 8700
  return ticks ≤ 8790 && fifteenCosineLower ticks ≥ upper

end CirclePacking
