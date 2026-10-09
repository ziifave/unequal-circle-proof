import CirclePacking.FifteenTickBounds

/-! Exact rational replay of the Stage 3 angle-tick table. -/

namespace CirclePacking

def fifteenStage3Bins : Array FifteenInterval := #[
  (fifteenRational 0 1, fifteenRational 1 2),
  (fifteenRational 1 2, fifteenRational 1 1),
  (fifteenRational 1 1, fifteenRational 3 2),
  (fifteenRational 3 2, fifteenRational 8 5),
  (fifteenRational 8 5, fifteenRational 5 3),
  (fifteenRational 5 3, fifteenRational 2 1),
  (fifteenRational 2 1, fifteenRational 2385432 1000000),
  (fifteenRational 35213569647 10000000000,
    fifteenRational 35213569648 10000000000)
]

def fifteenStage3Q : Array (Array Nat) := #[
  #[8700,8700,8700,6746,6142,4047,0,0],
  #[8700,8700,5105,4784,4585,3690,1738,0],
  #[8700,5105,4086,3923,3818,3321,2720,0],
  #[6746,4784,3923,3780,3688,3245,2744,0],
  #[6142,4585,3818,3688,3603,3194,2727,656],
  #[4047,3690,3321,3245,3194,2932,2609,868],
  #[0,1738,2720,2744,2727,2609,2422,1383],
  #[0,0,0,0,656,868,1383,1612]
]

def fifteenStage3PairTickValid (i j : Nat) : Bool := Id.run do
  let q := (fifteenStage3Q[i]!)[j]!
  let x := fifteenStage3Bins[i]!
  let y := fifteenStage3Bins[j]!
  if q == 0 then return true
  if x.2 + y.2 < 2 then return i < 2 && j < 2 && q == 8700
  return fifteenTickCertificateValid x y (i == 0 || j == 0) false q

def fifteenStage3TableValid : Bool :=
  (List.range 8).all fun i => (List.range 8).all fun j =>
    fifteenStage3PairTickValid i j

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fifteenStage3Table_valid : fifteenStage3TableValid = true := by
  native_decide

end CirclePacking
