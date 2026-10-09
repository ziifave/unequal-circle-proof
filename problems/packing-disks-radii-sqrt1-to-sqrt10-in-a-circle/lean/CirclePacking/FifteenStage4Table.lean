import CirclePacking.FifteenTickBounds

/-! Exact rational replay of the Stage 4 angle-tick table. -/

namespace CirclePacking

def fifteenStage4Bins : Array FifteenInterval := #[
  (fifteenRational 0 1, fifteenRational 1 2),
  (fifteenRational 1 2, fifteenRational 1 1),
  (fifteenRational 1 1, fifteenRational 3 2),
  (fifteenRational 3 2, fifteenRational 8 5),
  (fifteenRational 8 5, fifteenRational 5 3),
  (fifteenRational 5 3, fifteenRational 17 10),
  (fifteenRational 17 10, fifteenRational 37 20),
  (fifteenRational 37 20, fifteenRational 2 1),
  (fifteenRational 2 1, fifteenRational 43 20),
  (fifteenRational 43 20, fifteenRational 23 10),
  (fifteenRational 23 10, fifteenRational 2385432 1000000),
  (fifteenRational 35213569647 10000000000,
    fifteenRational 35213569648 10000000000)
]

def fifteenStage4Q : Array (Array Nat) := #[
  #[8700,8700,8700,6746,6142,5883,4896,4047,0,0,0,0],
  #[8700,8700,5105,4784,4585,4488,4077,3690,3228,2344,1738,0],
  #[8700,5105,4086,3923,3818,3767,3541,3321,3105,2889,2720,0],
  #[6746,4784,3923,3780,3688,3642,3442,3245,3051,2856,2744,0],
  #[6142,4585,3818,3688,3603,3561,3376,3194,3014,2832,2727,656],
  #[5883,4488,3767,3642,3561,3521,3344,3169,2994,2819,2717,868],
  #[4896,4077,3541,3442,3376,3344,3198,3051,2904,2754,2668,950],
  #[4047,3690,3321,3245,3194,3169,3051,2932,2809,2682,2609,1214],
  #[0,3228,3105,3051,3014,2994,2904,2809,2709,2604,2541,1383],
  #[0,2344,2889,2856,2832,2819,2754,2682,2604,2518,2467,1499],
  #[0,1738,2720,2744,2727,2717,2668,2609,2541,2467,2422,1579],
  #[0,0,0,0,656,868,950,1214,1383,1499,1579,1612]
]

def fifteenStage4PairTickValid (i j : Nat) : Bool := Id.run do
  let q := (fifteenStage4Q[i]!)[j]!
  let x := fifteenStage4Bins[i]!
  let y := fifteenStage4Bins[j]!
  if q == 0 then return true
  if x.2 + y.2 < 2 then return i < 2 && j < 2 && q == 8700
  return fifteenTickCertificateValid x y (i == 0 || j == 0) false q

def fifteenStage4TableValid : Bool :=
  (List.range 12).all fun i => (List.range 12).all fun j =>
    fifteenStage4PairTickValid i j

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fifteenStage4Table_valid : fifteenStage4TableValid = true := by
  native_decide

end CirclePacking
