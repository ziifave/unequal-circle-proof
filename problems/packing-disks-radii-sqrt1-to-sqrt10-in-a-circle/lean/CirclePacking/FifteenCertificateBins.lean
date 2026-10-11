import CirclePacking.FifteenTickBounds

/-! Shared rational radial interval table for the exact certificate and its
geometric handoff.  Keeping it separate avoids importing the large JSON
certificate just to reason about interval ownership. -/

namespace CirclePacking

def fifteenBins : Array FifteenInterval := #[
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

end CirclePacking
