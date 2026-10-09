import CirclePacking.FifteenStage3Certificate

namespace CirclePacking

def fifteenStage3Batch035Source : String :=
  include_str "../../../../problems/packing-15-equal-disks-in-a-circle/candidate_bundle/stage3_lean_batch_035.txt"

def fifteenStage3Batch035Patterns : List String := [
  "001011100110011",
  "001100110011011",
  "001100110101011",
  "001101010101011",
  "010101010101011"
]

def fifteenStage3Batch035Checks : Bool :=
  fifteenStage3CheckBatch fifteenStage3Batch035Source fifteenStage3Batch035Patterns

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fifteenStage3Batch035_checks : fifteenStage3Batch035Checks = true := by
  native_decide

end CirclePacking
