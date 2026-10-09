import CirclePacking.FifteenStage3Certificate

namespace CirclePacking

def fifteenStage3Batch005Source : String :=
  include_str "../../../../problems/packing-15-equal-disks-in-a-circle/candidate_bundle/stage3_lean_batch_005.txt"

def fifteenStage3Batch005Patterns : List String := [
  "000001001010111",
  "000001001011011",
  "000001001011101",
  "000001001101011",
  "000001001101101",
  "000001001110101",
  "000001010010111",
  "000001010011011",
  "000001010011101",
  "000001010100111"
]

def fifteenStage3Batch005Checks : Bool :=
  fifteenStage3CheckBatch fifteenStage3Batch005Source fifteenStage3Batch005Patterns

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fifteenStage3Batch005_checks : fifteenStage3Batch005Checks = true := by
  native_decide

end CirclePacking
