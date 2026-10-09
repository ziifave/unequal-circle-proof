import CirclePacking.FifteenStage3Certificate

namespace CirclePacking

def fifteenStage3Batch030Source : String :=
  include_str "../../../../problems/packing-15-equal-disks-in-a-circle/candidate_bundle/stage3_lean_batch_030.txt"

def fifteenStage3Batch030Patterns : List String := [
  "001001100101111",
  "001001100110111",
  "001001100111011",
  "001001101001111",
  "001001101010111",
  "001001101011011",
  "001001101100111",
  "001001110010111",
  "001010010101111",
  "001010010110111"
]

def fifteenStage3Batch030Checks : Bool :=
  fifteenStage3CheckBatch fifteenStage3Batch030Source fifteenStage3Batch030Patterns

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fifteenStage3Batch030_checks : fifteenStage3Batch030Checks = true := by
  native_decide

end CirclePacking
