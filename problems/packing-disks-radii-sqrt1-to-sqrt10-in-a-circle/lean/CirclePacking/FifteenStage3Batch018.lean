import CirclePacking.FifteenStage3Certificate

namespace CirclePacking

def fifteenStage3Batch018Source : String :=
  include_str "../../../../problems/packing-15-equal-disks-in-a-circle/candidate_bundle/stage3_lean_batch_018.txt"

def fifteenStage3Batch018Patterns : List String := [
  "000011010010111",
  "000011010011011",
  "000011010100111",
  "000011010101011",
  "000100100101111",
  "000100100110111",
  "000100100111011",
  "000100100111101",
  "000100101001111",
  "000100101010111"
]

def fifteenStage3Batch018Checks : Bool :=
  fifteenStage3CheckBatch fifteenStage3Batch018Source fifteenStage3Batch018Patterns

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fifteenStage3Batch018_checks : fifteenStage3Batch018Checks = true := by
  native_decide

end CirclePacking
