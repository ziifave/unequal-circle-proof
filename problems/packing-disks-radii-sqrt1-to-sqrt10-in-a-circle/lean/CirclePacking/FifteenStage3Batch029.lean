import CirclePacking.FifteenStage3Certificate

namespace CirclePacking

def fifteenStage3Batch029Source : String :=
  include_str "../../../../problems/packing-15-equal-disks-in-a-circle/candidate_bundle/stage3_lean_batch_029.txt"

def fifteenStage3Batch029Patterns : List String := [
  "001001010110111",
  "001001010111011",
  "001001010111101",
  "001001011001111",
  "001001011010111",
  "001001011011011",
  "001001011011101",
  "001001011100111",
  "001001011101011",
  "001001011110011"
]

def fifteenStage3Batch029Checks : Bool :=
  fifteenStage3CheckBatch fifteenStage3Batch029Source fifteenStage3Batch029Patterns

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fifteenStage3Batch029_checks : fifteenStage3Batch029Checks = true := by
  native_decide

end CirclePacking
