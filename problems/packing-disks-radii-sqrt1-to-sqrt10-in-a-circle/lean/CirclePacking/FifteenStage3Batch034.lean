import CirclePacking.FifteenStage3Certificate

namespace CirclePacking

def fifteenStage3Batch034Source : String :=
  include_str "../../../../problems/packing-15-equal-disks-in-a-circle/candidate_bundle/stage3_lean_batch_034.txt"

def fifteenStage3Batch034Patterns : List String := [
  "001011001100111",
  "001011001101011",
  "001011001101101",
  "001011001110011",
  "001011010010111",
  "001011010011011",
  "001011010101011",
  "001011010101101",
  "001011010110011",
  "001011011010011"
]

def fifteenStage3Batch034Checks : Bool :=
  fifteenStage3CheckBatch fifteenStage3Batch034Source fifteenStage3Batch034Patterns

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fifteenStage3Batch034_checks : fifteenStage3Batch034Checks = true := by
  native_decide

end CirclePacking
