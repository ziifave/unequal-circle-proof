import CirclePacking.FifteenStage3Certificate

namespace CirclePacking

def fifteenStage3Batch012Source : String :=
  include_str "../../../../problems/packing-15-equal-disks-in-a-circle/candidate_bundle/stage3_lean_batch_012.txt"

def fifteenStage3Batch012Patterns : List String := [
  "000100100010111",
  "000100100011011",
  "000100100100111",
  "000100100110011",
  "000100100111001",
  "000100101000111",
  "000100101001011",
  "000100101001101",
  "000100101010011",
  "000100101100011"
]

def fifteenStage3Batch012Checks : Bool :=
  fifteenStage3CheckBatch fifteenStage3Batch012Source fifteenStage3Batch012Patterns

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fifteenStage3Batch012_checks : fifteenStage3Batch012Checks = true := by
  native_decide

end CirclePacking
