import CirclePacking.FifteenStage3Certificate

namespace CirclePacking

def fifteenStage3Batch009Source : String :=
  include_str "../../../../problems/packing-15-equal-disks-in-a-circle/candidate_bundle/stage3_lean_batch_009.txt"

def fifteenStage3Batch009Patterns : List String := [
  "000010100010111",
  "000010100011011",
  "000010100011101",
  "000010100100111",
  "000010100101011",
  "000010100101101",
  "000010100110011",
  "000010100110101",
  "000010101000111",
  "000010101001011"
]

def fifteenStage3Batch009Checks : Bool :=
  fifteenStage3CheckBatch fifteenStage3Batch009Source fifteenStage3Batch009Patterns

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fifteenStage3Batch009_checks : fifteenStage3Batch009Checks = true := by
  native_decide

end CirclePacking
