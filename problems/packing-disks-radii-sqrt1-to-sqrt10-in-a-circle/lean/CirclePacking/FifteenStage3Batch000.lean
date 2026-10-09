import CirclePacking.FifteenStage3Certificate

namespace CirclePacking

def fifteenStage3Batch000Source : String :=
  include_str "../../../../problems/packing-15-equal-disks-in-a-circle/candidate_bundle/stage3_lean_batch_000.txt"

def fifteenStage3Batch000Patterns : List String := [
  "000000010101011",
  "000000010101101",
  "000000100101011",
  "000000100101101",
  "000000100110101",
  "000000101001011",
  "000000101001101",
  "000000101010011",
  "000000101010101",
  "000001000101011"
]

def fifteenStage3Batch000Checks : Bool :=
  fifteenStage3CheckBatch fifteenStage3Batch000Source fifteenStage3Batch000Patterns

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fifteenStage3Batch000_checks : fifteenStage3Batch000Checks = true := by
  native_decide

end CirclePacking
