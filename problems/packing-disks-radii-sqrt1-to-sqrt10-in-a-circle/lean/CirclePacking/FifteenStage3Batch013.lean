import CirclePacking.FifteenStage3Certificate

namespace CirclePacking

def fifteenStage3Batch013Source : String :=
  include_str "../../../../problems/packing-15-equal-disks-in-a-circle/candidate_bundle/stage3_lean_batch_013.txt"

def fifteenStage3Batch013Patterns : List String := [
  "000100101100101",
  "000100110001011",
  "000100110001101",
  "000100110010011",
  "000100110010101",
  "000100110011001",
  "000100110100011",
  "000100110100101",
  "000100111000101",
  "000101000101011"
]

def fifteenStage3Batch013Checks : Bool :=
  fifteenStage3CheckBatch fifteenStage3Batch013Source fifteenStage3Batch013Patterns

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fifteenStage3Batch013_checks : fifteenStage3Batch013Checks = true := by
  native_decide

end CirclePacking
