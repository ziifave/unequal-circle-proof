import CirclePacking.FifteenStage3Certificate

namespace CirclePacking

def fifteenStage3Batch004Source : String :=
  include_str "../../../../research/fifteen_equal_completion/candidate_bundle/stage3_lean_batch_004.txt"

def fifteenStage3Batch004Patterns : List String := [
  "000010100010011",
  "000010100010101",
  "000010100100011",
  "000010100100101",
  "000010101000011",
  "000100010001011",
  "000100010011001",
  "000100010100011",
  "000100010100101",
  "000100101000101"
]

def fifteenStage3Batch004Checks : Bool :=
  fifteenStage3CheckBatch fifteenStage3Batch004Source fifteenStage3Batch004Patterns

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fifteenStage3Batch004_checks : fifteenStage3Batch004Checks = true := by
  native_decide

end CirclePacking
