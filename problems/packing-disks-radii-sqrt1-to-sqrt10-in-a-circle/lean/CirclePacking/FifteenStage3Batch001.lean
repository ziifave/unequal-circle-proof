import CirclePacking.FifteenStage3Certificate

namespace CirclePacking

def fifteenStage3Batch001Source : String :=
  include_str "../../../../research/fifteen_equal_completion/candidate_bundle/stage3_lean_batch_001.txt"

def fifteenStage3Batch001Patterns : List String := [
  "000001000101101",
  "000001000110101",
  "000001001001011",
  "000001001001101",
  "000001001010011",
  "000001001010101",
  "000001001011001",
  "000001001100101",
  "000001010001011",
  "000001010001101"
]

def fifteenStage3Batch001Checks : Bool :=
  fifteenStage3CheckBatch fifteenStage3Batch001Source fifteenStage3Batch001Patterns

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fifteenStage3Batch001_checks : fifteenStage3Batch001Checks = true := by
  native_decide

end CirclePacking
