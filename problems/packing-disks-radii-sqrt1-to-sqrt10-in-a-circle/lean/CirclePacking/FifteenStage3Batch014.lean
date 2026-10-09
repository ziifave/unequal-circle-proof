import CirclePacking.FifteenStage3Certificate

namespace CirclePacking

def fifteenStage3Batch014Source : String :=
  include_str "../../../../research/fifteen_equal_completion/candidate_bundle/stage3_lean_batch_014.txt"

def fifteenStage3Batch014Patterns : List String := [
  "000101000101101",
  "000101000110011",
  "000101001001011",
  "000101001001101",
  "000101001010011",
  "000101001010101",
  "000101001100011",
  "000101001100101",
  "000101010001011",
  "000101010010011"
]

def fifteenStage3Batch014Checks : Bool :=
  fifteenStage3CheckBatch fifteenStage3Batch014Source fifteenStage3Batch014Patterns

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fifteenStage3Batch014_checks : fifteenStage3Batch014Checks = true := by
  native_decide

end CirclePacking
