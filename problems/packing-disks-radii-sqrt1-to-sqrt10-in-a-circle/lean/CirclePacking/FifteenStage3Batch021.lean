import CirclePacking.FifteenStage3Certificate

namespace CirclePacking

def fifteenStage3Batch021Source : String :=
  include_str "../../../../research/fifteen_equal_completion/candidate_bundle/stage3_lean_batch_021.txt"

def fifteenStage3Batch021Patterns : List String := [
  "000100111010101",
  "000100111100101",
  "000101000101111",
  "000101000110111",
  "000101001001111",
  "000101001010111",
  "000101001011011",
  "000101001011101",
  "000101001100111",
  "000101001101011"
]

def fifteenStage3Batch021Checks : Bool :=
  fifteenStage3CheckBatch fifteenStage3Batch021Source fifteenStage3Batch021Patterns

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fifteenStage3Batch021_checks : fifteenStage3Batch021Checks = true := by
  native_decide

end CirclePacking
