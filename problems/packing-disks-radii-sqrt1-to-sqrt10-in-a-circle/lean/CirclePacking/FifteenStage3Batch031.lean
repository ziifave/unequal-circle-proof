import CirclePacking.FifteenStage3Certificate

namespace CirclePacking

def fifteenStage3Batch031Source : String :=
  include_str "../../../../research/fifteen_equal_completion/candidate_bundle/stage3_lean_batch_031.txt"

def fifteenStage3Batch031Patterns : List String := [
  "001010010111011",
  "001010010111101",
  "001010011001111",
  "001010011010111",
  "001010011011011",
  "001010011100111",
  "001010100101111",
  "001010100110111",
  "001010101001111",
  "001010101010111"
]

def fifteenStage3Batch031Checks : Bool :=
  fifteenStage3CheckBatch fifteenStage3Batch031Source fifteenStage3Batch031Patterns

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fifteenStage3Batch031_checks : fifteenStage3Batch031Checks = true := by
  native_decide

end CirclePacking
