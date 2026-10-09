import CirclePacking.FifteenStage3Certificate

namespace CirclePacking

def fifteenStage3Batch025Source : String :=
  include_str "../../../../research/fifteen_equal_completion/candidate_bundle/stage3_lean_batch_025.txt"

def fifteenStage3Batch025Patterns : List String := [
  "000110010010111",
  "000110010011011",
  "000110010100111",
  "000110010101011",
  "000110010110011",
  "000110011001011",
  "000110100100111",
  "000110100101011",
  "001001001001111",
  "001001001010111"
]

def fifteenStage3Batch025Checks : Bool :=
  fifteenStage3CheckBatch fifteenStage3Batch025Source fifteenStage3Batch025Patterns

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fifteenStage3Batch025_checks : fifteenStage3Batch025Checks = true := by
  native_decide

end CirclePacking
