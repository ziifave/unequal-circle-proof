import CirclePacking.FifteenStage3Certificate

namespace CirclePacking

def fifteenStage3Batch026Source : String :=
  include_str "../../../../research/fifteen_equal_completion/candidate_bundle/stage3_lean_batch_026.txt"

def fifteenStage3Batch026Patterns : List String := [
  "001001001011011",
  "001001001011101",
  "001001001100111",
  "001001001101011",
  "001001010010111",
  "001001010011011",
  "001001010011101",
  "001001010100111",
  "001001010101011",
  "001001010110011"
]

def fifteenStage3Batch026Checks : Bool :=
  fifteenStage3CheckBatch fifteenStage3Batch026Source fifteenStage3Batch026Patterns

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fifteenStage3Batch026_checks : fifteenStage3Batch026Checks = true := by
  native_decide

end CirclePacking
