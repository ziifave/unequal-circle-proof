import CirclePacking.FifteenStage3Certificate

namespace CirclePacking

def fifteenStage3Batch033Source : String :=
  include_str "../../../../research/fifteen_equal_completion/candidate_bundle/stage3_lean_batch_033.txt"

def fifteenStage3Batch033Patterns : List String := [
  "001010110100111",
  "001010110101011",
  "001010110101101",
  "001010110110011",
  "001010110110101",
  "001010111001011",
  "001010111001101",
  "001010111010011",
  "001011001011011",
  "001011001011101"
]

def fifteenStage3Batch033Checks : Bool :=
  fifteenStage3CheckBatch fifteenStage3Batch033Source fifteenStage3Batch033Patterns

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fifteenStage3Batch033_checks : fifteenStage3Batch033Checks = true := by
  native_decide

end CirclePacking
