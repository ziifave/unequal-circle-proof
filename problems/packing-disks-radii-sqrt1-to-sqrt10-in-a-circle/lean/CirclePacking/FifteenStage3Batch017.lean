import CirclePacking.FifteenStage3Certificate

namespace CirclePacking

def fifteenStage3Batch017Source : String :=
  include_str "../../../../research/fifteen_equal_completion/candidate_bundle/stage3_lean_batch_017.txt"

def fifteenStage3Batch017Patterns : List String := [
  "000010110011101",
  "000010110100111",
  "000010110101011",
  "000010110101101",
  "000010110110011",
  "000010111001011",
  "000010111010011",
  "000011001010111",
  "000011001011011",
  "000011001101011"
]

def fifteenStage3Batch017Checks : Bool :=
  fifteenStage3CheckBatch fifteenStage3Batch017Source fifteenStage3Batch017Patterns

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fifteenStage3Batch017_checks : fifteenStage3Batch017Checks = true := by
  native_decide

end CirclePacking
