import CirclePacking.FifteenStage3Certificate

namespace CirclePacking

def fifteenStage3Batch008Source : String :=
  include_str "../../../../research/fifteen_equal_completion/candidate_bundle/stage3_lean_batch_008.txt"

def fifteenStage3Batch008Patterns : List String := [
  "000010010101101",
  "000010010110011",
  "000010010110101",
  "000010010111001",
  "000010011001011",
  "000010011001101",
  "000010011010011",
  "000010011010101",
  "000010011011001",
  "000010011100101"
]

def fifteenStage3Batch008Checks : Bool :=
  fifteenStage3CheckBatch fifteenStage3Batch008Source fifteenStage3Batch008Patterns

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fifteenStage3Batch008_checks : fifteenStage3Batch008Checks = true := by
  native_decide

end CirclePacking
