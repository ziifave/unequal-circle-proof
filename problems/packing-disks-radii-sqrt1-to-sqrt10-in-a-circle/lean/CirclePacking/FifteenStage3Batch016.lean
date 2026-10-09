import CirclePacking.FifteenStage3Certificate

namespace CirclePacking

def fifteenStage3Batch016Source : String :=
  include_str "../../../../research/fifteen_equal_completion/candidate_bundle/stage3_lean_batch_016.txt"

def fifteenStage3Batch016Patterns : List String := [
  "000010101010111",
  "000010101011011",
  "000010101011101",
  "000010101100111",
  "000010101101011",
  "000010101101101",
  "000010101110011",
  "000010101110101",
  "000010110010111",
  "000010110011011"
]

def fifteenStage3Batch016Checks : Bool :=
  fifteenStage3CheckBatch fifteenStage3Batch016Source fifteenStage3Batch016Patterns

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fifteenStage3Batch016_checks : fifteenStage3Batch016Checks = true := by
  native_decide

end CirclePacking
