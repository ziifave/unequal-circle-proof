import CirclePacking.FifteenStage3Certificate

namespace CirclePacking

def fifteenStage3Batch024Source : String :=
  include_str "../../../../research/fifteen_equal_completion/candidate_bundle/stage3_lean_batch_024.txt"

def fifteenStage3Batch024Patterns : List String := [
  "000101100101011",
  "000101100101101",
  "000101100110011",
  "000101101000111",
  "000101101001011",
  "000101101010011",
  "000101101100011",
  "000101110010011",
  "000101110100011",
  "000110001101011"
]

def fifteenStage3Batch024Checks : Bool :=
  fifteenStage3CheckBatch fifteenStage3Batch024Source fifteenStage3Batch024Patterns

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fifteenStage3Batch024_checks : fifteenStage3Batch024Checks = true := by
  native_decide

end CirclePacking
