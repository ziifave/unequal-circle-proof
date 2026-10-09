import CirclePacking.FifteenStage3Certificate

namespace CirclePacking

def fifteenStage3Batch027Source : String :=
  include_str "../../../../research/fifteen_equal_completion/candidate_bundle/stage3_lean_batch_027.txt"

def fifteenStage3Batch027Patterns : List String := [
  "001001011001011",
  "001001011001101",
  "001001011010011",
  "001001100100111",
  "001001100101011",
  "001001100110011",
  "001001101001011",
  "001010010100111",
  "001010010101011",
  "001010010101101"
]

def fifteenStage3Batch027Checks : Bool :=
  fifteenStage3CheckBatch fifteenStage3Batch027Source fifteenStage3Batch027Patterns

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fifteenStage3Batch027_checks : fifteenStage3Batch027Checks = true := by
  native_decide

end CirclePacking
