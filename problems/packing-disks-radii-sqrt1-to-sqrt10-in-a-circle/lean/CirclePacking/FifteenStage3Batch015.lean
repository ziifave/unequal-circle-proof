import CirclePacking.FifteenStage3Certificate

namespace CirclePacking

def fifteenStage3Batch015Source : String :=
  include_str "../../../../problems/packing-15-equal-disks-in-a-circle/candidate_bundle/stage3_lean_batch_015.txt"

def fifteenStage3Batch015Patterns : List String := [
  "000101010010101",
  "000101010100011",
  "000110010010011",
  "001001010010011",
  "001010010100101",
  "000010100101111",
  "000010100110111",
  "000010100111011",
  "000010100111101",
  "000010101001111"
]

def fifteenStage3Batch015Checks : Bool :=
  fifteenStage3CheckBatch fifteenStage3Batch015Source fifteenStage3Batch015Patterns

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fifteenStage3Batch015_checks : fifteenStage3Batch015Checks = true := by
  native_decide

end CirclePacking
