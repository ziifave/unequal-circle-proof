import CirclePacking.FifteenStage3Certificate

namespace CirclePacking

def fifteenStage3Batch022Source : String :=
  include_str "../../../../problems/packing-15-equal-disks-in-a-circle/candidate_bundle/stage3_lean_batch_022.txt"

def fifteenStage3Batch022Patterns : List String := [
  "000101001101101",
  "000101001110011",
  "000101001110101",
  "000101010001111",
  "000101010010111",
  "000101010011011",
  "000101010011101",
  "000101010100111",
  "000101010101011",
  "000101010101101"
]

def fifteenStage3Batch022Checks : Bool :=
  fifteenStage3CheckBatch fifteenStage3Batch022Source fifteenStage3Batch022Patterns

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fifteenStage3Batch022_checks : fifteenStage3Batch022Checks = true := by
  native_decide

end CirclePacking
