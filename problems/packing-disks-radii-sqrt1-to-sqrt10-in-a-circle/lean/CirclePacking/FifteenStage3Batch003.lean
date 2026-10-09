import CirclePacking.FifteenStage3Certificate

namespace CirclePacking

def fifteenStage3Batch003Source : String :=
  include_str "../../../../problems/packing-15-equal-disks-in-a-circle/candidate_bundle/stage3_lean_batch_003.txt"

def fifteenStage3Batch003Patterns : List String := [
  "000010001100101",
  "000010001101001",
  "000010010001011",
  "000010010001101",
  "000010010011001",
  "000010010100011",
  "000010010100101",
  "000010010101001",
  "000010011000101",
  "000010100001011"
]

def fifteenStage3Batch003Checks : Bool :=
  fifteenStage3CheckBatch fifteenStage3Batch003Source fifteenStage3Batch003Patterns

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fifteenStage3Batch003_checks : fifteenStage3Batch003Checks = true := by
  native_decide

end CirclePacking
