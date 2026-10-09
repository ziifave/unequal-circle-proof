import CirclePacking.FifteenStage3Certificate

namespace CirclePacking

def fifteenStage3Batch007Source : String :=
  include_str "../../../../problems/packing-15-equal-disks-in-a-circle/candidate_bundle/stage3_lean_batch_007.txt"

def fifteenStage3Batch007Patterns : List String := [
  "000010001011011",
  "000010001011101",
  "000010001101011",
  "000010001101101",
  "000010001110101",
  "000010010010111",
  "000010010011011",
  "000010010011101",
  "000010010100111",
  "000010010101011"
]

def fifteenStage3Batch007Checks : Bool :=
  fifteenStage3CheckBatch fifteenStage3Batch007Source fifteenStage3Batch007Patterns

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fifteenStage3Batch007_checks : fifteenStage3Batch007Checks = true := by
  native_decide

end CirclePacking
