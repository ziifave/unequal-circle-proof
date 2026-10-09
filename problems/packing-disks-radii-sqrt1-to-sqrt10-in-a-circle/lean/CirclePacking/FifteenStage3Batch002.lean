import CirclePacking.FifteenStage3Certificate

namespace CirclePacking

def fifteenStage3Batch002Source : String :=
  include_str "../../../../problems/packing-15-equal-disks-in-a-circle/candidate_bundle/stage3_lean_batch_002.txt"

def fifteenStage3Batch002Patterns : List String := [
  "000001010010011",
  "000001010010101",
  "000001010100011",
  "000010000101011",
  "000010000101101",
  "000010001001011",
  "000010001001101",
  "000010001010011",
  "000010001010101",
  "000010001011001"
]

def fifteenStage3Batch002Checks : Bool :=
  fifteenStage3CheckBatch fifteenStage3Batch002Source fifteenStage3Batch002Patterns

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fifteenStage3Batch002_checks : fifteenStage3Batch002Checks = true := by
  native_decide

end CirclePacking
