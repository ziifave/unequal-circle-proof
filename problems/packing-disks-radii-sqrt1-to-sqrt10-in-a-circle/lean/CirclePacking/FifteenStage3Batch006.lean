import CirclePacking.FifteenStage3Certificate

namespace CirclePacking

def fifteenStage3Batch006Source : String :=
  include_str "../../../../problems/packing-15-equal-disks-in-a-circle/candidate_bundle/stage3_lean_batch_006.txt"

def fifteenStage3Batch006Patterns : List String := [
  "000001010101011",
  "000001010101101",
  "000001010110011",
  "000001010110101",
  "000001011001011",
  "000001011001101",
  "000001011010011",
  "000001100101011",
  "000001101001011",
  "000010001010111"
]

def fifteenStage3Batch006Checks : Bool :=
  fifteenStage3CheckBatch fifteenStage3Batch006Source fifteenStage3Batch006Patterns

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fifteenStage3Batch006_checks : fifteenStage3Batch006Checks = true := by
  native_decide

end CirclePacking
