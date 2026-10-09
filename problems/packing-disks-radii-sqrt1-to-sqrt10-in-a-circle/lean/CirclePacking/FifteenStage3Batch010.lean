import CirclePacking.FifteenStage3Certificate

namespace CirclePacking

def fifteenStage3Batch010Source : String :=
  include_str "../../../../problems/packing-15-equal-disks-in-a-circle/candidate_bundle/stage3_lean_batch_010.txt"

def fifteenStage3Batch010Patterns : List String := [
  "000010101001101",
  "000010101010011",
  "000010101010101",
  "000010101100011",
  "000010110001011",
  "000010110001101",
  "000010110010011",
  "000010110100011",
  "000011000101011",
  "000011001001011"
]

def fifteenStage3Batch010Checks : Bool :=
  fifteenStage3CheckBatch fifteenStage3Batch010Source fifteenStage3Batch010Patterns

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fifteenStage3Batch010_checks : fifteenStage3Batch010Checks = true := by
  native_decide

end CirclePacking
