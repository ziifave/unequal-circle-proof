import CirclePacking.FifteenStage3Certificate

namespace CirclePacking

def fifteenStage3Batch032Source : String :=
  include_str "../../../../problems/packing-15-equal-disks-in-a-circle/candidate_bundle/stage3_lean_batch_032.txt"

def fifteenStage3Batch032Patterns : List String := [
  "001010101011011",
  "001010101011101",
  "001010101100111",
  "001010101101011",
  "001010101101101",
  "001010101110011",
  "001010101110101",
  "001010110010111",
  "001010110011011",
  "001010110011101"
]

def fifteenStage3Batch032Checks : Bool :=
  fifteenStage3CheckBatch fifteenStage3Batch032Source fifteenStage3Batch032Patterns

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fifteenStage3Batch032_checks : fifteenStage3Batch032Checks = true := by
  native_decide

end CirclePacking
