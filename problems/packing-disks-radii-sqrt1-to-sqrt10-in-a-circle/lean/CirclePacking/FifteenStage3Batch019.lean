import CirclePacking.FifteenStage3Certificate

namespace CirclePacking

def fifteenStage3Batch019Source : String :=
  include_str "../../../../problems/packing-15-equal-disks-in-a-circle/candidate_bundle/stage3_lean_batch_019.txt"

def fifteenStage3Batch019Patterns : List String := [
  "000100101011011",
  "000100101011101",
  "000100101100111",
  "000100101101011",
  "000100101101101",
  "000100101110011",
  "000100101110101",
  "000100101111001",
  "000100110010111",
  "000100110011011"
]

def fifteenStage3Batch019Checks : Bool :=
  fifteenStage3CheckBatch fifteenStage3Batch019Source fifteenStage3Batch019Patterns

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fifteenStage3Batch019_checks : fifteenStage3Batch019Checks = true := by
  native_decide

end CirclePacking
