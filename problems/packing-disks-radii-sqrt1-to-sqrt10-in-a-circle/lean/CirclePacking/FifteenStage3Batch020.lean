import CirclePacking.FifteenStage3Certificate

namespace CirclePacking

def fifteenStage3Batch020Source : String :=
  include_str "../../../../problems/packing-15-equal-disks-in-a-circle/candidate_bundle/stage3_lean_batch_020.txt"

def fifteenStage3Batch020Patterns : List String := [
  "000100110011101",
  "000100110100111",
  "000100110101011",
  "000100110101101",
  "000100110110011",
  "000100110110101",
  "000100110111001",
  "000100111001011",
  "000100111001101",
  "000100111010011"
]

def fifteenStage3Batch020Checks : Bool :=
  fifteenStage3CheckBatch fifteenStage3Batch020Source fifteenStage3Batch020Patterns

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fifteenStage3Batch020_checks : fifteenStage3Batch020Checks = true := by
  native_decide

end CirclePacking
