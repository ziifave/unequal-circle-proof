import CirclePacking.FifteenStage3Certificate

namespace CirclePacking

def fifteenStage3Batch011Source : String :=
  include_str "../../../../problems/packing-15-equal-disks-in-a-circle/candidate_bundle/stage3_lean_batch_011.txt"

def fifteenStage3Batch011Patterns : List String := [
  "000011001010011",
  "000011010001011",
  "000100010010111",
  "000100010011011",
  "000100010011101",
  "000100010100111",
  "000100010101011",
  "000100010101101",
  "000100010110011",
  "000100011001011"
]

def fifteenStage3Batch011Checks : Bool :=
  fifteenStage3CheckBatch fifteenStage3Batch011Source fifteenStage3Batch011Patterns

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fifteenStage3Batch011_checks : fifteenStage3Batch011Checks = true := by
  native_decide

end CirclePacking
