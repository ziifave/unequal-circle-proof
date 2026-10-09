import CirclePacking.FifteenStage3Certificate

namespace CirclePacking

def fifteenStage3Batch028Source : String :=
  include_str "../../../../problems/packing-15-equal-disks-in-a-circle/candidate_bundle/stage3_lean_batch_028.txt"

def fifteenStage3Batch028Patterns : List String := [
  "001010010110011",
  "001010011001011",
  "001010100101011",
  "001010100101101",
  "001010100110011",
  "001010101001011",
  "001010101010011",
  "001010101010101",
  "001001010011111",
  "001001010101111"
]

def fifteenStage3Batch028Checks : Bool :=
  fifteenStage3CheckBatch fifteenStage3Batch028Source fifteenStage3Batch028Patterns

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fifteenStage3Batch028_checks : fifteenStage3Batch028Checks = true := by
  native_decide

end CirclePacking
