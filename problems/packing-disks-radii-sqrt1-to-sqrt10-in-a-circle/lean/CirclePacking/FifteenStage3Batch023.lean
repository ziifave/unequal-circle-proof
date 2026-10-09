import CirclePacking.FifteenStage3Certificate

namespace CirclePacking

def fifteenStage3Batch023Source : String :=
  include_str "../../../../problems/packing-15-equal-disks-in-a-circle/candidate_bundle/stage3_lean_batch_023.txt"

def fifteenStage3Batch023Patterns : List String := [
  "000101010110011",
  "000101011000111",
  "000101011001011",
  "000101011001101",
  "000101011010011",
  "000101011100011",
  "000101100010111",
  "000101100011011",
  "000101100011101",
  "000101100100111"
]

def fifteenStage3Batch023Checks : Bool :=
  fifteenStage3CheckBatch fifteenStage3Batch023Source fifteenStage3Batch023Patterns

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fifteenStage3Batch023_checks : fifteenStage3Batch023Checks = true := by
  native_decide

end CirclePacking
