import CirclePacking.FifteenStage4Certificate

namespace CirclePacking

def fifteenStage4Batch014Source : String :=
  include_str "../../../../problems/packing-15-equal-disks-in-a-circle/candidate_bundle/stage4_lean_batch_014.txt"

def fifteenStage4Batch014Patterns : List String := ["001001001010101"]

def fifteenStage4Batch014Checks : Bool :=
  fifteenStage4CheckBatch fifteenStage4Batch014Source fifteenStage4Batch014Patterns

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fifteenStage4Batch014_checks : fifteenStage4Batch014Checks = true := by
  native_decide

end CirclePacking
