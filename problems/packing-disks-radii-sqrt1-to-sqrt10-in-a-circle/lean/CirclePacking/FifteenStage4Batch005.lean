import CirclePacking.FifteenStage4Certificate

namespace CirclePacking

def fifteenStage4Batch005Source : String :=
  include_str "../../../../problems/packing-15-equal-disks-in-a-circle/candidate_bundle/stage4_lean_batch_005.txt"

def fifteenStage4Batch005Patterns : List String := ["000100100100011"]

def fifteenStage4Batch005Checks : Bool :=
  fifteenStage4CheckBatch fifteenStage4Batch005Source fifteenStage4Batch005Patterns

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fifteenStage4Batch005_checks : fifteenStage4Batch005Checks = true := by
  native_decide

end CirclePacking
