import CirclePacking.FifteenStage4Certificate

namespace CirclePacking

def fifteenStage4Batch007Source : String :=
  include_str "../../../../problems/packing-15-equal-disks-in-a-circle/candidate_bundle/stage4_lean_batch_007.txt"

def fifteenStage4Batch007Patterns : List String := ["000100100101011"]

def fifteenStage4Batch007Checks : Bool :=
  fifteenStage4CheckBatch fifteenStage4Batch007Source fifteenStage4Batch007Patterns

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fifteenStage4Batch007_checks : fifteenStage4Batch007Checks = true := by
  native_decide

end CirclePacking
