import CirclePacking.FifteenStage4Certificate

namespace CirclePacking

def fifteenStage4Batch016Source : String :=
  include_str "../../../../problems/packing-15-equal-disks-in-a-circle/candidate_bundle/stage4_lean_batch_016.txt"

def fifteenStage4Batch016Patterns : List String := ["000101010110101"]

def fifteenStage4Batch016Checks : Bool :=
  fifteenStage4CheckBatch fifteenStage4Batch016Source fifteenStage4Batch016Patterns

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fifteenStage4Batch016_checks : fifteenStage4Batch016Checks = true := by
  native_decide

end CirclePacking
