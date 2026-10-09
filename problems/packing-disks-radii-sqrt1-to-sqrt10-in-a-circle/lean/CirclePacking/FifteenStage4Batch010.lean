import CirclePacking.FifteenStage4Certificate

namespace CirclePacking

def fifteenStage4Batch010Source : String :=
  include_str "../../../../problems/packing-15-equal-disks-in-a-circle/candidate_bundle/stage4_lean_batch_010.txt"

def fifteenStage4Batch010Patterns : List String := ["000100101010101"]

def fifteenStage4Batch010Checks : Bool :=
  fifteenStage4CheckBatch fifteenStage4Batch010Source fifteenStage4Batch010Patterns

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fifteenStage4Batch010_checks : fifteenStage4Batch010Checks = true := by
  native_decide

end CirclePacking
