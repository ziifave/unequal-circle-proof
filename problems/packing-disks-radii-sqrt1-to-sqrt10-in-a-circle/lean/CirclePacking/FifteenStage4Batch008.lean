import CirclePacking.FifteenStage4Certificate

namespace CirclePacking

def fifteenStage4Batch008Source : String :=
  include_str "../../../../problems/packing-15-equal-disks-in-a-circle/candidate_bundle/stage4_lean_batch_008.txt"

def fifteenStage4Batch008Patterns : List String := ["000100100101101"]

def fifteenStage4Batch008Checks : Bool :=
  fifteenStage4CheckBatch fifteenStage4Batch008Source fifteenStage4Batch008Patterns

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fifteenStage4Batch008_checks : fifteenStage4Batch008Checks = true := by
  native_decide

end CirclePacking
