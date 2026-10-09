import CirclePacking.FifteenStage4Certificate

namespace CirclePacking

def fifteenStage4Batch006Source : String :=
  include_str "../../../../problems/packing-15-equal-disks-in-a-circle/candidate_bundle/stage4_lean_batch_006.txt"

def fifteenStage4Batch006Patterns : List String := ["000100100101001"]

def fifteenStage4Batch006Checks : Bool :=
  fifteenStage4CheckBatch fifteenStage4Batch006Source fifteenStage4Batch006Patterns

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fifteenStage4Batch006_checks : fifteenStage4Batch006Checks = true := by
  native_decide

end CirclePacking
