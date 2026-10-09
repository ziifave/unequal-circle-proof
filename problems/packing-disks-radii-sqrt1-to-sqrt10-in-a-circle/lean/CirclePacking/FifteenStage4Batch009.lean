import CirclePacking.FifteenStage4Certificate

namespace CirclePacking

def fifteenStage4Batch009Source : String :=
  include_str "../../../../problems/packing-15-equal-disks-in-a-circle/candidate_bundle/stage4_lean_batch_009.txt"

def fifteenStage4Batch009Patterns : List String := ["000100100110101"]

def fifteenStage4Batch009Checks : Bool :=
  fifteenStage4CheckBatch fifteenStage4Batch009Source fifteenStage4Batch009Patterns

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fifteenStage4Batch009_checks : fifteenStage4Batch009Checks = true := by
  native_decide

end CirclePacking
