import CirclePacking.FifteenStage4Certificate

namespace CirclePacking

def fifteenStage4Batch004Source : String :=
  include_str "../../../../problems/packing-15-equal-disks-in-a-circle/candidate_bundle/stage4_lean_batch_004.txt"

def fifteenStage4Batch004Patterns : List String := ["000100100010011"]

def fifteenStage4Batch004Checks : Bool :=
  fifteenStage4CheckBatch fifteenStage4Batch004Source fifteenStage4Batch004Patterns

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fifteenStage4Batch004_checks : fifteenStage4Batch004Checks = true := by
  native_decide

end CirclePacking
