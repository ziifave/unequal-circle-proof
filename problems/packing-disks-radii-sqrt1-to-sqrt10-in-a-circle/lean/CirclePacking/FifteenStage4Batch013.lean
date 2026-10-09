import CirclePacking.FifteenStage4Certificate

namespace CirclePacking

def fifteenStage4Batch013Source : String :=
  include_str "../../../../problems/packing-15-equal-disks-in-a-circle/candidate_bundle/stage4_lean_batch_013.txt"

def fifteenStage4Batch013Patterns : List String := ["001001001010011"]

def fifteenStage4Batch013Checks : Bool :=
  fifteenStage4CheckBatch fifteenStage4Batch013Source fifteenStage4Batch013Patterns

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fifteenStage4Batch013_checks : fifteenStage4Batch013Checks = true := by
  native_decide

end CirclePacking
