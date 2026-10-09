import CirclePacking.FifteenStage4Certificate

namespace CirclePacking

def fifteenStage4Batch015Source : String :=
  include_str "../../../../problems/packing-15-equal-disks-in-a-circle/candidate_bundle/stage4_lean_batch_015.txt"

def fifteenStage4Batch015Patterns : List String := ["001001010010101"]

def fifteenStage4Batch015Checks : Bool :=
  fifteenStage4CheckBatch fifteenStage4Batch015Source fifteenStage4Batch015Patterns

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fifteenStage4Batch015_checks : fifteenStage4Batch015Checks = true := by
  native_decide

end CirclePacking
