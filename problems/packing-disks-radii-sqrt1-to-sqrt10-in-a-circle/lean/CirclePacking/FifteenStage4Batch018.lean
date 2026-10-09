import CirclePacking.FifteenStage4Certificate

namespace CirclePacking

def fifteenStage4Batch018Source : String :=
  include_str "../../../../problems/packing-15-equal-disks-in-a-circle/candidate_bundle/stage4_lean_batch_018.txt"

def fifteenStage4Batch018Patterns : List String := ["001001010110101"]

def fifteenStage4Batch018Checks : Bool :=
  fifteenStage4CheckBatch fifteenStage4Batch018Source fifteenStage4Batch018Patterns

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fifteenStage4Batch018_checks : fifteenStage4Batch018Checks = true := by
  native_decide

end CirclePacking
