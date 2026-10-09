import CirclePacking.FifteenStage4Certificate

namespace CirclePacking

def fifteenStage4Batch011Source : String :=
  include_str "../../../../problems/packing-15-equal-disks-in-a-circle/candidate_bundle/stage4_lean_batch_011.txt"

def fifteenStage4Batch011Patterns : List String := ["000100101011001"]

def fifteenStage4Batch011Checks : Bool :=
  fifteenStage4CheckBatch fifteenStage4Batch011Source fifteenStage4Batch011Patterns

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fifteenStage4Batch011_checks : fifteenStage4Batch011Checks = true := by
  native_decide

end CirclePacking
