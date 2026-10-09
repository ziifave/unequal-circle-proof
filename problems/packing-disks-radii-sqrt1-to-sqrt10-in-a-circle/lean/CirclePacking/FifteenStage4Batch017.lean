import CirclePacking.FifteenStage4Certificate

namespace CirclePacking

def fifteenStage4Batch017Source : String :=
  include_str "../../../../problems/packing-15-equal-disks-in-a-circle/candidate_bundle/stage4_lean_batch_017.txt"

def fifteenStage4Batch017Patterns : List String := ["001001010101101"]

def fifteenStage4Batch017Checks : Bool :=
  fifteenStage4CheckBatch fifteenStage4Batch017Source fifteenStage4Batch017Patterns

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fifteenStage4Batch017_checks : fifteenStage4Batch017Checks = true := by
  native_decide

end CirclePacking
