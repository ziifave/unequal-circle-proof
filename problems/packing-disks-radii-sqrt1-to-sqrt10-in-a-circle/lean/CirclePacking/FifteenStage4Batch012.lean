import CirclePacking.FifteenStage4Certificate

namespace CirclePacking

def fifteenStage4Batch012Source : String :=
  include_str "../../../../problems/packing-15-equal-disks-in-a-circle/candidate_bundle/stage4_lean_batch_012.txt"

def fifteenStage4Batch012Patterns : List String := ["000100101101001"]

def fifteenStage4Batch012Checks : Bool :=
  fifteenStage4CheckBatch fifteenStage4Batch012Source fifteenStage4Batch012Patterns

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fifteenStage4Batch012_checks : fifteenStage4Batch012Checks = true := by
  native_decide

end CirclePacking
