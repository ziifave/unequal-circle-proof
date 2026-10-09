import CirclePacking.FifteenStage4Certificate

namespace CirclePacking

def fifteenStage4Batch002Source : String :=
  include_str "../../../../problems/packing-15-equal-disks-in-a-circle/candidate_bundle/stage4_lean_batch_002.txt"

def fifteenStage4Batch002Patterns : List String := ["000100010010011"]

def fifteenStage4Batch002Checks : Bool :=
  fifteenStage4CheckBatch fifteenStage4Batch002Source fifteenStage4Batch002Patterns

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fifteenStage4Batch002_checks : fifteenStage4Batch002Checks = true := by
  native_decide

end CirclePacking
