import CirclePacking.FifteenStage4Certificate

namespace CirclePacking

def fifteenStage4Batch000Source : String :=
  include_str "../../../../problems/packing-15-equal-disks-in-a-circle/candidate_bundle/stage4_lean_batch_000.txt"

def fifteenStage4Batch000Patterns : List String := ["000010010010011"]

def fifteenStage4Batch000Checks : Bool :=
  fifteenStage4CheckBatch fifteenStage4Batch000Source fifteenStage4Batch000Patterns

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fifteenStage4Batch000_checks : fifteenStage4Batch000Checks = true := by
  native_decide

end CirclePacking
