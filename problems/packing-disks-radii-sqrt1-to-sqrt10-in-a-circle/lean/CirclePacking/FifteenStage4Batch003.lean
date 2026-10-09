import CirclePacking.FifteenStage4Certificate

namespace CirclePacking

def fifteenStage4Batch003Source : String :=
  include_str "../../../../problems/packing-15-equal-disks-in-a-circle/candidate_bundle/stage4_lean_batch_003.txt"

def fifteenStage4Batch003Patterns : List String := ["000100010010101"]

def fifteenStage4Batch003Checks : Bool :=
  fifteenStage4CheckBatch fifteenStage4Batch003Source fifteenStage4Batch003Patterns

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fifteenStage4Batch003_checks : fifteenStage4Batch003Checks = true := by
  native_decide

end CirclePacking
