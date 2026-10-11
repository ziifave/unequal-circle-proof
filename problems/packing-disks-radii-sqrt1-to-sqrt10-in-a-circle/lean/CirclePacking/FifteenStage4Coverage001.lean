import CirclePacking.FifteenStage4CoverageCertificate

namespace CirclePacking

def fifteenStage4Coverage001Source : String :=
  include_str "../../../../problems/packing-15-equal-disks-in-a-circle/candidate_bundle/stage4_coverage_000100100100101.txt"

def fifteenStage4Coverage001Valid : Bool :=
  s4CoverageSourceValid fifteenStage4Coverage001Source "000100100100101"

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem fifteenStage4Coverage001_replays : fifteenStage4Coverage001Valid = true := by
  native_decide

end CirclePacking
