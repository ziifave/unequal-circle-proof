import CirclePacking.FifteenStage4CoverageCertificate

namespace CirclePacking

def fifteenStage4Coverage003Source : String :=
  include_str "../../../../problems/packing-15-equal-disks-in-a-circle/candidate_bundle/stage4_coverage_001001001001011.txt"

def fifteenStage4Coverage003Valid : Bool :=
  s4CoverageSourceValid fifteenStage4Coverage003Source "001001001001011"

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem fifteenStage4Coverage003_replays : fifteenStage4Coverage003Valid = true := by
  native_decide

end CirclePacking
