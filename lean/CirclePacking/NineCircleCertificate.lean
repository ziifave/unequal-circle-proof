import CirclePacking.NineCircleCertificateData

namespace CirclePacking

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/- These replay the exact integer-scaled checks from the source certificate. -/
theorem nineCircleProofP_replays :
    nineCertificateValid nineCircleProofP = true := by
  native_decide

theorem nineCircleProofQ_replays :
    nineCertificateValid nineCircleProofQ = true := by
  native_decide

end CirclePacking
