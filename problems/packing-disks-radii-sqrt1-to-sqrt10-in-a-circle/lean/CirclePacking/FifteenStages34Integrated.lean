import CirclePacking.FifteenStages34
import CirclePacking.FifteenStage4

/-! The finite-certificate results for Stages 3 and 4, including their
manifest handoff, collected as one proposition. -/

namespace CirclePacking

theorem fifteenStage3AndStage4FiniteCertificates_replay :
    (fifteenStage3TableValid && fifteenStage3ManifestMatchesStageZero &&
      fifteenStage3ClosedCertificateCoverage &&
      fifteenStage3AllBatchChecks.all id = true) ∧
    (fifteenStage4TableValid && fifteenStage4ManifestMatchesStage3 &&
      fifteenStage4AllBatchChecks.all id = true) := by
  exact ⟨fifteenStage3FiniteCertificates_replay,
    fifteenStage4FiniteCertificates_replay⟩

end CirclePacking
