import CirclePacking.FifteenStageZero
import CirclePacking.FifteenStage4LocalHandoff

/-! A single proposition collecting the currently replayed finite layers for
the 15-disk argument. This is deliberately a dedicated build target rather
than an import of the default `CirclePacking` library, so the large certificate
replays remain opt-in. -/

namespace CirclePacking

theorem fifteenAllFiniteCertificates_replay :
    fifteenStage0CertificateReplay = true ∧
    fifteenStage0CoarseAngleTableReplay = true ∧
    fifteenStage0CanonicalCoverageReplay = true ∧
    (fifteenStage0OrbitWords.length = 760 ∧
      fifteenStage0OrbitCountByWeight = [111, 185, 232, 232]) ∧
    (fifteenStage3TableValid && fifteenStage3ManifestMatchesStageZero &&
      fifteenStage3ClosedCertificateCoverage &&
      fifteenStage3AllBatchChecks.all id = true) ∧
    (fifteenStage4TableValid && fifteenStage4ManifestMatchesStage3 &&
      fifteenStage4AllBatchChecks.all id = true) ∧
    fifteenExactCertificateReplay = true ∧
    fifteenStage4ExactHandoffValid = true := by
  exact ⟨fifteenStage0Certificate_replays,
    fifteenStage0CoarseAngleTable_replays,
    fifteenStage0CanonicalCoverage_replays,
    fifteenStage0DihedralClassCounts,
    fifteenStage3AndStage4FiniteCertificates_replay.1,
    fifteenStage3AndStage4FiniteCertificates_replay.2,
    fifteenExactCertificate_replays,
    fifteenStage4ExactHandoff_replays⟩

end CirclePacking
