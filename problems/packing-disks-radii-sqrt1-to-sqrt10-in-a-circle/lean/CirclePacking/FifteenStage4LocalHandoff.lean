import CirclePacking.FifteenStages34Integrated
import CirclePacking.FifteenCertificate
import CirclePacking.FifteenLocalBarrierAlgebra

/-! Connect the four patterns left by Stage 4 to the exact radial-subdivision
certificate. Three are its I5/O10 roots; the fourth is its I6/O9 special case.
The 31 local leaves in the exact certificate are restricted to the canonical
five-inner pattern and the rational box [42/25, 43/25]^5. -/

namespace CirclePacking

def fifteenStage4ExactHandoffValid : Bool :=
  fifteenStage4ResidualPatterns == [
    "000100100010101",
    "000100100100101",
    "001001001001001",
    "001001001001011"
  ] &&
  fifteenExpectedRoots "000100100010101" == 47 &&
  fifteenExpectedRoots "000100100100101" == 38 &&
  fifteenExpectedRoots "001001001001001" == 1181 &&
  fifteenSpecialPattern == "001001001001011" &&
  fifteenLocalLo == fifteenRational 42 25 &&
  fifteenLocalHi == fifteenRational 43 25

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fifteenStage4ExactHandoff_replays :
    fifteenStage4ExactHandoffValid = true := by
  native_decide

theorem fifteenStage4Residuals_exactly_replayed :
    (fifteenStage3TableValid && fifteenStage3ManifestMatchesStageZero &&
      fifteenStage3ClosedCertificateCoverage &&
      fifteenStage3AllBatchChecks.all id = true) ∧
    (fifteenStage4TableValid && fifteenStage4ManifestMatchesStage3 &&
      fifteenStage4AllBatchChecks.all id = true) ∧
    fifteenExactCertificateReplay = true ∧
    fifteenStage4ExactHandoffValid = true ∧
    (2 / 5 : ℝ) * (21 / 50) - 5 * (11 / 500) = 29 / 500 := by
  exact ⟨fifteenStage3FiniteCertificates_replay,
    fifteenStage4FiniteCertificates_replay,
    fifteenExactCertificate_replays,
    fifteenStage4ExactHandoff_replays,
    fifteenLocalBarrierRationalMargin⟩

end CirclePacking
