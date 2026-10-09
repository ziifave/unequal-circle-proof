import CirclePacking.FifteenStage3Batch000
import CirclePacking.FifteenStage3Batch001
import CirclePacking.FifteenStage3Batch002
import CirclePacking.FifteenStage3Batch003
import CirclePacking.FifteenStage3Batch004
import CirclePacking.FifteenStage3Batch005
import CirclePacking.FifteenStage3Batch006
import CirclePacking.FifteenStage3Batch007
import CirclePacking.FifteenStage3Batch008
import CirclePacking.FifteenStage3Batch009
import CirclePacking.FifteenStage3Batch010
import CirclePacking.FifteenStage3Batch011
import CirclePacking.FifteenStage3Batch012
import CirclePacking.FifteenStage3Batch013
import CirclePacking.FifteenStage3Batch014
import CirclePacking.FifteenStage3Batch015
import CirclePacking.FifteenStage3Batch016
import CirclePacking.FifteenStage3Batch017
import CirclePacking.FifteenStage3Batch018
import CirclePacking.FifteenStage3Batch019
import CirclePacking.FifteenStage3Batch020
import CirclePacking.FifteenStage3Batch021
import CirclePacking.FifteenStage3Batch022
import CirclePacking.FifteenStage3Batch023
import CirclePacking.FifteenStage3Batch024
import CirclePacking.FifteenStage3Batch025
import CirclePacking.FifteenStage3Batch026
import CirclePacking.FifteenStage3Batch027
import CirclePacking.FifteenStage3Batch028
import CirclePacking.FifteenStage3Batch029
import CirclePacking.FifteenStage3Batch030
import CirclePacking.FifteenStage3Batch031
import CirclePacking.FifteenStage3Batch032
import CirclePacking.FifteenStage3Batch033
import CirclePacking.FifteenStage3Batch034
import CirclePacking.FifteenStage3Batch035
import CirclePacking.FifteenStageZero

/-! Stage 3 certificates for all 355 closed patterns among the 378
Stage 0 survivors. Each batch theorem checks its full compact prefix tree. -/

namespace CirclePacking

private structure Stage3ManifestEntry where
  pattern : String
  innerCount : Nat
  closed : Bool

private def fifteenStage3ManifestSource : String :=
  include_str "../data/fifteen_stage3_manifest.tsv"

private def fifteenStage3ManifestLine? (line : String) : Option Stage3ManifestEntry := do
  let fields := line.splitOn "\t"
  let status ← fields[0]?
  let countText ← fields[1]?
  let pattern ← fields[2]?
  let count ← countText.toNat?
  let closed ← if status == "CLOSED" then some true
    else if status == "UNKNOWN" then some false else none
  some ⟨pattern, count, closed⟩

private def fifteenStage3ManifestRecords? : Option (List Stage3ManifestEntry) := do
  let lines := (fifteenStage3ManifestSource.splitOn "\n").filter (· != "")
  lines.mapM fifteenStage3ManifestLine?

private def fifteenStage3ManifestEntryValid (entry : Stage3ManifestEntry) : Bool :=
  let bits := entry.pattern.toList
  bits.length == 15 && bits.all (fun c => c == '0' || c == '1') &&
    (bits.filter (· == '1')).length == entry.innerCount &&
    5 ≤ entry.innerCount && entry.innerCount ≤ 8

def fifteenStage3CertifiedPatterns : List String :=
  fifteenStage3Batch000Patterns ++
  fifteenStage3Batch001Patterns ++
  fifteenStage3Batch002Patterns ++
  fifteenStage3Batch003Patterns ++
  fifteenStage3Batch004Patterns ++
  fifteenStage3Batch005Patterns ++
  fifteenStage3Batch006Patterns ++
  fifteenStage3Batch007Patterns ++
  fifteenStage3Batch008Patterns ++
  fifteenStage3Batch009Patterns ++
  fifteenStage3Batch010Patterns ++
  fifteenStage3Batch011Patterns ++
  fifteenStage3Batch012Patterns ++
  fifteenStage3Batch013Patterns ++
  fifteenStage3Batch014Patterns ++
  fifteenStage3Batch015Patterns ++
  fifteenStage3Batch016Patterns ++
  fifteenStage3Batch017Patterns ++
  fifteenStage3Batch018Patterns ++
  fifteenStage3Batch019Patterns ++
  fifteenStage3Batch020Patterns ++
  fifteenStage3Batch021Patterns ++
  fifteenStage3Batch022Patterns ++
  fifteenStage3Batch023Patterns ++
  fifteenStage3Batch024Patterns ++
  fifteenStage3Batch025Patterns ++
  fifteenStage3Batch026Patterns ++
  fifteenStage3Batch027Patterns ++
  fifteenStage3Batch028Patterns ++
  fifteenStage3Batch029Patterns ++
  fifteenStage3Batch030Patterns ++
  fifteenStage3Batch031Patterns ++
  fifteenStage3Batch032Patterns ++
  fifteenStage3Batch033Patterns ++
  fifteenStage3Batch034Patterns ++
  fifteenStage3Batch035Patterns

def fifteenStage3AllBatchChecks : List Bool := [
  fifteenStage3Batch000Checks,
  fifteenStage3Batch001Checks,
  fifteenStage3Batch002Checks,
  fifteenStage3Batch003Checks,
  fifteenStage3Batch004Checks,
  fifteenStage3Batch005Checks,
  fifteenStage3Batch006Checks,
  fifteenStage3Batch007Checks,
  fifteenStage3Batch008Checks,
  fifteenStage3Batch009Checks,
  fifteenStage3Batch010Checks,
  fifteenStage3Batch011Checks,
  fifteenStage3Batch012Checks,
  fifteenStage3Batch013Checks,
  fifteenStage3Batch014Checks,
  fifteenStage3Batch015Checks,
  fifteenStage3Batch016Checks,
  fifteenStage3Batch017Checks,
  fifteenStage3Batch018Checks,
  fifteenStage3Batch019Checks,
  fifteenStage3Batch020Checks,
  fifteenStage3Batch021Checks,
  fifteenStage3Batch022Checks,
  fifteenStage3Batch023Checks,
  fifteenStage3Batch024Checks,
  fifteenStage3Batch025Checks,
  fifteenStage3Batch026Checks,
  fifteenStage3Batch027Checks,
  fifteenStage3Batch028Checks,
  fifteenStage3Batch029Checks,
  fifteenStage3Batch030Checks,
  fifteenStage3Batch031Checks,
  fifteenStage3Batch032Checks,
  fifteenStage3Batch033Checks,
  fifteenStage3Batch034Checks,
  fifteenStage3Batch035Checks
]

theorem fifteenStage3AllBatchCertificates_replay :
    fifteenStage3AllBatchChecks.all id = true := by
  simp [fifteenStage3AllBatchChecks, fifteenStage3Batch000_checks,
      fifteenStage3Batch001_checks,
      fifteenStage3Batch002_checks,
      fifteenStage3Batch003_checks,
      fifteenStage3Batch004_checks,
      fifteenStage3Batch005_checks,
      fifteenStage3Batch006_checks,
      fifteenStage3Batch007_checks,
      fifteenStage3Batch008_checks,
      fifteenStage3Batch009_checks,
      fifteenStage3Batch010_checks,
      fifteenStage3Batch011_checks,
      fifteenStage3Batch012_checks,
      fifteenStage3Batch013_checks,
      fifteenStage3Batch014_checks,
      fifteenStage3Batch015_checks,
      fifteenStage3Batch016_checks,
      fifteenStage3Batch017_checks,
      fifteenStage3Batch018_checks,
      fifteenStage3Batch019_checks,
      fifteenStage3Batch020_checks,
      fifteenStage3Batch021_checks,
      fifteenStage3Batch022_checks,
      fifteenStage3Batch023_checks,
      fifteenStage3Batch024_checks,
      fifteenStage3Batch025_checks,
      fifteenStage3Batch026_checks,
      fifteenStage3Batch027_checks,
      fifteenStage3Batch028_checks,
      fifteenStage3Batch029_checks,
      fifteenStage3Batch030_checks,
      fifteenStage3Batch031_checks,
      fifteenStage3Batch032_checks,
      fifteenStage3Batch033_checks,
      fifteenStage3Batch034_checks,
      fifteenStage3Batch035_checks]

def fifteenStage3ManifestMatchesStageZero : Bool := Id.run do
  let some records := fifteenStage3ManifestRecords? | return false
  let patterns := records.map (·.pattern)
  let survivors := fifteenStage0SurvivorPatterns
  let closed := records.filter (·.closed)
  let remaining := records.filter (!·.closed)
  return records.all fifteenStage3ManifestEntryValid &&
    records.length == 378 && patterns.eraseDups.length == 378 &&
    closed.length == 355 && remaining.length == 23 &&
    survivors.length == 378 && survivors.eraseDups.length == 378 &&
    patterns.all survivors.contains && survivors.all patterns.contains

theorem fifteenStage3ManifestMatchesStageZero_replays :
    fifteenStage3ManifestMatchesStageZero = true := by
  native_decide

def fifteenStage3ResidualPatterns : List String :=
  match fifteenStage3ManifestRecords? with
  | some records => (records.filter (!·.closed)).map (·.pattern)
  | none => []

def fifteenStage3ClosedCertificateCoverage : Bool := Id.run do
  let some records := fifteenStage3ManifestRecords? | return false
  let closed := (records.filter (·.closed)).map (·.pattern)
  let certified := fifteenStage3CertifiedPatterns
  return closed.length == 355 && certified.length == 355 &&
    closed.eraseDups.length == 355 && certified.eraseDups.length == 355 &&
    closed.all certified.contains && certified.all closed.contains

theorem fifteenStage3ClosedCertificateCoverage_replays :
    fifteenStage3ClosedCertificateCoverage = true := by
  native_decide

theorem fifteenStage3FiniteCertificates_replay :
    fifteenStage3TableValid && fifteenStage3ManifestMatchesStageZero &&
      fifteenStage3ClosedCertificateCoverage &&
      fifteenStage3AllBatchChecks.all id = true := by
  rw [fifteenStage3Table_valid,
    fifteenStage3ManifestMatchesStageZero_replays,
    fifteenStage3ClosedCertificateCoverage_replays,
    fifteenStage3AllBatchCertificates_replay]
  rfl

end CirclePacking
