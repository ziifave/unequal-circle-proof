import CirclePacking.FifteenStage4Batch000
import CirclePacking.FifteenStage4Batch001
import CirclePacking.FifteenStage4Batch002
import CirclePacking.FifteenStage4Batch003
import CirclePacking.FifteenStage4Batch004
import CirclePacking.FifteenStage4Batch005
import CirclePacking.FifteenStage4Batch006
import CirclePacking.FifteenStage4Batch007
import CirclePacking.FifteenStage4Batch008
import CirclePacking.FifteenStage4Batch009
import CirclePacking.FifteenStage4Batch010
import CirclePacking.FifteenStage4Batch011
import CirclePacking.FifteenStage4Batch012
import CirclePacking.FifteenStage4Batch013
import CirclePacking.FifteenStage4Batch014
import CirclePacking.FifteenStage4Batch015
import CirclePacking.FifteenStage4Batch016
import CirclePacking.FifteenStage4Batch017
import CirclePacking.FifteenStage4Batch018

/-! Stage 4 replays the 19 CLOSED Stage 3 survivors. The four patterns that
remain after this finite certificate are handed on to the local analysis. -/

namespace CirclePacking

private structure Stage4ManifestEntry where
  pattern : String
  innerCount : Nat
  closed : Bool

private def fifteenStage4ManifestSource : String :=
  include_str "../data/fifteen_stage4_manifest.tsv"

private def fifteenStage3ManifestSource : String :=
  include_str "../data/fifteen_stage3_manifest.tsv"

private def fifteenStage4ManifestLine? (line : String) : Option Stage4ManifestEntry := do
  let fields := line.splitOn "\t"
  let status ← fields[0]?
  let countText ← fields[1]?
  let pattern ← fields[2]?
  let count ← countText.toNat?
  let closed ← if status == "CLOSED" then some true
    else if status == "UNKNOWN" then some false else none
  some ⟨pattern, count, closed⟩

private def fifteenStage4ParseManifest (source : String) : Option (List Stage4ManifestEntry) := do
  let lines := (source.splitOn "\n").filter (· != "")
  lines.mapM fifteenStage4ManifestLine?

private def fifteenStage4ManifestEntryValid (entry : Stage4ManifestEntry) : Bool :=
  let bits := entry.pattern.toList
  bits.length == 15 && bits.all (fun c => c == '0' || c == '1') &&
    (bits.filter (· == '1')).length == entry.innerCount &&
    5 ≤ entry.innerCount && entry.innerCount ≤ 8

def fifteenStage4ResidualPatterns : List String :=
  match fifteenStage4ParseManifest fifteenStage4ManifestSource with
  | some records => (records.filter (!·.closed)).map (·.pattern)
  | none => []

def fifteenStage4CertifiedPatterns : List String :=
  fifteenStage4Batch000Patterns ++
  fifteenStage4Batch001Patterns ++
  fifteenStage4Batch002Patterns ++
  fifteenStage4Batch003Patterns ++
  fifteenStage4Batch004Patterns ++
  fifteenStage4Batch005Patterns ++
  fifteenStage4Batch006Patterns ++
  fifteenStage4Batch007Patterns ++
  fifteenStage4Batch008Patterns ++
  fifteenStage4Batch009Patterns ++
  fifteenStage4Batch010Patterns ++
  fifteenStage4Batch011Patterns ++
  fifteenStage4Batch012Patterns ++
  fifteenStage4Batch013Patterns ++
  fifteenStage4Batch014Patterns ++
  fifteenStage4Batch015Patterns ++
  fifteenStage4Batch016Patterns ++
  fifteenStage4Batch017Patterns ++
  fifteenStage4Batch018Patterns

def fifteenStage4AllBatchChecks : List Bool := [
  fifteenStage4Batch000Checks,
  fifteenStage4Batch001Checks,
  fifteenStage4Batch002Checks,
  fifteenStage4Batch003Checks,
  fifteenStage4Batch004Checks,
  fifteenStage4Batch005Checks,
  fifteenStage4Batch006Checks,
  fifteenStage4Batch007Checks,
  fifteenStage4Batch008Checks,
  fifteenStage4Batch009Checks,
  fifteenStage4Batch010Checks,
  fifteenStage4Batch011Checks,
  fifteenStage4Batch012Checks,
  fifteenStage4Batch013Checks,
  fifteenStage4Batch014Checks,
  fifteenStage4Batch015Checks,
  fifteenStage4Batch016Checks,
  fifteenStage4Batch017Checks,
  fifteenStage4Batch018Checks
]

theorem fifteenStage4AllBatchCertificates_replay :
    fifteenStage4AllBatchChecks.all id = true := by
  simp [fifteenStage4AllBatchChecks, fifteenStage4Batch000_checks,
      fifteenStage4Batch001_checks,
      fifteenStage4Batch002_checks,
      fifteenStage4Batch003_checks,
      fifteenStage4Batch004_checks,
      fifteenStage4Batch005_checks,
      fifteenStage4Batch006_checks,
      fifteenStage4Batch007_checks,
      fifteenStage4Batch008_checks,
      fifteenStage4Batch009_checks,
      fifteenStage4Batch010_checks,
      fifteenStage4Batch011_checks,
      fifteenStage4Batch012_checks,
      fifteenStage4Batch013_checks,
      fifteenStage4Batch014_checks,
      fifteenStage4Batch015_checks,
      fifteenStage4Batch016_checks,
      fifteenStage4Batch017_checks,
      fifteenStage4Batch018_checks]

def fifteenStage4ManifestMatchesStage3 : Bool := Id.run do
  let some stage3Records := fifteenStage4ParseManifest fifteenStage3ManifestSource | return false
  let some stage4Records := fifteenStage4ParseManifest fifteenStage4ManifestSource | return false
  let stage3Patterns := stage3Records.map (·.pattern)
  let stage3Closed := stage3Records.filter (·.closed)
  let stage3Remaining := (stage3Records.filter (!·.closed)).map (·.pattern)
  let patterns := stage4Records.map (·.pattern)
  let closed := (stage4Records.filter (·.closed)).map (·.pattern)
  let remaining := (stage4Records.filter (!·.closed)).map (·.pattern)
  let certified := fifteenStage4CertifiedPatterns
  return stage3Records.all fifteenStage4ManifestEntryValid &&
    stage3Records.length == 378 && stage3Patterns.eraseDups.length == 378 &&
    stage3Closed.length == 355 && stage3Remaining.length == 23 &&
    stage4Records.all fifteenStage4ManifestEntryValid &&
    stage4Records.length == 23 && patterns.eraseDups.length == 23 &&
    closed.length == 19 && remaining.length == 4 &&
    patterns == stage3Remaining &&
    certified.length == 19 && certified.eraseDups.length == 19 &&
    closed.length == certified.length && closed.all certified.contains &&
    certified.all closed.contains

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fifteenStage4ManifestMatchesStage3_replays :
    fifteenStage4ManifestMatchesStage3 = true := by
  native_decide

theorem fifteenStage4FiniteCertificates_replay :
    fifteenStage4TableValid && fifteenStage4ManifestMatchesStage3 &&
      fifteenStage4AllBatchChecks.all id = true := by
  rw [fifteenStage4Table_valid,
    fifteenStage4ManifestMatchesStage3_replays,
    fifteenStage4AllBatchCertificates_replay]
  rfl

end CirclePacking
