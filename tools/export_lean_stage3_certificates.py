#!/usr/bin/env python3
"""Generate compact Lean replay batches for the 15-disk Stage 3 closures.

The C++ search is only a certificate producer.  Its prefix tree is rewritten
to refer to a per-pattern dictionary of cycle edge topologies; Lean recomputes
all weights and checks every reference, split, and prune leaf.
"""

from __future__ import annotations

import pathlib
import subprocess
import tempfile


ROOT = pathlib.Path(__file__).resolve().parents[1]
BUNDLE = ROOT / "problems/packing-15-equal-disks-in-a-circle/candidate_bundle"
LEAN = ROOT / "problems/packing-disks-radii-sqrt1-to-sqrt10-in-a-circle/lean/CirclePacking"
SOURCE = BUNDLE / "export_stage3_certificate.cpp"
TABLE = BUNDLE / "stage3.tsv"
BATCH_SIZE = 10
BASE64 = "0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz-_"


def encode_id(value: int) -> str:
    if not 0 <= value < 4096:
        raise ValueError(f"cycle dictionary is too large: {value}")
    return BASE64[value // 64] + BASE64[value % 64]


def compact_tree(source: str) -> tuple[str, list[str]]:
    cycles: list[str] = []
    cycle_ids: dict[str, int] = {}
    output: list[str] = []

    def visit(index: int) -> int:
        if index >= len(source):
            raise ValueError("truncated prefix certificate")
        token = source[index]
        index += 1
        if token == "B":
            output.append("B")
            for _ in range(8):
                index = visit(index)
        elif token == "C":
            if index >= len(source):
                raise ValueError("truncated cycle length")
            count = int(source[index], 16)
            index += 1
            end = index + 3 * count
            if end > len(source):
                raise ValueError("truncated cycle edge list")
            cycle = source[index:end]
            if len(cycle) % 3:
                raise ValueError("malformed edge triples")
            cycle_id = cycle_ids.get(cycle)
            if cycle_id is None:
                cycle_id = len(cycles)
                cycle_ids[cycle] = cycle_id
                cycles.append(cycle)
            output.append("C" + encode_id(cycle_id))
            index = end
        elif token in "SORM":
            output.append(token)
        else:
            raise ValueError(f"unknown certificate token {token!r}")
        return index

    end = visit(0)
    if end != len(source):
        raise ValueError(f"{len(source) - end} trailing certificate characters")
    return "".join(output), cycles


def parse_stage3_table() -> list[tuple[str, int, str]]:
    records = []
    for line_number, line in enumerate(TABLE.read_text().splitlines(), 1):
        fields = line.split("\t")
        if len(fields) < 4 or fields[0] not in {"CLOSED", "UNKNOWN"}:
            raise ValueError(f"malformed Stage 3 row {line_number}")
        status, count, pattern = fields[:3]
        if len(pattern) != 15 or set(pattern) - {"0", "1"}:
            raise ValueError(f"invalid pattern in Stage 3 row {line_number}")
        count_value = int(count)
        if pattern.count("1") != count_value:
            raise ValueError(f"inner count mismatch in row {line_number}")
        records.append((status, count_value, pattern))
    patterns = [record[2] for record in records]
    if len(records) != 378 or len(set(patterns)) != len(patterns):
        raise ValueError("Stage 3 table must contain 378 unique patterns")
    if sum(status == "CLOSED" for status, _, _ in records) != 355:
        raise ValueError("Stage 3 table must contain 355 closed patterns")
    if sum(status == "UNKNOWN" for status, _, _ in records) != 23:
        raise ValueError("Stage 3 table must contain 23 survivor patterns")
    return records


def lean_batch_source(index: int, records: list[tuple[str, str, str]]) -> str:
    name = f"fifteenStage3Batch{index:03}"
    data_name = f"stage3_lean_batch_{index:03}.txt"
    patterns = ",\n  ".join(f'"{pattern}"' for pattern, _, _ in records)
    return f'''import CirclePacking.FifteenStage3Certificate

namespace CirclePacking

def {name}Source : String :=
  include_str "../../../../problems/packing-15-equal-disks-in-a-circle/candidate_bundle/{data_name}"

def {name}Patterns : List String := [
  {patterns}
]

def {name}Checks : Bool :=
  fifteenStage3CheckBatch {name}Source {name}Patterns

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem {name}_checks : {name}Checks = true := by
  native_decide

end CirclePacking
'''


def main() -> None:
    table = parse_stage3_table()
    closed = [pattern for status, _, pattern in table if status == "CLOSED"]
    records: list[tuple[str, str, str]] = []
    with tempfile.TemporaryDirectory(prefix="stage3-lean-export-") as temporary:
        tmp = pathlib.Path(temporary)
        executable = tmp / "export_stage3_certificate"
        subprocess.run(
            ["g++", "-O3", "-std=c++17", str(SOURCE), "-o", str(executable)],
            check=True,
        )
        for index, pattern in enumerate(closed):
            workdir = tmp / f"pattern-{index:03}"
            workdir.mkdir()
            result = subprocess.run(
                [str(executable), pattern],
                cwd=workdir,
                text=True,
                capture_output=True,
                check=False,
            )
            if result.returncode:
                raise RuntimeError(
                    f"producer failed for {pattern}: {result.stderr.strip()}"
                )
            raw_path = workdir / "stage3_certificate_000000010101011.txt"
            fields = raw_path.read_text().strip().split("\t")
            if len(fields) != 2 or fields[0] != pattern:
                raise ValueError(f"wrong raw certificate for {pattern}")
            tree, cycles = compact_tree(fields[1])
            if not cycles:
                raise ValueError(f"closed pattern {pattern} has no cycle witness")
            dictionary = ";".join(cycles)
            records.append((pattern, dictionary, tree))
            if (index + 1) % 50 == 0 or index + 1 == len(closed):
                print(f"generated {index + 1}/{len(closed)} Stage 3 certificates")

    batch_count = (len(records) + BATCH_SIZE - 1) // BATCH_SIZE
    imports = [
        f"import CirclePacking.FifteenStage3Batch{index:03}"
        for index in range(batch_count)
    ]
    for index in range(batch_count):
        batch = records[index * BATCH_SIZE : (index + 1) * BATCH_SIZE]
        data_path = BUNDLE / f"stage3_lean_batch_{index:03}.txt"
        data_path.write_text(
            "".join(f"{pattern}\t{cycles}\t{tree}\n" for pattern, cycles, tree in batch)
        )
        (LEAN / f"FifteenStage3Batch{index:03}.lean").write_text(
            lean_batch_source(index, batch)
        )

    index_names = [f"fifteenStage3Batch{index:03}" for index in range(batch_count)]
    patterns_expr = " ++\n  ".join(f"{name}Patterns" for name in index_names)
    checks_expr = ",\n  ".join(f"{name}Checks" for name in index_names)
    theorem_args = ",\n      ".join(f"{name}_checks" for name in index_names)
    aggregator = f'''{chr(10).join(imports)}
import CirclePacking.FifteenStageZero

/-! Stage 3 certificates for all 355 closed patterns among the 378
Stage 0 survivors. Each batch theorem checks its full compact prefix tree. -/

namespace CirclePacking

private structure Stage3ManifestEntry where
  pattern : String
  innerCount : Nat
  closed : Bool

private def fifteenStage3ManifestSource : String :=
  include_str "../../../../problems/packing-15-equal-disks-in-a-circle/candidate_bundle/stage3.tsv"

private def fifteenStage3ManifestLine? (line : String) : Option Stage3ManifestEntry := do
  let fields := line.splitOn "\\t"
  let status ← fields[0]?
  let countText ← fields[1]?
  let pattern ← fields[2]?
  let count ← countText.toNat?
  let closed ← if status == "CLOSED" then some true
    else if status == "UNKNOWN" then some false else none
  some ⟨pattern, count, closed⟩

private def fifteenStage3ManifestRecords? : Option (List Stage3ManifestEntry) := do
  let lines := (fifteenStage3ManifestSource.splitOn "\\n").filter (· != "")
  lines.mapM fifteenStage3ManifestLine?

private def fifteenStage3ManifestEntryValid (entry : Stage3ManifestEntry) : Bool :=
  let bits := entry.pattern.toList
  bits.length == 15 && bits.all (fun c => c == '0' || c == '1') &&
    (bits.filter (· == '1')).length == entry.innerCount &&
    5 ≤ entry.innerCount && entry.innerCount ≤ 8

def fifteenStage3CertifiedPatterns : List String :=
  {patterns_expr}

def fifteenStage3AllBatchChecks : List Bool := [
  {checks_expr}
]

theorem fifteenStage3AllBatchCertificates_replay :
    fifteenStage3AllBatchChecks.all id = true := by
  simp [fifteenStage3AllBatchChecks, {theorem_args}]

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
'''
    (LEAN / "FifteenStages34.lean").write_text(aggregator)
    print(
        f"wrote {batch_count} Lean batches, {len(records)} certificates, "
        f"{sum((BUNDLE / f'stage3_lean_batch_{i:03}.txt').stat().st_size for i in range(batch_count)):,} data bytes"
    )


if __name__ == "__main__":
    main()
