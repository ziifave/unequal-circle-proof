#!/usr/bin/env python3
"""Generate Stage 4 prefix-tree certificates for Lean replay.

The C++ program only searches for pruning witnesses.  The generated Lean
checker validates branch coverage, every structural leaf, and the topology
and exact tick-weight of each recorded negative cycle without rerunning
Bellman--Ford.
"""

from __future__ import annotations

import pathlib
import subprocess
import tempfile


ROOT = pathlib.Path(__file__).resolve().parents[1]
NEW_BUNDLE = ROOT / "problems/packing-15-equal-disks-in-a-circle/candidate_bundle"
OLD_BUNDLE = ROOT / "problems/packing-15-equal-disks-in-a-circle/candidate_bundle"
BUNDLE = NEW_BUNDLE if (NEW_BUNDLE / "stage4.tsv").exists() else OLD_BUNDLE
LEAN = ROOT / "problems/packing-disks-radii-sqrt1-to-sqrt10-in-a-circle/lean/CirclePacking"
LEAN_DATA = LEAN.parent / "data"
SOURCE = NEW_BUNDLE / "export_stage4_certificate.cpp"
BASE64 = "0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz-_"
CHOICES = 12


def write_if_changed(path: pathlib.Path, content: str) -> None:
    if not path.exists() or path.read_text() != content:
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(content)


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
            for _ in range(CHOICES):
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


def read_rows(path: pathlib.Path, expected_count: int) -> list[tuple[str, int, str]]:
    records: list[tuple[str, int, str]] = []
    for line_number, line in enumerate(path.read_text().splitlines(), 1):
        fields = line.split("\t")
        if len(fields) < 3 or fields[0] not in {"CLOSED", "UNKNOWN"}:
            raise ValueError(f"malformed row {line_number} in {path}")
        status, count_text, pattern = fields[:3]
        count = int(count_text)
        if len(pattern) != 15 or set(pattern) - {"0", "1"}:
            raise ValueError(f"invalid pattern in row {line_number} of {path}")
        if pattern.count("1") != count or not 5 <= count <= 8:
            raise ValueError(f"inner count mismatch in row {line_number} of {path}")
        records.append((status, count, pattern))
    patterns = [record[2] for record in records]
    if len(records) != expected_count or len(set(patterns)) != expected_count:
        raise ValueError(f"{path} must contain {expected_count} unique records")
    return records


def validate_manifests() -> list[tuple[str, int, str]]:
    stage3 = read_rows(BUNDLE / "stage3.tsv", 378)
    stage4 = read_rows(BUNDLE / "stage4.tsv", 23)
    stage3_remaining = [pattern for status, _, pattern in stage3 if status == "UNKNOWN"]
    stage4_patterns = [pattern for _, _, pattern in stage4]
    if len(stage3_remaining) != 23 or stage4_patterns != stage3_remaining:
        raise ValueError("Stage 4 input does not exactly match Stage 3 survivors")
    closed = [row for row in stage4 if row[0] == "CLOSED"]
    remaining = [row for row in stage4 if row[0] == "UNKNOWN"]
    if len(closed) != 19 or len(remaining) != 4:
        raise ValueError("Stage 4 manifest must have 19 closed and 4 residual rows")
    return stage4


def batch_module(index: int, pattern: str) -> str:
    name = f"fifteenStage4Batch{index:03}"
    data_name = f"stage4_lean_batch_{index:03}.txt"
    return f'''import CirclePacking.FifteenStage4Certificate

namespace CirclePacking

def {name}Source : String :=
  include_str "../../../../problems/packing-15-equal-disks-in-a-circle/candidate_bundle/{data_name}"

def {name}Patterns : List String := ["{pattern}"]

def {name}Checks : Bool :=
  fifteenStage4CheckBatch {name}Source {name}Patterns

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem {name}_checks : {name}Checks = true := by
  native_decide

end CirclePacking
'''


def manifest_module(rows: list[tuple[str, int, str]]) -> str:
    modules = [f"FifteenStage4Batch{i:03}" for i in range(19)]
    imports = "\n".join(f"import CirclePacking.{module}" for module in modules)
    pattern_names = [f"fifteenStage4Batch{i:03}Patterns" for i in range(19)]
    check_names = [f"fifteenStage4Batch{i:03}Checks" for i in range(19)]
    theorem_names = [f"fifteenStage4Batch{i:03}_checks" for i in range(19)]
    patterns_expr = " ++\n  ".join(pattern_names)
    checks_expr = ",\n  ".join(check_names)
    theorem_args = ",\n      ".join(theorem_names)
    return f'''{imports}

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
  let fields := line.splitOn "\\t"
  let status ← fields[0]?
  let countText ← fields[1]?
  let pattern ← fields[2]?
  let count ← countText.toNat?
  let closed ← if status == "CLOSED" then some true
    else if status == "UNKNOWN" then some false else none
  some ⟨pattern, count, closed⟩

private def fifteenStage4ParseManifest (source : String) : Option (List Stage4ManifestEntry) := do
  let lines := (source.splitOn "\\n").filter (· != "")
  lines.mapM fifteenStage4ManifestLine?

private def fifteenStage4ManifestEntryValid (entry : Stage4ManifestEntry) : Bool :=
  let bits := entry.pattern.toList
  bits.length == 15 && bits.all (fun c => c == '0' || c == '1') &&
    (bits.filter (· == '1')).length == entry.innerCount &&
    5 ≤ entry.innerCount && entry.innerCount ≤ 8

def fifteenStage4CertifiedPatterns : List String :=
  {patterns_expr}

def fifteenStage4AllBatchChecks : List Bool := [
  {checks_expr}
]

theorem fifteenStage4AllBatchCertificates_replay :
    fifteenStage4AllBatchChecks.all id = true := by
  simp [fifteenStage4AllBatchChecks, {theorem_args}]

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
'''


def main() -> None:
    rows = validate_manifests()
    closed = [pattern for status, _, pattern in rows if status == "CLOSED"]
    LEAN_DATA.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(prefix="stage4-lean-export-") as temporary:
        tmp = pathlib.Path(temporary)
        executable = tmp / "export_stage4_certificate"
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
            raw_path = workdir / f"stage4_certificate_{pattern}.txt"
            fields = raw_path.read_text().strip().split("\t")
            if len(fields) != 2 or fields[0] != pattern:
                raise ValueError(f"wrong raw certificate for {pattern}")
            tree, cycles = compact_tree(fields[1])
            if not cycles:
                raise ValueError(f"closed pattern {pattern} has no cycle witness")
            dictionary = ";".join(cycles)
            data_name = f"stage4_lean_batch_{index:03}.txt"
            write_if_changed(
                NEW_BUNDLE / data_name,
                f"{pattern}\t{dictionary}\t{tree}\n",
            )
            write_if_changed(
                LEAN / f"FifteenStage4Batch{index:03}.lean",
                batch_module(index, pattern),
            )
            print(
                f"generated {index + 1}/{len(closed)} Stage 4 certificates: "
                f"{pattern}, {result.stderr.strip()}, {len(tree)} compact bytes",
                flush=True,
            )

    write_if_changed(
        LEAN_DATA / "fifteen_stage3_manifest.tsv",
        (BUNDLE / "stage3.tsv").read_text(),
    )
    manifest = BUNDLE / "stage4.tsv"
    write_if_changed(LEAN_DATA / "fifteen_stage4_manifest.tsv", manifest.read_text())
    write_if_changed(LEAN / "FifteenStage4.lean", manifest_module(rows))
    print(f"wrote 19 Stage 4 certificate modules and manifest", flush=True)


if __name__ == "__main__":
    main()
