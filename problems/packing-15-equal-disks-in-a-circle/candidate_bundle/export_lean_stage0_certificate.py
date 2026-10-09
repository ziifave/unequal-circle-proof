#!/usr/bin/env python3
"""Export the stage-zero JSON witnesses to a compact Lean-readable format.

The generated files are proof data, not trusted computations: the Lean replay
checks orbit coverage, assignment coverage, every edge, and every negative
cycle using exact finite arithmetic.
"""

from __future__ import annotations

import gzip
import json
from pathlib import Path


ROOT = Path(__file__).resolve().parent
SOURCE = ROOT / "stage0_certificate.json.gz"
CYCLE_OUTPUT = ROOT / "stage0_cycles.txt"
ORBIT_OUTPUT = ROOT / "stage0_orbits.txt"
N = 15
TWO_PI_UP = 17600
Q = (
    (1610, 0, 0, 840),
    (0, 0, 0, 0),
    (0, 0, 3360, 2408),
    (840, 0, 2408, 2408),
)


def edge_code(edge: list[object]) -> str:
    source, target, kind = edge
    if not isinstance(source, int) or not isinstance(target, int):
        raise ValueError(f"invalid edge vertices: {edge!r}")
    if not 0 <= source < N or not 0 <= target < N:
        raise ValueError(f"edge vertex outside 0..14: {edge!r}")
    if kind not in {"O", "L", "U"}:
        raise ValueError(f"unknown edge kind: {edge!r}")
    encode_vertex = lambda value: str(value) if value < 10 else chr(ord("A") + value - 10)
    return encode_vertex(source) + encode_vertex(target) + str(kind)


def no_negative_cycle_potential(pattern: str, assignment: str) -> list[int]:
    labels = [0] * N
    inner = [i for i, bit in enumerate(pattern) if bit == "1"]
    if len(inner) != len(assignment) or set(assignment) - {"1", "2", "3"}:
        raise ValueError(f"invalid UNKNOWN witness: {pattern} {assignment}")
    for vertex, digit in zip(inner, assignment):
        labels[vertex] = int(digit)

    edges: list[tuple[int, int, int]] = [(i + 1, i, 0) for i in range(N - 1)]
    for i in range(N):
        for j in range(i + 1, N):
            q = Q[labels[i]][labels[j]]
            edges.append((j, i, -q))
            edges.append((i, j, TWO_PI_UP - q))

    distance = [0] * N
    for _ in range(N):
        for source, target, weight in edges:
            distance[target] = min(distance[target], distance[source] + weight)
    offset = min(distance)
    potential = [value - offset for value in distance]
    if any(potential[target] > potential[source] + weight
           for source, target, weight in edges):
        raise ValueError(f"UNKNOWN witness has a negative cycle: {pattern} {assignment}")
    return potential


def main() -> None:
    with gzip.open(SOURCE, "rt", encoding="utf-8") as source:
        document = json.load(source)
    if document.get("format") != "unequal-circle-stage0-v1":
        raise ValueError("unexpected stage-zero certificate format")
    records = document.get("orbits")
    if not isinstance(records, list) or len(records) != 760:
        raise ValueError("expected exactly 760 orbit records")

    cycle_encodings: set[str] = set()
    record_codes: dict[str, dict[str, object]] = {}
    for record in records:
        pattern = record["pattern"]
        status = record["status"]
        if not isinstance(pattern, str) or len(pattern) != N or set(pattern) - {"0", "1"}:
            raise ValueError(f"invalid orbit pattern: {pattern!r}")
        if pattern in record_codes:
            raise ValueError(f"duplicate orbit pattern: {pattern}")
        if status == "NEGATIVE_CYCLES":
            cases = record["cases"]
            if not isinstance(cases, list) or not cases:
                raise ValueError(f"missing cycle cases for {pattern}")
            for case in cases:
                code = "".join(edge_code(edge) for edge in case["cycle"])
                if not code or len(code) % 3:
                    raise ValueError(f"invalid cycle encoding for {pattern}")
                cycle_encodings.add(code)
            record_codes[pattern] = record
        elif status == "UNKNOWN":
            if record.get("cases") != []:
                raise ValueError(f"UNKNOWN record has cycle cases: {pattern}")
            record_codes[pattern] = record
        else:
            raise ValueError(f"unexpected orbit status: {status!r}")

    cycles = sorted(cycle_encodings)
    cycle_ids = {code: index for index, code in enumerate(cycles)}
    CYCLE_OUTPUT.write_text("\n".join(cycles) + "\n", encoding="ascii")

    orbit_lines: list[str] = []
    for pattern in sorted(record_codes):
        record = record_codes[pattern]
        if record["status"] == "NEGATIVE_CYCLES":
            assignments = []
            seen: set[str] = set()
            for case in record["cases"]:
                assignment = case["assignment"]
                if assignment in seen:
                    raise ValueError(f"duplicate assignment {assignment} for {pattern}")
                seen.add(assignment)
                code = "".join(edge_code(edge) for edge in case["cycle"])
                assignments.append(f"{assignment}:{cycle_ids[code]}")
            orbit_lines.append(f"{pattern}|E|{','.join(assignments)}")
        else:
            witness = record["witness"]
            potential = ",".join(map(str, no_negative_cycle_potential(pattern, witness)))
            orbit_lines.append(f"{pattern}|U|{witness}|{potential}")
    ORBIT_OUTPUT.write_text("\n".join(orbit_lines) + "\n", encoding="ascii")

    print(
        f"wrote {len(cycles)} unique cycles and {len(orbit_lines)} orbit records; "
        f"{sum(len(row.get('cases', [])) for row in records)} excluded assignments; "
        f"{CYCLE_OUTPUT.stat().st_size + ORBIT_OUTPUT.stat().st_size:,} bytes"
    )


if __name__ == "__main__":
    main()
