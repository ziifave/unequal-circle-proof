"""Replay all-pair Farkas records with directed Decimal arithmetic."""
from __future__ import annotations

import argparse
import gzip
import json
from decimal import Decimal, ROUND_CEILING, ROUND_FLOOR
from pathlib import Path

from proof.interval import D, _binary, set_precision
from proof.angular import _angle_lower
from proof.interval import Interval
from proof.model import Box, PackingModel


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("certificate", type=Path)
    parser.add_argument("--survivors", type=Path,
                        help="recompute the recorded angle bounds from boxes")
    args = parser.parse_args()
    with gzip.open(args.certificate, "rt", encoding="utf-8") as stream:
        rows = [json.loads(line) for line in stream if line.strip()]
    header = rows[0]
    set_precision(int(header["precision"]))
    threshold = _binary(D(2), D("3.14159265358979323846264338327950288419716939937511"), "*", ROUND_CEILING)
    expected_angles = {}
    if args.survivors:
        frontier = json.loads(args.survivors.read_text(encoding="utf-8"))
        labels = tuple(frontier["radii_squared"])
        model = PackingModel(len(labels), frontier["rho"], labels)
        for raw in frontier["queued_boxes"]:
            if raw["node"] not in header["nodes"]:
                continue
            box = Box(tuple(Interval.from_json(pair) for pair in raw["coords"]))
            expected_angles[raw["node"]] = {
                (min(labels[i], labels[j]), max(labels[i], labels[j])):
                _angle_lower(model, box, i, j)
                for i in range(model.n) for j in range(i)
            }
    failures = 0
    for row in rows[1:]:
        angles = [D(value) for value in row["angles"]]
        coeffs = [D(value) for value in row["coefficients"]]
        n = len(row["order"])
        if expected_angles:
            weights = expected_angles[row["node"]]
            expected = []
            for a in range(n):
                for b in range(a + 1, n):
                    edge = (min(row["order"][a], row["order"][b]),
                            max(row["order"][a], row["order"][b]))
                    expected.extend((weights[edge], weights[edge]))
            if any(recorded > actual for recorded, actual in zip(angles, expected)):
                failures += 1
        columns = [D(0)] * n
        total = D(0)
        k = 0
        for value, coeff in zip(angles, coeffs):
            if coeff < 0:
                failures += 1
                continue
            total = _binary(total, _binary(coeff, value, "*", ROUND_FLOOR), "+", ROUND_FLOOR)
            # Reconstruct path incidence from the record order.
            pair_index = k // 2
            pair = []
            cursor = 0
            for a in range(n):
                for b in range(a + 1, n):
                    if cursor == pair_index:
                        pair = [a, b]
                    cursor += 1
            a, b = pair
            path = list(range(a, b)) if k % 2 == 0 else list(range(b, n)) + list(range(0, a))
            for gap in path:
                columns[gap] = _binary(columns[gap], coeff, "+", ROUND_CEILING)
            k += 1
        if any(value > D(1) for value in columns) or total <= threshold:
            failures += 1
    print(json.dumps({"records": len(rows) - 1, "failures": failures,
                      "status": "PASSED" if failures == 0 else "FAILED"}, indent=2))
    raise SystemExit(1 if failures else 0)


if __name__ == "__main__":
    main()
