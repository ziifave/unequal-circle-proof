"""Replay fixed-order angular Farkas certificates without SciPy."""
from __future__ import annotations

import argparse
import itertools
import json
from pathlib import Path

from proof.angular import PI_HI, _angle_lower, _binary
from proof.interval import D, set_precision
from proof.model import PackingModel
from decimal import ROUND_CEILING

S = (5, 6, 7, 8, 9, 10)


def rows_for_order(order):
    rows = []
    for a in range(6):
        for b in range(a + 1, 6):
            for path in ([(a + t) % 6 for t in range(b - a)],
                         [(b + t) % 6 for t in range(a - b + 6)]):
                row = [0] * 6
                for gap in path:
                    row[gap] = 1
                rows.append(row)
    return rows


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("certificate", type=Path)
    ap.add_argument("--precision", type=int, default=90)
    args = ap.parse_args()
    data = json.loads(args.certificate.read_text())
    set_precision(args.precision)
    model = PackingModel(6, data["rho"], tuple(data["subset"]))
    box = model.root_box()
    two_pi = _binary(D(2), PI_HI, "*", ROUND_CEILING)
    failures = []
    minimum = None
    for record in data["orders"]:
        order = tuple(record["order"])
        rows = rows_for_order(order)
        coeffs = [D(x) for x in record["coefficients"]]
        if len(rows) != len(coeffs):
            failures.append((order, "coefficient count")); continue
        for g in range(6):
            used = sum((coeffs[k] for k, row in enumerate(rows) if row[g]), D(0))
            if used > D(1):
                failures.append((order, f"column {g}={used}"))
        values = []
        for a in range(6):
            for b in range(a + 1, 6):
                angle = _angle_lower(model, box, S.index(order[a]), S.index(order[b]))
                values.extend((angle, angle))
        value = sum((coeffs[k] * values[k] for k in range(len(rows))), D(0))
        if minimum is None or value < minimum:
            minimum = value
        if value <= two_pi:
            failures.append((order, f"dual value {value}"))
    if failures:
        raise SystemExit(json.dumps({"status": "failed", "failures": failures[:5]}, indent=2))
    print(json.dumps({"status": "passed", "orders": len(data["orders"]),
                      "minimum_dual_value": str(minimum),
                      "two_pi_upper": str(two_pi),
                      "margin": str(minimum - two_pi)}, indent=2))


if __name__ == "__main__":
    main()
