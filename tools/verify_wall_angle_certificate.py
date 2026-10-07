"""SciPy-free replay of a wall-contact Farkas certificate."""
from __future__ import annotations

import argparse
import itertools
import json
from decimal import ROUND_CEILING
from pathlib import Path

from proof.angular import PI_HI, _acos_lower, _binary, _div
from proof.interval import D, Interval, set_precision


def rows_for_order(order):
    n = len(order)
    rows = []
    for a in range(n):
        for b in range(a + 1, n):
            for path in ([(a + t) % n for t in range(b - a)],
                         [(b + t) % n for t in range(a - b + n)]):
                row = [0] * n
                for gap in path:
                    row[gap] = 1
                rows.append(row)
    return rows


def wall_angle(i, j, rho):
    ri = Interval.sqrt_integer(i).lo
    rj = Interval.sqrt_integer(j).lo
    numerator = _binary(D(2), _binary(ri, rj, "*", "ROUND_FLOOR"), "*", "ROUND_FLOOR")
    di = _binary(rho, ri, "-", "ROUND_CEILING")
    dj = _binary(rho, rj, "-", "ROUND_CEILING")
    denominator = _binary(di, dj, "*", "ROUND_CEILING")
    cosine = _binary(D(1), _div(numerator, denominator, "ROUND_FLOOR"), "-", "ROUND_CEILING")
    return _acos_lower(cosine)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("certificate", type=Path)
    ap.add_argument("--precision", type=int, default=90)
    args = ap.parse_args()
    set_precision(args.precision)
    data = json.loads(args.certificate.read_text())
    labels = tuple(data["wall_set"])
    rho = D(data["rho"])
    two_pi = _binary(D(2), PI_HI, "*", ROUND_CEILING)
    failures = []
    minimum = None
    for record in data["orders"]:
        order = tuple(record["order"])
        rows = rows_for_order(order)
        coeffs = [D(x) for x in record["coefficients"]]
        values = []
        for a in range(len(order)):
            for b in range(a + 1, len(order)):
                value = wall_angle(order[a], order[b], rho)
                values.extend((value, value))
        for g in range(len(order)):
            used = sum((coeffs[k] for k, row in enumerate(rows) if row[g]), D(0))
            if used > D(1):
                failures.append((order, f"column {g}={used}"))
        dual = sum((coeffs[k] * values[k] for k in range(len(rows))), D(0))
        minimum = dual if minimum is None or dual < minimum else minimum
        if dual <= two_pi:
            failures.append((order, f"dual={dual}"))
    if failures:
        raise SystemExit(json.dumps({"status": "failed", "failures": failures[:5]}, indent=2))
    print(json.dumps({"status": "passed", "orders": len(data["orders"]),
                      "minimum_dual_value": str(minimum), "two_pi_upper": str(two_pi),
                      "margin": str(minimum - two_pi)}, indent=2))


if __name__ == "__main__":
    main()
