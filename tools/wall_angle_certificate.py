"""Discover Farkas certificates for exact wall-contact angular cuts.

SciPy is used only to discover nonnegative multipliers.  The emitted JSON is
replayed by verify_wall_angle_certificate.py without SciPy.
"""
from __future__ import annotations

import argparse
import itertools
import json
from decimal import Decimal, ROUND_CEILING, ROUND_FLOOR
from pathlib import Path

import numpy as np
from scipy.optimize import linprog

from proof.angular import PI_HI, _acos_lower, _binary, _div
from proof.interval import D, Interval, set_precision

R0 = D("8.30346812211148907870438118751619932995021374053538480956519718050601105313024902726198893075288755767902953233329724278")


def orders(labels: tuple[int, ...]):
    first = labels[0]
    return [(first,) + tail for tail in itertools.permutations(labels[1:])
            if tail[0] < tail[-1]]


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


def wall_angle(i: int, j: int, rho: Decimal = R0) -> Decimal:
    ri = Interval.sqrt_integer(i).lo
    rj = Interval.sqrt_integer(j).lo
    numerator = _binary(D(2), _binary(ri, rj, "*", ROUND_FLOOR), "*", ROUND_FLOOR)
    di = _binary(rho, ri, "-", ROUND_CEILING)
    dj = _binary(rho, rj, "-", ROUND_CEILING)
    denominator = _binary(di, dj, "*", ROUND_CEILING)
    quotient = _div(numerator, denominator, ROUND_FLOOR)
    cosine = _binary(D(1), quotient, "-", ROUND_CEILING)
    return _acos_lower(cosine)


def discover(values, rows):
    result = linprog(np.ones(len(rows[0])),
                     A_ub=-np.asarray(rows, dtype=float),
                     b_ub=-np.asarray([float(v) for v in values]),
                     bounds=[(0, None)] * len(rows[0]), method="highs")
    if not result.success:
        return None
    coeffs = [Decimal(str(max(0.0, -v))).quantize(Decimal("1e-15"), rounding=ROUND_FLOOR)
              for v in result.ineqlin.marginals]
    return [(v * Decimal("0.999999999999")).quantize(Decimal("1e-15"), rounding=ROUND_FLOOR)
            for v in coeffs]


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--wall-set", required=True, help="comma-separated labels")
    ap.add_argument("--output", type=Path, required=True)
    ap.add_argument("--precision", type=int, default=90)
    args = ap.parse_args()
    set_precision(args.precision)
    labels = tuple(sorted(int(x) for x in args.wall_set.split(",")))
    records = []
    for order in orders(labels):
        rows = rows_for_order(order)
        values = []
        for a in range(len(order)):
            for b in range(a + 1, len(order)):
                value = wall_angle(order[a], order[b])
                values.extend((value, value))
        coeffs = discover(values, rows)
        if coeffs is None:
            records.append({"order": list(order), "passed": False, "reason": "LP feasible"})
            continue
        dual = sum((c * v for c, v in zip(coeffs, values)), D(0))
        columns = [sum((coeffs[k] for k, row in enumerate(rows) if row[g]), D(0))
                   for g in range(len(order))]
        two_pi = _binary(D(2), PI_HI, "*", ROUND_CEILING)
        records.append({"order": list(order), "coefficients": [str(c) for c in coeffs],
                        "dual_value": str(dual), "column_sums": [str(c) for c in columns],
                        "passed": dual > two_pi})
    payload = {"rho": str(R0), "wall_set": list(labels), "order_count": len(records),
               "all_passed": all(r["passed"] for r in records), "orders": records}
    args.output.write_text(json.dumps(payload, indent=2) + "\n")
    print(json.dumps({"output": str(args.output), "orders": len(records),
                      "all_passed": payload["all_passed"]}, indent=2))


if __name__ == "__main__":
    main()
