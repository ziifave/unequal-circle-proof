"""Build a Farkas certificate from MPFI-produced angular lower bounds.

SciPy is used only to discover a dual solution.  The emitted coefficients are
decimal-rounded inward; the MPFI C replay is the proof check.
"""
from __future__ import annotations

import argparse
import json
from decimal import Decimal, ROUND_FLOOR
from pathlib import Path

import numpy as np
from scipy.optimize import linprog


N = 6


def rows_for_order(order: tuple[int, ...]) -> list[list[int]]:
    rows: list[list[int]] = []
    for a in range(N):
        for b in range(a + 1, N):
            for path in (
                [(a + t) % N for t in range(b - a)],
                [(b + t) % N for t in range(a - b + N)],
            ):
                row = [0] * N
                for gap in path:
                    row[gap] = 1
                rows.append(row)
    return rows


def inward_coefficients(values: list[Decimal], rows: list[list[int]]) -> list[str]:
    # Discover a feasible dual with floating point only.  The result is not
    # trusted: every emitted decimal is rounded inward and replayed with MPFI.
    b = -np.asarray([float(v) for v in values], dtype=float)
    A = -np.asarray(rows, dtype=float)
    result = linprog(np.ones(N), A_ub=A, b_ub=b, bounds=[(0, None)] * N,
                     method="highs")
    if not result.success:
        raise RuntimeError(result.message)
    raw = [max(0.0, -x) for x in result.ineqlin.marginals]
    out = []
    for x in raw:
        d = Decimal(str(x)).quantize(Decimal("1e-15"), rounding=ROUND_FLOOR)
        d = (d * Decimal("0.999999999999")).quantize(
            Decimal("1e-15"), rounding=ROUND_FLOOR)
        out.append(str(d))
    return out


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("source", type=Path, help="certificate with the order list")
    ap.add_argument("angles", type=Path, help="MPFI --dump-angles output")
    ap.add_argument("output", type=Path)
    ap.add_argument("--rho", help="override rho in the output certificate")
    args = ap.parse_args()

    source = json.loads(args.source.read_text())
    lines = [line.split() for line in args.angles.read_text().splitlines()
             if line.startswith("ANGLE")]
    if len(lines) != len(source["orders"]):
        raise RuntimeError(f"expected {len(source['orders'])} angle rows, got {len(lines)}")

    orders_out = []
    for old, tokens in zip(source["orders"], lines):
        order = tuple(map(int, tokens[1:1 + N]))
        if list(order) != old["order"]:
            raise RuntimeError(f"order mismatch: {order} != {old['order']}")
        angles = [Decimal(x) for x in tokens[1 + N:]]
        if len(angles) != 15:
            raise RuntimeError(f"expected 15 angles, got {len(angles)}")
        values = [x for angle in angles for x in (angle, angle)]
        rows = rows_for_order(order)
        coeffs = inward_coefficients(values, rows)
        orders_out.append({
            "order": list(order),
            "coefficients": coeffs,
            "mpfi_angle_lower_bounds": [str(x) for x in angles],
        })

    payload = {
        "rho": args.rho or source["rho"],
        "subset": source["subset"],
        "order_count": len(orders_out),
        "all_passed": None,
        "certificate_kernel": "MPFI 1.5.4, precision 256 bits",
        "orders": orders_out,
    }
    args.output.write_text(json.dumps(payload, indent=2) + "\n")
    print(json.dumps({"output": str(args.output), "order_count": len(orders_out)}, indent=2))


if __name__ == "__main__":
    main()
