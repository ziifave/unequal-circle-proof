"""Build a radial-partition certificate from MPFI dump lines."""
from __future__ import annotations

import argparse
from decimal import Decimal, ROUND_FLOOR
from pathlib import Path

import numpy as np
from scipy.optimize import linprog

def rows_for_order(n: int) -> list[list[int]]:
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


def coeffs(values: list[Decimal], rows: list[list[int]], n: int) -> list[str]:
    result = linprog(np.ones(n), A_ub=-np.asarray(rows, dtype=float),
                     b_ub=-np.asarray([float(x) for x in values]),
                     bounds=[(0, None)] * n, method="highs")
    if not result.success:
        raise RuntimeError(result.message)
    out = []
    for x in result.ineqlin.marginals:
        d = Decimal(str(max(0.0, -x))).quantize(Decimal("1e-15"),
                                                  rounding=ROUND_FLOOR)
        d = (d * Decimal("0.999999999999")).quantize(
            Decimal("1e-15"), rounding=ROUND_FLOOR)
        out.append(str(d))
    return out


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("dump", type=Path)
    ap.add_argument("output", type=Path)
    ap.add_argument("--rho", required=True)
    ap.add_argument("--n", type=int, default=6)
    args = ap.parse_args()
    lines = [line.split() for line in args.dump.read_text().splitlines()
             if line.startswith("CELL")]
    n = args.n
    rows = rows_for_order(n)
    with args.output.open("w") as out:
        out.write(f"RHO {args.rho} {len(lines)}\n")
        for tokens in lines:
            order = list(map(int, tokens[1:1 + n]))
            offset = 1 + n
            bounds = tokens[offset:offset + 2 * n]
            angles = [Decimal(x) for x in tokens[offset + 2 * n:]]
            if len(angles) != n * (n - 1) // 2:
                raise RuntimeError(f"bad angle count: {len(angles)}")
            dual = coeffs([x for a in angles for x in (a, a)], rows, n)
            out.write("CELL " + " ".join(map(str, order)) + " " +
                      " ".join(bounds + dual) + "\n")
    print(f"wrote {len(lines)} cells to {args.output}")


if __name__ == "__main__":
    main()
