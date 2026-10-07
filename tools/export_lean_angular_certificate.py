"""Export a validated angular certificate as exact rational data for Lean.

The MPFI/Decimal verifier remains responsible for discovering the lower
angles.  This exporter deliberately rounds every lower angle downward and
every coefficient upward to rational values.  The resulting file is data,
not a proof: Lean must still replay the cosine inequalities and the finite
Farkas checks.
"""
from __future__ import annotations

import argparse
import json
import sys
from decimal import Context, ROUND_CEILING, ROUND_FLOOR, localcontext
from fractions import Fraction
from pathlib import Path

# Allow direct execution from the repository root or from any working
# directory, matching the other certificate tools.
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from proof.angular import _angle_lower, _radius_bounds, _div
from proof.interval import D, set_precision, _binary
from proof.model import PackingModel


def rows_for_order(order: tuple[int, ...]) -> list[list[int]]:
    n = len(order)
    rows: list[list[int]] = []
    for a in range(n):
        for b in range(a + 1, n):
            paths = (
                [(a + t) % n for t in range(b - a)],
                [(b + t) % n for t in range(a - b + n)],
            )
            for path in paths:
                row = [0] * n
                for gap in path:
                    row[gap] = 1
                rows.append(row)
    return rows


def rational_decimal(value: D, digits: int, mode: str) -> Fraction:
    rounding = ROUND_FLOOR if mode == "floor" else ROUND_CEILING
    # Decimal's process-wide default precision is commonly 28.  Perform the
    # scaling and directed rounding in an explicit context, otherwise a
    # requested 60-digit certificate silently collapses to 28 digits.
    with localcontext(Context(prec=max(digits + 20, 100), rounding=rounding)):
        scale = D(10) ** digits
        integer = int((value * scale).to_integral_value(rounding=rounding))
    return Fraction(integer, 10**digits)


def frac_obj(x: Fraction) -> dict[str, int]:
    return {"num": x.numerator, "den": x.denominator}


def cosine_upper_from_bounds(model, box, i: int, j: int) -> D:
    """Return the same directed-rounding cosine upper bound used by `_angle_lower`."""
    a_lo, a_hi = _radius_bounds(model, box, i)
    b_lo, b_hi = _radius_bounds(model, box, j)
    if a_lo <= 0 or b_lo <= 0:
        raise ValueError("the exported certificate requires positive radial lower bounds")
    d = _binary(model.radii[i].lo, model.radii[j].lo, "+", ROUND_FLOOR)
    d2 = _binary(d, d, "*", ROUND_FLOOR)
    best = None
    for a in (a_lo, a_hi):
        for b in (b_lo, b_hi):
            numerator = _binary(
                _binary(_binary(a, a, "*", ROUND_CEILING),
                        _binary(b, b, "*", ROUND_CEILING), "+", ROUND_CEILING),
                d2, "-", ROUND_CEILING,
            )
            denominator = _binary(D(2), _binary(a, b, "*", ROUND_FLOOR),
                                  "*", ROUND_FLOOR)
            value = _div(numerator, denominator, ROUND_CEILING)
            best = value if best is None or value > best else best
    assert best is not None
    return best


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("certificate", type=Path)
    ap.add_argument("output", type=Path)
    ap.add_argument("--precision", type=int, default=120)
    ap.add_argument("--digits", type=int, default=60)
    args = ap.parse_args()

    set_precision(args.precision)
    source = json.loads(args.certificate.read_text())
    model = PackingModel(len(source["subset"]), source["rho"], tuple(source["subset"]))
    box = model.root_box()
    records = []
    for record in source["orders"]:
        order = tuple(record["order"])
        rows = rows_for_order(order)
        weights = [
            frac_obj(rational_decimal(D(w), args.digits, "ceil"))
            for w in record["coefficients"]
        ]
        lower_angles = []
        cosine_upper = []
        for a in range(len(order)):
            for b in range(a + 1, len(order)):
                i = source["subset"].index(order[a])
                j = source["subset"].index(order[b])
                angle = _angle_lower(
                    model, box, i, j,
                )
                lower = rational_decimal(angle, args.digits, "floor")
                upper = rational_decimal(cosine_upper_from_bounds(model, box, i, j),
                                         args.digits, "ceil")
                lower_angles.extend([frac_obj(lower), frac_obj(lower)])
                cosine_upper.extend([frac_obj(upper), frac_obj(upper)])
        records.append({"order": list(order), "rows": rows,
                        "weights": weights, "lower_angles": lower_angles,
                        "cosine_upper": cosine_upper})
    args.output.write_text(json.dumps({
        "kind": "lean-rational-angular-certificate",
        "rho": source["rho"], "subset": source["subset"],
        "orders": records,
    }, indent=2) + "\n")


if __name__ == "__main__":
    main()
