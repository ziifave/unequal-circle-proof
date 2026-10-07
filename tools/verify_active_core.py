"""Create an interval Krawczyk local-uniqueness report for refined-core.json."""
from __future__ import annotations

import argparse
import json
from decimal import Decimal
from pathlib import Path

import mpmath as mp

from proof.core_krawczyk import functions_and_jacobian, krawczyk, vector_from_centres
from proof.interval import Interval, set_precision


def decimal_matrix_inverse(center: list[Interval], dps: int) -> list[list[Interval]]:
    mp.mp.dps = dps
    _, jac = functions_and_jacobian(center)
    matrix = mp.matrix([[mp.mpf(str(entry.midpoint)) for entry in row] for row in jac])
    inverse = matrix ** -1
    digits = dps - 15
    return [[Interval.point(mp.nstr(inverse[i, j], digits)) for j in range(14)] for i in range(14)]


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--input", type=Path, default=Path("artifacts/refined-core.json"))
    parser.add_argument("--precision", type=int, default=120)
    parser.add_argument("--width", default="1e-65", help="symmetric half-width of the test box")
    parser.add_argument("--output", type=Path, default=Path("artifacts/core-krawczyk-report.json"))
    args = parser.parse_args()
    set_precision(args.precision)
    data = json.loads(args.input.read_text(encoding="utf-8"))
    center = vector_from_centres(data["core_centres"], data["R"])
    width = Interval.point(args.width)
    box = [value + Interval(-width.hi, width.hi) for value in center]
    preconditioner = decimal_matrix_inverse(center, args.precision + 30)
    image, certified = krawczyk(center, box, preconditioner)
    margins = [min(k.lo - x.lo, x.hi - k.hi) for k, x in zip(image, box)]
    payload = {
        "precision": args.precision,
        "half_width": args.width,
        "variables": len(center),
        "krawczyk_strictly_inside": certified,
        "minimum_inclusion_margin": str(min(margins)),
        "image_width_max": str(max(v.width for v in image)),
        "box_width": str(Decimal(args.width) * 2),
        "center": [[str(value.lo), str(value.hi)] for value in center],
        "box": [[str(value.lo), str(value.hi)] for value in box],
        "image": [[str(value.lo), str(value.hi)] for value in image],
        "preconditioner": [[[str(value.lo), str(value.hi)] for value in row] for row in preconditioner],
        "note": "A true result certifies exactly one root of this 14-equation active-core system in the displayed box; it is not a global packing proof.",
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(json.dumps(payload, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
