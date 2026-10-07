"""Certify positive slack for every inactive constraint of the Krawczyk core.

Together with a successful core Krawczyk inclusion, this turns the published
layout into a rigorously enclosed feasible witness (upper bound).  It remains
entirely separate from the still-incomplete global lower-bound proof.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path

from proof.candidate import centres_in_target_convention
from proof.core_krawczyk import PAIRS, WALLS, vector_from_centres
from proof.interval import Interval, set_precision


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--input", type=Path, default=Path("artifacts/refined-core.json"))
    parser.add_argument("--precision", type=int, default=120)
    parser.add_argument("--width", default="1e-65")
    parser.add_argument("--output", type=Path, default=Path("artifacts/upper-witness-report.json"))
    args = parser.parse_args()
    set_precision(args.precision)
    data = json.loads(args.input.read_text(encoding="utf-8"))
    core_vector = vector_from_centres(data["core_centres"], data["R"])
    half_width = Interval.point(args.width)
    core_box = [value + Interval(-half_width.hi, half_width.hi) for value in core_vector]

    # Rebuild full coordinate intervals.  Disks 1,3,4 are rattlers and retain
    # their published (strictly interior / separated) decimal coordinates.
    published = centres_in_target_convention()
    centres: dict[int, tuple[Interval, Interval]] = {
        i: (Interval.point(x), Interval.point(y)) for i, (x, y) in enumerate(published, start=1)
    }
    cursor = 0
    for disk in (2, 5, 6, 7, 8, 9, 10):
        x = core_box[cursor]
        cursor += 1
        y = Interval.point(0) if disk == 10 else core_box[cursor]
        if disk != 10:
            cursor += 1
        centres[disk] = (x, y)
    radius = core_box[-1]
    radii = {i: Interval.sqrt_integer(i) for i in range(1, 11)}
    active_pairs = {tuple(pair) for pair in PAIRS}
    active_walls = set(WALLS)

    inactive: dict[str, str] = {}
    for i in range(1, 11):
        if i not in active_walls:
            x, y = centres[i]
            slack = (radius - radii[i]).square() - (x.square() + y.square())
            inactive[f"wall:{i}"] = str(slack.lo)
    for i in range(1, 11):
        xi, yi = centres[i]
        for j in range(1, i):
            if (j, i) not in active_pairs:
                xj, yj = centres[j]
                slack = (xi - xj).square() + (yi - yj).square() - (radii[i] + radii[j]).square()
                inactive[f"pair:{j}-{i}"] = str(slack.lo)
    smallest_name, smallest_value = min(inactive.items(), key=lambda row: __import__("decimal").Decimal(row[1]))
    payload = {
        "precision": args.precision,
        "core_half_width": args.width,
        "R_upper": str(radius.hi),
        "inactive_constraints_checked": len(inactive),
        "minimum_inactive_squared_slack": {"constraint": smallest_name, "lower_bound": smallest_value},
        "inactive_squared_slack_lower_bounds": dict(sorted(inactive.items())),
        "all_inactive_slacks_strictly_positive": all(__import__("decimal").Decimal(v) > 0 for v in inactive.values()),
        "active_walls": list(WALLS),
        "active_pairs": [list(pair) for pair in PAIRS],
        "note": "If the corresponding Krawczyk report is true, active equations hold at one core root. Positive values here then certify all remaining containment/non-overlap inequalities for that root plus disks 1,3,4.",
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(json.dumps(payload, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
