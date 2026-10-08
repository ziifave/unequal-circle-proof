"""Generate the small rational witness for the four-large-disk lemma."""
from __future__ import annotations

import argparse
from fractions import Fraction
from itertools import permutations
import json
from math import isqrt
from pathlib import Path

from proof.large_four_certificate import LABELS, SCHEMA, canonical_cycles, verify_certificate


def build_certificate() -> dict:
    scale = 10 ** 12
    roots = []
    for label in LABELS:
        floor = isqrt(label * scale * scale)
        ceiling = floor if floor * floor == label * scale * scale else floor + 1
        roots.append({"label": label, "lo": str(Fraction(floor, scale)),
                      "hi": str(Fraction(ceiling, scale))})
    # These are proposed lower bounds. Only replay, not their origin in a
    # numerical diagnostic, establishes that they hold on the entire domain.
    proposed = {(7, 8): "1.0276", (7, 9): "1.0804", (7, 10): "1.1321",
                (8, 9): "1.1422", (8, 10): "1.1977", (9, 10): "1.2617"}
    return {"schema": SCHEMA, "labels": list(LABELS),
            "container_radius_upper": "8.303468122111490", "pi_upper": "3.1416",
            "sqrt_enclosures": roots,
            "angle_lower_bounds": [{"pair": list(pair), "lower": lower}
                                   for pair, lower in proposed.items()],
            "orders": [list(order) for order in permutations(LABELS)],
            "cyclic_representatives": [list(order) for order in canonical_cycles()]}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    data = build_certificate()
    result = verify_certificate(data)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(data, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"certificate": str(args.output), "status": result["status"],
                      "minimum_margin": result["minimum_margin"]}, indent=2))


if __name__ == "__main__":
    main()
