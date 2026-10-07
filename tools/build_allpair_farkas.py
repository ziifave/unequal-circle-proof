"""Build replayable Farkas certificates for all-pair angular LP boxes.

SciPy only discovers multipliers.  The emitted decimal multipliers are
rounded downward; a later replay must verify every column bound and the strict
2*pi margin with directed arithmetic.
"""
from __future__ import annotations

import argparse
import gzip
import itertools
import json
from decimal import Decimal, ROUND_FLOOR
from pathlib import Path

import numpy as np
from scipy.optimize import linprog

from proof.angular import _angle_lower
from proof.interval import Interval, set_precision
from proof.model import Box, PackingModel
from tools.all_pair_order_lp import path_rows


def rows_for_order(order: tuple[int, ...]):
    n = len(order)
    rows = []
    for a in range(n):
        for b in range(a + 1, n):
            rows.append(list(range(a, b)))
            rows.append(list(range(b, n)) + list(range(0, a)))
    return rows


def discover(values: list[Decimal], paths: list[list[int]], n: int) -> list[Decimal] | None:
    incidence = np.zeros((len(paths), n), dtype=float)
    for k, path in enumerate(paths):
        incidence[k, path] = 1.0
    result = linprog(-np.asarray([float(v) for v in values]),
                     A_ub=incidence.T, b_ub=np.ones(n),
                     bounds=[(0.0, None)] * len(paths), method="highs")
    if not result.success:
        return None
    out = []
    for value in result.x:
        d = Decimal(str(max(0.0, float(value))))
        d = d.quantize(Decimal("1e-15"), rounding=ROUND_FLOOR)
        d = (d * Decimal("0.999999999999")).quantize(
            Decimal("1e-15"), rounding=ROUND_FLOOR)
        out.append(d)
    return out


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("survivors", type=Path)
    parser.add_argument("--nodes", nargs="+", required=True)
    parser.add_argument("--precision", type=int, default=90)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    set_precision(args.precision)
    data = json.loads(args.survivors.read_text(encoding="utf-8"))
    labels = tuple(data["radii_squared"])
    model = PackingModel(len(labels), data["rho"], labels)
    wanted = set(args.nodes)
    boxes = {raw["node"]: raw for raw in data["queued_boxes"] if raw["node"] in wanted}
    if boxes != {node: boxes[node] for node in wanted if node in boxes} or len(boxes) != len(wanted):
        raise SystemExit(f"requested nodes not found: {sorted(wanted - boxes)}")
    with gzip.open(args.output, "wt", encoding="utf-8") as out:
        out.write(json.dumps({"kind": "allpair-farkas", "rho": data["rho"],
                              "radii_squared": list(labels), "precision": args.precision,
                              "nodes": sorted(wanted)}) + "\n")
        for node in sorted(wanted):
            box = Box(tuple(Interval.from_json(pair) for pair in boxes[node]["coords"]))
            weights = {(labels[j], labels[i]): _angle_lower(model, box, i, j)
                       for i in range(model.n) for j in range(i)}
            for tail in itertools.permutations(labels[1:]):
                if tail[0] >= tail[-1]:
                    continue
                order = (labels[0],) + tail
                paths = rows_for_order(order)
                values = [weights[(min(order[a], order[b]), max(order[a], order[b]))]
                          for a in range(model.n) for b in range(a + 1, model.n)
                          for _ in (0, 1)]
                coeffs = discover(values, paths, model.n)
                if coeffs is None:
                    raise SystemExit(f"dual solve failed at node={node}, order={order}")
                out.write(json.dumps({"node": node, "order": list(order),
                                      "angles": [str(v) for v in values],
                                      "coefficients": [str(v) for v in coeffs]}) + "\n")
    print(f"wrote Farkas records for {len(wanted)} boxes")


if __name__ == "__main__":
    main()
