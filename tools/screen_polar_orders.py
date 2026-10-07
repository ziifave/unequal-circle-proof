"""Fast diagnostic screen for shared-radial fixed-order polar systems.

For each interval box, fix every radial variable at the midpoint of its
certified radial interval, derive the resulting pair-angle bounds, and test
all cyclic orders with the difference-constraint solver.  A rejected order
is only a numerical routing result, not a proof: the true radii may differ
from the midpoint.  Surviving orders can be passed to the nonlinear polar
diagnostic or a future interval contractor.
"""
from __future__ import annotations

import argparse
import json
import math
from pathlib import Path

from proof.angular import _radius_bounds
from proof.interval import Interval, set_precision
from proof.model import Box, PackingModel
from tools.all_pair_order_lp import all_orders
from tools.diagnose_survivors_allpair import order_feasible


def box_from_raw(raw: dict) -> Box:
    return Box(tuple(Interval.from_json(pair) for pair in raw["coords"]))


def midpoint_weights(model: PackingModel, raw: dict) -> dict[tuple[int, int], float]:
    box = box_from_raw(raw)
    radial = [_radius_bounds(model, box, i) for i in range(model.n)]
    a = {model.labels[i]: float((lo + hi) / 2) for i, (lo, hi) in enumerate(radial)}
    weights = {}
    for i, ri in enumerate(model.labels):
        for rj in model.labels[:i]:
            c = (a[ri] ** 2 + a[rj] ** 2 - (math.sqrt(ri) + math.sqrt(rj)) ** 2) / (2.0 * a[ri] * a[rj])
            c = max(-1.0, min(1.0, c))
            weights[(rj, ri)] = math.acos(c)
    return weights


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("survivors", type=Path)
    ap.add_argument("--precision", type=int, default=90)
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    set_precision(args.precision)
    data = json.loads(args.survivors.read_text())
    model = PackingModel(len(data["radii_squared"]), "8.0", data["radii_squared"])
    orders = tuple(all_orders(tuple(model.labels)))
    results = []
    for raw in data["queued_boxes"]:
        weights = midpoint_weights(model, raw)
        surviving = [list(order) for order in orders if order_feasible(order, weights)]
        results.append({"node": raw["node"], "orders_tested": len(orders),
                        "midpoint_surviving_count": len(surviving),
                        "midpoint_surviving_orders": surviving})
    args.output.write_text(json.dumps({"kind": "diagnostic-only", "rho": data["rho"],
                                       "radii_squared": data["radii_squared"],
                                       "results": results}, indent=2) + "\n")
    print(json.dumps({"boxes": len(results),
                      "zero_survivors": sum(r["midpoint_surviving_count"] == 0 for r in results),
                      "max_survivors": max(r["midpoint_surviving_count"] for r in results)}, indent=2))


if __name__ == "__main__":
    main()
