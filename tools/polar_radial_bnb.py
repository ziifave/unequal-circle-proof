"""Diagnostic B&B over shared radial intervals for fixed-origin orders.

The original Cartesian survivor box is relaxed to independent radial
intervals.  Splitting those intervals and re-running the all-pair gap test
therefore gives a useful strength estimate for a future interval proof.  The
current implementation uses floating arithmetic and is explicitly diagnostic.
"""
from __future__ import annotations

import argparse
import heapq
import json
import math
import time
from pathlib import Path

from proof.angular import _radius_bounds
from proof.interval import Interval, set_precision
from proof.model import Box, PackingModel
from tools.all_pair_order_lp import all_orders
from tools.diagnose_survivors_allpair import order_feasible


def box_from_raw(raw: dict) -> Box:
    return Box(tuple(Interval.from_json(pair) for pair in raw["coords"]))


def angle_weights(labels: tuple[int, ...], radial: list[tuple[float, float]]) -> dict[tuple[int, int], float]:
    out = {}
    for i, ri in enumerate(labels):
        for j in range(i):
            rj = labels[j]
            best = -1.0
            for a in radial[i][0], radial[i][1]:
                for b in radial[j][0], radial[j][1]:
                    if a <= 0.0 or b <= 0.0:
                        best = 1.0
                        continue
                    c = (a*a + b*b - (math.sqrt(ri)+math.sqrt(rj))**2) / (2*a*b)
                    best = max(best, max(-1.0, min(1.0, c)))
            out[(rj, ri)] = math.acos(best)
    return out


def radial_bounds(model: PackingModel, raw: dict) -> list[tuple[float, float]]:
    box = box_from_raw(raw)
    return [(float(lo), float(hi)) for lo, hi in
            (_radius_bounds(model, box, i) for i in range(model.n))]


def node_status(labels, radial, orders):
    weights = angle_weights(labels, radial)
    alive = 0
    for order in orders:
        if order_feasible(order, weights):
            alive += 1
    return alive


def solve_box(model, raw, orders, max_nodes, deadline):
    labels = tuple(model.labels)
    root = radial_bounds(model, raw)
    queue = [(0.0, 0, root)]
    unresolved = 0
    processed = 0
    best_alive = len(orders)
    while queue and processed < max_nodes and time.monotonic() < deadline:
        _, depth, radial = heapq.heappop(queue)
        processed += 1
        alive = node_status(labels, radial, orders)
        best_alive = min(best_alive, alive)
        if alive == 0:
            continue
        widths = [hi-lo for lo, hi in radial]
        k = max(range(len(widths)), key=lambda i: widths[i])
        if widths[k] <= 1e-7:
            unresolved += 1
            continue
        lo, hi = radial[k]
        mid = (lo + hi) / 2.0
        left, right = list(radial), list(radial)
        left[k] = (lo, mid)
        right[k] = (mid, hi)
        heapq.heappush(queue, (-alive, depth + 1, left))
        heapq.heappush(queue, (-alive, depth + 1, right))
    return {"node": raw["node"], "processed": processed,
            "frontier": len(queue), "unresolved": unresolved,
            "best_alive_orders": best_alive,
            "closed": not queue and unresolved == 0}


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("survivors", type=Path)
    ap.add_argument("--max-nodes", type=int, default=1000)
    ap.add_argument("--seconds", type=float, default=120.0)
    ap.add_argument("--precision", type=int, default=90)
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    set_precision(args.precision)
    data = json.loads(args.survivors.read_text())
    model = PackingModel(len(data["radii_squared"]), "8.0", data["radii_squared"])
    orders = tuple(all_orders(tuple(model.labels)))
    deadline = time.monotonic() + args.seconds
    results = []
    for raw in data["queued_boxes"]:
        if time.monotonic() >= deadline:
            break
        results.append(solve_box(model, raw, orders, args.max_nodes, deadline))
    args.output.write_text(json.dumps({"kind": "diagnostic-only", "rho": data["rho"],
                                       "radii_squared": data["radii_squared"],
                                       "results": results}, indent=2) + "\n")
    print(json.dumps({"boxes": len(results),
                      "closed": sum(r["closed"] for r in results),
                      "unresolved": sum(r["unresolved"] for r in results)}, indent=2))


if __name__ == "__main__":
    main()
