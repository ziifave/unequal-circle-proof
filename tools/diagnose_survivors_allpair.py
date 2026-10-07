"""Apply the fixed-order all-pair angular LP to unresolved boxes.

Diagnostic only: SciPy feasibility is not a proof.  Boxes for which every
cyclic order is reported infeasible are candidates for later Farkas replay.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path

import numpy as np

from proof.angular import _angle_lower
from proof.interval import Interval, set_precision
from proof.model import Box, PackingModel
from tools.all_pair_order_lp import all_orders, path_rows
from scipy.optimize import linprog


def box_from_raw(raw: dict) -> Box:
    return Box(tuple(Interval.from_json(pair) for pair in raw["coords"]))


def order_feasible(order: tuple[int, ...], weights: dict[tuple[int, int], float]) -> bool:
    """Feasibility of the fixed-order gap system via difference constraints.

    Let y_k be cumulative angle, with y_0=0 and y_n=2*pi.  Every pair
    constraint is a lower bound on both directed paths, hence a difference
    constraint y_v >= y_u + c.  The system is feasible iff it has no positive
    cycle.  This is equivalent to the LP used previously, but avoids starting
    a HiGHS instance for every one of the 20,160 orders.
    """
    n = len(order)
    source = n + 1
    edges: list[tuple[int, int, float]] = []
    # Fix y_0=0 and y_n=2*pi using the source node y_source=0.
    edges.extend([(source, 0, 0.0), (0, source, 0.0),
                  (source, n, 2.0 * np.pi),
                  (n, source, -2.0 * np.pi)])
    # Gaps are nonnegative.
    for k in range(n):
        edges.append((k, k + 1, 0.0))
    # Both directed paths between every pair must clear its angle lower bound.
    for a in range(n):
        for b in range(a + 1, n):
            i, j = order[a], order[b]
            w = weights[(min(i, j), max(i, j))]
            edges.append((a, b, w))
            edges.append((b, a, w - 2.0 * np.pi))
    values = [0.0] * (n + 2)
    for _ in range(n + 2):
        changed = False
        for u, v, c in edges:
            candidate = values[u] + c
            if values[v] < candidate - 1e-12:
                values[v] = candidate
                changed = True
        if not changed:
            return True
    return False


def adjacent_cycle_possible(order: tuple[int, ...], weights: dict[tuple[int, int], float]) -> bool:
    """Cheap necessary test before invoking a floating LP.

    Every order-specific gap LP contains the adjacent-cycle inequalities and
    has total gap 2*pi.  Thus the sum of the adjacent lower bounds must not
    exceed 2*pi.  This is only a routing optimization; the LP remains the
    final diagnostic test.
    """
    total = 0.0
    for i, j in zip(order, order[1:] + order[:1]):
        total += weights[(min(i, j), max(i, j))]
    return total <= 2.0 * np.pi + 1e-12


def diagnose(model: PackingModel, raw: dict, order_limit: int | None,
             collect: bool) -> dict:
    box = box_from_raw(raw)
    weights: dict[tuple[int, int], float] = {}
    for i in range(model.n):
        for j in range(i):
            weights[(model.labels[j], model.labels[i])] = float(_angle_lower(model, box, i, j))
    tested = 0
    cycle_possible = 0
    lp_calls = 0
    feasible_orders = []
    for order in all_orders(tuple(model.labels)):
        if order_limit is not None and tested >= order_limit:
            break
        tested += 1
        if not adjacent_cycle_possible(order, weights):
            continue
        cycle_possible += 1
        lp_calls += 1
        if order_feasible(order, weights):
            feasible_orders.append(list(order))
            if not collect:
                return {"node": raw["node"], "tested_orders": tested,
                        "cycle_possible_orders": cycle_possible,
                        "lp_calls": lp_calls,
                        "all_orders_infeasible": False, "witness_order": list(order)}
    result = {"node": raw["node"], "tested_orders": tested,
              "cycle_possible_orders": cycle_possible, "lp_calls": lp_calls,
              "all_orders_infeasible": order_limit is None and not feasible_orders}
    if collect:
        result["feasible_order_count"] = len(feasible_orders)
        result["feasible_orders"] = feasible_orders
    return result


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("survivors", type=Path)
    parser.add_argument("--precision", type=int, default=90)
    parser.add_argument("--max-orders", type=int,
                        help="diagnostic cap; omit for complete order scan")
    parser.add_argument("--collect", action="store_true",
                        help="collect every LP-feasible order")
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    set_precision(args.precision)
    data = json.loads(args.survivors.read_text(encoding="utf-8"))
    model = PackingModel(len(data["radii_squared"]), data["rho"], data["radii_squared"])
    results = [diagnose(model, raw, args.max_orders, args.collect)
               for raw in data["queued_boxes"]]
    payload = {"kind": "diagnostic-only", "rho": data["rho"],
               "radii_squared": data["radii_squared"], "results": results}
    args.output.write_text(json.dumps(payload, indent=2) + "\n")
    print(json.dumps({"boxes": len(results),
                      "all_orders_infeasible": sum(r["all_orders_infeasible"] for r in results),
                      "order_witnesses": sum("witness_order" in r for r in results)}, indent=2))


if __name__ == "__main__":
    main()
