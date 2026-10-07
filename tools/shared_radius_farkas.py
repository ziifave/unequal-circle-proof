"""Shared-radius Farkas certificates from midpoint difference-constraint cycles.

For a fixed cyclic order, the all-pair gap system is a difference-constraint
system.  A positive cycle at the midpoint gives a sparse Farkas witness.  We
reuse its combinatorial support over the whole radial box and evaluate every
angle term with certified lower bounds.  This is proof-safe for a box when
the reported robust margin is positive; midpoint cycle discovery itself is
only a witness-selection heuristic.
"""
from __future__ import annotations

import argparse
import json
import math
from dataclasses import dataclass
from pathlib import Path

from proof.angular import PI_HI, PI_LO, _angle_lower_from_bounds, _radius_bounds
from proof.interval import D, Interval, ROUND_FLOOR, _binary, set_precision
from proof.model import Box, PackingModel
from tools.all_pair_order_lp import all_orders
from tools.diagnose_survivors_allpair import order_feasible


@dataclass(frozen=True)
class Edge:
    u: int
    v: int
    c: float
    pair: tuple[int, int] | None = None
    const: str = "zero"


def box_from_raw(raw: dict) -> Box:
    return Box(tuple(Interval.from_json(pair) for pair in raw["coords"]))


def radial_bounds(model: PackingModel, raw: dict):
    box = box_from_raw(raw)
    return [_radius_bounds(model, box, i) for i in range(model.n)]


def midpoint_weights(model: PackingModel, raw: dict) -> dict[tuple[int, int], float]:
    radial = radial_bounds(model, raw)
    a = {model.labels[i]: float((lo + hi) / 2) for i, (lo, hi) in enumerate(radial)}
    out = {}
    for i, ri in enumerate(model.labels):
        for rj in model.labels[:i]:
            c = (a[ri]**2 + a[rj]**2 - (math.sqrt(ri)+math.sqrt(rj))**2) / (2*a[ri]*a[rj])
            out[(rj, ri)] = math.acos(max(-1.0, min(1.0, c)))
    return out


def positive_cycle(order, weights):
    """Return one positive cycle of the difference system, if present."""
    n = len(order)
    source = n + 1
    edges: list[Edge] = [Edge(source, 0, 0.0, const="zero"),
                         Edge(0, source, 0.0, const="zero"),
                         Edge(source, n, 2*math.pi, const="plus2pi"),
                         Edge(n, source, -2*math.pi, const="minus2pi")]
    for k in range(n):
        edges.append(Edge(k, k+1, 0.0, const="zero"))
    for a in range(n):
        for b in range(a+1, n):
            pair = (min(order[a], order[b]), max(order[a], order[b]))
            w = weights[pair]
            edges.append(Edge(a, b, w, pair=pair, const="zero"))
            edges.append(Edge(b, a, w-2*math.pi, pair=pair, const="minus2pi"))
    values = [0.0] * (n+2)
    pred: list[int | None] = [None] * (n+2)
    changed_v = None
    for _ in range(n+2):
        changed_v = None
        for k, edge in enumerate(edges):
            if values[edge.v] < values[edge.u] + edge.c - 1e-12:
                values[edge.v] = values[edge.u] + edge.c
                pred[edge.v] = k
                changed_v = edge.v
        if changed_v is None:
            return None
    v = changed_v
    for _ in range(n+2):
        if pred[v] is None:
            return None
        v = edges[pred[v]].u
    cycle: list[int] = []
    cur = v
    while True:
        k = pred[cur]
        if k is None:
            return None
        cycle.append(k)
        cur = edges[k].u
        if cur == v:
            break
        if len(cycle) > n + 3:
            return None
    cycle.reverse()
    return [edges[k] for k in cycle]


def radial_angle_lowers(model: PackingModel, raw: dict):
    radial = radial_bounds(model, raw)
    lower = {}
    for ii, i in enumerate(model.labels):
        for jj in range(ii):
            j = model.labels[jj]
            lower[(j, i)] = _angle_lower_from_bounds(
                model.radii[ii].lo, model.radii[jj].lo,
                radial[ii][0], radial[ii][1], radial[jj][0], radial[jj][1])
    return lower


def robust_margin(model: PackingModel, raw: dict, cycle: list[Edge,],
                  lower=None) -> object:
    if lower is None:
        lower = radial_angle_lowers(model, raw)
    total = D(0)
    for edge in cycle:
        if edge.pair is not None:
            total = _binary(total, lower[edge.pair], "+", ROUND_FLOOR)
        if edge.const == "plus2pi":
            total = _binary(total, _binary(D(2), PI_LO, "*", ROUND_FLOOR), "+", ROUND_FLOOR)
        elif edge.const == "minus2pi":
            total = _binary(total, _binary(D(-2), PI_HI, "*", ROUND_FLOOR), "+", ROUND_FLOOR)
    return total


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("survivors", type=Path)
    ap.add_argument("--precision", type=int, default=90)
    ap.add_argument("--nodes", help="comma-separated node ids; omit for all boxes")
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    set_precision(args.precision)
    data = json.loads(args.survivors.read_text())
    model = PackingModel(len(data["radii_squared"]), "8.0", data["radii_squared"])
    orders = tuple(all_orders(tuple(model.labels)))
    selected = set(args.nodes.split(",")) if args.nodes else None
    results = []
    for raw in data["queued_boxes"]:
        if selected is not None and raw["node"] not in selected:
            continue
        weights = midpoint_weights(model, raw)
        lower = radial_angle_lowers(model, raw)
        certified = 0
        max_margin = None
        example = None
        certificates = []
        for order in orders:
            # A midpoint-feasible order has no positive-cycle witness.  Avoid
            # the more expensive predecessor reconstruction in that case.
            if order_feasible(order, weights):
                continue
            cycle = positive_cycle(order, weights)
            if cycle is None:
                continue
            margin = robust_margin(model, raw, cycle, lower)
            if max_margin is None or margin > max_margin:
                max_margin = margin
            if margin > 0:
                certified += 1
                certificates.append({
                    "order": list(order),
                    "margin": str(margin),
                    "cycle": [{"u": e.u, "v": e.v, "pair": list(e.pair) if e.pair else None,
                               "const": e.const} for e in cycle],
                })
                if example is None:
                    example = {"order": list(order), "cycle_edges": len(cycle),
                               "margin": str(margin)}
        results.append({"node": raw["node"], "orders": len(orders),
                        "certified_order_count": certified,
                        "max_cycle_margin": str(max_margin) if max_margin is not None else None,
                        "example": example,
                        "certificates": certificates})
        print(raw["node"], certified, max_margin)
    args.output.write_text(json.dumps({"kind": "shared-radius-farkas-diagnostic",
                                       "rho": data["rho"], "radii_squared": data["radii_squared"],
                                       "results": results}, indent=2) + "\n")
    print(json.dumps({"boxes": len(results),
                      "fully_certified": sum(r["certified_order_count"] == r["orders"] for r in results),
                      "certified_orders": sum(r["certified_order_count"] for r in results)}, indent=2))


if __name__ == "__main__":
    main()
