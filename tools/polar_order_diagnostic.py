"""Floating fixed-order polar diagnostic for unresolved angular boxes.

This is not a certificate.  It keeps one shared radial variable per circle
and one shared angular gap per consecutive pair, so it is strictly stronger
than the pairwise all-angle LP relaxation.  Its purpose is to route the
remaining boxes toward a future interval contractor.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path

import numpy as np
from scipy.optimize import minimize

from proof.angular import _radius_bounds
from proof.interval import Interval, set_precision
from proof.model import Box, PackingModel


def box_from_raw(raw: dict) -> Box:
    return Box(tuple(Interval.from_json(pair) for pair in raw["coords"]))


def polar_slacks(z: np.ndarray, order: tuple[int, ...], labels: tuple[int, ...],
                 rho: float) -> np.ndarray:
    n = len(order)
    a = z[:n]
    gaps = z[n:]
    angles = np.zeros(n)
    angles[1:] = np.cumsum(gaps[:-1])
    radii = {label: np.sqrt(float(label)) for label in labels}
    pos = {label: k for k, label in enumerate(order)}
    out: list[float] = []
    for label in order:
        k = pos[label]
        out.append((rho - radii[label]) ** 2 - a[k] ** 2)
    for u in range(n):
        for v in range(u):
            i, j = order[u], order[v]
            delta = angles[u] - angles[v]
            d2 = a[u] ** 2 + a[v] ** 2 - 2.0 * a[u] * a[v] * np.cos(delta)
            out.append(d2 - (radii[i] + radii[j]) ** 2)
    return np.asarray(out)


def solve_order(raw: dict, model: PackingModel, order: tuple[int, ...],
                starts: int, seed: int) -> dict:
    box = box_from_raw(raw)
    radial = [_radius_bounds(model, box, i) for i in range(model.n)]
    # Labels are the radius-square labels and model order is label order here.
    bounds_a = [tuple(float(x) for x in radial[model.labels.index(label)])
                for label in order]
    n = len(order)
    bounds = bounds_a + [(0.0, 2.0 * np.pi)] * n
    rng = np.random.default_rng(seed)
    mid_a = np.asarray([(lo + hi) / 2 for lo, hi in bounds_a])
    starts_z = [np.r_[mid_a, np.full(n, 2.0 * np.pi / n)]]
    for _ in range(starts - 1):
        aa = np.asarray([rng.uniform(lo, hi) for lo, hi in bounds_a])
        gg = rng.dirichlet(np.ones(n)) * (2.0 * np.pi)
        starts_z.append(np.r_[aa, gg])
    best = -float("inf")
    best_z = None
    for start in starts_z:
        z0 = np.r_[start, min(float(np.min(polar_slacks(start, order, model.labels, float(model.rho)))), 0.0)]
        # z[-1] is a common slack; the preceding variables are a and gaps.
        x0 = start
        y0 = np.r_[x0, 0.0]
        constraints = [
            {"type": "eq", "fun": lambda y: np.sum(y[n:2*n]) - 2.0 * np.pi},
            {"type": "ineq", "fun": lambda y: polar_slacks(y[:2*n], order, model.labels, float(model.rho)) - y[-1]},
        ]
        result = minimize(lambda y: -y[-1], y0, method="SLSQP", bounds=bounds + [(-100.0, 100.0)],
                          constraints=constraints,
                          options={"maxiter": 1500, "ftol": 1e-11})
        margin = float(np.min(polar_slacks(result.x[:2*n], order, model.labels, float(model.rho))))
        if margin > best:
            best, best_z = margin, result.x[:2*n]
    return {"node": raw["node"], "order": list(order),
            "best_margin_squared": best,
            "positive_candidate": best > 1e-8,
            "success": best_z is not None,
            "variables": best_z.tolist() if best_z is not None else None}


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("survivors", type=Path)
    ap.add_argument("orders", type=Path)
    ap.add_argument("--starts", type=int, default=4)
    ap.add_argument("--precision", type=int, default=90)
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    set_precision(args.precision)
    data = json.loads(args.survivors.read_text())
    order_data = json.loads(args.orders.read_text())
    model = PackingModel(len(data["radii_squared"]), data["rho"], data["radii_squared"])
    by_node = {row["node"]: row for row in order_data["results"]}
    results = []
    for raw in data["queued_boxes"]:
        row = by_node.get(raw["node"], {})
        order = row.get("witness_order")
        if order is None:
            continue
        results.append(solve_order(raw, model, tuple(order), args.starts, 20261006 + len(results)))
    results.sort(key=lambda r: r["best_margin_squared"], reverse=True)
    payload = {"kind": "diagnostic-only", "rho": data["rho"],
               "radii_squared": data["radii_squared"], "results": results}
    args.output.write_text(json.dumps(payload, indent=2) + "\n")
    print(json.dumps({"orders_tested": len(results),
                      "positive_candidates": sum(r["positive_candidate"] for r in results),
                      "best_margin_squared": results[0]["best_margin_squared"] if results else None}, indent=2))


if __name__ == "__main__":
    main()
