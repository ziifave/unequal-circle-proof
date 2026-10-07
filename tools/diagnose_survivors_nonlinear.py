"""Numerical diagnostic for unresolved interval boxes.

This is intentionally not a certificate component.  It searches each box for
a point with nonnegative squared containment and pair-separation slacks using
SLSQP, only to distinguish plausible feasible islands from interval
relaxation residue.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path

import numpy as np
from scipy.optimize import minimize


def slacks(x: np.ndarray, labels: list[int], rho: float) -> np.ndarray:
    radii = np.sqrt(np.asarray(labels, dtype=float))
    points = x.reshape(-1, 2)
    values = [
        (rho - radii[i]) ** 2 - float(points[i] @ points[i])
        for i in range(len(labels))
    ]
    for i in range(len(labels)):
        for j in range(i):
            d = points[i] - points[j]
            values.append(float(d @ d) - (radii[i] + radii[j]) ** 2)
    return np.asarray(values)


def solve_box(raw: dict, labels: list[int], rho: float, starts: int, seed: int) -> dict:
    rng = np.random.default_rng(seed)
    coords = raw["coords"]
    bounds = [(float(a), float(b)) for a, b in coords]
    mid = np.asarray([(a + b) / 2 for a, b in bounds], dtype=float)
    candidates = [mid]
    for _ in range(starts - 1):
        candidates.append(np.asarray([rng.uniform(a, b) for a, b in bounds]))
    best = -float("inf")
    best_x = None
    for start in candidates:
        initial_slack = float(np.min(slacks(start, labels, rho)))
        z0 = np.r_[start, initial_slack]
        # z[-1] is a common slack margin.  A positive optimum is a numerical
        # feasible witness with strict separation; zero is only borderline.
        fun = lambda z: -z[-1]
        cons = {"type": "ineq", "fun": lambda z: slacks(z[:-1], labels, rho) - z[-1]}
        result = minimize(fun, z0, method="SLSQP", bounds=bounds + [(-100.0, 100.0)],
                          constraints=cons, options={"maxiter": 1200, "ftol": 1e-12})
        margin = float(np.min(slacks(result.x[:-1], labels, rho)))
        if margin > best:
            best, best_x = margin, result.x[:-1]
    return {"node": raw["node"], "best_margin_squared": best,
            "success_candidate": best > 1e-8,
            "coords": best_x.tolist() if best_x is not None else None}


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("survivors", type=Path)
    parser.add_argument("--starts", type=int, default=12)
    parser.add_argument("--seed", type=int, default=20261006)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    data = json.loads(args.survivors.read_text(encoding="utf-8"))
    labels = data["radii_squared"]
    rho = float(data["rho"])
    results = [solve_box(raw, labels, rho, args.starts, args.seed + i)
               for i, raw in enumerate(data["queued_boxes"])]
    results.sort(key=lambda row: row["best_margin_squared"], reverse=True)
    payload = {"kind": "diagnostic-only", "rho": data["rho"], "labels": labels,
               "boxes": len(results), "starts_per_box": args.starts,
               "results": results}
    if args.output:
        args.output.write_text(json.dumps(payload, indent=2) + "\n")
    print(json.dumps({"boxes": len(results),
                      "positive_candidates": sum(r["success_candidate"] for r in results),
                      "best_margin_squared": results[0]["best_margin_squared"]}, indent=2))


if __name__ == "__main__":
    main()
