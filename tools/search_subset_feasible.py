"""Numerically search for a packing of a labeled radius subset at fixed rho."""
from __future__ import annotations

import argparse
import itertools
import json
from pathlib import Path

import numpy as np
from scipy.optimize import minimize


def slacks(x: np.ndarray, labels: tuple[int, ...], rho: float) -> np.ndarray:
    radii = np.sqrt(np.asarray(labels, dtype=float))
    points = x.reshape(-1, 2)
    values = [(rho - radii[i]) ** 2 - float(points[i] @ points[i])
              for i in range(len(labels))]
    for i in range(len(labels)):
        for j in range(i):
            d = points[i] - points[j]
            values.append(float(d @ d) - (radii[i] + radii[j]) ** 2)
    return np.asarray(values)


def search(labels: tuple[int, ...], rho: float, starts: int, seed: int) -> dict:
    rng = np.random.default_rng(seed)
    radii = np.sqrt(np.asarray(labels, dtype=float))
    bounds = [(-rho + r, rho - r) for r in radii for _ in range(2)]
    best = -float("inf")
    best_x = None
    for _ in range(starts):
        x = np.asarray([rng.uniform(a, b) for a, b in bounds])
        z0 = np.r_[x, float(np.min(slacks(x, labels, rho)))]
        result = minimize(lambda z: -z[-1], z0, method="SLSQP",
                          bounds=bounds + [(-100.0, 100.0)],
                          constraints={"type": "ineq", "fun": lambda z: slacks(z[:-1], labels, rho) - z[-1]},
                          options={"maxiter": 1800, "ftol": 1e-11})
        actual_margin = float(np.min(slacks(result.x[:-1], labels, rho)))
        if actual_margin > best:
            best = actual_margin
            best_x = result.x[:-1].copy()
    return {"subset": list(labels), "rho": rho, "best_margin_squared": best,
            "positive_candidate": best > 1e-8,
            "coordinates": best_x.tolist() if best_x is not None else None}


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--rho", type=float, default=8.0)
    parser.add_argument("--size", type=int, choices=(9, 10), default=9)
    parser.add_argument("--starts", type=int, default=20)
    parser.add_argument("--seed", type=int, default=20261006)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    subsets = [tuple(range(1, 11))] if args.size == 10 else list(itertools.combinations(range(1, 11), 9))
    results = [search(labels, args.rho, args.starts, args.seed + i)
               for i, labels in enumerate(subsets)]
    results.sort(key=lambda row: row["best_margin_squared"], reverse=True)
    payload = {"kind": "diagnostic-only", "results": results,
               "starts_per_subset": args.starts}
    args.output.write_text(json.dumps(payload, indent=2) + "\n")
    print(json.dumps({"subsets": len(results),
                      "positive_candidates": sum(r["positive_candidate"] for r in results),
                      "best": results[0]}, indent=2))


if __name__ == "__main__":
    main()
