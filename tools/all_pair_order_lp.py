"""Floating diagnostic for the fixed-cyclic-order all-pair angular LP.

This module is deliberately diagnostic: the returned LP status is not a
certificate.  A future proof path can replace the SciPy solve by a replayed
Farkas multiplier certificate.
"""
from __future__ import annotations

import itertools
from dataclasses import dataclass

import numpy as np
from scipy.optimize import linprog


@dataclass(frozen=True)
class OrderLPResult:
    order: tuple[int, ...]
    feasible: bool
    objective: float | None


def path_rows(order: tuple[int, ...], weights: dict[tuple[int, int], float]):
    n = len(order)
    rows = []
    rhs = []
    for a in range(n):
        for b in range(a + 1, n):
            i, j = order[a], order[b]
            paths = [list(range(a, b)), list(range(b, n)) + list(range(0, a))]
            for indices in paths:
                row = np.zeros(n)
                for k in indices:
                    row[k % n] = -1.0
                edge = (min(i, j), max(i, j))
                rows.append(row)
                rhs.append(-weights[edge])
    return np.asarray(rows), np.asarray(rhs)


def solve_order(order: tuple[int, ...], weights: dict[tuple[int, int], float]) -> OrderLPResult:
    # Use the two directed paths between every pair.  The equality fixes the
    # total angular measure to 2*pi; the objective is immaterial.
    a_ub, b_ub = path_rows(order, weights)
    n = len(order)
    result = linprog(np.zeros(n), A_ub=a_ub, b_ub=b_ub,
                     A_eq=np.ones((1, n)), b_eq=np.array([2 * np.pi]),
                     bounds=[(0.0, None)] * n, method="highs")
    return OrderLPResult(order, bool(result.success),
                         None if not result.success else float(result.fun))


def all_orders(labels: tuple[int, ...]):
    root = labels[0]
    for tail in itertools.permutations(labels[1:]):
        if tail[0] < tail[-1]:
            yield (root,) + tail
