"""Proof-safe radius-label branch-and-bound over rooted topologies.

This is intentionally an upper-level search layer: it never treats a failed
floating-point solve as rejection.  A node is discarded only by a directed
radius-only angular necessary condition.  Surviving leaves are unresolved
and are handed to later geometry certificates.
"""
from __future__ import annotations

import argparse
import itertools
import json
from functools import lru_cache
from pathlib import Path
from decimal import ROUND_CEILING, ROUND_FLOOR

from tools.local_stress_angle import beta
from tools.verify_wall_angle_certificate import wall_angle
from tools.diamond_filter import inspect as diamond_inspect
from proof.angular import PI_HI, _binary
from proof.interval import D, set_precision

ALL = tuple(range(1, 11))
R0 = D("8.30346812211148907870438118751619932995021374053538480956519718050601105313024902726198893075288755767902953233329724278")


def cycle_min(weights):
    n = len(weights)
    if n < 3:
        return D(0)
    dp = {(1, 0): D(0)}
    for size in range(1, n):
        for (mask, last), value in list(dp.items()):
            if mask.bit_count() != size:
                continue
            for nxt in range(1, n):
                if mask & (1 << nxt):
                    continue
                key = (mask | (1 << nxt), nxt)
                candidate = _binary(value, weights[last][nxt], "+", ROUND_FLOOR)
                if key not in dp or candidate < dp[key]:
                    dp[key] = candidate
    full = (1 << n) - 1
    return min(_binary(dp[(full, last)], weights[last][0], "+", ROUND_FLOOR)
               for last in range(1, n))


@lru_cache(maxsize=None)
def beta_domain(di: tuple[int, ...], dj: tuple[int, ...], dk: tuple[int, ...]):
    return min(beta(i, j, k) for i in di for j in dj for k in dk)


@lru_cache(maxsize=None)
def wall_domain(di: tuple[int, ...], dj: tuple[int, ...]):
    return min(wall_angle(i, j, R0) for i in di for j in dj)


def angle_check(domains, adjacency, wall_vertices):
    two_pi = _binary(D(2), PI_HI, "*", ROUND_CEILING)
    for i, neighbors in adjacency.items():
        if len(neighbors) < 3:
            continue
        di = domains[i]
        weights = [[D(0) if a == b else
                    beta_domain(di, domains[neighbors[a]], domains[neighbors[b]])
                    for b in range(len(neighbors))]
                   for a in range(len(neighbors))]
        lower = cycle_min(weights)
        if lower > two_pi:
            return "LOCAL_ANGLE_FAIL", {"vertex": i, "lower": str(lower)}
    if len(wall_vertices) >= 3:
        weights = [[D(0) if a == b else
                    wall_domain(domains[wall_vertices[a]], domains[wall_vertices[b]])
                    for b in range(len(wall_vertices))]
                   for a in range(len(wall_vertices))]
        lower = cycle_min(weights)
        if lower > two_pi:
            return "WALL_ANGLE_FAIL", {"lower": str(lower)}
    return None, None


def search_record(record, ledger):
    vertices = tuple(record["circles"])
    adjacency = {v: [] for v in vertices}
    wall_vertices = []
    for a, b in record["edges"]:
        if a == 0:
            wall_vertices.append(b)
        else:
            adjacency[a].append(b); adjacency[b].append(a)
    domains = {v: ALL for v in vertices}
    stack = [(domains, 0)]
    leaves = 0
    while stack:
        current, depth = stack.pop()
        reason, detail = angle_check(current, adjacency, wall_vertices)
        if reason:
            ledger[reason] += 1
            ledger["examples"].setdefault(reason, {"topology": record["edges"], **detail})
            continue
        unassigned = [v for v in vertices if len(current[v]) > 1]
        if not unassigned:
            labels = {v: current[v][0] for v in vertices}
            diamond_passes, diamond_checks = diamond_inspect(record, labels)
            if not diamond_passes:
                ledger["DIAMOND_OVERLAP"] += 1
                ledger["examples"].setdefault("DIAMOND_OVERLAP",
                                               {"topology": record["edges"],
                                                "checks": diamond_checks})
                continue
            leaves += 1
            ledger["UNRESOLVED_LEAF"] += 1
            continue
        v = max(unassigned, key=lambda x: (len(adjacency[x]), x))
        used = set().union(*(set(current[u]) for u in vertices if u != v and len(current[u]) == 1))
        choices = tuple(x for x in current[v] if x not in used)
        if not choices:
            ledger["LABEL_DOMAIN_EMPTY"] += 1
            continue
        for label in choices:
            child = dict(current)
            child[v] = (label,)
            # All other domains remain conservative; distinctness is enforced
            # only at complete leaves, so this never creates an unsound prune.
            stack.append((child, depth + 1))
    return leaves


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("input", type=Path)
    ap.add_argument("--output", type=Path, required=True)
    ap.add_argument("--precision", type=int, default=70)
    ap.add_argument("--max-topologies", type=int, default=None)
    args = ap.parse_args()
    set_precision(args.precision)
    data = json.loads(args.input.read_text())
    records = data["records"] if args.max_topologies is None else data["records"][:args.max_topologies]
    ledger = {"topologies": len(records), "UNRESOLVED_LEAF": 0,
              "LOCAL_ANGLE_FAIL": 0, "WALL_ANGLE_FAIL": 0,
              "LABEL_DOMAIN_EMPTY": 0, "DIAMOND_OVERLAP": 0, "examples": {}}
    for record in records:
        search_record(record, ledger)
    payload = {"input": str(args.input), "m": data["m"],
               "ledger": ledger,
               "note": "Only directed radius-only necessary conditions reject nodes; unresolved leaves require later interval geometry."}
    args.output.write_text(json.dumps(payload, indent=2) + "\n")
    print(json.dumps({k: payload["ledger"][k] for k in
                      ("topologies", "LOCAL_ANGLE_FAIL", "WALL_ANGLE_FAIL",
                       "LABEL_DOMAIN_EMPTY", "DIAMOND_OVERLAP", "UNRESOLVED_LEAF")}, indent=2))


if __name__ == "__main__":
    main()
