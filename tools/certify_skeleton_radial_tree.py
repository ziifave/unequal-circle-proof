"""Discover/resume a complete adaptive radial cover, retaining open leaves."""
from __future__ import annotations

import argparse
from fractions import Fraction as Q
import heapq
import json
from pathlib import Path
import time

from proof.skeleton_cover import (
    LABELS, RADIUS_UPPER, SCALE, global_radial_bounds, parse_roots, propagate_radial,
)
from proof.skeleton_radial_tree import SCHEMA, leaf_report, split_bounds, verify
from tools.certify_skeleton_cover import build_radial_leaf, root_witnesses


def priority(bounds: dict, original: dict, pending: int) -> float:
    # Discovery heuristic only. Every postponed leaf stays in the certificate.
    volume = 1.0
    for i in LABELS:
        volume *= float((bounds[i][1] - bounds[i][0]) / (original[i][1] - original[i][0]))
    return -volume * pending / 12288


def choose_split(bounds: dict, roots: dict, depth: int) -> tuple[int, Q]:
    # Establish the four-large-disk skeleton first; then refine all ten radii.
    # Positive widths for disks 1,3,4 are never removed just because they are
    # rattlers in the known configuration.
    if depth < 8:
        label = (7, 8, 9, 10)[depth % 4]
    else:
        label = max(LABELS, key=lambda i: float((bounds[i][1] - bounds[i][0]) * roots[i][0]))
    return label, sum(bounds[label]) / 2


def explore(data: dict, split_budget: int, seconds: float = 0, progress: bool = False,
            all_pair_orders: bool = False) -> dict:
    # Resume reconstructs boxes from the verified tree, never from a stale
    # search snapshot. Only unknown leaves are eligible for further splitting.
    initial_report = verify(data)
    roots = parse_roots(data["sqrt_enclosures"])
    original = global_radial_bounds(roots)
    heap = []
    for row in initial_report["frontier"]:
        bounds = {i: tuple(Q(x) for x in row["bounds"][i - 1]) for i in LABELS}
        heapq.heappush(heap, (priority(bounds, original, row["unknown_sector_cases"]),
                              row["node"], row["depth"], bounds))
    nodes = data["nodes"]
    start = time.monotonic()
    for iteration in range(split_budget):
        if not heap or (seconds and time.monotonic() - start >= seconds):
            break
        _, index, depth, bounds = heapq.heappop(heap)
        bounds = propagate_radial(bounds, roots)
        label, cut = choose_split(bounds, roots, depth)
        children = []
        # Complete both children before replacing their parent. This retains
        # coverage even when the budget expires between iterations.
        for child_bounds in split_bounds(bounds, label, cut):
            leaf = build_radial_leaf(child_bounds, roots, all_pair_orders)
            report = leaf_report(leaf, child_bounds, roots)
            child = len(nodes)
            nodes.append(leaf)
            children.append(child)
            if report["unknown_cases"]:
                heapq.heappush(heap, (priority(child_bounds, original, report["unknown_cases"]),
                                      child, depth + 1, child_bounds))
        nodes[index] = {"kind": "RADIAL_SPLIT", "label": label, "cut": str(cut), "children": children}
        if progress and (iteration + 1) % 25 == 0:
            print(json.dumps({"new_splits": iteration + 1, "nodes": len(nodes),
                              "frontier": len(heap), "seconds": time.monotonic() - start}), flush=True)
    data["frontier"] = sorted(row[1] for row in heap)
    return data


def new_tree(lemma: dict, all_pair_orders: bool = False) -> dict:
    witnesses = root_witnesses()
    roots = parse_roots(witnesses)
    leaf = build_radial_leaf(global_radial_bounds(roots), roots, all_pair_orders)
    return {"schema": SCHEMA, "container_radius_upper": str(RADIUS_UPPER),
            "angle_scale": SCALE, "large_four_certificate": lemma,
            "sqrt_enclosures": witnesses, "nodes": [leaf], "frontier": [0]}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lemma", type=Path, default=Path("certificates/large-four-skeleton-v1.json"))
    parser.add_argument("--resume", type=Path)
    parser.add_argument("--splits", type=int, default=250)
    parser.add_argument("--seconds", type=float, default=0)
    parser.add_argument("--all-pair-orders", action="store_true")
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--report", type=Path, required=True)
    args = parser.parse_args()
    if args.splits < 0 or args.seconds < 0:
        parser.error("budgets must be nonnegative")
    data = (json.loads(args.resume.read_text()) if args.resume else
            new_tree(json.loads(args.lemma.read_text()), args.all_pair_orders))
    data = explore(data, args.splits, args.seconds, progress=True, all_pair_orders=args.all_pair_orders)
    report = verify(data)
    for path in (args.output, args.report):
        path.parent.mkdir(parents=True, exist_ok=True)
    # Rename a complete file so a partially written checkpoint cannot replace
    # a valid previous checkpoint.
    temporary = args.output.with_suffix(args.output.suffix + ".tmp")
    temporary.write_text(json.dumps(data, separators=(",", ":")) + "\n")
    temporary.replace(args.output)
    args.report.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({k: v for k, v in report.items() if k != "frontier"}, indent=2))


if __name__ == "__main__":
    main()
