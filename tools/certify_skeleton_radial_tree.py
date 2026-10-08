"""Discover/resume a complete adaptive radial cover, retaining open leaves."""
from __future__ import annotations

import argparse
from fractions import Fraction as Q
import heapq
import json
from math import hypot
from pathlib import Path
import time

from proof.skeleton_cover import (
    LABELS, RADIUS_UPPER, SCALE, global_radial_bounds, parse_roots, propagate_radial,
    verify_angles, core_order_refinements,
)
from proof.skeleton_radial_tree import SCHEMA, leaf_report, split_bounds, verify
from proof.skeleton_local_terminal import order_is_local, verify_local_certificate
from proof.candidate import centres_in_target_convention
from tools.certify_skeleton_cover import (
    build_radial_leaf, order_refinements, root_witnesses,
)


def root_radial_guide() -> dict[int, float]:
    # This rounded known configuration affects search order only. No box is
    # narrowed, omitted, or accepted because it agrees with the guide.
    centres = centres_in_target_convention()
    return {i: hypot(float(centres[i - 1][0]), float(centres[i - 1][1]))
            for i in LABELS}


def priority(bounds: dict, original: dict, pending: int, depth: int,
             guide: dict[int, float]) -> tuple:
    # A guide-compatible box is searched first to expose the route to the
    # local terminal. Every sibling and postponed leaf stays in the tree.
    contains_guide = all(float(bounds[i][0]) <= value <= float(bounds[i][1])
                         for i, value in guide.items())
    volume = 1.0
    for i in LABELS:
        volume *= float((bounds[i][1] - bounds[i][0]) / (original[i][1] - original[i][0]))
    return (0 if contains_guide else 1, -depth if contains_guide else 0,
            -volume * pending / 12288)


def choose_split(bounds: dict, roots: dict, depth: int) -> tuple[int, Q]:
    # Establish the four-large-disk skeleton first; then refine all ten radii.
    # Positive widths for disks 1,3,4 are never removed just because they are
    # rattlers in the known configuration.
    if depth < 8:
        label = (7, 8, 9, 10)[depth % 4]
    else:
        active_core = {2, 5, 6, 7, 8, 9, 10}
        def score(i: int) -> float:
            focus = 2.0 if i in active_core else 0.5
            return focus * float((bounds[i][1] - bounds[i][0]) * roots[i][0])
        label = max(LABELS, key=score)
    return label, sum(bounds[label]) / 2


def attach_core_order_cover(node: dict, bounds: dict, roots: dict) -> None:
    """Add a complete seven-core angular-order cover to an open radial leaf."""
    if node.get("kind") != "ANGLE_COVER" or "core_orders" in node:
        return
    base = leaf_report(node, bounds, roots)
    if base["unknown_cases"] == 0:
        return
    propagated = propagate_radial(bounds, roots)
    weights = verify_angles(node["angles"], propagated, roots)
    node["core_orders"] = core_order_refinements(weights)


def attach_full_order_cover(node: dict, bounds: dict, roots: dict,
                            local_raw: dict | None = None,
                            max_pending_cases: int = 64) -> None:
    """Refine small residual sector ledgers by every full in-sector order.

    The all-pair order search is deliberately limited to leaves with a small
    residual ledger. Wide leaves remain open for radial splitting first.
    """
    if node.get("kind") != "ANGLE_COVER":
        return
    pending = sum(record.get("outcomes", []).count(-1)
                  for record in node.get("cycles", []))
    if pending == 0 or pending > max_pending_cases:
        return
    propagated = propagate_radial(bounds, roots)
    weights = verify_angles(node.get("angles"), propagated, roots)
    local = verify_local_certificate(local_raw)
    local_classifier = (lambda order: order_is_local(
        order, weights, propagated, roots, local)) if local is not None else None
    for record in node.get("cycles", []):
        if record.get("kind") == "SECTOR_CASES":
            record["order_groups"] = order_refinements(
                tuple(record["order"]), weights, record["outcomes"],
                local_classifier=local_classifier)


def explore(data: dict, split_budget: int, seconds: float = 0, progress: bool = False,
            all_pair_orders: bool = False) -> dict:
    # Resume reconstructs boxes from the verified tree, never from a stale
    # search snapshot. Only unknown leaves are eligible for further splitting.
    initial_report = verify(data)
    roots = parse_roots(data["sqrt_enclosures"])
    original = global_radial_bounds(roots)
    guide = root_radial_guide()
    heap = []
    for row in initial_report["frontier"]:
        bounds = {i: tuple(Q(x) for x in row["bounds"][i - 1]) for i in LABELS}
        index, depth = row["node"], row["depth"]
        attach_core_order_cover(data["nodes"][index], bounds, roots)
        if all_pair_orders:
            attach_full_order_cover(data["nodes"][index], bounds, roots,
                                    data.get("local_lower_bound"))
        report = leaf_report(data["nodes"][index], bounds, roots, data.get("local_lower_bound"))
        if report["unknown_cases"]:
            heapq.heappush(heap, (priority(bounds, original, report["unknown_cases"], depth, guide),
                                  index, depth, bounds))
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
            leaf = build_radial_leaf(child_bounds, roots)
            report = leaf_report(leaf, child_bounds, roots, data.get("local_lower_bound"))
            if report["unknown_cases"]:
                attach_core_order_cover(leaf, child_bounds, roots)
                if all_pair_orders:
                    attach_full_order_cover(leaf, child_bounds, roots,
                                            data.get("local_lower_bound"))
                report = leaf_report(leaf, child_bounds, roots, data.get("local_lower_bound"))
            child = len(nodes)
            nodes.append(leaf)
            children.append(child)
            if report["unknown_cases"]:
                heapq.heappush(heap, (priority(child_bounds, original, report["unknown_cases"], depth + 1, guide),
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
    leaf = build_radial_leaf(global_radial_bounds(roots), roots)
    return {"schema": SCHEMA, "container_radius_upper": str(RADIUS_UPPER),
            "angle_scale": SCALE, "large_four_certificate": lemma,
            "sqrt_enclosures": witnesses, "nodes": [leaf], "frontier": [0]}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lemma", type=Path, default=Path("certificates/large-four-skeleton-v1.json"))
    parser.add_argument("--local-certificate", type=Path,
                        default=Path("artifacts/local-optimality-constants.json"))
    parser.add_argument("--resume", type=Path)
    parser.add_argument("--splits", type=int, default=250)
    parser.add_argument("--seconds", type=float, default=0)
    parser.add_argument("--all-pair-orders", action="store_true")
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--report", type=Path, required=True)
    args = parser.parse_args()
    if args.splits < 0 or args.seconds < 0:
        parser.error("budgets must be nonnegative")
    local_raw = json.loads(args.local_certificate.read_text()) if args.local_certificate.exists() else None
    data = (json.loads(args.resume.read_text()) if args.resume else
            new_tree(json.loads(args.lemma.read_text()), args.all_pair_orders))
    if "local_lower_bound" not in data and local_raw is not None:
        data["local_lower_bound"] = local_raw
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
