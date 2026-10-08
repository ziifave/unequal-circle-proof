"""Exact replay of an adaptive radial cover of every ten-disk configuration.

All bounds are reconstructed from the root and rational binary splits. A leaf
is either proved empty or retains every unexcluded sector assignment. There
is no terminal rule for small boxes, elapsed time, or a numerical solution.
"""
from __future__ import annotations

import argparse
from fractions import Fraction as Q
import hashlib
import json
from pathlib import Path

from .large_four_certificate import rational, require, verify_certificate as verify_large_four
from .skeleton_cover import (
    CASES_PER_CYCLE, LABELS, PAIRS, RADIUS_UPPER, SCALE, global_radial_bounds,
    pair_sum_contradiction, parse_roots, propagate_radial, verify_angular_cover,
    verify_angles, verify_core_orders, core_order_refinements,
    core_closed_sector_assignments,
)
from .skeleton_local_terminal import order_is_local, verify_local_certificate

SCHEMA = "ten-disk-skeleton-adaptive-radial-tree-v1"


def split_bounds(bounds: dict, label: int, cut: Q) -> tuple[dict, dict]:
    require(type(label) is int and label in LABELS, "invalid split label")
    lo, hi = bounds[label]
    require(lo < cut < hi, "split must be strictly inside its interval")
    left, right = dict(bounds), dict(bounds)
    left[label], right[label] = (lo, cut), (cut, hi)
    return left, right


def leaf_report(node: dict, bounds: dict, roots: dict, local_raw: dict | None = None) -> dict:
    if node.get("kind") == "PAIR_SUM":
        pair = tuple(node.get("pair", []))
        require(pair in PAIRS, "invalid pair-sum witness")
        i, j = pair
        require(bounds[i][1] + bounds[j][1] < roots[i][0] + roots[j][0],
                "invalid pair-sum contradiction")
        return {"closed_cases": 3 * CASES_PER_CYCLE, "unknown_cases": 0,
                "order_groups_closed": 0, "local_order_groups_closed": 0,
                "angular_models_verified": 0}
    propagated = propagate_radial(bounds, roots)
    weights = verify_angles(node.get("angles"), propagated, roots)
    local = verify_local_certificate(local_raw)
    local_classifier = (lambda order: order_is_local(
        order, weights, propagated, roots, local)) if local is not None else None
    report = verify_angular_cover(node, bounds, roots,
                                  local_classifier=local_classifier)
    if "core_orders" in node:
        core = verify_core_orders(node["core_orders"], weights,
                                  local_classifier=local_classifier)
        report["core_orders_checked"] = core["orders"]
        report["core_order_models"] = core["models"]
        report["core_all_orders_excluded"] = core["all_orders_excluded"]
        report["local_order_models_closed"] = core["local_models_closed"]
        report["core_all_orders_closed"] = core["all_orders_closed"]
        case_closures = core_closed_sector_assignments(node.get("cycles", []),
                                                       core["closed_orders"], weights)
        report["core_order_assignment_closures"] = case_closures
        report["closed_cases"] += case_closures
        report["unknown_cases"] -= case_closures
        if core["all_orders_closed"]:
            report["closed_cases"] = 3 * CASES_PER_CYCLE
            report["unknown_cases"] = 0
    else:
        report["core_orders_checked"] = report["core_order_models"] = 0
        report["core_all_orders_excluded"] = False
        report["local_order_models_closed"] = 0
        report["core_all_orders_closed"] = False
        report["core_order_assignment_closures"] = 0
    return report


def verify(data: dict) -> dict:
    require(data.get("schema") == SCHEMA, "unsupported adaptive-tree schema")
    require(rational(data.get("container_radius_upper")) == RADIUS_UPPER, "wrong radius scope")
    require(type(data.get("angle_scale")) is int and data["angle_scale"] == SCALE,
            "unsupported angle scale")
    verify_large_four(data.get("large_four_certificate", {}))
    roots = parse_roots(data.get("sqrt_enclosures", []))
    local = verify_local_certificate(data.get("local_lower_bound"))
    nodes = data.get("nodes")
    require(isinstance(nodes, list) and bool(nodes), "missing proof tree")
    stack = [(0, global_radial_bounds(roots), 0)]
    seen, frontier = set(), []
    leaves = excluded = splits = unknown_cases = closed_cases = 0
    order_groups_closed = angular_models_verified = depth_max = 0
    core_order_leaves = core_order_models = 0
    local_order_models_closed = local_terminal_leaves = 0
    local_order_groups_closed = local_order_terminal_leaves = 0
    core_order_assignment_closures = 0
    while stack:
        index, bounds, depth = stack.pop()
        require(type(index) is int and 0 <= index < len(nodes) and index not in seen,
                "invalid, reused, or cyclic tree node")
        seen.add(index)
        depth_max = max(depth, depth_max)
        node = nodes[index]
        require(isinstance(node, dict), "invalid tree node")
        if node.get("kind") == "RADIAL_SPLIT":
            require(pair_sum_contradiction(bounds, roots) is None, "split of inconsistent bounds")
            bounds = propagate_radial(bounds, roots)
            children = node.get("children")
            require(isinstance(children, list) and len(children) == 2
                    and all(type(i) is int for i in children), "split must have both children")
            left, right = split_bounds(bounds, node.get("label"), rational(node.get("cut")))
            stack.extend(((children[1], right, depth + 1), (children[0], left, depth + 1)))
            splits += 1
            continue
        report = leaf_report(node, bounds, roots, data.get("local_lower_bound"))
        if report["core_orders_checked"]:
            core_order_leaves += 1
            core_order_models += report["core_order_models"]
            local_order_models_closed += report["local_order_models_closed"]
            core_order_assignment_closures += report["core_order_assignment_closures"]
            if report["core_all_orders_closed"] and report["local_order_models_closed"]:
                local_terminal_leaves += 1
        leaves += 1
        closed_cases += report["closed_cases"]
        unknown_cases += report["unknown_cases"]
        order_groups_closed += report["order_groups_closed"]
        local_order_groups_closed += report.get("local_order_groups_closed", 0)
        angular_models_verified += report["angular_models_verified"]
        if report["unknown_cases"]:
            frontier.append({"node": index, "depth": depth,
                             "unknown_sector_cases": report["unknown_cases"],
                             "bounds": [[str(v) for v in bounds[i]] for i in LABELS]})
        else:
            excluded += 1
            if report.get("local_order_groups_closed", 0):
                local_order_terminal_leaves += 1
    require(seen == set(range(len(nodes))), "unreachable tree nodes")
    require(data.get("frontier") == sorted(row["node"] for row in frontier),
            "frontier does not equal unresolved leaves")
    require(len(nodes) == 2 * splits + 1 and leaves == splits + 1, "incomplete binary tree")
    status = "UNKNOWN" if frontier else (
        "COMPLETE_LOCAL_OR_INFEASIBLE_AT_U" if local is not None else "COMPLETE_EXCLUSION_AT_U")
    return {"status": status,
            "coverage_verified": True, "nodes": len(nodes), "splits": splits,
            "leaves": leaves, "excluded_leaves": excluded, "unknown_leaves": len(frontier),
            "unknown_leaf_sector_cases": unknown_cases, "closed_leaf_sector_cases": closed_cases,
            "max_depth": depth_max, "order_groups_closed": order_groups_closed,
            "local_order_groups_closed": local_order_groups_closed,
            "local_order_terminal_leaves": local_order_terminal_leaves,
            "core_order_leaves": core_order_leaves,
            "core_order_models": core_order_models,
            "local_order_models_closed": local_order_models_closed,
            "core_order_assignment_closures": core_order_assignment_closures,
            "local_terminal_leaves": local_terminal_leaves,
            "local_terminal_enabled": local is not None,
            "local_delta_lower": str(local["delta"]) if local is not None else None,
            "angular_models_verified": angular_models_verified,
            "all_leaves_closed": not frontier, "global_optimality_proved": False,
            "frontier": frontier}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("certificate", type=Path)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    raw = args.certificate.read_bytes()
    report = verify(json.loads(raw))
    report["certificate_sha256"] = hashlib.sha256(raw).hexdigest()
    report["verifier_sha256"] = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({k: v for k, v in report.items() if k != "frontier"}, indent=2))


if __name__ == "__main__":
    main()
