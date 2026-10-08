#!/usr/bin/env python3
"""Compose the exact ten-disk global optimality proof certificates.

All theorem premises are replayed locally. The result checks the v27
exhaustive tree, both attached geometric theorems, and the exact 10-disk
upper witness. It then maps every v27 open/local terminal model to one of the
attached angle-barrier or nine-circle impossibility theorems.
"""
from __future__ import annotations

import hashlib
import importlib.util
import json
import runpy
import sys
import gzip
from collections import Counter
from fractions import Fraction as F
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

from proof.skeleton_cover import (  # noqa: E402
    assignment_masks,
    canonical_cycles,
    effective_masks,
    global_radial_bounds,
    parse_roots,
    projected_orders,
    propagate_radial,
    verify_angles,
)
from proof.skeleton_local_terminal import order_is_local, verify_local_certificate  # noqa: E402
from proof.skeleton_radial_tree import split_bounds, verify as verify_radial_tree  # noqa: E402
from proof.large_four_certificate import rational  # noqa: E402

U_MAIN = F("8.303468122111490")
U_ALT = F("8.30346812212")
T_RANGE = (F("0.8588"), F("1.1265"))
MAIN_RADIUS_FLOOR = F(6) + F(31, 10) - T_RANGE[1]
CORE = frozenset((2, 5, 6, 7, 8, 9, 10))
MAIN_ORDER = (10, 5, 7, 9, 2, 8, 6)
ALT_ORDERS = {
    (10, 3, 7, 5, 8, 4, 6, 9, 2),
    (10, 3, 7, 5, 8, 6, 4, 9, 2),
}
EXPECTED_ALT_MASKS = Counter({(5, 16, 40, 2): 3, (4, 16, 41, 2): 1})


def load_module(path: Path, name: str):
    spec = importlib.util.spec_from_file_location(name, path)
    assert spec and spec.loader
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def require_main_order(order: tuple[int, ...], radial10: tuple[F, F]) -> None:
    assert tuple(label for label in order if label in CORE) == MAIN_ORDER, order
    assert radial10[0] >= T_RANGE[0] and radial10[1] <= T_RANGE[1], radial10
    # Non-overlap of disks 9 and 10 gives s_9 + t >= 3 + sqrt(10);
    # containment gives R >= 3 + s_9. Since sqrt(10) > 31/10 and
    # t <= 1.1265, every such packing has R > 15947/2000.
    assert F(31, 10) ** 2 < F(10)
    assert MAIN_RADIUS_FLOOR == F(15947, 2000)
    assert MAIN_RADIUS_FLOOR > F(79, 10)


def replay_tree_and_connect(data: dict) -> dict:
    report = verify_radial_tree(data)
    assert report["coverage_verified"] is True
    assert report["status"] == "UNKNOWN"
    assert report["unknown_leaf_sector_cases"] == 197
    assert report["angular_models_verified"] == 197
    assert report["local_order_models_closed"] == 145
    assert report["local_order_groups_closed"] == 2

    roots = parse_roots(data["sqrt_enclosures"])
    local = verify_local_certificate(data.get("local_lower_bound"))
    assert local is not None
    stack = [(0, global_radial_bounds(roots))]
    main_cases = alt_cases = 0
    unknown_assignment_count = 0
    alt_mask_counts: Counter[tuple[int, ...]] = Counter()
    alt_order_counts: Counter[tuple[int, ...]] = Counter()
    local_core_models = local_full_witnesses = 0
    target_t_boxes = 0
    seen_leaves = 0

    while stack:
        index, bounds = stack.pop()
        node = data["nodes"][index]
        if node.get("kind") == "RADIAL_SPLIT":
            bounds = propagate_radial(bounds, roots)
            left, right = split_bounds(bounds, node["label"], rational(node["cut"]))
            stack.extend(((node["children"][0], left), (node["children"][1], right)))
            continue

        seen_leaves += 1
        bounds = propagate_radial(bounds, roots)
        weights = verify_angles(node["angles"], bounds, roots)
        for record in node.get("cycles", []):
            if record.get("kind") != "SECTOR_CASES":
                continue
            pending_by_masks: Counter[tuple[int, ...]] = Counter()
            for masks, outcome in zip(assignment_masks(), record["outcomes"]):
                if outcome == -1:
                    pending_by_masks[effective_masks(weights, masks)] += 1
            for group in record.get("order_groups", []):
                kind = group.get("kind")
                masks = tuple(group.get("masks", []))
                pending_count = pending_by_masks[masks]
                if kind == "ANGLE_MODEL":
                    order = tuple(group["order"])
                    unknown_assignment_count += pending_count
                    core_order = tuple(label for label in order if label in CORE)
                    if core_order == MAIN_ORDER:
                        require_main_order(order, bounds[10])
                        main_cases += pending_count
                        target_t_boxes += 1
                    else:
                        nine_order = tuple(label for label in order if label != 1)
                        assert nine_order in ALT_ORDERS, (order, nine_order)
                        assert set(nine_order) == set(range(2, 11))
                        alt_cases += pending_count
                        alt_mask_counts[masks] += pending_count
                        alt_order_counts[nine_order] += pending_count
                    continue

                # The only remaining terminal witnesses that used the local
                # premise are explicit None entries. Re-check their complete
                # order and radial box against the new angle-barrier theorem.
                if kind in {"ALL_ORDERS_LOCAL_OR_EXCLUDED", "ALL_ORDERS_CERTIFIED"}:
                    skeleton = tuple(record["order"])
                    projected = list(projected_orders(skeleton, masks))
                    witnesses = group["witnesses"]
                    assert len(projected) == len(witnesses)
                    for order, witness in zip(projected, witnesses):
                        if witness is None:
                            assert order_is_local(order, weights, bounds, roots, local)
                            require_main_order(order, bounds[10])
                            local_full_witnesses += 1

        core_record = node.get("core_orders")
        if core_record is not None:
            for outcome in core_record["outcomes"]:
                if outcome >= 0:
                    continue
                model = core_record["models"][-outcome - 1]
                order = tuple(model["order"])
                if order_is_local(order, weights, bounds, roots, local):
                    require_main_order(order, bounds[10])
                    local_core_models += 1

    assert seen_leaves == report["leaves"]
    assert (main_cases, alt_cases, unknown_assignment_count) == (193, 4, 197)
    assert alt_mask_counts == EXPECTED_ALT_MASKS, alt_mask_counts
    assert set(alt_order_counts).issubset(ALT_ORDERS)
    assert sum(alt_order_counts.values()) == 4
    assert local_core_models == 145
    assert local_full_witnesses == 2
    assert target_t_boxes >= 193
    total_sector_cases = 3 * 4**6 * report["leaves"]
    assert report["closed_leaf_sector_cases"] + report["unknown_leaf_sector_cases"] == total_sector_cases

    return {
        "v27_tree_status_before_completion": report["status"],
        "tree_coverage_verified": True,
        "tree_nodes": report["nodes"],
        "tree_splits": report["splits"],
        "tree_leaves": report["leaves"],
        "total_sector_cases": total_sector_cases,
        "closed_sector_cases_before_new_theorems": report["closed_leaf_sector_cases"],
        "unresolved_sector_cases_before_new_theorems": report["unknown_leaf_sector_cases"],
        "unresolved_sector_cases_after_theorem_connection": 0,
        "all_sector_cases_closed_after_theorem_connection": total_sector_cases,
        "main_order_residual_assignments": main_cases,
        "alternate_nine_circle_residual_assignments": alt_cases,
        "alternate_masks": {"/".join(map(str, key)): value
                            for key, value in sorted(alt_mask_counts.items())},
        "alternate_nine_orders": {"/".join(map(str, key)): value
                                  for key, value in sorted(alt_order_counts.items())},
        "local_core_order_models_reclassified": local_core_models,
        "local_full_order_witnesses_reclassified": local_full_witnesses,
        "main_and_local_orders_fit_barrier_range": True,
        "strict_main_order_radius_lower_bound": f">{MAIN_RADIUS_FLOOR}",
        "all_alternate_orders_are_in_the_nine_circle_certificate": True,
    }


def run_all() -> dict:
    angle_dir = ROOT / "proof/global_completion/angle_barrier"
    four_dir = ROOT / "proof/global_completion/four_cases"

    # The attachment's monotonicity checker runs all rational sign/corner
    # inequalities as top-level assertions.
    runpy.run_path(str(angle_dir / "verify_radial_angle_monotonicity.py"))
    angle_root = load_module(angle_dir / "certified_angle_root.py", "global_angle_root")
    angle_root.main()
    angle_root.geometry_core_check()
    angle_root.interval_sign_proof()
    angle_root.full_ten_check()
    refined_root = angle_root.certify_root_below_global_upper()
    assert refined_root["R_hi"] == U_MAIN

    # Exact rational replay of the 9-circle cycle proof for both possible
    # orders. The attachment verifier reads the adjacent JSON certificate.
    nine = load_module(four_dir / "verify_nine_circle_certificate.py", "global_nine_cycle")
    nine.main()
    nine_doc = json.loads((four_dir / "nine_circle_cycle_certificate.json").read_text())
    assert F(nine_doc["U"]) == U_ALT and U_MAIN < U_ALT

    tree_path = ROOT / "certificates/skeleton-radial-tree-v27.json.gz"
    with gzip.open(tree_path, "rt", encoding="utf-8") as stream:
        tree_data = json.load(stream)
    tree_summary = replay_tree_and_connect(tree_data)
    assert F(tree_data["container_radius_upper"]) == U_MAIN

    # Every remaining leaf/order is now covered: prior negative-cycle and
    # radial contradictions, 193 + 145 + 2 applications of the radial angle
    # barrier, and four alternative cases covered by the 9-circle theorem.
    theorem_applications = {
        "main_residual_angle_barrier": 193,
        "local_core_angle_barrier": 145,
        "local_full_order_angle_barrier": 2,
        "alternate_nine_circle_theorem": 4,
    }
    assert sum(theorem_applications.values()) == 344

    inputs = [
        ROOT / "certificates/skeleton-radial-tree-v27.json.gz",
        ROOT / "proof/skeleton_radial_tree.py",
        ROOT / "proof/skeleton_cover.py",
        ROOT / "proof/skeleton_local_terminal.py",
        ROOT / "proof/large_four_certificate.py",
        ROOT / "tools/verify_global_optimality_completion.py",
        ROOT / "GLOBAL_OPTIMALITY_COMPLETION_2026-10-09.md",
        *sorted(p for p in (ROOT / "proof/global_completion").rglob("*")
                if p.is_file() and p.suffix != ".pyc"),
    ]
    hashes = {str(path.relative_to(ROOT)): sha256(path) for path in inputs}
    return {
        "status": "GLOBAL_OPTIMALITY_CERTIFIED",
        "claim": "The optimal container radius for disks of radii sqrt(1),...,sqrt(10) equals the exact angle-root Rcrit.",
        "critical_radius_bracket": [str(refined_root["R_lo"]), str(refined_root["R_hi"])],
        "global_tree_upper_scope": str(U_MAIN),
        "alternate_nine_certificate_scope": str(U_ALT),
        "strict_root_below_tree_cap": True,
        "exact_ten_disk_upper_witness": "verified; 37 non-contact pairs separated and 3 extra centers strictly contained",
        "global_tree_and_case_linkage": tree_summary,
        "theorem_applications": theorem_applications,
        "input_sha256": hashes,
    }


def main() -> None:
    report = run_all()
    out = ROOT / "artifacts/global-optimality-completion-2026-10-09.json"
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({k: v for k, v in report.items() if k != "input_sha256"}, indent=2))
    print("REPORT", out.relative_to(ROOT))
    print("REPORT_SHA256", sha256(out))


if __name__ == "__main__":
    main()
