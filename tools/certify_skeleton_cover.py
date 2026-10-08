"""Discover a full radial/sector ledger; all exclusions have exact replay."""
from __future__ import annotations

import argparse
from fractions import Fraction as Q
from itertools import product
import json
from math import acos, floor, isqrt
from pathlib import Path
import time

from proof.skeleton_cover import (
    LABELS, PAIRS, SCALE, SCHEMA, RADIUS_UPPER, assignment_masks,
    canonical_cycles, cell_bounds, cosine_lower, cosine_upper, negative_cycle,
    pair_sum_contradiction, parse_roots, partition_spec, pi_ticks,
    propagate_radial, sector_graph, sector_spans, spans_for_case,
    verify, verify_angles, verify_cycle, core_order_refinements,
    effective_masks, full_order_graph, projected_orders,
)


def root_witnesses() -> list[dict]:
    scale = 10 ** 12
    rows = []
    for i in LABELS:
        lo = isqrt(i * scale * scale)
        hi = lo if lo * lo == i * scale * scale else lo + 1
        rows.append({"label": i, "lo": str(Q(lo, scale)), "hi": str(Q(hi, scale))})
    return rows


def discover_angles(bounds: dict, roots: dict) -> list[int]:
    result = []
    pi_lo, _ = pi_ticks()
    for i, j in PAIRS:
        hi = cosine_upper(i, j, bounds, roots)
        if hi is None or hi >= 1:
            result.append(0)
            continue
        # Float acos only proposes a grid value. The exact Taylor inequality
        # below, and again the separate replay, decide whether it is valid.
        proposed = max(0, min(pi_lo, floor(acos(max(-1.0, float(hi))) * SCALE)))
        while proposed and cosine_lower(Q(proposed, SCALE)) < hi:
            proposed -= 1
        result.append(proposed)
    return result


def order_refinements(order: tuple, weights: tuple, outcomes: list,
                      local_classifier=None) -> list[dict]:
    groups = sorted({effective_masks(weights, masks)
                     for masks, outcome in zip(assignment_masks(), outcomes) if outcome == -1})
    records = []
    for masks in groups:
        witnesses = []
        for candidate in projected_orders(order, masks):
            edges = full_order_graph(candidate, weights, order)
            witness = negative_cycle(len(candidate), edges)
            if witness is not None:
                verify_cycle(edges, witness)
                witnesses.append(list(witness))
                continue
            core_order = tuple(label for label in candidate if label not in (1, 3, 4))
            if local_classifier is not None and local_classifier(core_order):
                witnesses.append(None)
                continue
            if witness is None:
                # Produce an actual feasible point of the RELAXATION. It is
                # neither a Cartesian placement nor a packing certificate.
                values = [0] * len(candidate)
                for _ in candidate:
                    for u, v, c in edges:
                        values[v] = min(values[v], values[u] + c)
                shift = values[0]
                values = [v - shift for v in values]
                if not all(values[v] <= values[u] + c for u, v, c in edges):
                    raise ValueError("failed to construct angular model")
                records.append({"masks": list(masks), "kind": "ANGLE_MODEL",
                                "order": list(candidate), "potentials": values})
                break
        else:
            kind = ("ALL_ORDERS_LOCAL_OR_EXCLUDED" if any(
                witness is None for witness in witnesses) else "ALL_ORDERS_EXCLUDED")
            records.append({"masks": list(masks), "kind": kind,
                            "witnesses": witnesses})
    return records


def build_cell(roots: dict, spec: tuple, index: tuple, all_pair_orders: bool = False) -> dict:
    return {"index": list(index), **build_radial_leaf(cell_bounds(roots, spec, index), roots,
                                                    all_pair_orders)}


def build_radial_leaf(bounds: dict, roots: dict, all_pair_orders: bool = False) -> dict:
    pair = pair_sum_contradiction(bounds, roots)
    if pair is not None:
        return {"kind": "PAIR_SUM", "pair": list(pair)}
    bounds = propagate_radial(bounds, roots)
    angles = discover_angles(bounds, roots)
    weights = verify_angles(angles, bounds, roots)
    records = []
    tables = None
    for order in canonical_cycles():
        spans = tuple(weights[order[k]][order[(k + 1) % 4]] for k in range(4))
        edges = sector_graph(order, weights, spans)
        witness = negative_cycle(4, edges)
        if witness is not None:
            verify_cycle(edges, witness)
            records.append({"order": list(order), "kind": "CYCLE", "witness": list(witness)})
            continue
        if tables is None:
            tables = sector_spans(weights)
        cache = {}
        pool = []
        indices = {}
        outcomes = []
        for masks in assignment_masks():
            spans = spans_for_case(order, masks, tables)
            if spans not in cache:
                edges = sector_graph(order, weights, spans)
                witness = negative_cycle(4, edges)
                if witness is None:
                    cache[spans] = -1
                else:
                    verify_cycle(edges, witness)
                    if witness not in indices:
                        indices[witness] = len(pool)
                        pool.append(list(witness))
                    cache[spans] = indices[witness]
            outcomes.append(cache[spans])
        record = {"order": list(order), "kind": "SECTOR_CASES",
                  "outcomes": outcomes, "witnesses": pool}
        if all_pair_orders:
            record["order_groups"] = order_refinements(order, weights, outcomes)
        records.append(record)
    return {"kind": "ANGLE_COVER", "angles": angles, "cycles": records}


def build(large_four: dict, partitions: dict, progress: bool = False,
          all_pair_orders: bool = False) -> dict:
    rows = root_witnesses()
    roots = parse_roots(rows)
    spec = partition_spec(partitions)
    cells = []
    for index in product(*(range(parts) for _, parts in spec)):
        cell = build_cell(roots, spec, index, all_pair_orders)
        cells.append(cell)
        if progress:
            pending = sum(row.get("outcomes", []).count(-1) for row in cell.get("cycles", []))
            print(json.dumps({"cell": list(index), "kind": cell["kind"],
                              "unknown_cases": pending}), flush=True)
    return {"schema": SCHEMA, "container_radius_upper": str(RADIUS_UPPER),
            "angle_scale": SCALE, "large_four_certificate": large_four,
            "sqrt_enclosures": rows, "radial_partitions": partitions, "cells": cells}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lemma", type=Path, default=Path("certificates/large-four-skeleton-v1.json"))
    parser.add_argument("--partitions", default="7:2,8:2,9:2,10:2",
                        help="label:part-count pairs; empty string means one radial cell")
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--all-pair-orders", action="store_true",
                        help="check all projected cyclic orders, including cross-sector pairs")
    args = parser.parse_args()
    partitions = dict(item.split(":") for item in args.partitions.split(",") if item)
    partitions = {key: int(value) for key, value in partitions.items()}
    start = time.monotonic()
    data = build(json.loads(args.lemma.read_text()), partitions, progress=True,
                 all_pair_orders=args.all_pair_orders)
    report = verify(data)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(data, separators=(",", ":")) + "\n")
    print(json.dumps({**{k: report[k] for k in (
        "status", "radial_cells", "covered_cases", "closed_cases", "unknown_cases")},
                     "elapsed_seconds": time.monotonic() - start}, indent=2))


if __name__ == "__main__":
    main()
