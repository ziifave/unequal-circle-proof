"""Radial-box covering contractor using shared-radius Farkas witnesses.

Each node stores independent radial intervals and the still-uncovered order
set is recomputed at its midpoint.  An order is removed only when its
midpoint positive cycle has a strictly positive certified lower margin over
the whole node.  Thus a fully closed leaf is proof-safe; this prototype also
records unresolved leaves for continuation.
"""
from __future__ import annotations

import argparse
import heapq
import json
import time
from math import sqrt
from decimal import ROUND_FLOOR
from pathlib import Path

from proof.angular import _angle_lower_from_bounds
from proof.interval import D, _binary, set_precision
from proof.model import PackingModel
from tools.all_pair_order_lp import all_orders
from tools.shared_radius_farkas import (Edge, midpoint_weights, positive_cycle,
                                         radial_bounds, robust_margin)


def lower_angles(model, radial):
    out = {}
    for ii, i in enumerate(model.labels):
        for jj in range(ii):
            j = model.labels[jj]
            out[(j, i)] = _angle_lower_from_bounds(
                model.radii[ii].lo, model.radii[jj].lo,
                radial[ii][0], radial[ii][1], radial[jj][0], radial[jj][1])
    return out


def midpoint_weights_radial(model, radial):
    from math import acos, sqrt
    out = {}
    for ii, i in enumerate(model.labels):
        a = float((radial[ii][0] + radial[ii][1]) / 2)
        for jj in range(ii):
            j = model.labels[jj]
            b = float((radial[jj][0] + radial[jj][1]) / 2)
            c = (a*a+b*b-(sqrt(i)+sqrt(j))**2)/(2*a*b)
            out[(j, i)] = acos(max(-1.0, min(1.0, c)))
    return out


def margin_from_cycle(cycle, lower):
    total = D(0)
    for edge in cycle:
        if edge.pair is not None:
            total = _binary(total, lower[edge.pair], "+", ROUND_FLOOR)
        if edge.const == "plus2pi":
            from proof.angular import PI_LO
            total = _binary(total, _binary(D(2), PI_LO, "*", ROUND_FLOOR), "+", ROUND_FLOOR)
        elif edge.const == "minus2pi":
            from proof.angular import PI_HI
            total = _binary(total, _binary(D(-2), PI_HI, "*", ROUND_FLOOR), "+", ROUND_FLOOR)
    return total


def inspect(model, radial, orders):
    weights = midpoint_weights_radial(model, radial)
    lower = lower_angles(model, radial)
    unresolved = 0
    certified = 0
    scores = [0.0] * model.n
    unresolved_orders = []
    mids = [float((lo + hi) / 2) for lo, hi in radial]
    half = [float((hi - lo) / 2) for lo, hi in radial]
    for order in orders:
        cycle = positive_cycle(order, weights)
        if cycle is None:
            unresolved += 1
            unresolved_orders.append(order)
            continue
        if margin_from_cycle(cycle, lower) > 0:
            certified += 1
        else:
            unresolved += 1
            unresolved_orders.append(order)
            for edge in cycle:
                if edge.pair is None:
                    continue
                i, j = edge.pair
                ii, jj = model.labels.index(i), model.labels.index(j)
                a, b = mids[ii], mids[jj]
                d = sqrt(i) + sqrt(j)
                c = (a*a + b*b - d*d) / (2*a*b)
                den = max(1e-12, sqrt(max(0.0, 1.0-c*c)))
                da = abs((a*a-b*b+d*d) / (2*a*a*b*den))
                db = abs((b*b-a*a+d*d) / (2*b*b*a*den))
                scores[ii] += da * half[ii]
                scores[jj] += db * half[jj]
    return unresolved, certified, scores, unresolved_orders


def lookahead_dimension(model, radial, orders):
    """Choose a split coordinate by testing both children on a sample."""
    sample = list(orders)
    if len(sample) > 256:
        step = max(1, len(sample) // 256)
        sample = sample[::step][:256]
    widths = [hi-lo for lo, hi in radial]
    candidates = sorted(range(len(widths)), key=lambda i: widths[i], reverse=True)[:5]
    best = None
    diagnostics = []
    for k in candidates:
        lo, hi = radial[k]
        mid = _binary(lo, hi, "+", ROUND_FLOOR) / 2
        left, right = list(radial), list(radial)
        left[k] = (lo, mid)
        right[k] = (mid, hi)
        left_unresolved, _, _, _ = inspect(model, left, sample)
        right_unresolved, _, _, _ = inspect(model, right, sample)
        score = 2 * len(sample) - left_unresolved - right_unresolved
        if best is None or score > best[0]:
            best = (score, k)
    return best[1] if best is not None else max(range(len(widths)), key=lambda i: widths[i])


def exact_lookahead_dimension(model, radial, orders):
    """Pick among the three widest coordinates using full child scans."""
    widths = [hi-lo for lo, hi in radial]
    candidates = sorted(range(len(widths)), key=lambda i: widths[i], reverse=True)[:3]
    best = None
    diagnostics = []
    for k in candidates:
        lo, hi = radial[k]
        mid = _binary(lo, hi, "+", ROUND_FLOOR) / 2
        left, right = list(radial), list(radial)
        left[k] = (lo, mid)
        right[k] = (mid, hi)
        lu, lc, _, luo = inspect(model, left, orders)
        ru, rc, _, ruo = inspect(model, right, orders)
        overlap = len(set(luo).intersection(ruo))
        score = lc + rc - 0.25 * overlap
        diagnostics.append({"dimension": k, "score": score,
                            "left_certified": lc, "right_certified": rc,
                            "overlap": overlap})
        if best is None or score > best[0]:
            best = (score, k, lc, rc, overlap)
    return best[1], (best[0], best[1], best[2], best[3], best[4], diagnostics)


def split_radial(radial):
    widths = [hi-lo for lo, hi in radial]
    k = max(range(len(widths)), key=lambda i: widths[i])
    lo, hi = radial[k]
    mid = _binary(lo, hi, "+", ROUND_FLOOR) / 2
    a, b = list(radial), list(radial)
    a[k] = (lo, mid)
    b[k] = (mid, hi)
    return a, b


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("survivors", type=Path)
    ap.add_argument("--node", required=True)
    ap.add_argument("--max-nodes", type=int, default=20)
    ap.add_argument("--seconds", type=float, default=120)
    ap.add_argument("--precision", type=int, default=90)
    ap.add_argument("--branching", choices=("width", "lookahead"), default="width")
    ap.add_argument("--exact-lookahead", action="store_true")
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    set_precision(args.precision)
    data = json.loads(args.survivors.read_text())
    raw = next(x for x in data["queued_boxes"] if x["node"] == args.node)
    model = PackingModel(len(data["radii_squared"]), "8.0", data["radii_squared"])
    orders = tuple(all_orders(tuple(model.labels)))
    root = radial_bounds(model, raw)
    queue = [(0, root)]
    leaves = []
    deadline = time.monotonic() + args.seconds
    processed = 0
    split_log = []
    while queue and processed < args.max_nodes and time.monotonic() < deadline:
        depth, radial = queue.pop()
        processed += 1
        unresolved, certified, scores, unresolved_orders = inspect(model, radial, orders)
        if unresolved == 0:
            leaves.append({"depth": depth, "status": "CLOSED", "certified": certified})
            continue
        if processed >= args.max_nodes or time.monotonic() >= deadline:
            leaves.append({"depth": depth, "status": "OPEN", "unresolved": unresolved,
                           "certified": certified, "split_score": max(scores)})
            continue
        if args.exact_lookahead:
            k, detail = exact_lookahead_dimension(model, radial, orders)
            split_log.append({"depth": depth, "dimension": k,
                              "score": detail[0], "left_certified": detail[2],
                              "right_certified": detail[3], "overlap": detail[4],
                              "candidates": detail[5]})
        elif args.branching == "lookahead":
            k = lookahead_dimension(model, radial, unresolved_orders)
        else:
            k = max(range(len(radial)), key=lambda i: radial[i][1] - radial[i][0])
        lo, hi = radial[k]
        mid = _binary(lo, hi, "+", ROUND_FLOOR) / 2
        left, right = list(radial), list(radial)
        left[k] = (lo, mid)
        right[k] = (mid, hi)
        queue.append((depth+1, left))
        queue.append((depth+1, right))
    leaves.extend({"depth": depth, "status": "FRONTIER"} for depth, _ in queue)
    payload = {"kind": "shared-radius-cover-diagnostic", "node": args.node,
               "orders": len(orders), "processed": processed, "frontier": len(queue),
               "leaves": leaves, "split_log": split_log}
    args.output.write_text(json.dumps(payload, indent=2) + "\n")
    print(json.dumps({"node": args.node, "processed": processed,
                      "closed": sum(x.get("status") == "CLOSED" for x in leaves),
                      "frontier": len(queue)}, indent=2))


if __name__ == "__main__":
    main()
