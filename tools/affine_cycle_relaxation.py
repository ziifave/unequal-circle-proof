"""Experimental shared-radius affine/Taylor relaxation.

This version is a routing experiment, not a certificate: derivatives and
Hessian envelopes are sampled in floating arithmetic.  It preserves the
shared radial variables in the affine part and reports how many midpoint
negative-cycle witnesses become robust over a box.
"""
from __future__ import annotations

import argparse
import json
import math
from pathlib import Path

from proof.interval import set_precision
from proof.model import PackingModel
from tools.all_pair_order_lp import all_orders
from tools.shared_radius_farkas import (midpoint_weights, positive_cycle,
                                         radial_bounds)


def alpha(a, b, d):
    c = (a*a + b*b - d*d) / (2*a*b)
    return math.acos(max(-1.0, min(1.0, c)))


def pair_model(a, b, d, ha, hb):
    """Return midpoint value, gradient, and sampled Hessian envelope."""
    f0 = alpha(a, b, d)
    eps_a = max(1e-7, ha * 1e-4)
    eps_b = max(1e-7, hb * 1e-4)
    ga = (alpha(a+eps_a, b, d) - alpha(a-eps_a, b, d))/(2*eps_a)
    gb = (alpha(a, b+eps_b, d) - alpha(a, b-eps_b, d))/(2*eps_b)
    haa = abs((alpha(a+eps_a,b,d)-2*f0+alpha(a-eps_a,b,d))/(eps_a*eps_a))
    hbb = abs((alpha(a,b+eps_b,d)-2*f0+alpha(a,b-eps_b,d))/(eps_b*eps_b))
    hab = abs((alpha(a+eps_a,b+eps_b,d)-alpha(a+eps_a,b-eps_b,d)
               -alpha(a-eps_a,b+eps_b,d)+alpha(a-eps_a,b-eps_b,d))/(4*eps_a*eps_b))
    # Inflate sampled bounds deliberately; this remains diagnostic only.
    return f0, ga, gb, 2.0*haa, 2.0*hbb, 2.0*hab


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("survivors", type=Path)
    ap.add_argument("--node", required=True)
    ap.add_argument("--precision", type=int, default=90)
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    set_precision(args.precision)
    data = json.loads(args.survivors.read_text())
    raw = next(x for x in data["queued_boxes"] if x["node"] == args.node)
    model = PackingModel(len(data["radii_squared"]), "8.0", data["radii_squared"])
    labels = tuple(model.labels)
    rb = radial_bounds(model, raw)
    mid = [(float(lo+hi)/2, float(hi-lo)/2) for lo, hi in rb]
    pair_data = {}
    for i, ri in enumerate(labels):
        for j in labels[:i]:
            ii, jj = labels.index(ri), labels.index(j)
            pair_data[(j, ri)] = pair_model(mid[ii][0], mid[jj][0],
                                             math.sqrt(ri)+math.sqrt(j),
                                             mid[ii][1], mid[jj][1])
    weights = midpoint_weights(model, raw)
    orders = tuple(all_orders(labels))
    certified = 0
    max_margin = -float("inf")
    for order in orders:
        cycle = positive_cycle(order, weights)
        if cycle is None:
            continue
        value = 0.0
        coeff = {}
        for edge in cycle:
            if edge.pair is not None:
                f0, ga, gb, haa, hbb, hab = pair_data[edge.pair]
                value += f0
                i, j = edge.pair
                ii, jj = labels.index(i), labels.index(j)
                coeff[ii] = coeff.get(ii, 0.0) + ga
                coeff[jj] = coeff.get(jj, 0.0) + gb
                # Pairwise Taylor remainder for this cycle term.
                value -= 0.5*(haa*mid[ii][1]**2 + hbb*mid[jj][1]**2
                              + 2*hab*mid[ii][1]*mid[jj][1])
            elif edge.const == "plus2pi":
                value += 2*math.pi
            elif edge.const == "minus2pi":
                value -= 2*math.pi
        for i, g in coeff.items():
            value -= abs(g)*mid[i][1]
        max_margin = max(max_margin, value)
        if value > 0:
            certified += 1
    result = {"kind": "diagnostic-only", "node": args.node,
              "orders": len(orders), "affine_certified": certified,
              "max_affine_margin": max_margin}
    args.output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
