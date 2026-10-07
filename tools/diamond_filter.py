"""Proof-safe four-circle two-anchor (diamond) filter."""
from __future__ import annotations

from functools import lru_cache
from decimal import ROUND_CEILING, ROUND_FLOOR

from proof.interval import D, Interval, _binary


def _div_interval(a: Interval, b: Interval) -> Interval:
    return a / b


def _child(anchor_a: Interval, anchor_b: Interval, child: Interval,
           other_anchor: Interval):
    dab = anchor_a + anchor_b
    dac = anchor_a + child
    dbc = other_anchor + child
    x = (dac.square() - dbc.square() + dab.square()) / (Interval.point(2) * dab)
    h2 = dac.square() - x.square()
    if h2.hi < 0:
        return None
    h = Interval.sqrt_nonnegative(max(D(0), h2.lo))
    return x, h


@lru_cache(maxsize=None)
def diamond_status(ra: int, rb: int, rc: int, rd: int) -> str:
    a, b, c, d = (Interval.sqrt_integer(v) for v in (ra, rb, rc, rd))
    pc = _child(a, b, c, b)
    pd = _child(a, b, d, b)
    if pc is None or pd is None:
        return "NO_ANCHOR_INTERSECTION"
    xc, hc = pc
    xd, hd = pd
    required = (c + d).square().lo
    feasible_branch = False
    for sc in (-1, 1):
        for sd in (-1, 1):
            dy = (hc if sc == 1 else Interval.point(0) - hc) - (hd if sd == 1 else Interval.point(0) - hd)
            distance2 = (xc - xd).square() + dy.square()
            if distance2.hi >= required:
                feasible_branch = True
    return "PASS" if feasible_branch else "DIAMOND_OVERLAP"


def inspect(record: dict, labels: dict[int, int]):
    edges = {tuple(sorted(e)) for e in record["edges"] if e[0] and e[1]}
    neighbors = {v: set() for v in record["circles"]}
    for a, b in edges:
        neighbors[a].add(b); neighbors[b].add(a)
    checked = []
    for a, b in edges:
        common = sorted(neighbors[a] & neighbors[b])
        for c_i in range(len(common)):
            for d_i in range(c_i + 1, len(common)):
                c, d = common[c_i], common[d_i]
                status = diamond_status(labels[a], labels[b], labels[c], labels[d])
                checked.append({"anchors": [a, b], "children": [c, d], "status": status})
                if status == "DIAMOND_OVERLAP":
                    return False, checked
    return True, checked
