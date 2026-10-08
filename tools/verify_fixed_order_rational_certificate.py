#!/usr/bin/env python3
"""Exact-rational replay of the 7.9 fixed-order radial certificate.

This verifier replaces the original MPFI angle/remainder checks with a
Fraction-only check. Decimal values in the compressed certificate are parsed
as exact rationals. Float acos is used only to propose a rational angle tick;
each proposed tick is accepted only after an exact Taylor inequality proves
that its cosine exceeds the exact rational cosine upper bound.
"""
from __future__ import annotations

import gzip
import itertools
import json
import math
from fractions import Fraction as F
from math import factorial, isqrt
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
CERT = ROOT / "certificates/fixed-order-radial-partition7-mpfi-7.9.dat.gz"
RHO = F("7.9")
START, N, SPLIT = 4, 7, 2
SCALE = 10**12
SQRT_SCALE = 10**100
TAYLOR_LAST = 21  # odd: the remaining alternating cosine tail is positive


def atan_upper(x: int, terms: int) -> F:
    """Upper/lower alternating-series partial sum for atan(1/x)."""
    return sum(((-1) ** k) * F(1, (2 * k + 1) * x ** (2 * k + 1))
               for k in range(terms))


PI_UP = 16 * atan_upper(5, 7) - 4 * atan_upper(239, 2)
assert 3 < PI_UP < F(355, 113)


def cosine_lower(q: F) -> F:
    assert 0 <= q < F(355, 113)
    return sum(((-1) ** k) * q ** (2 * k) / factorial(2 * k)
               for k in range(TAYLOR_LAST + 1))


ROOT_LO = {i: F(isqrt(i * SQRT_SCALE * SQRT_SCALE), SQRT_SCALE)
           for i in range(START, START + N)}
assert all(x * x <= i < (x + F(1, SQRT_SCALE)) ** 2
           for i, x in ROOT_LO.items())


def decimal_fraction(raw: str) -> F:
    # Fraction accepts decimal and scientific-notation strings exactly.
    return F(raw)


def proposed_angle_tick(cosine_upper: F) -> F:
    """Choose q with cos(q)>cosine_upper, then certify it exactly."""
    if cosine_upper >= 1:
        return F(0)
    if cosine_upper <= -1:
        tick = F(1, SCALE)
        q = F(math.floor((math.pi - 2 * float(tick)) * SCALE), SCALE)
    else:
        q = F(math.floor(math.acos(float(cosine_upper)) * SCALE), SCALE)
        tick = F(1, SCALE)
    # Floating point only proposes q. Exact Fraction arithmetic decides.
    while q > 0 and cosine_lower(q) <= cosine_upper:
        q -= tick
    assert q >= 0 and cosine_lower(q) > cosine_upper
    return q


def angle_tick(label_i: int, label_j: int,
               radial_i: tuple[F, F], radial_j: tuple[F, F]) -> F:
    # Reuse the at-most 4 radial interval combinations for every record/order.
    lo_i, hi_i = radial_i
    lo_j, hi_j = radial_j
    d_lo = ROOT_LO[label_i] + ROOT_LO[label_j]
    d2_lo = d_lo * d_lo
    c_upper = max((x * x + y * y - d2_lo) / (2 * x * y)
                  for x in (lo_i, hi_i) for y in (lo_j, hi_j))
    return proposed_angle_tick(c_upper)


def order_representatives() -> set[tuple[int, ...]]:
    return {(START,) + tail for tail in itertools.permutations(range(START + 1, START + N))
            if tail[0] < tail[-1]}


def base_domain() -> dict[int, tuple[F, F]]:
    return {
        i: (max(F(0), max(ROOT_LO[i] + 2 * ROOT_LO[j] - RHO
                          for j in ROOT_LO if j != i)), RHO - ROOT_LO[i])
        for i in ROOT_LO
    }


def verify(path: Path = CERT) -> dict:
    expected_orders = order_representatives()
    domain = base_domain()
    by_order: dict[tuple[int, ...], dict[tuple[int, ...], tuple]] = {
        order: {} for order in expected_orders
    }
    tick_cache: dict[tuple, F] = {}
    records = 0
    minimum_angle_margin: F | None = None
    minimum_cycle_margin: F | None = None
    minimum_column_slack: F | None = None

    with gzip.open(path, "rt", encoding="ascii") as stream:
        header = stream.readline().split()
        expected_records = len(expected_orders) * SPLIT**N
        assert header == ["RHO", "7.9", str(expected_records)], header
        for line_number, line in enumerate(stream, 2):
            tokens = line.split()
            assert len(tokens) == 1 + N + 2 * N + N * (N - 1), (line_number, len(tokens))
            assert tokens[0] == "CELL", line_number
            order = tuple(map(int, tokens[1:1 + N]))
            assert order in expected_orders
            bounds_raw = [decimal_fraction(x) for x in tokens[1 + N:1 + 3 * N]]
            assert all(bounds_raw[2 * k] <= bounds_raw[2 * k + 1] for k in range(N))
            box = tuple((bounds_raw[2 * k], bounds_raw[2 * k + 1]) for k in range(N))
            # Same Cartesian radial partition is repeated for all 360 orders.
            key = tuple(box)
            assert key not in by_order[order], (line_number, "duplicate radial box")
            by_order[order][key] = box

            coefficients = [decimal_fraction(x) for x in tokens[1 + 3 * N:]]
            assert len(coefficients) == N * (N - 1)
            assert all(c >= 0 for c in coefficients)
            radial_by_label = dict(zip(range(START, START + N), box))
            columns = [F(0)] * N
            total = F(0)
            k = 0
            for p in range(N):
                for q in range(p + 1, N):
                    i, j = order[p], order[q]
                    radial_i, radial_j = radial_by_label[i], radial_by_label[j]
                    cache_key = (i, j, radial_i, radial_j)
                    if cache_key not in tick_cache:
                        tick_cache[cache_key] = angle_tick(i, j, radial_i, radial_j)
                    angle = tick_cache[cache_key]
                    if minimum_angle_margin is None or angle < minimum_angle_margin:
                        minimum_angle_margin = angle
                    for path_index in range(2):
                        coefficient = coefficients[k]
                        total += coefficient * angle
                        length = (q - p) if path_index == 0 else (p - q + N)
                        start = p if path_index == 0 else q
                        for step in range(length):
                            gap = (start + step) % N
                            columns[gap] += coefficient
                        k += 1
            assert k == len(coefficients)
            assert all(value <= 1 for value in columns), (line_number, "Farkas column exceeds one")
            column_slack = min(1 - value for value in columns)
            if minimum_column_slack is None or column_slack < minimum_column_slack:
                minimum_column_slack = column_slack
            cycle_margin = total - 2 * PI_UP
            assert cycle_margin > 0, (line_number, "Farkas angle sum does not exceed 2*pi")
            if minimum_cycle_margin is None or cycle_margin < minimum_cycle_margin:
                minimum_cycle_margin = cycle_margin
            records += 1

    assert records == len(expected_orders) * SPLIT**N
    assert set(by_order) == expected_orders
    first_boxes = set(by_order[next(iter(expected_orders))])
    assert len(first_boxes) == SPLIT**N
    assert all(set(boxes) == first_boxes for boxes in by_order.values())

    # The certificate is a complete Cartesian cover: every coordinate has two
    # intervals, and every combination occurs once. Outward rounding may make
    # adjacent intervals overlap; that is safe and explicitly checked.
    coordinate_options = []
    for k, label in enumerate(range(START, START + N)):
        intervals = sorted({box[k] for box in first_boxes})
        assert len(intervals) == SPLIT, (label, intervals)
        lower, upper = domain[label]
        assert intervals[0][0] <= lower and intervals[-1][1] >= upper, label
        assert intervals[0][1] >= intervals[1][0], (label, "radial gap")
        coordinate_options.append({interval: idx for idx, interval in enumerate(intervals)})
    for boxes in first_boxes:
        pattern = tuple(coordinate_options[k][boxes[k]] for k in range(N))
        assert len(pattern) == N
    # Enforce uniqueness of all 2^N coordinate-choice tuples.
    patterns = {tuple(coordinate_options[k][box[k]] for k in range(N))
                for box in first_boxes}
    assert patterns == set(itertools.product(range(SPLIT), repeat=N))

    return {
        "status": "CERTIFIED_EXACT_RATIONAL",
        "certificate": str(path.relative_to(ROOT)),
        "orders": len(expected_orders),
        "radial_boxes_per_order": SPLIT**N,
        "records": records,
        "exact_angle_ticks_checked": len(tick_cache),
        "minimum_angle_tick": str(minimum_angle_margin),
        "minimum_farkas_cycle_margin_over_2pi_upper": str(minimum_cycle_margin),
        "minimum_farkas_column_slack": str(minimum_column_slack),
    }


def main() -> None:
    report = verify()
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
