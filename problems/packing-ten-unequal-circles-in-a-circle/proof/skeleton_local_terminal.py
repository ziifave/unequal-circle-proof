"""Replay the local active-core lemma on radial/angle outer boxes.

The local constants are an explicit external theorem premise. This module
checks their scalar witnesses and root box, then verifies that every point in
one angular-order/radial projection lies in its reflected delta-neighbourhood.
"""
from __future__ import annotations

from fractions import Fraction as Q
from functools import lru_cache
from math import factorial

from .large_four_certificate import rational, require
from .skeleton_cover import SCALE, full_order_graph, pi_ticks

CORE = (2, 5, 6, 7, 8, 9, 10)


def verify_local_certificate(raw: dict | None) -> dict | None:
    if raw is None:
        return None
    require(isinstance(raw, dict) and raw.get("kind") == "local-optimality-constants",
            "invalid local theorem premise")
    require(raw.get("local_lower_bound_certified") is True
            and raw.get("all_lambda_strictly_positive") is True,
            "local theorem premise is not certified")
    delta = rational(raw.get("delta_lower"))
    M = rational(raw.get("M_inf_inverse_upper"))
    m = rational(raw.get("m_min_lambda_lower"))
    Lambda = rational(raw.get("Lambda_l1_upper"))
    B = rational(raw.get("quadratic_remainder_B"))
    terms = [rational(value) for value in raw.get("delta_terms", [])]
    lambdas = raw.get("lambda_intervals")
    row_norms = [rational(value) for value in raw.get("inverse_row_norm_upper", [])]
    require(delta > 0 and M > 0 and m > 0 and Lambda > 0 and B > 0,
            "nonpositive local theorem constant")
    require(len(terms) == 2 and len(lambdas) == 14 and len(row_norms) == 14,
            "incomplete local theorem witnesses")
    lambda_intervals = [(rational(row[0]), rational(row[1])) for row in lambdas]
    require(all(lo > 0 and lo <= hi for lo, hi in lambda_intervals),
            "local multiplier is not strictly positive")
    require(M >= max(row_norms) and m <= min(lo for lo, _ in lambda_intervals)
            and Lambda >= sum((hi for _, hi in lambda_intervals), Q(0)),
            "local scalar bounds understate their witnesses")
    require(delta <= min(terms) and delta <= 1 / (2 * M * B)
            and delta <= m / (4 * M * Lambda * B),
            "local radius exceeds the Taylor bound")
    raw_box = raw.get("root_box")
    require(isinstance(raw_box, list) and len(raw_box) == 14,
            "invalid local active-core root box")
    root = [(rational(pair[0]), rational(pair[1])) for pair in raw_box]
    require(all(lo <= hi for lo, hi in root), "empty local root interval")
    return {"root_box_reflected": reflect_root_box(root), "delta": delta}


def reflect_root_box(root: list[tuple[Q, Q]]) -> list[tuple[Q, Q]]:
    """Apply y -> -y to the 14-variable core chart; x_10 is unchanged."""
    result = []
    k = 0
    for label in CORE:
        result.append(root[k])
        k += 1
        if label != 10:
            lo, hi = root[k]
            result.append((-hi, -lo))
            k += 1
    result.append(root[-1])
    return result


@lru_cache(maxsize=100_000)
def _sin_cos_midpoint(ticks_twice: int) -> tuple[Q, Q, Q, Q]:
    """Rational sine/cosine enclosures at a half-tick angle in [0,2*pi]."""
    t = Q(ticks_twice, 2 * SCALE)
    require(0 <= t <= 2 * Q(pi_ticks()[1], SCALE), "angle outside trig enclosure")
    cos_mid = sum(((-1) ** k * t ** (2 * k) / factorial(2 * k)
                   for k in range(17)), Q(0))
    sin_mid = sum(((-1) ** k * t ** (2 * k + 1) / factorial(2 * k + 1)
                   for k in range(17)), Q(0))
    cos_error = t ** 33 / factorial(33)
    sin_error = t ** 34 / factorial(34)
    return cos_mid - cos_error, cos_mid + cos_error, sin_mid - sin_error, sin_mid + sin_error


def _trig_interval(lo_tick: int, hi_tick: int) -> tuple[tuple[Q, Q], tuple[Q, Q]]:
    require(type(lo_tick) is int and type(hi_tick) is int and lo_tick <= hi_tick,
            "invalid angle interval")
    midpoint_twice = lo_tick + hi_tick
    half_width = Q(hi_tick - lo_tick, 2 * SCALE)
    cos_lo, cos_hi, sin_lo, sin_hi = _sin_cos_midpoint(midpoint_twice)
    # |sin x - sin m|, |cos x - cos m| <= |x-m|.
    return ((max(Q(-1), cos_lo - half_width), min(Q(1), cos_hi + half_width)),
            (max(Q(-1), sin_lo - half_width), min(Q(1), sin_hi + half_width)))


def _mul_interval(a: tuple[Q, Q], b: tuple[Q, Q]) -> tuple[Q, Q]:
    products = (a[0] * b[0], a[0] * b[1], a[1] * b[0], a[1] * b[1])
    return min(products), max(products)


def _farthest_interval_distance(box: tuple[Q, Q], target: tuple[Q, Q]) -> Q:
    return max(abs(box[0] - target[1]), abs(box[1] - target[0]))


def _floyd_bounds(order: tuple, weights: tuple, skeleton: tuple) -> list[tuple[int, int]] | None:
    count = len(order)
    inf = 10 ** 30
    distance = [[inf] * count for _ in range(count)]
    for i in range(count):
        distance[i][i] = 0
    for u, v, bound in full_order_graph(order, weights, skeleton):
        distance[u][v] = min(distance[u][v], bound)
    for k in range(count):
        for i in range(count):
            if distance[i][k] == inf:
                continue
            for j in range(count):
                if distance[k][j] != inf:
                    distance[i][j] = min(distance[i][j], distance[i][k] + distance[k][j])
    if any(distance[i][i] < 0 for i in range(count)):
        return None
    anchor = order.index(10)
    _, pi_hi = pi_ticks()
    result = []
    for i in range(count):
        lo = max(0, -distance[i][anchor])
        hi = min(2 * pi_hi, distance[anchor][i])
        if lo > hi:
            return None
        result.append((lo, hi))
    return result


def order_is_local(order: tuple, weights: tuple, bounds: dict,
                    roots: dict, local: dict | None) -> bool:
    """True only if the entire core projection is inside local delta.

    Keep non-core labels in the difference-constraint graph: their pairwise
    angle bounds can tighten the projected angles of the active core.
    """
    if local is None or not set(CORE).issubset(order):
        return False
    delta = local["delta"]
    root_box = local["root_box_reflected"]
    # A local coordinate box can vary in radius by at most 2*sqrt(2)*delta.
    # Three delta is a rationally safe, inexpensive necessary prefilter.
    if any(bounds[i][1] - bounds[i][0] > 3 * delta for i in CORE):
        return False
    if bounds[2][1] - bounds[2][0] > 2 * delta:
        return False
    skeleton = tuple(i for i in order if i in (7, 8, 9, 10))
    angle_ranges = _floyd_bounds(order, weights, skeleton)
    if angle_ranges is None:
        return False
    position = {label: k for k, label in enumerate(order)}
    coord_box: list[tuple[Q, Q]] = []
    for label in CORE:
        radial = bounds[label]
        angle_lo, angle_hi = angle_ranges[position[label]]
        cosine, sine = _trig_interval(angle_lo, angle_hi)
        x_box = _mul_interval(radial, cosine)
        y_box = (Q(0), Q(0)) if label == 10 else _mul_interval(radial, sine)
        coord_box.append(x_box)
        if label != 10:
            coord_box.append(y_box)
    for candidate, target in zip(coord_box, root_box[:-1]):
        if _farthest_interval_distance(candidate, target) > delta:
            return False
    # Each disk gives R >= |p_i|+r_i; the outer cap gives R<=U.
    radius_lower = max(bounds[i][0] + roots[i][0] for i in bounds)
    radius_box = (radius_lower, Q("8.303468122111490"))
    if _farthest_interval_distance(radius_box, root_box[-1]) > delta:
        return False
    return True
