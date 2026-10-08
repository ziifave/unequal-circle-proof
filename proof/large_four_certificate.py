"""Exact-rational replay of the four-large-disk semicircle lemma.

This verifier uses only the Python standard library. It imports neither the
search engine nor its Decimal, interval, or trigonometric implementations.
The analytic implications checked numerically here are documented in
LARGE_FOUR_SKELETON_STATUS.md. This is not a complete packing-tree verifier.
"""
from __future__ import annotations

import argparse
from fractions import Fraction as Q
import hashlib
from itertools import combinations, permutations, product
import json
from math import factorial
from pathlib import Path


LABELS = (7, 8, 9, 10)
RADIUS_UPPER = Q("8.303468122111490")
SCHEMA = "large-four-semicircle-rational-v1"


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def rational(value: object) -> Q:
    """Accept exact textual fractions/decimals only, never JSON floats."""
    require(isinstance(value, str), "rational values must be strings")
    try:
        return Q(value)
    except (ValueError, ZeroDivisionError) as exc:
        raise ValueError("invalid rational value") from exc


def atan_partial(x: Q, last: int) -> Q:
    return sum(((-1) ** k * x ** (2 * k + 1) / (2 * k + 1)
                for k in range(last + 1)), Q(0))


def pi_bounds() -> tuple[Q, Q]:
    """Machin's identity and exact alternating partial sums.

    For 0<x<1, S_9(x)<atan(x)<S_8(x). Therefore
    16*S_9(1/5)-4*S_8(1/239) < pi <
    16*S_8(1/5)-4*S_9(1/239).
    """
    x, y = Q(1, 5), Q(1, 239)
    return (16 * atan_partial(x, 9) - 4 * atan_partial(y, 8),
            16 * atan_partial(x, 8) - 4 * atan_partial(y, 9))


def cosine_lower(x: Q) -> Q:
    """Degree-14 alternating cosine partial sum, bounded below exactly."""
    require(0 <= x <= Q(13, 10), "angle outside cosine-series domain")
    # Terms decrease in magnitude since x^2/2 <= 169/200 < 1.
    # Ending with the negative k=7 term gives a lower bound on cos(x).
    return sum(((-1) ** k * x ** (2 * k) / factorial(2 * k)
                for k in range(8)), Q(0))


def canonical_cycles() -> list[tuple[int, ...]]:
    """All cyclic orders modulo rotation and reflection, rooted at disk 10."""
    return sorted({min((10,) + tail, (10,) + tail[::-1])
                   for tail in permutations((7, 8, 9))})


def verify_certificate(data: dict) -> dict:
    require(data.get("schema") == SCHEMA, "unsupported certificate schema")
    require(data.get("labels") == list(LABELS), "wrong disk labels")
    radius = rational(data.get("container_radius_upper"))
    require(radius == RADIUS_UPPER, "wrong container-radius scope")
    pi_lo, machin_hi = pi_bounds()
    pi_hi = rational(data.get("pi_upper"))
    require(machin_hi <= pi_hi, "claimed pi upper bound is not justified")

    # The roots are untrusted witnesses, checked by exact integer/rational
    # squaring rather than the generator's integer-square-root algorithm.
    roots: dict[int, tuple[Q, Q]] = {}
    for row in data.get("sqrt_enclosures", []):
        label = row.get("label")
        require(type(label) is int and label in LABELS and label not in roots,
                "invalid or duplicate square-root label")
        lo, hi = rational(row.get("lo")), rational(row.get("hi"))
        require(0 < lo <= hi and lo * lo <= label <= hi * hi,
                f"invalid square-root enclosure for {label}")
        roots[label] = lo, hi
    require(set(roots) == set(LABELS), "missing square-root enclosure")

    radial = {}
    for i in LABELS:
        lo = max(Q(0), max(roots[i][0] + 2 * roots[j][0] - radius
                          for j in LABELS if i != j))
        hi = radius - roots[i][0]
        require(0 < lo <= hi, f"unsupported radial interval for {i}")
        radial[i] = lo, hi

    expected_pairs = set(combinations(LABELS, 2))
    angles: dict[tuple[int, int], Q] = {}
    pair_checks = []
    for row in data.get("angle_lower_bounds", []):
        raw_pair = row.get("pair", [])
        require(isinstance(raw_pair, list) and len(raw_pair) == 2
                and all(type(i) is int for i in raw_pair), "invalid pair")
        pair = tuple(raw_pair)
        require(pair in expected_pairs and pair not in angles,
                "invalid or duplicate angle pair")
        i, j = pair
        theta = rational(row.get("lower"))
        require(0 < theta <= Q(13, 10) and theta < pi_lo,
                "angle must be positive and in the supported domain")
        distance_lo = roots[i][0] + roots[j][0]
        # The maximum of (a^2+b^2-d^2)/(2ab) on a positive rectangle
        # occurs at a corner: each one-variable section is either increasing
        # or decreases then increases, with no interior maximum.
        corners = [(a * a + b * b - distance_lo * distance_lo) / (2 * a * b)
                   for a, b in product(radial[i], radial[j])]
        cosine_hi = max(corners)
        taylor_lo = cosine_lower(theta)
        require(cosine_hi <= taylor_lo, f"overstated angle lower bound for {pair}")
        angles[pair] = theta
        pair_checks.append({"pair": list(pair), "angle_lower": str(theta),
                            "cosine_upper": str(cosine_hi),
                            "cosine_taylor_lower": str(taylor_lo),
                            "cosine_margin": str(taylor_lo - cosine_hi)})
    require(set(angles) == expected_pairs, "missing pairwise angle bound")

    expected_orders = set(permutations(LABELS))
    seen_orders = set()
    path_checks = []
    for raw in data.get("orders", []):
        require(isinstance(raw, list) and len(raw) == 4
                and all(type(i) is int for i in raw), "invalid path order")
        order = tuple(raw)
        require(order in expected_orders and order not in seen_orders,
                "invalid or duplicate path order")
        seen_orders.add(order)
        total = sum((angles[tuple(sorted((a, b)))]
                     for a, b in zip(order, order[1:])), Q(0))
        require(total > pi_hi, f"path does not exclude a semicircle: {order}")
        path_checks.append({"order": list(order), "angle_sum_lower": str(total),
                            "margin_over_pi_upper": str(total - pi_hi)})
    require(seen_orders == expected_orders, "missing path order")
    representatives = [list(order) for order in canonical_cycles()]
    require(data.get("cyclic_representatives") == representatives,
            "cyclic representatives do not cover the reflection classes")
    minimum = min(rational(row["angle_sum_lower"]) for row in path_checks)
    return {
        "status": "VERIFIED_FOUR_DISK_SEMICIRCLE_LEMMA",
        "container_radius_upper": str(radius), "labels": list(LABELS),
        "arithmetic": "exact fractions; no floating-point or Decimal operations",
        "radial_intervals": {str(i): [str(x) for x in radial[i]] for i in LABELS},
        "pi_upper": str(pi_hi), "machin_pi_upper": str(machin_hi),
        "pair_checks": pair_checks, "path_checks": path_checks,
        "orders_verified": len(path_checks),
        "minimum_path_lower": str(minimum),
        "minimum_margin": str(minimum - pi_hi),
        "consecutive_gap_upper": str(2 * pi_hi - minimum),
        "cyclic_representatives": representatives,
        "coarse_sector_assignment_count": len(representatives) * 4 ** 6,
        "global_optimality_proved": False,
    }


def halfplane_witness(coords: list) -> dict | None:
    """Find an axis half-plane containing every represented large centre.

    This is a box predicate only. Its use as an exclusion requires a verified
    lemma with matching radius/labels, as enforced by verify_frontier below.
    Closed half-planes include their boundary; touching zero is intentional.
    """
    require(isinstance(coords, list) and len(coords) == 20, "expected 20 coordinates")
    intervals = []
    for raw in coords:
        require(isinstance(raw, list) and len(raw) == 2, "invalid coordinate interval")
        lo, hi = map(rational, raw)
        require(lo <= hi, "empty coordinate interval")
        intervals.append((lo, hi))
    for normal in ((1, 0), (-1, 0), (0, 1), (0, -1)):
        lower = {}
        for label in LABELS:
            value = Q(0)
            for axis, coefficient in enumerate(normal):
                lo, hi = intervals[2 * (label - 1) + axis]
                value += coefficient * (lo if coefficient >= 0 else hi)
            lower[label] = value
        if all(value >= 0 for value in lower.values()):
            return {"normal": list(normal),
                    "projection_lower_bounds": {str(i): str(x) for i, x in lower.items()}}
    return None


def verify_frontier(data: dict, certificate: dict) -> dict:
    lemma = verify_certificate(certificate)
    require(data.get("n") == 10 and data.get("radii_squared") == list(range(1, 11)),
            "frontier disk model does not match the lemma")
    rho = rational(data.get("rho"))
    require(0 < rho <= rational(lemma["container_radius_upper"]),
            "frontier radius is outside the lemma scope")
    boxes = data.get("queued_boxes")
    require(isinstance(boxes, list), "missing frontier boxes")
    paths = []
    matches = []
    for index, box in enumerate(boxes):
        node = box.get("node")
        require(isinstance(node, str) and set(node) <= {"0", "1"}, "invalid node path")
        paths.append(node)
        witness = halfplane_witness(box.get("coords"))
        if witness is not None:
            matches.append({"index": index, "node": node, **witness})
    ordered = sorted(paths)
    require(all(not right.startswith(left) for left, right in zip(ordered, ordered[1:])),
            "frontier contains duplicate or ancestor node paths")
    return {"status": "BOX_LEMMAS_VERIFIED_TREE_NOT_REPLAYED",
            "frontier_boxes": len(boxes), "matched_boxes": len(matches),
            "unmatched_boxes": len(boxes) - len(matches), "matches": matches,
            "initial_domain_coverage_verified": False}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("certificate", type=Path)
    parser.add_argument("--frontier", type=Path)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    source = args.certificate.read_bytes()
    data = json.loads(source)
    result = verify_certificate(data)
    result["certificate_sha256"] = hashlib.sha256(source).hexdigest()
    result["verifier_sha256"] = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    if args.frontier:
        frontier_source = args.frontier.read_bytes()
        result["frontier"] = verify_frontier(json.loads(frontier_source), data)
        result["frontier"]["sha256"] = hashlib.sha256(frontier_source).hexdigest()
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    summary = {key: result[key] for key in (
        "status", "orders_verified", "minimum_path_lower", "minimum_margin",
        "coarse_sector_assignment_count", "global_optimality_proved")}
    if "frontier" in result:
        summary["frontier"] = {key: result["frontier"][key] for key in (
            "status", "frontier_boxes", "matched_boxes", "unmatched_boxes")}
    print(json.dumps(summary, indent=2))


if __name__ == "__main__":
    main()
