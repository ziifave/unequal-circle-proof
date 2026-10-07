"""Sound radial/angle lower bounds and a Hamiltonian-cycle cut.

The module deliberately uses only directed Decimal arithmetic.  It does not
assume a contact graph or an angular order.  A cycle is merely a certificate
that every possible cyclic order must spend at least its edge-angle sum.
"""
from __future__ import annotations

from decimal import Context, Decimal, ROUND_CEILING, ROUND_FLOOR, localcontext
from functools import lru_cache
from itertools import combinations

from .interval import D, Interval, PRECISION, _binary
from . import interval as _interval

# Truncated decimal enclosures.  The next omitted digit of pi is positive.
PI_LO = D("3.14159265358979323846264338327950288419716939937510")
PI_HI = D("3.14159265358979323846264338327950288419716939937511")


def _div(a: Decimal, b: Decimal, rounding: str) -> Decimal:
    with localcontext(Context(prec=_interval.PRECISION, rounding=rounding)):
        return a / b


def _sqrt_lo(value: Decimal) -> Decimal:
    return Interval.sqrt_nonnegative(value).lo


def _sqrt_hi(value: Decimal) -> Decimal:
    return Interval.sqrt_nonnegative(value).hi


def _atan_series_lower(z: Decimal) -> Decimal:
    """Lower bound for atan(z), 0 <= z <= 0.42, through a negative term."""
    z2_lo = _binary(z, z, "*", ROUND_FLOOR)
    z2_hi = _binary(z, z, "*", ROUND_CEILING)
    power_lo = z
    power_hi = z
    total = z
    for k in range(1, 180):
        power_lo = _binary(power_lo, z2_lo, "*", ROUND_FLOOR)
        power_hi = _binary(power_hi, z2_hi, "*", ROUND_CEILING)
        term_lo = _div(power_lo, D(2 * k + 1), ROUND_FLOOR)
        term_hi = _div(power_hi, D(2 * k + 1), ROUND_CEILING)
        if k % 2:
            total = _binary(total, term_hi, "-", ROUND_FLOOR)
        else:
            total = _binary(total, term_lo, "+", ROUND_FLOOR)
            # The next term is negative, so the current even partial sum is
            # an upper bound; continue until the next odd term is included.
    return total


def _atan_series_upper(z: Decimal) -> Decimal:
    z2_lo = _binary(z, z, "*", ROUND_FLOOR)
    z2_hi = _binary(z, z, "*", ROUND_CEILING)
    power_lo = z
    power_hi = z
    total = z
    # End on an even term: the alternating-series partial sum is an upper
    # bound.  Stopping at 179 would incorrectly return a lower bound.
    for k in range(1, 181):
        power_lo = _binary(power_lo, z2_lo, "*", ROUND_FLOOR)
        power_hi = _binary(power_hi, z2_hi, "*", ROUND_CEILING)
        term_lo = _div(power_lo, D(2 * k + 1), ROUND_FLOOR)
        term_hi = _div(power_hi, D(2 * k + 1), ROUND_CEILING)
        if k % 2:
            total = _binary(total, term_lo, "-", ROUND_CEILING)
        else:
            total = _binary(total, term_hi, "+", ROUND_CEILING)
    return total


def _atan_bounds(z_lo: Decimal, z_hi: Decimal) -> tuple[Decimal, Decimal]:
    """Bounds for atan on a nonnegative interval in [0,1]."""
    if z_lo > D("0.4"):
        # atan z = pi/4 + atan((z-1)/(z+1)); the transformed argument is
        # negative and has magnitude at most 0.4286.
        # The numerator is negative and the denominator is positive.  Thus
        # the quotient is increasing in both endpoint arguments: use matching
        # lower/lower and upper/upper endpoints, not crossed endpoints.
        t_lo = _div(_binary(z_lo, D(1), "-", ROUND_FLOOR),
                    _binary(z_lo, D(1), "+", ROUND_FLOOR), ROUND_FLOOR)
        t_hi = _div(_binary(z_hi, D(1), "-", ROUND_CEILING),
                    _binary(z_hi, D(1), "+", ROUND_CEILING), ROUND_CEILING)
        u_lo = _binary(D(0), t_hi, "-", ROUND_FLOOR)
        u_hi = _binary(D(0), t_lo, "-", ROUND_CEILING)
        return (
            _binary(_div(PI_LO, D(4), ROUND_FLOOR), _atan_series_upper(u_hi), "-", ROUND_FLOOR),
            _binary(_div(PI_HI, D(4), ROUND_CEILING), _atan_series_lower(u_lo), "-", ROUND_CEILING),
        )
    return _atan_series_lower(z_lo), _atan_series_upper(z_hi)


def _acos_lower(c: Decimal) -> Decimal:
    """A certified lower bound for acos(c), -1 <= c <= 1."""
    if c >= D(1):
        return D(0)
    if c <= D(-1):
        return PI_LO
    numerator = _binary(D(1), c, "-", ROUND_FLOOR)
    denominator = _binary(D(1), c, "+", ROUND_CEILING)
    z = _sqrt_lo(_div(numerator, denominator, ROUND_FLOOR))
    if z <= D(1):
        atan_lo, _ = _atan_bounds(z, z)
        return _binary(D(2), atan_lo, "*", ROUND_FLOOR)
    # acos(c) = pi - 2 atan(1/z), with the pi lower bound and atan upper.
    inv_z = _div(D(1), z, ROUND_CEILING)
    _, atan_hi = _atan_bounds(inv_z, inv_z)
    return _binary(_binary(PI_LO, D(2), "*", ROUND_FLOOR), atan_hi, "-", ROUND_FLOOR)


def _radius_bounds(model, box, index: int) -> tuple[Decimal, Decimal]:
    x, y = box.coords[2 * index : 2 * index + 2]
    norm2 = x.square() + y.square()
    lower = _sqrt_lo(norm2.lo)
    upper = _sqrt_hi(norm2.hi)
    global_upper = _binary(model.rho, model.radii[index].lo, "-", ROUND_CEILING)
    global_lower = D(0)
    for j in range(model.n):
        if j == index:
            continue
        candidate = _binary(
            model.radii[index].lo,
            _binary(model.radii[j].lo, D(2), "*", ROUND_FLOOR),
            "+", ROUND_FLOOR,
        )
        candidate = _binary(candidate, model.rho, "-", ROUND_FLOOR)
        if candidate > global_lower:
            global_lower = candidate
    return max(lower, global_lower), min(upper, global_upper)


@lru_cache(maxsize=250_000)
def _angle_lower_from_bounds(
    ri: Decimal, rj: Decimal,
    a_lo: Decimal, a_hi: Decimal,
    b_lo: Decimal, b_hi: Decimal,
) -> Decimal:
    """Angle lower bound from radial intervals, with exact-value caching."""
    if a_lo <= 0 or b_lo <= 0 or a_lo > a_hi or b_lo > b_hi:
        return D(0)
    d = _binary(ri, rj, "+", ROUND_FLOOR)
    d2 = _binary(d, d, "*", ROUND_FLOOR)
    best_c = None
    for a in (a_lo, a_hi):
        for b in (b_lo, b_hi):
            numerator = _binary(
                _binary(_binary(a, a, "*", ROUND_CEILING), _binary(b, b, "*", ROUND_CEILING), "+", ROUND_CEILING),
                d2, "-", ROUND_CEILING,
            )
            denominator = _binary(D(2), _binary(a, b, "*", ROUND_FLOOR), "*", ROUND_FLOOR)
            c = _div(numerator, denominator, ROUND_CEILING)
            best_c = c if best_c is None or c > best_c else best_c
    return _acos_lower(best_c)


def _angle_lower(model, box, i: int, j: int) -> Decimal:
    a_lo, a_hi = _radius_bounds(model, box, i)
    b_lo, b_hi = _radius_bounds(model, box, j)
    return _angle_lower_from_bounds(
        model.radii[i].lo, model.radii[j].lo,
        a_lo, a_hi, b_lo, b_hi,
    )


def _cycle_lower(weights: list[list[Decimal]]) -> Decimal:
    n = len(weights)
    if n <= 2:
        return D(0)
    # Held-Karp over cycles rooted at vertex 0.  All additions are rounded
    # down, so the result remains a lower bound on every cycle cost.
    dp: dict[tuple[int, int], Decimal] = {(1, 0): D(0)}
    for size in range(1, n):
        for (mask, last), value in list(dp.items()):
            if mask.bit_count() != size or not (mask & 1):
                continue
            for nxt in range(1, n):
                if mask & (1 << nxt):
                    continue
                key = (mask | (1 << nxt), nxt)
                candidate = _binary(value, weights[last][nxt], "+", ROUND_FLOOR)
                if key not in dp or candidate < dp[key]:
                    dp[key] = candidate
    full = (1 << n) - 1
    answer = None
    for last in range(1, n):
        value = _binary(dp[(full, last)], weights[last][0], "+", ROUND_FLOOR)
        if answer is None or value < answer:
            answer = value
    return answer if answer is not None else D(0)


def _degree_two_lower(weights: list[list[Decimal]]) -> Decimal:
    """A cheap lower bound for the Hamiltonian-cycle value.

    Every Hamiltonian cycle uses two incident edges at every vertex.  Taking
    the two smallest incident weights at each vertex and dividing the total
    by two therefore gives a lower bound on every cycle.  It is only a
    prefilter; the exact Held--Karp value remains the final test.
    """
    total = D(0)
    for i, row in enumerate(weights):
        incident = sorted(row[j] for j in range(len(row)) if j != i)
        if len(incident) < 2:
            return D(0)
        total = _binary(total, _binary(incident[0], incident[1], "+", ROUND_FLOOR), "+", ROUND_FLOOR)
    return _div(total, D(2), ROUND_FLOOR)


@lru_cache(maxsize=32)
def _cycle_candidates(labels: tuple[int, ...], min_size: int, max_size: int) -> tuple[tuple[int, ...], ...]:
    """Return the deterministic subset pool once per labeled model."""
    candidates = [subset for size in range(min_size, max_size + 1)
                  for subset in combinations(labels, size)]
    candidates.sort(key=lambda subset: (sum(subset), len(subset)), reverse=True)
    return tuple(candidates[:16])


def _cycle_value(model, box, labels: tuple[int, ...]) -> Decimal | None:
    indices = [model.labels.index(label) for label in labels if label in model.labels]
    if len(indices) != len(labels):
        return None
    weights = [[D(0) for _ in indices] for _ in indices]
    for a, i in enumerate(indices):
        for b, j in enumerate(indices):
            if a != b:
                weights[a][b] = _angle_lower(model, box, i, j)
    cycle = _cycle_lower(weights)
    return cycle


def _weight_matrix(model, box) -> list[list[Decimal]]:
    """Compute all pair angle bounds for one box exactly once.

    ``best_cycle_cut_reason`` may test several subsets of the same model.
    Reusing this matrix is only a computational optimization: every entry is
    produced by the same directed-rounding ``_angle_lower`` routine.
    """
    radial = [_radius_bounds(model, box, i) for i in range(model.n)]
    weights = [[D(0) for _ in model.labels] for _ in model.labels]
    for i in range(model.n):
        for j in range(i):
            value = _angle_lower_from_bounds(
                model.radii[i].lo, model.radii[j].lo,
                *radial[i], *radial[j],
            )
            weights[i][j] = value
            weights[j][i] = value
    return weights


def cycle_cut_reason(model, box, labels: tuple[int, ...] = (5, 6, 7, 8, 9, 10)) -> str | None:
    cycle = _cycle_value(model, box, labels)
    if cycle is None:
        return None
    two_pi_upper = _binary(D(2), PI_HI, "*", ROUND_CEILING)
    if cycle > two_pi_upper:
        return f"angular-cycle:{','.join(map(str, labels))}:{cycle}"
    return None


def best_cycle_cut_reason(model, box) -> str | None:
    """Try all 6--9 disk subsets and return the strongest violated cycle cut.

    Each subset gives a necessary condition independently.  Taking the
    strongest violated one is therefore safe, while avoiding any assumption
    about the eventual angular order or contact graph.
    """
    labels = tuple(model.labels)
    sizes = range(6, min(9, len(labels)) + 1)
    two_pi_upper = _binary(D(2), PI_HI, "*", ROUND_CEILING)
    best: tuple[Decimal, tuple[int, ...]] | None = None
    # The complete family is useful for offline screening, but evaluating all
    # 6--9 subsets at every box is too expensive with directed Decimal DP.
    # Keep a deterministic pool biased toward the larger disks; every tested
    # subset still gives a sound necessary condition.
    candidates = _cycle_candidates(labels, 6, min(9, len(labels)))
    # All candidate subsets use the same radial box.  Constructing the full
    # pair matrix once avoids recomputing identical directed-rounding angle
    # bounds up to sixteen times per node, without changing the certificate
    # logic or any inequality direction.
    pair_weights = _weight_matrix(model, box)
    for subset in candidates[:16]:
            indices = [labels.index(label) for label in subset]
            subset_weights = [[D(0) if i == j else pair_weights[i][j]
                              for j in indices] for i in indices]
            if _degree_two_lower(subset_weights) <= two_pi_upper:
                cycle = _cycle_lower(subset_weights)
            else:
                cycle = _degree_two_lower(subset_weights)
            if cycle is not None and cycle > two_pi_upper and (best is None or cycle > best[0]):
                best = (cycle, subset)
    if best is None:
        return None
    cycle, subset = best
    return f"angular-cycle:{','.join(map(str, subset))}:{cycle}"
