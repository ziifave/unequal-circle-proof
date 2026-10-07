"""Interval Krawczyk verification for the active seven-disk core.

The core is a local-structure certificate only.  It deliberately makes no
claim about other contact graphs or global optimality.
"""
from __future__ import annotations

from fractions import Fraction
from typing import Sequence

from .interval import D, Interval
from .contact_graph import CORE_CONTACT_GRAPH


CORE = CORE_CONTACT_GRAPH.disks
WALLS = CORE_CONTACT_GRAPH.wall_contacts
PAIRS = CORE_CONTACT_GRAPH.pair_contacts


def vector_from_centres(raw: dict[str, list[str]], radius: str) -> list[Interval]:
    result: list[Interval] = []
    for disk in CORE:
        result.append(Interval.point(raw[str(disk)][0]))
        if disk != 10:
            result.append(Interval.point(raw[str(disk)][1]))
    result.append(Interval.point(radius))
    return result


def _unpack(z: Sequence[Interval]) -> tuple[dict[int, tuple[Interval, Interval]], Interval]:
    coords: dict[int, tuple[Interval, Interval]] = {}
    k = 0
    for disk in CORE:
        x = z[k]
        k += 1
        if disk == 10:
            coords[disk] = (x, Interval.point(0))
        else:
            coords[disk] = (x, z[k])
            k += 1
    return coords, z[k]


def _zero_row() -> list[Interval]:
    return [Interval.point(0) for _ in range(14)]


def _position(disk: int) -> tuple[int, int | None]:
    k = 0
    for current in CORE:
        x = k
        k += 1
        if current == disk:
            return x, None if disk == 10 else k
        if current != 10:
            k += 1
    raise KeyError(disk)


def functions_and_jacobian(z: Sequence[Interval]) -> tuple[list[Interval], list[list[Interval]]]:
    coords, radius = _unpack(z)
    radii = {disk: Interval.sqrt_integer(disk) for disk in CORE}
    two = Interval.point(2)
    f: list[Interval] = []
    jac: list[list[Interval]] = []
    for disk in WALLS:
        x, y = coords[disk]
        f.append(x.square() + y.square() - (radius - radii[disk]).square())
        row = _zero_row()
        xcol, ycol = _position(disk)
        row[xcol] = two * x
        assert ycol is not None
        row[ycol] = two * y
        row[-1] = Interval.point(-2) * (radius - radii[disk])
        jac.append(row)
    for i, j in PAIRS:
        xi, yi = coords[i]
        xj, yj = coords[j]
        dx, dy = xi - xj, yi - yj
        f.append(dx.square() + dy.square() - (radii[i] + radii[j]).square())
        row = _zero_row()
        ix, iy = _position(i)
        jx, jy = _position(j)
        row[ix] = two * dx
        row[jx] = Interval.point(-2) * dx
        if iy is not None:
            row[iy] = two * dy
        # y_10 is fixed to zero by the rotation symmetry and is not a
        # variable in this reduced system.
        if jy is not None:
            row[jy] = Interval.point(-2) * dy
        jac.append(row)
    return f, jac


def _sum(values: Sequence[Interval]) -> Interval:
    answer = Interval.point(0)
    for value in values:
        answer = answer + value
    return answer


def _mat_vec(a: Sequence[Sequence[Interval]], x: Sequence[Interval]) -> list[Interval]:
    return [_sum([entry * value for entry, value in zip(row, x)]) for row in a]


def _mat_mul(a: Sequence[Sequence[Interval]], b: Sequence[Sequence[Interval]]) -> list[list[Interval]]:
    return [[_sum([a[i][k] * b[k][j] for k in range(len(b))]) for j in range(len(b[0]))] for i in range(len(a))]


def _point_matrix_is_nonsingular(a: Sequence[Sequence[Interval]]) -> bool:
    """Exact rational Gaussian elimination of the finite-decimal preconditioner."""
    m = [[Fraction(str(entry.lo)) for entry in row] for row in a]
    for col in range(len(m)):
        pivot = next((row for row in range(col, len(m)) if m[row][col] != 0), None)
        if pivot is None:
            return False
        m[col], m[pivot] = m[pivot], m[col]
        p = m[col][col]
        for row in range(col + 1, len(m)):
            factor = m[row][col] / p
            for j in range(col, len(m)):
                m[row][j] -= factor * m[col][j]
    return True


def krawczyk(center: Sequence[Interval], box: Sequence[Interval], preconditioner: Sequence[Sequence[Interval]]) -> tuple[list[Interval], bool]:
    """Return K(x0,X) and whether its strict inclusion proves one root in X."""
    f0, _ = functions_and_jacobian(center)
    _, jacobian_box = functions_and_jacobian(box)
    cf = _mat_vec(preconditioner, f0)
    term = [x - y for x, y in zip(center, cf)]
    cj = _mat_mul(preconditioner, jacobian_box)
    identity_minus_cj = [
        [((Interval.point(1) if i == j else Interval.point(0)) - cj[i][j]) for j in range(14)]
        for i in range(14)
    ]
    delta = [x - c for x, c in zip(box, center)]
    result = [base + correction for base, correction in zip(term, _mat_vec(identity_minus_cj, delta))]
    strict = all(k.lo > x.lo and k.hi < x.hi for k, x in zip(result, box))
    return result, strict and _point_matrix_is_nonsingular(preconditioner)
