"""Rigorous necessary-condition contractors for a fixed container radius."""
from __future__ import annotations

from dataclasses import dataclass
from decimal import Context, Decimal, ROUND_CEILING, ROUND_FLOOR, localcontext
from typing import Sequence

from .interval import D, Interval, PRECISION, _binary
from .angular import best_cycle_cut_reason


def _directed_divide(a: Decimal, b: Decimal, rounding: str) -> Decimal:
    with localcontext(Context(prec=PRECISION, rounding=rounding)):
        return a / b


@dataclass(frozen=True, slots=True)
class Box:
    """Coordinates [x1, y1, x2, y2, ...] in a closed Cartesian box."""

    coords: tuple[Interval, ...]
    # Branch-local linear facts of the form coordinate[left]-coordinate[right]
    # >= threshold.  Unlike endpoint clipping, retaining these facts preserves
    # correlations introduced by a non-overlap sign case.
    orders: tuple["Difference", ...] = ()
    # Optional angular sign facts around the anchor disk.  A fact means
    # cross(c_left-c_anchor, c_right-c_anchor) >= 0 when positive, and <= 0
    # otherwise.  This is a branch-local order case, never an assumed contact
    # graph or a fixed geometric property of the instance.
    angles: tuple["AngularOrder", ...] = ()
    directions: tuple["DirectionFact", ...] = ()

    def split(self, dim: int) -> tuple["Box", "Box"]:
        left, right = self.coords[dim].split()
        a = list(self.coords)
        b = list(self.coords)
        a[dim] = left
        b[dim] = right
        return Box(tuple(a), self.orders, self.angles, self.directions), Box(tuple(b), self.orders, self.angles, self.directions)

    def replace(self, dim: int, value: Interval) -> "Box":
        coords = list(self.coords)
        coords[dim] = value
        return Box(tuple(coords), self.orders, self.angles, self.directions)

    def to_json(self) -> list[list[str]]:
        return [coord.to_json() for coord in self.coords]

    def with_order(self, left: int, right: int, threshold: Decimal) -> "Box":
        orders = list(self.orders)
        for k, order in enumerate(orders):
            if order.left == left and order.right == right:
                if threshold > order.threshold:
                    orders[k] = Difference(left, right, threshold)
                return Box(self.coords, tuple(orders), self.angles, self.directions)
        orders.append(Difference(left, right, threshold))
        return Box(self.coords, tuple(orders), self.angles, self.directions)

    def with_angle(self, anchor: int, left: int, right: int, positive: bool) -> "Box":
        facts = list(self.angles)
        for fact in facts:
            if (fact.anchor, fact.left, fact.right) == (anchor, left, right):
                if fact.positive != positive:
                    raise ValueError("conflicting angular branch")
                return self
        facts.append(AngularOrder(anchor, left, right, positive))
        return Box(self.coords, self.orders, tuple(facts), self.directions)

    def with_direction(self, fact: "DirectionFact") -> "Box":
        facts = list(self.directions)
        if fact not in facts:
            facts.append(fact)
        return Box(self.coords, self.orders, self.angles, tuple(facts))


@dataclass(frozen=True, slots=True)
class Difference:
    left: int
    right: int
    threshold: Decimal


@dataclass(frozen=True, slots=True)
class AngularOrder:
    anchor: int
    left: int
    right: int
    positive: bool


@dataclass(frozen=True, slots=True)
class DirectionFact:
    i: int
    j: int
    ux: Decimal
    uy: Decimal
    threshold: Decimal


@dataclass(frozen=True, slots=True)
class Separation:
    """A sound two-case consequence of one disk-pair constraint."""

    i: int
    j: int
    axis: int  # 0=x, 1=y
    threshold: Decimal
    positive: Box  # c_i[axis] - c_j[axis] >= threshold
    negative: Box  # c_j[axis] - c_i[axis] >= threshold


@dataclass(frozen=True, slots=True)
class AngularSeparation:
    anchor: int
    left: int
    right: int
    positive: Box
    negative: Box


class PackingModel:
    """All discard tests are necessary conditions, so discarding is sound."""

    def __init__(
        self,
        n: int,
        rho: str | Decimal,
        radius_squares: Sequence[int] | None = None,
        *,
        order_propagation: bool = False,
        split_mode: str = "width",
        angular_order: bool = False,
        angular_cycle: bool = False,
        directional: bool = False,
        hc4: bool = False,
    ):
        if not 1 <= n <= 10:
            raise ValueError("this prototype accepts 1 <= n <= 10")
        if radius_squares is None:
            radius_squares = tuple(range(1, n + 1))
        if len(radius_squares) != n or any(value <= 0 for value in radius_squares):
            raise ValueError("radius_squares must contain n positive integers")
        self.n = n
        self.labels = tuple(radius_squares)
        self.rho = D(rho)
        self.order_propagation = order_propagation
        self.angular_order = angular_order
        self.angular_cycle = angular_cycle
        self.directional = directional
        self.hc4 = hc4
        if split_mode not in {"width", "radius-weighted", "radius-balanced"}:
            raise ValueError("unknown split_mode")
        self.split_mode = split_mode
        self.radii = tuple(Interval.sqrt_integer(i) for i in self.labels)

    def root_box(self) -> Box:
        coords: list[Interval] = []
        for radius in self.radii:
            # rho - radius.lo is an outward upper bound for every feasible
            # coordinate magnitude, because the actual radius is >= radius.lo.
            extent = _binary(self.rho, radius.lo, "-", ROUND_CEILING)
            if extent < 0:
                extent = D(0)
            coords.extend((Interval(-extent, extent), Interval(-extent, extent)))

        # Rotation: place c_n on the nonnegative x-axis.  Reflection: choose
        # c_(n-1) in the upper half-plane.  Both transformations preserve every
        # feasible packing, including degenerate on-axis cases.
        if self.n >= 2:
            last = 2 * (self.n - 1)
            coords[last] = Interval(D(0), coords[last].hi)
            coords[last + 1] = Interval.point(0)
            prev_y = 2 * (self.n - 2) + 1
            coords[prev_y] = Interval(D(0), coords[prev_y].hi)
        return Box(tuple(coords))

    def analytic_discard(self) -> str | None:
        # Areas are i*pi and the container has rho^2*pi.
        with __import__("decimal").localcontext(__import__("decimal").Context(prec=100, rounding=ROUND_CEILING)):
            if self.rho * self.rho < D(sum(self.labels)):
                return "area"
        # Any two contained disks i,j require R >= r_i + r_j.
        for i in range(self.n):
            for j in range(i):
                # This is a lower bound on the true sum of radii, so its
                # addition must itself be rounded downward.  Using Decimal's
                # ambient (usually round-to-nearest) context here could make
                # a general-purpose proof engine reject a radius just above
                # the true pair bound.  The current core certificate never
                # uses this shortcut, but the primitive must be sound on its
                # own.
                pair_lower = _binary(self.radii[i].lo, self.radii[j].lo, "+", ROUND_FLOOR)
                if self.rho < pair_lower:
                    return f"pair-radius:{self.labels[j]}-{self.labels[i]}"
        return None

    def discard_reason(self, box: Box) -> str | None:
        immediate = self.analytic_discard()
        if immediate:
            return immediate

        if self.angular_order:
            angular_reason = self._angular_discard(box)
            if angular_reason is not None:
                return angular_reason
        if self.angular_cycle:
            cycle_reason = best_cycle_cut_reason(self, box)
            if cycle_reason is not None:
                return cycle_reason

        radial_reason = self._radial_lower_discard(box)
        if radial_reason is not None:
            return radial_reason

        # A feasible centre must lie in its containment disk.  If the minimum
        # possible squared norm in the box already exceeds the maximum possible
        # (rho-r_i)^2, no point in the box can be feasible.
        for i, radius in enumerate(self.radii):
            x, y = box.coords[2 * i : 2 * i + 2]
            norm2 = x.square() + y.square()
            allowance = Interval.point(self.rho) - Interval(radius.lo, radius.lo)
            if norm2.lo > allowance.square().hi:
                return f"containment:{self.labels[i]}"

        # If even the maximum possible separation in this box is too small,
        # the pair overlaps throughout the box.
        for i in range(self.n):
            xi, yi = box.coords[2 * i : 2 * i + 2]
            for j in range(i):
                xj, yj = box.coords[2 * j : 2 * j + 2]
                distance2 = (xi - xj).square() + (yi - yj).square()
                required = self.radii[i] + self.radii[j]
                if distance2.hi < required.square().lo:
                    return f"overlap:{self.labels[j]}-{self.labels[i]}"
        return None

    def prepare(self, box: Box) -> tuple[Box | None, str | None]:
        """Apply safe containment contraction until stable, then test discard."""
        current = box
        for _ in range(30 if self.order_propagation else 12):
            if self.order_propagation:
                propagated, reason = self._propagate_orders(current)
                if reason is not None:
                    return None, reason
                assert propagated is not None
                current = propagated
            coords = list(current.coords)
            changed = False
            for i, radius in enumerate(self.radii):
                x_index, y_index = 2 * i, 2 * i + 1
                x, y = coords[x_index], coords[y_index]
                allowance = Interval.point(self.rho) - Interval(radius.lo, radius.lo)
                allowance2 = allowance.square().hi
                for own_index, other in ((x_index, y), (y_index, x)):
                    # Every feasible value satisfies own^2 <= allowance^2 -
                    # min(other^2).  The right hand side is rounded outward
                    # upward, so clipping is an outer (never excluding) step.
                    bound = _binary(allowance2, other.square().lo, "-", ROUND_CEILING)
                    if bound < 0:
                        return None, f"containment:{self.labels[i]}"
                    cap = Interval.sqrt_nonnegative(bound).hi
                    old = coords[own_index]
                    clipped_lo, clipped_hi = max(old.lo, -cap), min(old.hi, cap)
                    if clipped_lo > clipped_hi:
                        return None, f"containment:{self.labels[i]}"
                    clipped = Interval(clipped_lo, clipped_hi)
                    if clipped != old:
                        coords[own_index] = clipped
                        changed = True
            if self.hc4 and max(c.width for c in coords) <= D("0.5"):
                tangent, reason = self._containment_tangent_contract(Box(tuple(coords), current.orders, current.angles, current.directions))
                if reason is not None:
                    return None, reason
                if tangent.coords != tuple(coords):
                    coords = list(tangent.coords)
                    changed = True
            current = Box(tuple(coords), current.orders, current.angles, current.directions)
            radial, reason = self._radial_lower_contract(current)
            if reason is not None:
                return None, reason
            if radial != current:
                current = radial
                changed = True
            if self.directional:
                directed, reason = self._propagate_directions(current)
                if reason is not None:
                    return None, reason
                if directed != current:
                    current = directed
                    changed = True
            forced, reason = self.forced_separation(current)
            if reason is not None:
                return None, reason
            if forced is not None:
                current = forced
                changed = True
            if not changed:
                break
        return current, self.discard_reason(current)

    def _containment_tangent_contract(self, box: Box) -> tuple[Box, str | None]:
        """HC4-style safe contraction for ||p_i||^2 <= (rho-r_i)^2.

        Convexity gives the necessary tangent inequality
        2*m dot p - ||m||^2 <= A^2 for every feasible p, where m is the
        current box midpoint and A=rho-r_i.  Intersecting this half-space with
        the coordinate box is an outer contraction; no contact assumption is
        involved.
        """
        coords = list(box.coords)
        changed = False
        for i, radius in enumerate(self.radii):
            xdim, ydim = 2 * i, 2 * i + 1
            mx, my = coords[xdim].midpoint, coords[ydim].midpoint
            allowance = _binary(self.rho, radius.lo, "-", ROUND_CEILING)
            rhs = _binary(allowance, allowance, "*", ROUND_CEILING)
            rhs = _binary(rhs, _binary(mx, mx, "*", ROUND_CEILING), "+", ROUND_CEILING)
            rhs = _binary(rhs, _binary(my, my, "*", ROUND_CEILING), "+", ROUND_CEILING)
            for dim, coefficient, other_dim in ((xdim, _binary(mx, D(2), "*", ROUND_FLOOR), ydim),
                                                 (ydim, _binary(my, D(2), "*", ROUND_FLOOR), xdim)):
                if coefficient == 0:
                    continue
                other_coefficient = _binary((my if dim == xdim else mx), D(2), "*", ROUND_FLOOR)
                other = Interval.point(other_coefficient) * coords[other_dim]
                if coefficient > 0:
                    bound = _directed_divide(_binary(rhs, other.lo, "-", ROUND_FLOOR), coefficient, ROUND_FLOOR)
                    new_hi = min(coords[dim].hi, bound)
                    if coords[dim].lo > new_hi:
                        return box, f"containment:{self.labels[i]}"
                    new_interval = Interval(coords[dim].lo, new_hi)
                else:
                    bound = _directed_divide(_binary(rhs, other.lo, "-", ROUND_FLOOR), coefficient, ROUND_CEILING)
                    new_lo = max(coords[dim].lo, bound)
                    if new_lo > coords[dim].hi:
                        return box, f"containment:{self.labels[i]}"
                    new_interval = Interval(new_lo, coords[dim].hi)
                if new_interval != coords[dim]:
                    coords[dim] = new_interval
                    changed = True
        return (Box(tuple(coords), box.orders, box.angles, box.directions) if changed else box), None

    def _radial_lower(self, index: int) -> Decimal:
        """Necessary lower bound on |centre_i| from every other disk."""
        lower = D(0)
        for j in range(self.n):
            if j == index:
                continue
            candidate = _binary(
                self.radii[index].lo,
                _binary(self.radii[j].lo, D(2), "*", ROUND_FLOOR),
                "+", ROUND_FLOOR,
            )
            candidate = _binary(candidate, self.rho, "-", ROUND_FLOOR)
            if candidate > lower:
                lower = candidate
        return lower

    def _radial_lower_discard(self, box: Box) -> str | None:
        for i in range(self.n):
            lower = self._radial_lower(i)
            if lower <= 0:
                continue
            x, y = box.coords[2 * i : 2 * i + 2]
            max_norm2 = _binary(x.square().hi, y.square().hi, "+", ROUND_CEILING)
            required2 = _binary(lower, lower, "*", ROUND_FLOOR)
            if max_norm2 < required2:
                return f"radial-lower:{self.labels[i]}"
        return None

    def _radial_lower_contract(self, box: Box) -> tuple[Box, str | None]:
        """Contract one-sided coordinates against |x|^2+|y|^2 >= lower^2."""
        coords = list(box.coords)
        changed = False
        for i in range(self.n):
            lower = self._radial_lower(i)
            if lower <= 0:
                continue
            required2 = _binary(lower, lower, "*", ROUND_FLOOR)
            xi, yi = 2 * i, 2 * i + 1
            x, y = coords[xi], coords[yi]
            max_norm2 = _binary(x.square().hi, y.square().hi, "+", ROUND_CEILING)
            if max_norm2 < required2:
                return box, f"radial-lower:{self.labels[i]}"
            for own, other in ((xi, y), (yi, x)):
                coord = coords[own]
                if coord.lo < 0 < coord.hi:
                    continue
                residual = _binary(required2, other.square().hi, "-", ROUND_FLOOR)
                if residual <= 0:
                    continue
                cap = Interval.sqrt_nonnegative(residual).lo
                if coord.lo >= 0:
                    new_coord = Interval(max(coord.lo, cap), coord.hi)
                else:
                    new_coord = Interval(coord.lo, min(coord.hi, -cap))
                if new_coord.lo > new_coord.hi:
                    return box, f"radial-lower:{self.labels[i]}"
                if new_coord != coord:
                    coords[own] = new_coord
                    changed = True
        return (Box(tuple(coords), box.orders, box.angles, box.directions) if changed else box), None

    def _cross_interval(self, box: Box, anchor: int, left: int, right: int) -> Interval:
        """Interval cross product around one anchor centre."""
        ax, ay = box.coords[2 * anchor : 2 * anchor + 2]
        lx, ly = box.coords[2 * left : 2 * left + 2]
        rx, ry = box.coords[2 * right : 2 * right + 2]
        return (lx - ax) * (ry - ay) - (ly - ay) * (rx - ax)

    def _angular_discard(self, box: Box) -> str | None:
        for fact in box.angles:
            cross = self._cross_interval(box, fact.anchor, fact.left, fact.right)
            if fact.positive and cross.hi < 0:
                return f"angular:{fact.anchor}-{fact.left}-{fact.right}:positive"
            if not fact.positive and cross.lo > 0:
                return f"angular:{fact.anchor}-{fact.left}-{fact.right}:negative"
        return None

    def best_angular_separation(self, box: Box) -> AngularSeparation | None:
        if not self.angular_order:
            return None
        anchor = self.n - 1
        facts = {(fact.anchor, fact.left, fact.right) for fact in box.angles}
        candidates: list[tuple[Decimal, AngularSeparation]] = []
        for left in range(self.n):
            if left == anchor:
                continue
            for right in range(left + 1, self.n):
                if right == anchor or (anchor, left, right) in facts:
                    continue
                cross = self._cross_interval(box, anchor, left, right)
                if cross.lo < 0 < cross.hi:
                    # Prefer a nearly resolved sign interval.  This is only a
                    # branching heuristic; both signs remain exhaustive.
                    width = cross.width
                    positive = box.with_angle(anchor, left, right, True)
                    negative = box.with_angle(anchor, left, right, False)
                    candidates.append((width, AngularSeparation(anchor, left, right, positive, negative)))
        return min(candidates, key=lambda item: item[0])[1] if candidates else None

    def _propagate_orders(self, box: Box) -> tuple[Box | None, str | None]:
        """Run difference-constraint propagation and strengthen known orders.

        An order is created only after a complete sign split of a pair-distance
        constraint.  Given its sign, the pair inequality yields a sharpened
        lower bound for that coordinate difference as the other coordinate
        interval narrows.  Iterating these two cheap operations preserves the
        correlation that a plain rectangle representation would lose.
        """
        current = box
        for _ in range(30):
            coords = list(current.coords)
            changed = False
            # Transitive closure of lower bounds x_a-x_b >= t.  The dimension
            # is at most 20, so a tiny Floyd-Warshall pass is cheaper and much
            # stronger than retaining only the direct branch facts.
            count = len(coords)
            closure: list[list[Decimal | None]] = [[None] * count for _ in range(count)]
            for i in range(count):
                closure[i][i] = D(0)
            for order in current.orders:
                if order.left % 2 != order.right % 2:
                    return None, f"order-shape:{order.left}-{order.right}"
                old = closure[order.left][order.right]
                if old is None or order.threshold > old:
                    closure[order.left][order.right] = order.threshold
            for pivot in range(count):
                for left in range(count):
                    if closure[left][pivot] is None:
                        continue
                    for right in range(count):
                        if closure[pivot][right] is None:
                            continue
                        implied = _binary(closure[left][pivot], closure[pivot][right], "+", ROUND_FLOOR)
                        old = closure[left][right]
                        if old is None or implied > old:
                            closure[left][right] = implied
            for i in range(count):
                if closure[i][i] is not None and closure[i][i] > 0:
                    return None, f"order-cycle:{i}"
            for left in range(count):
                for right in range(count):
                    threshold = closure[left][right]
                    if threshold is None or left == right:
                        continue
                    a, b = coords[left], coords[right]
                    new_a_lo = max(a.lo, _binary(b.lo, threshold, "+", ROUND_FLOOR))
                    new_b_hi = min(b.hi, _binary(a.hi, threshold, "-", ROUND_CEILING))
                    if new_a_lo > a.hi or b.lo > new_b_hi:
                        return None, f"order:{left}-{right}"
                    if new_a_lo != a.lo:
                        coords[left] = Interval(new_a_lo, a.hi)
                        changed = True
                    if new_b_hi != b.hi:
                        coords[right] = Interval(b.lo, new_b_hi)
                        changed = True
            current = Box(tuple(coords), current.orders, current.angles, current.directions)

            strengthened = current
            for order in current.orders:
                i, j = order.left // 2, order.right // 2
                axis = order.left % 2
                if axis != order.right % 2 or i == j:
                    return None, f"order-shape:{order.left}-{order.right}"
                required = (self.radii[i] + self.radii[j]).square().lo
                other = (current.coords[2 * i + (1 - axis)] - current.coords[2 * j + (1 - axis)]).square().hi
                residual = _binary(required, other, "-", ROUND_FLOOR)
                if residual > 0:
                    threshold = Interval.sqrt_nonnegative(residual).lo
                    if threshold > order.threshold:
                        strengthened = strengthened.with_order(order.left, order.right, threshold)
                        changed = True
            current = strengthened
            if not changed:
                return current, None
        return current, None

    def _difference_geq(self, box: Box, left: int, right: int, threshold: Decimal) -> Box | None:
        """Outer-contract the condition coord[left] - coord[right] >= threshold."""
        if box.orders:
            for order in box.orders:
                if order.left == right and order.right == left and order.threshold + threshold > 0:
                    return None
        a, b = box.coords[left], box.coords[right]
        new_a_lo = max(a.lo, _binary(b.lo, threshold, "+", ROUND_FLOOR))
        new_b_hi = min(b.hi, _binary(a.hi, threshold, "-", ROUND_CEILING))
        if new_a_lo > a.hi or b.lo > new_b_hi:
            return None
        coords = list(box.coords)
        coords[left] = Interval(new_a_lo, a.hi)
        coords[right] = Interval(b.lo, new_b_hi)
        result = Box(tuple(coords), box.orders, box.angles, box.directions)
        return result.with_order(left, right, threshold) if self.order_propagation else result

    def _separation_options(self, box: Box, i: int, j: int, axis: int) -> tuple[Decimal, Box | None, Box | None] | None:
        """Return the two outer boxes for the sign cases forced by one pair."""
        required = (self.radii[i] + self.radii[j]).square().lo
        left = 2 * i + axis
        right = 2 * j + axis
        other = (box.coords[2 * i + (1 - axis)] - box.coords[2 * j + (1 - axis)]).square().hi
        residual = _binary(required, other, "-", ROUND_FLOOR)
        if residual <= 0:
            return None
        threshold = Interval.sqrt_nonnegative(residual).lo
        if threshold <= 0:
            return None
        return (
            threshold,
            self._difference_geq(box, left, right, threshold),
            self._difference_geq(box, right, left, threshold),
        )

    def _direction_geq(self, box: Box, i: int, j: int, ux: Decimal, uy: Decimal,
                       threshold: Decimal) -> Box | None:
        coeffs = {2 * i: ux, 2 * i + 1: uy, 2 * j: -ux, 2 * j + 1: -uy}
        coords = list(box.coords)
        for dim, coefficient in coeffs.items():
            if coefficient == 0:
                continue
            others = Interval.point(0)
            for other_dim, value in enumerate(coords):
                if other_dim != dim:
                    c = coeffs.get(other_dim, D(0))
                    if c != 0:
                        others = others + Interval.point(c) * value
            remainder = _binary(threshold, others.hi, "-", ROUND_FLOOR)
            if coefficient > 0:
                bound = _directed_divide(remainder, coefficient, ROUND_FLOOR)
                new_lo = max(coords[dim].lo, bound)
                if new_lo > coords[dim].hi:
                    return None
                coords[dim] = Interval(new_lo, coords[dim].hi)
            else:
                bound = _directed_divide(remainder, coefficient, ROUND_CEILING)
                new_hi = min(coords[dim].hi, bound)
                if coords[dim].lo > new_hi:
                    return None
                coords[dim] = Interval(coords[dim].lo, new_hi)
        return Box(tuple(coords), box.orders, box.angles, box.directions).with_direction(
            DirectionFact(i, j, ux, uy, threshold))

    def _direction_options(self, box: Box, i: int, j: int, slope: int):
        dx = box.coords[2 * i] - box.coords[2 * j]
        dy = box.coords[2 * i + 1] - box.coords[2 * j + 1]
        perpendicular = Interval.point(-slope) * dx + dy
        bmax = max(abs(perpendicular.lo), abs(perpendicular.hi))
        required = (self.radii[i] + self.radii[j]).square().lo
        scale = D(1 + slope * slope)
        residual = _binary(_binary(scale, required, "*", ROUND_FLOOR),
                           _binary(bmax, bmax, "*", ROUND_CEILING), "-", ROUND_FLOOR)
        if residual <= 0:
            return None
        threshold = Interval.sqrt_nonnegative(residual).lo
        positive = self._direction_geq(box, i, j, D(1), D(slope), threshold)
        negative = self._direction_geq(box, i, j, D(-1), D(-slope), threshold)
        return threshold, D(1), D(slope), positive, negative

    def best_directional_separation(self, box: Box):
        if not self.directional:
            return None
        best = None
        for i in range(self.n):
            for j in range(i):
                for slope in (1, 2):
                    options = self._direction_options(box, i, j, slope)
                    if options is None:
                        continue
                    threshold, ux, uy, positive, negative = options
                    if positive is None or negative is None:
                        continue
                    gain = sum(c.width for c in box.coords) - max(
                        sum(c.width for c in positive.coords), sum(c.width for c in negative.coords))
                    if gain > 0 and (best is None or gain > best[0]):
                        best = (gain, (i, j, ux, uy, threshold, positive, negative))
        return None if best is None else best[1]

    def _propagate_directions(self, box: Box):
        current = box
        for _ in range(12):
            changed = False
            for fact in current.directions:
                contracted = self._direction_geq(current, fact.i, fact.j, fact.ux, fact.uy, fact.threshold)
                if contracted is None:
                    return None, f"direction:{fact.i}-{fact.j}"
                if contracted != current:
                    current = contracted
                    changed = True
            if not changed:
                return current, None
        return current, None

    def forced_separation(self, box: Box) -> tuple[Box | None, str | None]:
        """Propagate a sign-disjunction when exactly one of its cases remains."""
        best: tuple[Decimal, Box] | None = None
        for i in range(self.n):
            for j in range(i):
                for axis in (0, 1):
                    options = self._separation_options(box, i, j, axis)
                    if options is None:
                        continue
                    _, positive, negative = options
                    if positive is None and negative is None:
                        return None, f"separation:{self.labels[j]}-{self.labels[i]}:{'xy'[axis]}"
                    if (positive is None) == (negative is None):
                        continue
                    forced = positive if positive is not None else negative
                    assert forced is not None
                    left, right = 2 * i + axis, 2 * j + axis
                    gain = (box.coords[left].width + box.coords[right].width
                            - forced.coords[left].width - forced.coords[right].width)
                    if gain > 0 and (best is None or gain > best[0]):
                        best = (gain, forced)
        return (None, None) if best is None else (best[1], None)

    def best_separation(self, box: Box) -> Separation | None:
        """Find a complete, useful sign-disjunction implied by non-overlap.

        If the maximum possible separation on the other axis is insufficient,
        non-overlap forces either x_i-x_j >= t or its reverse (and likewise
        for y).  The threshold is rounded *down*, hence both contracted boxes
        still cover every feasible point in the parent box.
        """
        best: tuple[Decimal, Separation] | None = None
        for i in range(self.n):
            for j in range(i):
                for axis in (0, 1):
                    options = self._separation_options(box, i, j, axis)
                    if options is None:
                        continue
                    threshold, positive, negative = options
                    if positive is None or negative is None:
                        continue
                    left, right = 2 * i + axis, 2 * j + axis
                    original_width = box.coords[left].width + box.coords[right].width
                    branch_width = max(
                        positive.coords[left].width + positive.coords[right].width,
                        negative.coords[left].width + negative.coords[right].width,
                    )
                    gain = original_width - branch_width
                    if gain <= 0:
                        continue
                    candidate = Separation(i, j, axis, threshold, positive, negative)
                    if best is None or gain > best[0]:
                        best = (gain, candidate)
        return None if best is None else best[1]

    @staticmethod
    def reason_is_valid(reason: str, recomputed: str | None) -> bool:
        return reason == recomputed

    def choose_split(self, box: Box) -> int:
        candidates = []
        for dim, coord in enumerate(box.coords):
            if coord.lo == coord.hi:
                continue
            score = coord.width
            if self.split_mode == "radius-weighted":
                score = _binary(score, self.radii[dim // 2].lo, "*", ROUND_FLOOR)
            elif self.split_mode == "radius-balanced":
                # Preserve the successful large-disk bias without starving a
                # small rattler once it is the only broad coordinate left.
                # Its largest/smallest factor ratio is about 2.08 here,
                # instead of about 3.16 for pure r weighting.
                factor = _binary(D(1), self.radii[dim // 2].lo, "+", ROUND_FLOOR)
                score = _binary(score, factor, "*", ROUND_FLOOR)
            candidates.append((score, dim))
        if not candidates:
            raise ValueError("box is a point but no constraint discarded it")
        # Ties go to larger circles, which are at later coordinate indices.
        return max(candidates)[1]
