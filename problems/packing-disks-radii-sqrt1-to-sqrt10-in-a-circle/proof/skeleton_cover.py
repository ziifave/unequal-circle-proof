"""Exact replay of a complete, possibly unresolved, ten-disk sector cover.

The three large-disk cyclic classes come from large_four_certificate. Radial
partitions cover every global radial interval. Each cell/class either has a
checked contradiction or explicitly lists all 4**6 small-disk assignments.
UNKNOWN entries remain open; coverage is not a proof that they are feasible.
All verification arithmetic is integer or Fraction arithmetic.
"""
from __future__ import annotations

import argparse
from fractions import Fraction as Q
from functools import lru_cache
import hashlib
from itertools import combinations, permutations, product
import json
from math import factorial
from pathlib import Path

from .large_four_certificate import (
    RADIUS_UPPER, canonical_cycles, pi_bounds, rational, require,
    verify_certificate as verify_large_four,
)

LABELS = tuple(range(1, 11))
PAIRS = tuple(combinations(LABELS, 2))
SCALE = 10 ** 6
SCHEMA = "ten-disk-skeleton-sector-cover-v1"
CASES_PER_CYCLE = 4 ** 6


def cosine_lower(t: Q) -> Q:
    require(0 <= t <= Q(16, 5), "cosine argument outside certified range")
    # The tail after the negative k=11 term alternates with decreasing
    # magnitudes: t^2/((2k+1)(2k+2)) < 1 for every k>=11.
    return sum(((-1) ** k * t ** (2 * k) / factorial(2 * k)
                for k in range(12)), Q(0))


@lru_cache(maxsize=1)
def pi_ticks() -> tuple[int, int]:
    lo, hi = pi_bounds()
    return (lo.numerator * SCALE // lo.denominator,
            -((-hi.numerator * SCALE) // hi.denominator))


def parse_roots(rows: list) -> dict[int, tuple[Q, Q]]:
    roots = {}
    for row in rows:
        i = row.get("label")
        require(type(i) is int and i in LABELS and i not in roots, "invalid root label")
        lo, hi = rational(row.get("lo")), rational(row.get("hi"))
        require(0 < lo <= hi and lo * lo <= i <= hi * hi, "invalid square-root enclosure")
        roots[i] = lo, hi
    require(set(roots) == set(LABELS), "missing disk radius")
    return roots


def global_radial_bounds(roots: dict) -> dict[int, tuple[Q, Q]]:
    return {i: (max(Q(0), max(roots[i][0] + 2 * roots[j][0] - RADIUS_UPPER
                             for j in LABELS if j != i)),
                RADIUS_UPPER - roots[i][0]) for i in LABELS}


def partition_spec(raw: dict) -> tuple[tuple[int, int], ...]:
    require(isinstance(raw, dict), "invalid radial partition specification")
    result = []
    for key, parts in raw.items():
        require(key in tuple(str(i) for i in LABELS), "invalid partition label")
        require(type(parts) is int and 1 <= parts <= 16, "invalid partition count")
        result.append((int(key), parts))
    return tuple(sorted(result))


def cell_bounds(roots: dict, spec: tuple, index: tuple) -> dict[int, tuple[Q, Q]]:
    require(len(index) == len(spec), "invalid radial cell index")
    result = global_radial_bounds(roots)
    for (label, parts), part in zip(spec, index):
        require(type(part) is int and 0 <= part < parts, "invalid radial cell index")
        lo, hi = result[label]
        step = (hi - lo) / parts
        result[label] = lo + part * step, lo + (part + 1) * step
    return result


def pair_sum_contradiction(bounds: dict, roots: dict) -> tuple[int, int] | None:
    return next(((i, j) for i, j in PAIRS
                 if bounds[i][1] + bounds[j][1] < roots[i][0] + roots[j][0]), None)


def propagate_radial(bounds: dict, roots: dict) -> dict[int, tuple[Q, Q]]:
    # Non-overlap implies s_i+s_j >= r_i+r_j. In particular, placing a
    # large disk near the centre forces every other disk radially outward.
    result = {i: (max(bounds[i][0], max(roots[i][0] + roots[j][0] - bounds[j][1]
                                     for j in LABELS if i != j)), bounds[i][1])
              for i in LABELS}
    require(all(lo <= hi for lo, hi in result.values()), "empty propagated radial interval")
    return result


def cosine_upper(i: int, j: int, bounds: dict, roots: dict) -> Q | None:
    if bounds[i][0] <= 0 or bounds[j][0] <= 0:
        return None
    d = roots[i][0] + roots[j][0]
    return max((a * a + b * b - d * d) / (2 * a * b)
               for a, b in product(bounds[i], bounds[j]))


def verify_angles(raw: list, bounds: dict, roots: dict) -> tuple[tuple[int, ...], ...]:
    require(isinstance(raw, list) and len(raw) == len(PAIRS), "missing angle bounds")
    pi_lo, _ = pi_ticks()
    weights = [[0] * 11 for _ in range(11)]
    for (i, j), tick in zip(PAIRS, raw):
        require(type(tick) is int and 0 <= tick <= pi_lo, "invalid angle tick")
        if tick:
            hi = cosine_upper(i, j, bounds, roots)
            require(hi is not None, "positive angle with an undefined centre direction")
            require(hi <= cosine_lower(Q(tick, SCALE)), f"overstated angle: {i},{j}")
        weights[i][j] = weights[j][i] = tick
    return tuple(tuple(row) for row in weights)


@lru_cache(maxsize=1)
def assignment_masks() -> tuple[tuple[int, ...], ...]:
    return tuple(tuple(sum(1 << k for k, assigned in enumerate(case) if assigned == sector)
                       for sector in range(4)) for case in product(range(4), repeat=6))


def assignment_index(assignment: tuple[int, ...]) -> int:
    require(len(assignment) == 6 and all(type(s) is int and 0 <= s < 4 for s in assignment),
            "invalid sector assignment")
    index = 0
    for sector in assignment:
        index = 4 * index + sector
    return index


def effective_masks(weights: tuple, masks: tuple) -> tuple[int, ...]:
    active = sum(1 << (i - 1) for i in range(1, 7) if any(weights[i]))
    return tuple(mask & active for mask in masks)


def projected_orders(order: tuple, masks: tuple):
    """Exhaust all sector-local orders of disks with nonzero angle bounds.

    Every full order projects to one of these orders. Deleting zero-weight
    disks only relaxes necessary inequalities, so excluding all projections
    excludes every original full order, including centres at the origin.
    """
    groups = [tuple(i for i in range(1, 7) if mask & (1 << (i - 1))) for mask in masks]
    for choices in product(*(permutations(group) for group in groups)):
        yield tuple(i for k in range(4) for i in ((order[k],) + choices[k]))


def full_order_graph(order: tuple, weights: tuple, skeleton: tuple) -> list:
    _, pi_hi = pi_ticks()
    pi_lo, _ = pi_ticks()
    edges = []
    for p, q in combinations(range(len(order)), 2):
        alpha = weights[order[p]][order[q]]
        edges.extend(((q, p, -alpha), (p, q, 2 * pi_hi - alpha)))
    positions = [order.index(i) for i in skeleton]
    edges.extend((positions[k], positions[k + 1], pi_hi) for k in range(3))
    edges.append((positions[3], positions[0], -pi_lo))
    return edges


def verify_pair_distance_witness(witness: dict, order: tuple, weights: tuple,
                                 skeleton: tuple, bounds: dict,
                                 roots: dict) -> None:
    """Replay a radial-box contradiction using an order-implied angle cap."""
    require(isinstance(witness, dict) and witness.get("kind") == "PAIR_DISTANCE",
            "invalid pair-distance witness")
    pair = witness.get("pair")
    require(isinstance(pair, list) and len(pair) == 2
            and all(type(label) is int and label in order for label in pair)
            and pair[0] != pair[1], "invalid pair-distance labels")
    edges = full_order_graph(order, weights, skeleton)
    count = len(order)
    infinity = 10 ** 30
    distance = [[infinity] * count for _ in range(count)]
    for i in range(count):
        distance[i][i] = 0
    for u, v, cap in edges:
        distance[u][v] = min(distance[u][v], cap)
    for k in range(count):
        for i in range(count):
            if distance[i][k] == infinity:
                continue
            for j in range(count):
                if distance[k][j] != infinity:
                    distance[i][j] = min(distance[i][j],
                                         distance[i][k] + distance[k][j])
    require(all(distance[i][i] >= 0 for i in range(count)),
            "pair-distance witness uses an inconsistent angular graph")
    positions = {label: i for i, label in enumerate(order)}
    first, second = pair
    if positions[first] > positions[second]:
        first, second = second, first
    u, v = positions[first], positions[second]
    gap_lower = max(0, -distance[v][u])
    _, pi_upper = pi_ticks()
    period_upper = 2 * pi_upper
    gap_upper = min(period_upper, distance[u][v])
    require(0 <= gap_lower <= gap_upper <= period_upper,
            "invalid directed angular gap interval")
    # The shortest angular separation is at most each directed arc bound.
    short_angle_upper = min(pi_upper, gap_upper, period_upper - gap_lower)
    cosine_lo = max(Q(-1), cosine_lower(Q(short_angle_upper, SCALE)))
    i, j = first, second
    a_lo, a_hi = bounds[i]
    b_lo, b_hi = bounds[j]
    distance_squared_upper = max(
        a * a + b * b - 2 * a * b * cosine_lo
        for a in (a_lo, a_hi) for b in (b_lo, b_hi))
    required_squared_lower = (roots[i][0] + roots[j][0]) ** 2
    require(witness.get("angle_short_upper_ticks") == short_angle_upper,
            "pair-distance angular cap mismatch")
    require(rational(witness.get("max_distance_squared_upper"))
            == distance_squared_upper,
            "pair-distance upper bound mismatch")
    require(distance_squared_upper < required_squared_lower,
            "pair-distance upper bound does not exclude contact")


def verify_order_group(group: dict, skeleton: tuple, masks: tuple, weights: tuple,
                       local_classifier=None, bounds: dict | None = None,
                       roots: dict | None = None) -> bool:
    """Return true for an excluded group, false for a verified angular model."""
    orders = list(projected_orders(skeleton, masks))
    if group.get("kind") == "ALL_ORDERS_EXCLUDED":
        witnesses = group.get("witnesses")
        require(isinstance(witnesses, list) and len(witnesses) == len(orders),
                "missing projected order witness")
        for order, witness in zip(orders, witnesses):
            verify_cycle(full_order_graph(order, weights, skeleton), witness)
        return True
    if group.get("kind") in {"ALL_ORDERS_LOCAL_OR_EXCLUDED", "ALL_ORDERS_CERTIFIED"}:
        witnesses = group.get("witnesses")
        require(isinstance(witnesses, list) and len(witnesses) == len(orders),
                "missing projected order witness")
        for order, witness in zip(orders, witnesses):
            if witness is None:
                require(local_classifier is not None and local_classifier(order),
                        "projected order is neither excluded nor locally certified")
            elif isinstance(witness, dict):
                require(group.get("kind") == "ALL_ORDERS_CERTIFIED"
                        and bounds is not None and roots is not None,
                        "pair-distance witness lacks radial context")
                verify_pair_distance_witness(witness, order, weights, skeleton,
                                             bounds, roots)
            else:
                verify_cycle(full_order_graph(order, weights, skeleton), witness)
        return True
    require(group.get("kind") == "ANGLE_MODEL", "invalid order-group kind")
    order = tuple(group.get("order", []))
    require(order in orders, "angular model order outside its assigned sectors")
    values = group.get("potentials")
    require(isinstance(values, list) and len(values) == len(order)
            and all(type(v) is int for v in values), "invalid angular potentials")
    require(all(values[v] <= values[u] + c for u, v, c in full_order_graph(order, weights, skeleton)),
            "angular model violates a difference constraint")
    return False


def core_order_classes(weights: tuple) -> tuple[tuple[tuple[int, ...], tuple[int, ...]], ...]:
    """All cyclic orders of the seven active-core centres modulo reflection.

    Disk 2 can have zero radial lower bound in the global domain. Its zero
    angle weights then make its assigned sector/order arbitrary, so this
    projection still covers a centre at the origin.
    """
    result = []
    for skeleton in canonical_cycles():
        for assignment in product(range(4), repeat=3):
            groups = [[] for _ in range(4)]
            for label, sector in zip((2, 5, 6), assignment):
                groups[sector].append(label)
            for choices in product(*(permutations(group) for group in groups)):
                order = tuple(label for k in range(4)
                              for label in ((skeleton[k],) + choices[k]))
                result.append((tuple(skeleton), order))
    require(len(result) == 360 and len({order for _, order in result}) == 360,
            "active-core cyclic orders do not form a complete quotient")
    return tuple(result)


@lru_cache(maxsize=1)
def core_order_sector_map() -> dict:
    """Map each core triple of sector choices to its complete order indices."""
    mapping = {}
    for index, (skeleton, order) in enumerate(core_order_classes(())):
        positions = {label: k for k, label in enumerate(order)}
        sectors = []
        for label in (2, 5, 6):
            sector = max(k for k in range(4) if positions[skeleton[k]] < positions[label])
            sectors.append(sector)
        mapping.setdefault((skeleton, tuple(sectors)), []).append(index)
    require(len(mapping) == 3 * 4 ** 3, "active-core sector projection is incomplete")
    return mapping


def verify_core_orders(record: dict, weights: tuple,
                       local_classifier=None) -> dict:
    """Verify every active-core cyclic order; return whether all are impossible."""
    classes = core_order_classes(weights)
    outcomes, cycles, models = (record.get("outcomes"), record.get("cycles"),
                                record.get("models"))
    require(isinstance(outcomes, list) and len(outcomes) == len(classes),
            "incomplete active-core order ledger")
    require(isinstance(cycles, list) and isinstance(models, list),
            "missing active-core order witnesses")
    used_cycles, used_models = set(), set()
    local_models = 0
    closed_orders = []
    for (skeleton, order), outcome in zip(classes, outcomes):
        edges = full_order_graph(order, weights, skeleton)
        require(type(outcome) is int, "invalid active-core order outcome")
        if outcome < 0:
            require(-len(models) <= outcome < 0,
                    "invalid active-core order outcome")
            model_id = -outcome - 1
            model = models[model_id]
            require(model.get("order") == list(order), "active-core model has wrong order")
            potentials = model.get("potentials")
            require(isinstance(potentials, list) and len(potentials) == len(order)
                    and all(type(value) is int for value in potentials),
                    "invalid active-core angular potentials")
            require(all(potentials[v] <= potentials[u] + weight
                        for u, v, weight in edges),
                    "active-core angular model violates a difference constraint")
            used_models.add(model_id)
            if local_classifier is not None and local_classifier(order):
                local_models += 1
                closed_orders.append(True)
            else:
                closed_orders.append(False)
        else:
            require(outcome < len(cycles), "invalid active-core cycle outcome")
            verify_cycle(edges, cycles[outcome])
            used_cycles.add(outcome)
            closed_orders.append(True)
    require(used_cycles == set(range(len(cycles))), "unused active-core cycle witness")
    require(used_models == set(range(len(models))), "unused active-core angular model")
    return {"all_orders_excluded": not models, "all_orders_closed":
            not models or (local_classifier is not None and local_models == len(models)),
            "orders": len(classes), "models": len(models), "cycles": len(cycles),
            "local_models_closed": local_models, "closed_orders": closed_orders}


def core_closed_sector_assignments(cycles: list, core_closed: list[bool],
                                   weights: tuple | None = None) -> int:
    """Count open six-disk sector cases covered by closed core-order classes."""
    order_classes = core_order_classes(())
    sector_map = core_order_sector_map()
    closed = 0
    for record, skeleton in zip(cycles, canonical_cycles()):
        if record.get("kind") != "SECTOR_CASES":
            continue
        outcomes = record.get("outcomes", [])
        require(isinstance(outcomes, list) and len(outcomes) == CASES_PER_CYCLE,
                "incomplete sector ledger for active-core projection")
        fully_closed_masks = {
            tuple(group.get("masks", [])) for group in record.get("order_groups", [])
            if group.get("kind") in {"ALL_ORDERS_EXCLUDED", "ALL_ORDERS_LOCAL_OR_EXCLUDED",
                                      "ALL_ORDERS_CERTIFIED"}
        }
        for masks, outcome in zip(assignment_masks(), outcomes):
            if outcome != -1:
                continue
            if weights is not None and effective_masks(weights, masks) in fully_closed_masks:
                continue
            sectors = tuple(next(k for k, mask in enumerate(masks)
                                 if mask & (1 << (label - 1)))
                            for label in (2, 5, 6))
            indices = sector_map[(tuple(skeleton), sectors)]
            if all(core_closed[index] for index in indices):
                closed += 1
    return closed


def core_order_refinements(weights: tuple) -> dict:
    """Discover witnesses for all cyclic orders of the active seven disks."""
    cycles, models, outcomes = [], [], []
    for skeleton, order in core_order_classes(weights):
        edges = full_order_graph(order, weights, skeleton)
        witness = negative_cycle(len(order), edges)
        if witness is not None:
            verify_cycle(edges, witness)
            outcomes.append(len(cycles))
            cycles.append(list(witness))
            continue
        values = [0] * len(order)
        for _ in order:
            for u, v, bound in edges:
                values[v] = min(values[v], values[u] + bound)
        shift = values[0]
        values = [value - shift for value in values]
        if not all(values[v] <= values[u] + bound for u, v, bound in edges):
            raise ValueError("failed to construct active-core angular model")
        outcomes.append(-len(models) - 1)
        models.append({"order": list(order), "potentials": values})
    return {"outcomes": outcomes, "cycles": cycles, "models": models}


@lru_cache(maxsize=4)
def sector_spans(weights: tuple[tuple[int, ...], ...]) -> dict:
    """Minimum necessary sector span over EVERY order of its assigned disks.

    For a fixed order, the all-pair forward inequalities give a longest-path
    lower bound on its width. Taking the minimum over orders is necessary
    for every arrangement, not an assumption of a convenient contact order.
    """
    active_mask = sum(1 << (i - 1) for i in range(1, 7) if any(weights[i]))
    table = {}
    for a, b in combinations((7, 8, 9, 10), 2):
        cache = {}
        values = []
        for mask in range(64):
            effective = mask & active_mask
            if effective not in cache:
                group = tuple(i for i in range(1, 7) if effective & (1 << (i - 1)))
                best = None
                for inside in permutations(group):
                    order = (a,) + inside + (b,)
                    distances = [0]
                    for q, label in enumerate(order[1:], 1):
                        distances.append(max(distances[p] + weights[order[p]][label]
                                             for p in range(q)))
                    best = distances[-1] if best is None else min(best, distances[-1])
                cache[effective] = best
            values.append(cache[effective])
        # Globally zero-weight vertices can be inserted anywhere without
        # strengthening these angular inequalities; their masks still occur
        # in the complete 4**6 case ledger.
        table[(a, b)] = tuple(values)
    return table


def spans_for_case(order: tuple, masks: tuple, tables: dict) -> tuple[int, ...]:
    return tuple(tables[tuple(sorted((order[k], order[(k + 1) % 4])))][masks[k]]
                 for k in range(4))


def sector_graph(order: tuple, weights: tuple, spans: tuple) -> list[tuple[int, int, int]]:
    """Edges (u,v,c) mean theta[v] <= theta[u] + c/SCALE."""
    pi_lo, pi_hi = pi_ticks()
    edges = []
    for p, q in combinations(range(4), 2):
        alpha = weights[order[p]][order[q]]
        edges.extend(((q, p, -alpha), (p, q, 2 * pi_hi - alpha)))
    for k in range(3):
        edges.extend(((k + 1, k, -spans[k]), (k, k + 1, pi_hi)))
    # Last gap is 2*pi-theta[3]+theta[0]. Its lower/upper bounds
    # use opposite safe endpoints of pi; no equality to rounded pi is used.
    edges.extend(((0, 3, 2 * pi_hi - spans[3]), (3, 0, -pi_lo)))
    return edges


def negative_cycle(count: int, edges: list) -> tuple[int, ...] | None:
    """Certificate discovery only; verification is a separate exact check."""
    distances = [0] * count
    predecessor = [-1] * count
    changed = -1
    for _ in range(count):
        changed = -1
        for index, (u, v, weight) in enumerate(edges):
            candidate = distances[u] + weight
            if candidate < distances[v]:
                distances[v] = candidate
                predecessor[v] = index
                changed = v
        if changed < 0:
            return None
    node = changed
    for _ in range(count):
        require(predecessor[node] >= 0, "broken predecessor chain")
        node = edges[predecessor[node]][0]
    start = node
    cycle = []
    while True:
        edge = predecessor[node]
        cycle.append(edge)
        node = edges[edge][0]
        if node == start:
            return tuple(cycle)
        require(len(cycle) <= count, "cycle extraction failed")


def verify_cycle(edges: list, cycle: list | tuple) -> None:
    require(isinstance(cycle, (list, tuple)) and bool(cycle), "empty cycle")
    require(all(type(i) is int and 0 <= i < len(edges) for i in cycle), "invalid cycle edge")
    chosen = [edges[i] for i in cycle]
    outgoing = {}
    incoming = set()
    for u, v, _ in chosen:
        require(u not in outgoing and v not in incoming, "cycle repeats a vertex")
        outgoing[u] = v
        incoming.add(v)
    require(set(outgoing) == incoming, "edges do not close")
    start = chosen[0][0]
    node = start
    seen = set()
    for _ in chosen:
        require(node not in seen, "disconnected cycles")
        seen.add(node)
        node = outgoing[node]
    require(node == start and len(seen) == len(chosen), "not one simple cycle")
    require(sum(weight for _, _, weight in chosen) < 0, "cycle is not strictly negative")


def verify_angular_cover(cell: dict, bounds: dict, roots: dict,
                         local_classifier=None) -> dict:
    """Replay one angular ledger on bounds derived by a coverage verifier."""
    closed = opened = 0
    order_groups_checked = order_groups_closed = angular_models_verified = 0
    local_order_groups_closed = 0
    pair_distance_models_closed = 0
    cycles = canonical_cycles()
    per_cycle = [{"order": list(order), "closed": 0, "unknown": 0} for order in cycles]
    require(cell.get("kind") == "ANGLE_COVER", "invalid radial-cell kind")
    require(pair_sum_contradiction(bounds, roots) is None, "unexpected inconsistent cell")
    bounds = propagate_radial(bounds, roots)
    weights = verify_angles(cell.get("angles"), bounds, roots)
    records = cell.get("cycles")
    require(isinstance(records, list) and len(records) == 3, "missing cyclic class")
    tables = None
    cell_closed = cell_open = 0
    for c, (order, record) in enumerate(zip(cycles, records)):
        require(record.get("order") == list(order), "wrong cyclic class")
        if record.get("kind") == "CYCLE":
            spans = tuple(weights[order[k]][order[(k + 1) % 4]] for k in range(4))
            verify_cycle(sector_graph(order, weights, spans), record.get("witness"))
            rejected, pending = CASES_PER_CYCLE, 0
        else:
            require(record.get("kind") == "SECTOR_CASES", "invalid cyclic-class kind")
            outcomes, witnesses = record.get("outcomes"), record.get("witnesses")
            require(isinstance(outcomes, list) and len(outcomes) == CASES_PER_CYCLE,
                    "incomplete sector-assignment ledger")
            require(isinstance(witnesses, list), "missing witness pool")
            if tables is None:
                tables = sector_spans(weights)
            cache = set()
            used = set()
            pending_groups = {}
            rejected = pending = 0
            for masks, outcome in zip(assignment_masks(), outcomes):
                require(type(outcome) is int and -1 <= outcome < len(witnesses), "invalid outcome")
                if outcome == -1:
                    pending += 1
                    key = effective_masks(weights, masks)
                    pending_groups[key] = pending_groups.get(key, 0) + 1
                    continue
                used.add(outcome)
                spans = spans_for_case(order, masks, tables)
                key = spans, outcome
                if key not in cache:
                    verify_cycle(sector_graph(order, weights, spans), witnesses[outcome])
                    cache.add(key)
                rejected += 1
            require(used == set(range(len(witnesses))), "unused witness in pool")
            if "order_groups" in record:
                groups = record["order_groups"]
                require(isinstance(groups, list), "invalid order groups")
                seen_groups = set()
                for group in groups:
                    key = tuple(group.get("masks", []))
                    require(key in pending_groups and key not in seen_groups,
                            "invalid or duplicate order group")
                    seen_groups.add(key)
                    excluded = verify_order_group(
                        group, order, key, weights,
                        local_classifier=local_classifier, bounds=bounds, roots=roots)
                    order_groups_checked += 1
                    if excluded:
                        count = pending_groups[key]
                        rejected += count
                        pending -= count
                        order_groups_closed += 1
                        if (group.get("kind") == "ALL_ORDERS_LOCAL_OR_EXCLUDED"
                                or (group.get("kind") == "ALL_ORDERS_CERTIFIED"
                                    and any(witness is None
                                            for witness in group.get("witnesses", [])))):
                            local_order_groups_closed += 1
                        pair_distance_models_closed += sum(
                            isinstance(witness, dict)
                            and witness.get("kind") == "PAIR_DISTANCE"
                            for witness in group.get("witnesses", []))
                    else:
                        angular_models_verified += 1
                require(seen_groups == set(pending_groups), "missing order group")
        closed += rejected
        opened += pending
        cell_closed += rejected
        cell_open += pending
        per_cycle[c]["closed"] += rejected
        per_cycle[c]["unknown"] += pending
    return {"closed_cases": closed, "unknown_cases": opened, "per_cycle": per_cycle,
            "order_groups_checked": order_groups_checked,
            "order_groups_closed": order_groups_closed,
            "local_order_groups_closed": local_order_groups_closed,
            "pair_distance_models_closed": pair_distance_models_closed,
            "angular_models_verified": angular_models_verified}


def verify(data: dict) -> dict:
    require(data.get("schema") == SCHEMA, "unsupported cover schema")
    require(rational(data.get("container_radius_upper")) == RADIUS_UPPER, "wrong radius scope")
    require(data.get("angle_scale") == SCALE, "unsupported angle scale")
    verify_large_four(data.get("large_four_certificate", {}))
    roots = parse_roots(data.get("sqrt_enclosures", []))
    spec = partition_spec(data.get("radial_partitions"))
    expected = set(product(*(range(parts) for _, parts in spec)))
    seen = set()
    cycles = canonical_cycles()
    closed = opened = 0
    order_groups_checked = order_groups_closed = angular_models_verified = 0
    per_cycle = [{"order": list(order), "closed": 0, "unknown": 0} for order in cycles]
    cell_reports = []
    for cell in data.get("cells", []):
        index = tuple(cell.get("index", []))
        require(index in expected and index not in seen, "duplicate or invalid radial cell")
        seen.add(index)
        bounds = cell_bounds(roots, spec, index)
        if cell.get("kind") == "PAIR_SUM":
            pair = tuple(cell.get("pair", []))
            require(pair in PAIRS, "invalid pair-sum witness")
            i, j = pair
            require(bounds[i][1] + bounds[j][1] < roots[i][0] + roots[j][0],
                    "invalid pair-sum contradiction")
            closed += 3 * CASES_PER_CYCLE
            for row in per_cycle:
                row["closed"] += CASES_PER_CYCLE
            cell_reports.append({"index": list(index), "closed": 3 * CASES_PER_CYCLE, "unknown": 0})
            continue
        report = verify_angular_cover(cell, bounds, roots)
        closed += report["closed_cases"]
        opened += report["unknown_cases"]
        order_groups_checked += report["order_groups_checked"]
        order_groups_closed += report["order_groups_closed"]
        angular_models_verified += report["angular_models_verified"]
        for target, source in zip(per_cycle, report["per_cycle"]):
            target["closed"] += source["closed"]
            target["unknown"] += source["unknown"]
        cell_reports.append({"index": list(index), "closed": report["closed_cases"],
                             "unknown": report["unknown_cases"]})
    require(seen == expected, "missing radial cell")
    total = len(expected) * 3 * CASES_PER_CYCLE
    require(closed + opened == total, "coverage accounting mismatch")
    return {"status": "UNKNOWN" if opened else "COMPLETE_EXCLUSION_AT_U",
            "coverage_verified": True, "radial_cells": len(expected),
            "covered_cases": total, "closed_cases": closed, "unknown_cases": opened,
            "per_cycle": per_cycle, "cells": cell_reports,
            "order_groups_checked": order_groups_checked,
            "order_groups_closed": order_groups_closed,
            "angular_models_verified": angular_models_verified,
            "all_leaves_closed": opened == 0, "global_optimality_proved": False}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("certificate", type=Path)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    source = args.certificate.read_bytes()
    report = verify(json.loads(source))
    report["certificate_sha256"] = hashlib.sha256(source).hexdigest()
    report["verifier_sha256"] = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({k: v for k, v in report.items() if k not in ("cells",)}, indent=2))


if __name__ == "__main__":
    main()
