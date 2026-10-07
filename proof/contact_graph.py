"""Explicit contact-graph data for local active-structure certificates.

This module is intentionally separate from ``PackingModel``.  A contact graph
is a hypothesis about a candidate optimum, not a necessary condition for an
arbitrary feasible packing and therefore must not be used by the global
UNSAT contractor.
"""
from __future__ import annotations

from dataclasses import dataclass


@dataclass(frozen=True, slots=True)
class ContactGraph:
    disks: tuple[int, ...]
    wall_contacts: tuple[int, ...]
    pair_contacts: tuple[tuple[int, int], ...]

    def __post_init__(self) -> None:
        available = set(self.disks)
        if not set(self.wall_contacts) <= available:
            raise ValueError("wall contact outside graph disks")
        normalized = tuple(tuple(sorted(pair)) for pair in self.pair_contacts)
        if any(i == j or i not in available or j not in available for i, j in normalized):
            raise ValueError("invalid pair contact")
        if len(set(normalized)) != len(normalized):
            raise ValueError("duplicate pair contact")
        object.__setattr__(self, "pair_contacts", normalized)

    @property
    def edges(self) -> tuple[tuple[int, int], ...]:
        return tuple((i, 0) for i in self.wall_contacts) + self.pair_contacts

    def is_connected(self) -> bool:
        seen = {0}
        changed = True
        while changed:
            changed = False
            for a, b in self.edges:
                if a in seen and b not in seen:
                    seen.add(b); changed = True
                if b in seen and a not in seen:
                    seen.add(a); changed = True
        return seen >= set(self.disks)

    def is_isostatic_count(self) -> bool:
        return len(self.edges) == 2 * len(self.disks)

    def graph_signature(self) -> tuple[tuple[int, ...], tuple[tuple[int, int], ...]]:
        return tuple(sorted(self.wall_contacts)), tuple(sorted(self.pair_contacts))


CORE_CONTACT_GRAPH = ContactGraph(
    disks=(2, 5, 6, 7, 8, 9, 10),
    wall_contacts=(2, 5, 6, 7, 8, 9),
    pair_contacts=((5, 7), (2, 8), (6, 8), (2, 9), (7, 9),
                   (5, 10), (6, 10), (7, 10)),
)
