"""Persistent Hamiltonian-cycle bookkeeping for angular branch-and-bound.

The state is deliberately independent of interval construction.  Its only
inputs are certified lower bounds for unordered pair angles.  Consequently,
it can be used as a proof-safe acceleration layer: child edge weights may only
increase, and a cycle marked dead can never become live again.
"""
from __future__ import annotations

from dataclasses import dataclass
from decimal import Decimal, ROUND_FLOOR
from itertools import permutations

from .interval import D, _binary


def canonical_cycles(labels: tuple[int, ...]) -> tuple[tuple[int, ...], ...]:
    """All labeled cycles, modulo rotation and reversal."""
    root = labels[0]
    result = []
    for tail in permutations(labels[1:]):
        if tail[0] < tail[-1]:
            result.append((root,) + tail)
    return tuple(result)


def canonical_cycle_count(n: int) -> int:
    """Number of labeled cycles modulo rotation and reversal."""
    if n < 3:
        return 0
    # Fix the first label for rotation and choose one orientation from each
    # reversal pair.
    result = 1
    for value in range(2, n):
        result *= value
    return result // 2


def iter_canonical_cycles(labels: tuple[int, ...]):
    """Lazy canonical-cycle iterator, useful for n=9 and n=10."""
    root = labels[0]
    for tail in permutations(labels[1:]):
        if tail[0] < tail[-1]:
            yield (root,) + tail


def cycle_edges(cycle: tuple[int, ...]) -> tuple[tuple[int, int], ...]:
    return tuple((min(a, b), max(a, b))
                 for a, b in zip(cycle, cycle[1:] + cycle[:1]))


@dataclass(frozen=True, slots=True)
class CycleState:
    cycles: tuple[tuple[int, ...], ...]
    sums: tuple[Decimal, ...]
    alive: tuple[bool, ...]

    @classmethod
    def from_weights(
        cls,
        cycles: tuple[tuple[int, ...], ...],
        weights: dict[tuple[int, int], Decimal],
        threshold: Decimal,
    ) -> "CycleState":
        sums = tuple(
            _sum_floor((weights[e] for e in cycle_edges(cycle)))
            for cycle in cycles
        )
        return cls(cycles, sums, tuple(value <= threshold for value in sums))

    def update(
        self,
        old_weights: dict[tuple[int, int], Decimal],
        new_weights: dict[tuple[int, int], Decimal],
        threshold: Decimal,
    ) -> "CycleState":
        """Update cycle sums from certified monotone child edge bounds."""
        sums = list(self.sums)
        for index, cycle in enumerate(self.cycles):
            if not self.alive[index]:
                continue
            value = sums[index]
            for edge in cycle_edges(cycle):
                old = old_weights[edge]
                new = new_weights[edge]
                if new < old:
                    raise ValueError("child angle bound decreased")
                delta = _binary(new, old, "-", ROUND_FLOOR)
                value = _binary(value, delta, "+", ROUND_FLOOR)
            sums[index] = value
        return CycleState(self.cycles, tuple(sums),
                          tuple(value <= threshold for value in sums))

    def all_dead(self) -> bool:
        return not any(self.alive)


def _sum_floor(values) -> Decimal:
    total = D(0)
    for value in values:
        total = _binary(total, value, "+", ROUND_FLOOR)
    return total
