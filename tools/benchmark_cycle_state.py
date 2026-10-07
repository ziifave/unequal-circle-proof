"""Measure persistent cycle-state size and update cost for n=8,9,10."""
from __future__ import annotations

import argparse
import time
from decimal import Decimal

from proof.cycle_state import (
    CycleState,
    canonical_cycle_count,
    canonical_cycles,
    iter_canonical_cycles,
)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--n", type=int, choices=(8, 9, 10), default=9)
    parser.add_argument("--materialize", action="store_true",
                        help="materialize all cycles; otherwise only count")
    args = parser.parse_args()
    labels = tuple(range(1, args.n + 1))
    expected = canonical_cycle_count(args.n)
    start = time.perf_counter()
    if args.materialize:
        cycles = canonical_cycles(labels)
        observed = len(cycles)
    else:
        observed = sum(1 for _ in iter_canonical_cycles(labels))
        cycles = ()
    elapsed = time.perf_counter() - start
    if observed != expected:
        raise SystemExit(f"count mismatch: expected {expected}, got {observed}")
    result = {
        "n": args.n,
        "expected_cycles": expected,
        "observed_cycles": observed,
        "materialized": args.materialize,
        "seconds": elapsed,
    }
    if args.materialize:
        edges = {(min(a, b), max(a, b)): Decimal("0.1")
                 for a in labels for b in labels if a < b}
        state = CycleState.from_weights(cycles, edges, Decimal("100"))
        result["state_entries"] = len(state.sums)
        result["alive_entries"] = sum(state.alive)
    print(result)


if __name__ == "__main__":
    main()
