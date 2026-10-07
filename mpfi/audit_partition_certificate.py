"""Independent structural audit for a radial-partition certificate.

This does not evaluate the MPFI inequalities.  It checks the certificate's
record count, order representatives, box multiplicity, and radial coverage
using an independent Decimal implementation.
"""
from __future__ import annotations

import argparse
import gzip
import itertools
from collections import defaultdict
from decimal import Decimal, getcontext
from pathlib import Path


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("certificate", type=Path)
    ap.add_argument("--rho", required=True)
    ap.add_argument("--start", type=int, required=True)
    ap.add_argument("--n", type=int, required=True)
    ap.add_argument("--split", type=int, default=2)
    args = ap.parse_args()
    getcontext().prec = 100
    opener = gzip.open if args.certificate.suffix == ".gz" else open
    groups = defaultdict(list)
    with opener(args.certificate, "rt") as stream:
        header = stream.readline().split()
        expected_cells = ((args.n - 1) // 2)  # overwritten below
        expected_orders = set()
        for tail in itertools.permutations(range(args.start + 1,
                                                  args.start + args.n)):
            if tail[0] < tail[-1]:
                expected_orders.add((args.start,) + tail)
        expected_cells = len(expected_orders) * args.split ** args.n
        assert header == ["RHO", args.rho, str(expected_cells)], header
        records = 0
        for line in stream:
            tokens = line.split()
            assert tokens[0] == "CELL"
            assert len(tokens) == 1 + args.n + 2 * args.n + args.n * (args.n - 1)
            order = tuple(map(int, tokens[1:1 + args.n]))
            bounds = list(map(Decimal, tokens[1 + args.n:1 + 3 * args.n]))
            groups[order].append(bounds)
            records += 1
    assert records == expected_cells
    assert set(groups) == expected_orders
    assert all(len(cells) == args.split ** args.n
               for cells in groups.values())
    radii = {i: Decimal(i).sqrt() for i in range(args.start, args.start + args.n)}
    rho = Decimal(args.rho)
    base = {}
    for i in radii:
        lower = max([Decimal(0)] + [radii[i] + 2 * radii[j] - rho
                                    for j in radii if j != i])
        base[i] = (lower, rho - radii[i])
    first = groups[next(iter(groups))]
    intervals = {i: set() for i in radii}
    for bounds in first:
        for k, i in enumerate(radii):
            intervals[i].add((bounds[2 * k], bounds[2 * k + 1]))
    for i in radii:
        parts = sorted(intervals[i])
        assert len(parts) == args.split
        assert parts[0][0] <= base[i][0] and parts[-1][1] >= base[i][1]
        assert all(parts[k][1] >= parts[k + 1][0]
                   for k in range(len(parts) - 1))
    assert all(cells == first for cells in groups.values())
    print(f"independent structural audit: PASSED; records={records} "
          f"orders={len(groups)} cells/order={args.split ** args.n}")


if __name__ == "__main__":
    main()
