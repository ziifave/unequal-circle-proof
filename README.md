# Circle-packing problems and proof archives

This repository collects manuscripts, certificates, verification code, and
research notes for several problems about packing circles inside a circular
container. The directories below distinguish the problems by their disk radii
and by the claim being studied.

## Ten unequal circles with radii √1 through √10

The main result is the minimum-container-radius problem for ten pairwise
disjoint circles of radii `sqrt(1), sqrt(2), ..., sqrt(10)`.

- [Global optimality proof](problems/packing-ten-unequal-circles-in-a-circle/README.md)
- [Algebraic identification of the critical radius](problems/ten-circle-critical-radius-algebraic-identification/README.md)

To replay the global-optimality proof from the repository root:

```bash
cd problems/packing-ten-unequal-circles-in-a-circle
uv run --locked python tools/verify_global_optimality_completion.py
```

## Integer-radius disks

These are separate minimum-container problems with disk radii `1, ..., n`:

- [Radii 1 through 5](problems/packing-disks-radii-1-to-5-in-a-circle/README.md)
- [Radii 1 through 7](problems/packing-disks-radii-1-to-7-in-a-circle/README.md)
- [Radii 1 through 8](problems/packing-disks-radii-1-to-8-in-a-circle/README.md)
- [Radii 1 through 9](problems/packing-disks-radii-1-to-9-in-a-circle/README.md)
- [Radii 1 through 10](problems/packing-disks-radii-1-to-10-in-a-circle/README.md)

## Fifteen equal circles

- [Working and progress notes](problems/15-equal-circles-in-a-circle-working-notes/README.md) — the included notes do not claim a global-optimality proof.

Each problem directory has its own README with the contents and scope. The
original nested proof-bundle ZIPs are kept beside their extracted files.
