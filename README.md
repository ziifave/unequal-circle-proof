# Ten unequal circles in a circular container

This repository studies the smallest circle containing ten pairwise disjoint
circles with radii `sqrt(1), sqrt(2), ..., sqrt(10)`. The work is grouped by
the statement each package addresses:

- [Global optimality](problems/packing-ten-unequal-circles-in-a-circle/README.md) proves
  that the minimum container radius is the unique root of the certified angle
  equations. It includes the manuscript, exact certificate replayers, Lean
  development, and the reproducible proof composition.
- [Algebraic identification of the critical radius](problems/ten-circle-critical-radius-algebraic-identification/README.md)
  records the exact polynomial and root-isolation work for a candidate contact
  configuration. This does not by itself prove global optimality.

To replay the global-optimality proof from this repository root:

```bash
cd problems/packing-ten-unequal-circles-in-a-circle
uv run --locked python tools/verify_global_optimality_completion.py
```

Each problem directory has its own README with scope, files, and reproduction
instructions. The project environment and proof files live beside the result
they support; this root README is the navigation page.

## Additional circle-packing files from the supplied ZIP

The ZIP contained a separate family with **integer** disk radii `1, ..., n`;
these are distinct from the `sqrt(1), ..., sqrt(10)` problem above. Its files
are extracted into these directories:

- [Disks of radii 1 to 5](problems/packing-disks-radii-1-to-5-in-a-circle/README.md)
- [Disks of radii 1 to 7](problems/packing-disks-radii-1-to-7-in-a-circle/README.md)
- [Disks of radii 1 to 8](problems/packing-disks-radii-1-to-8-in-a-circle/README.md)
- [Disks of radii 1 to 9](problems/packing-disks-radii-1-to-9-in-a-circle/README.md)
- [Disks of radii 1 to 10](problems/packing-disks-radii-1-to-10-in-a-circle/README.md)
- [15 equal circles: working and progress notes](problems/15-equal-circles-in-a-circle-working-notes/README.md)

Original nested proof-bundle ZIPs are kept alongside their extracted files.
