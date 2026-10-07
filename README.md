# Certified lower bound for ten unequal circles

This repository contains the minimal artifacts for the current lower-bound
certificate for packing circles of radii `sqrt(1), ..., sqrt(10)` in a circle.

The checked result is conditional on the directed-decimal interval
implementation:

```text
7.9 <= R* <= 8.303468122111490
```

The lower bound uses only circles `{4,5,6,7,8,9,10}`. Each of the 360 cyclic
orders is combined with a 2^7 partition of the radial intervals, giving
46,080 radial boxes. Every box has an all-pair angular Farkas certificate.

## Replay

Requirements: a C compiler, MPFI/MPFR/GMP development packages, Python 3.12+,
and `uv`.

```bash
cc -O2 -std=c11 -DN=7 -DSTART=4 mpfi/radial_partition_replay.c \
  -lmpfi -lmpfr -lgmp \
  -o fixed_order_replay
gzip -dc certificates/fixed-order-radial-partition7-mpfi-7.9.dat.gz | \
  ./fixed_order_replay -
```

The PDF is [paper/main.pdf](paper/main.pdf), with source in
[paper/main.tex](paper/main.tex).

## Upper-witness replay

The upper-witness supplement contains the refined seven-circle core, the full
Krawczyk box/image/preconditioner data, and all 41 inactive squared-slack lower
bounds. The replay scripts can regenerate/check these reports with:

```bash
PYTHONPATH=. uv run -- python tools/verify_active_core.py
PYTHONPATH=. uv run -- python tools/validate_upper_witness.py
```

The Krawczyk result is a local active-core certificate; together with the
positive slack report it certifies the displayed feasible witness, not global
optimality.

The optional wall-angle certificate discovery tool requires the `discovery`
extra; its SciPy-free verifier does not:

```bash
uv run --extra discovery python tools/wall_angle_certificate.py \
  --wall-set 5,6,7,8,9,10 --output wall-cert.json
PYTHONPATH=. uv run python tools/verify_wall_angle_certificate.py wall-cert.json
```

The upper-level support-label branch-and-bound ledger is described in
[SUPPORT_LABEL_BNB.md](SUPPORT_LABEL_BNB.md). It rejects only certified
necessary-condition failures and records all unresolved leaves for later
interval geometry; floating-point non-discovery is never treated as rejection.

This repository does not claim the upper bound is optimal; proving
`R*=8.303468...` remains open.
