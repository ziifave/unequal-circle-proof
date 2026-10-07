# MPFI proof-kernel prototype

This directory contains the first MPFI-backed replay kernel for the lower
bound. MPFI provides interval arithmetic on top of MPFR's correctly rounded
multiple-precision arithmetic.

Install the system packages `libmpfi-dev`, `libmpfr-dev`, and `libgmp-dev`,
then build with:

```bash
cc -O2 -std=c11 -DN=7 -DSTART=4 radial_partition_replay.c \
  -lmpfi -lmpfr -lgmp \
  -o fixed_order_replay
gzip -dc ../certificates/fixed-order-radial-partition7-mpfi-7.9.dat.gz | \
  ./fixed_order_replay -
```

The Python script only converts JSON to a simple input format. The interval
geometry, angle bounds, and strict Farkas comparison are evaluated in C using
MPFI. `build_certificate.py` consumes MPFI's angle dump and only uses SciPy to
discover multipliers; the emitted decimal certificate is accepted only after
the C replay passes. The radial-partition replay checks 46080 boxes at
`rho=7.9`; the Krawczyk upper-bound kernel remains a separate migration
step.
